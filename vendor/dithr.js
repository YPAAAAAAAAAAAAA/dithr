/* dithr — pocket dither press.
   Layers, type, and shapes settle into e-paper and color-screen dots.
   2D only: the first plate is drawn on the CPU, then ready() is signaled.
   idea after @redphx (redphx/dithr); clean-room implementation, no code copied.
   House licence: LICENSE.txt */
(function () {
  "use strict";

  var PAPER = [243, 238, 228];
  var MIST = [200, 194, 180];
  var STONE = [168, 162, 152];
  var ASH = [112, 106, 98];
  var AMBER = [224, 160, 32];
  var RED = [196, 69, 44];
  var TEAL = [60, 110, 140];
  var GREEN = [63, 107, 70];
  var BROWN = [110, 78, 56];
  var BLUE = [36, 78, 170];
  var INK = [27, 24, 20];
  var FONT = '"Noto Serif CJK SC", "Noto Serif", Georgia, serif';

  var INKS = [
    { id: "mono", name: "Mono", colors: [PAPER, INK] },
    { id: "gray", name: "Gray", colors: [PAPER, STONE, ASH, INK] },
    { id: "red", name: "Red", colors: [PAPER, RED, INK] },
    { id: "four", name: "Four", colors: [PAPER, AMBER, RED, INK] },
    { id: "press", name: "Press", colors: [PAPER, MIST, AMBER, RED, TEAL, GREEN, BROWN, INK] },
    { id: "spectra", name: "Spectra", colors: [PAPER, AMBER, RED, GREEN, BLUE, INK] }
  ];

  var METHODS = [
    { id: "half", name: "Halftone" },
    { id: "bayer", name: "Bayer" },
    { id: "floyd", name: "Floyd" },
    { id: "atk", name: "Atkinson" }
  ];

  var WORDS = ["QUAY", "INK", "PAPER", "PORT", "港湾", "纸鸢"];

  var stage = document.getElementById("stage");
  var toggle = document.getElementById("toggle");
  var panel = document.getElementById("panel");
  var hint = document.getElementById("hint");
  var methodsEl = document.getElementById("methods");
  var inksEl = document.getElementById("inks");
  var addsEl = document.getElementById("adds");
  var platesEl = document.getElementById("plates");
  var wordsEl = document.getElementById("words");
  var layersEl = document.getElementById("layers");
  var dotEl = document.getElementById("dot");
  var gainEl = document.getElementById("gain");
  var fileEl = document.getElementById("file");
  var stageCtx = stage.getContext("2d", { alpha: false });
  var plate = document.createElement("canvas");
  var plateCtx = plate.getContext("2d", { alpha: true });
  var sample = document.createElement("canvas");
  var sampleCtx = sample.getContext("2d", { alpha: false, willReadFrequently: true });

  var endian = (function () {
    var bytes = new Uint8Array(4);
    var view = new Uint32Array(bytes.buffer);
    view[0] = 0xff030201;
    return bytes[0] === 1 && bytes[1] === 2 && bytes[2] === 3 && bytes[3] === 255;
  })();

  var state = { method: "half", ink: "press", dot: 3, gain: 0.72 };
  var layers = [];
  var selected = 0;
  var plateId = 0;
  var paintMode = false;
  var panelOpen = false;
  var plateDirty = true;
  var gesture = null;
  var fingers = {};
  var fingerN = 0;
  var dragLayer = null;
  var dragDx = 0;
  var dragDy = 0;
  var lastNx = 0;
  var lastNy = 0;
  var pinchBase = null;
  var stroke = null;
  var loadToken = 1;
  var seq = 7;
  var queued = false;
  var readySent = false;
  var booted = false;
  var saving = false;
  var frameBuf = null;
  var frameU32 = null;
  var bayer8 = bayerMatrix(8);

  function clamp(v, a, b) {
    if (v < a) return a;
    if (v > b) return b;
    return v;
  }

  function rgb(c) {
    return "rgb(" + (c[0] | 0) + "," + (c[1] | 0) + "," + (c[2] | 0) + ")";
  }

  function byte(v) {
    var n = Math.round(v * 255);
    if (n < 0) return 0;
    if (n > 255) return 255;
    return n;
  }

  function packColor(c) {
    return (255 << 24) | ((c[2] | 0) << 16) | ((c[1] | 0) << 8) | (c[0] | 0);
  }

  function jitter() {
    seq = (Math.imul(seq, 1664525) + 1013904223) >>> 0;
    return (seq >>> 8) / 16777216;
  }

  function bayerMatrix(n) {
    var m = new Float32Array(1);
    m[0] = 0;
    var size = 1;
    while (size < n) {
      var nsize = size * 2;
      var next = new Float32Array(nsize * nsize);
      var y, x, v;
      for (y = 0; y < size; y++) {
        for (x = 0; x < size; x++) {
          v = m[y * size + x];
          next[y * nsize + x] = 4 * v;
          next[y * nsize + x + size] = 4 * v + 2;
          next[(y + size) * nsize + x] = 4 * v + 3;
          next[(y + size) * nsize + x + size] = 4 * v + 1;
        }
      }
      m = next;
      size = nsize;
    }
    return m;
  }

  function paletteUnits() {
    var colors = INKS[0].colors;
    var i, c;
    for (i = 0; i < INKS.length; i++) {
      if (INKS[i].id === state.ink) colors = INKS[i].colors;
    }
    var out = new Array(colors.length);
    for (c = 0; c < colors.length; c++) {
      out[c] = [colors[c][0] / 255, colors[c][1] / 255, colors[c][2] / 255];
    }
    return out;
  }

  function dist2(r, g, b, p) {
    var dr = r - p[0];
    var dg = g - p[1];
    var db = b - p[2];
    var e = dr * dr * 0.9 + dg * dg * 1.15 + db * db * 0.75;
    if (p[1] > p[0] + 0.04 && p[1] > p[2] + 0.04 && b > g + 0.02) e += 0.08;
    return e;
  }

  function nearestIndex(r, g, b, pal) {
    var best = 0;
    var be = 1e9;
    var i, e;
    for (i = 0; i < pal.length; i++) {
      e = dist2(r, g, b, pal[i]);
      if (e < be) {
        be = e;
        best = i;
      }
    }
    return best;
  }

  function dotIndex(r, g, b, pal) {
    var best = 0;
    var alt = pal.length > 1 ? 1 : 0;
    var be = 1e9;
    var ae = 1e9;
    var i, e;
    for (i = 0; i < pal.length; i++) {
      e = dist2(r, g, b, pal[i]);
      if (e < be) {
        ae = be;
        alt = best;
        be = e;
        best = i;
      } else if (e < ae) {
        ae = e;
        alt = i;
      }
    }
    if (best === 0) return alt;
    return best;
  }

  function layer(kind, name, x, y, sx, sy, fill, extra) {
    var o = {
      kind: kind,
      name: name,
      x: x,
      y: y,
      sx: sx,
      sy: sy,
      rot: 0,
      fill: (fill || INK).slice(),
      text: "",
      sub: ""
    };
    var k;
    if (extra) {
      for (k in extra) o[k] = extra[k];
    }
    return o;
  }

  function ridge(seed, n) {
    var pts = [[-1.05, 0.42]];
    var i, t, s;
    for (i = 0; i <= n; i++) {
      t = -1 + (2 * i) / n;
      s = Math.sin(i * 1.35 + seed);
      pts.push([t, -0.05 - 0.9 * s * s]);
    }
    pts.push([1.05, 0.42]);
    return pts;
  }

  function buildQuay() {
    return {
      focus: 4,
      layers: [
        layer("ellipse", "Sun", 0.8, 0.22, 0.32, 0.32, AMBER, { soft: true, core: [255, 246, 220] }),
        layer("poly", "Far hill", 0.5, 0.44, 2.55, 0.36, TEAL, { pts: ridge(1.2, 6) }),
        layer("poly", "Near hill", 0.36, 0.54, 2.55, 0.32, INK, { pts: ridge(2.3, 5) }),
        layer("rect", "Pier", 0.16, 0.78, 0.038, 0.28, BROWN),
        layer("boat", "Boat", 0.64, 0.74, 0.48, 0.28, INK),
        layer("text", "Title", 0.42, 0.08, 0.78, 0.22, INK, { text: "QUAY", sub: "港湾", subFill: RED.slice(), align: "left" })
      ]
    };
  }

  function buildOrchard() {
    var spots = [
      [0.3, 0.4, 0.2, RED],
      [0.5, 0.32, 0.16, AMBER],
      [0.68, 0.42, 0.22, GREEN],
      [0.4, 0.52, 0.14, BROWN],
      [0.74, 0.56, 0.13, RED]
    ];
    var list = [layer("rect", "Trunk", 0.5, 0.72, 0.055, 0.38, BROWN)];
    var i, s;
    for (i = 0; i < spots.length; i++) {
      s = spots[i];
      list.push(layer("ellipse", "Fruit", s[0], s[1], s[2], s[2], s[3]));
    }
    list.push(layer("text", "Title", 0.5, 0.12, 0.9, 0.26, INK, { text: "ORCHARD", sub: "果园", subFill: GREEN.slice(), align: "left" }));
    return { focus: 2, layers: list };
  }

  function buildNight() {
    return {
      focus: 1,
      layers: [
        layer("ellipse", "Moon", 0.78, 0.16, 0.16, 0.16, PAPER),
        layer("tram", "Tram", 0.5, 0.62, 0.8, 0.42, MIST),
        layer("rect", "Post", 0.16, 0.6, 0.028, 0.3, INK),
        layer("ellipse", "Lamp", 0.16, 0.42, 0.11, 0.11, AMBER, { soft: true, core: [255, 236, 190] }),
        layer("text", "Title", 0.46, 0.16, 0.84, 0.26, PAPER, { text: "NIGHT", sub: "夜车", subFill: AMBER.slice(), align: "left" })
      ]
    };
  }

  function buildKite() {
    return {
      focus: 0,
      layers: [
        layer("kite", "Red kite", 0.36, 0.38, 0.28, 0.36, RED),
        layer("kite", "Amber kite", 0.7, 0.3, 0.22, 0.28, AMBER),
        layer("kite", "Teal kite", 0.56, 0.54, 0.2, 0.26, TEAL),
        layer("text", "Title", 0.46, 0.12, 0.8, 0.26, INK, { text: "KITE", sub: "纸鸢", subFill: RED.slice(), align: "left" })
      ]
    };
  }

  var PLATES = [
    { id: "quay", name: "Quay", build: buildQuay },
    { id: "orchard", name: "Orchard", build: buildOrchard },
    { id: "night", name: "Night", build: buildNight },
    { id: "kite", name: "Kite", build: buildKite }
  ];

  function wash(g, w, h, id) {
    var sky = g.createLinearGradient(0, 0, 0, h);
    if (id === 1) {
      sky.addColorStop(0, "#e5f0cf");
      sky.addColorStop(0.42, "#f4efe4");
      sky.addColorStop(0.72, "#e7d7b0");
      sky.addColorStop(1, "#4e7c4a");
    } else if (id === 2) {
      sky.addColorStop(0, "#121820");
      sky.addColorStop(0.42, "#1a2838");
      sky.addColorStop(0.72, "#14181e");
      sky.addColorStop(1, "#100e0c");
    } else if (id === 3) {
      sky.addColorStop(0, "#8eb6ce");
      sky.addColorStop(0.5, "#e7eef2");
      sky.addColorStop(0.78, "#f3eee4");
      sky.addColorStop(1, "#4e7c4a");
    } else {
      sky.addColorStop(0, "#f7e2c4");
      sky.addColorStop(0.34, "#f0c2ae");
      sky.addColorStop(0.62, "#e7b89a");
      sky.addColorStop(1, "#f3e6d4");
    }
    g.fillStyle = sky;
    g.fillRect(0, 0, w, h);
    if (id === 0) {
      var water = g.createLinearGradient(0, h * 0.56, 0, h);
      water.addColorStop(0, "#4e7c96");
      water.addColorStop(0.45, "#5d8ea3");
      water.addColorStop(1, "#7f9aab");
      g.fillStyle = water;
      g.fillRect(0, h * 0.56, w, h * 0.44);
      g.globalAlpha = 0.35;
      g.fillStyle = "#fff4e2";
      g.beginPath();
      g.ellipse(w * 0.22, h * 0.16, w * 0.2, h * 0.035, 0, 0, Math.PI * 2);
      g.fill();
      g.globalAlpha = 1;
    }
  }

  function tracePoly(g, pts, hw, hh) {
    g.beginPath();
    g.moveTo(pts[0][0] * hw, pts[0][1] * hh);
    var i;
    for (i = 1; i < pts.length; i++) g.lineTo(pts[i][0] * hw, pts[i][1] * hh);
    g.closePath();
  }

  function drawEllipse(g, L, hw, hh) {
    var rx = hw || 1;
    var ry = hh || 1;
    if (L.soft) {
      var rad = rx > ry ? rx : ry;
      var core = L.core || L.fill;
      var grd = g.createRadialGradient(0, 0, rad * 0.08, 0, 0, rad);
      grd.addColorStop(0, rgb(core));
      grd.addColorStop(0.48, rgb(L.fill));
      grd.addColorStop(1, "rgba(" + L.fill[0] + "," + L.fill[1] + "," + L.fill[2] + ",0)");
      g.fillStyle = grd;
    } else {
      g.fillStyle = rgb(L.fill);
    }
    g.beginPath();
    g.save();
    g.scale(rx, ry);
    g.arc(0, 0, 1, 0, Math.PI * 2);
    g.restore();
    g.fill();
  }

  function tracked(g, text, x, y, track) {
    if (!text) return 0;
    var widths = [];
    var total = 0;
    var i, w, n, cx, pen;
    for (i = 0; i < text.length; i++) {
      w = g.measureText(text.charAt(i)).width;
      widths.push(w);
      total += w;
    }
    if (text.length > 1) total += track * (text.length - 1);
    pen = x - total / 2;
    for (n = 0; n < text.length; n++) {
      cx = pen + widths[n] / 2;
      g.fillText(text.charAt(n), cx, y);
      pen += widths[n] + track;
    }
    return total;
  }

  function drawText(g, L, hw, hh) {
    var size = Math.max(20, hh * 1.7);
    var track = size * 0.015;
    var text = L.text || "";
    var width = 0;
    var i, limit, anchor, y, subSize, sub, sw, subX;
    g.textAlign = "center";
    g.textBaseline = "middle";
    g.font = "700 " + size + "px " + FONT;
    for (i = 0; i < text.length; i++) width += g.measureText(text.charAt(i)).width;
    if (text.length > 1) width += track * (text.length - 1);
    limit = hw * 2 * 0.98;
    if (width > limit && width > 0) {
      size = size * (limit / width);
      track = size * 0.015;
      g.font = "700 " + size + "px " + FONT;
      width = limit;
    }
    anchor = L.align === "left" ? -hw + width / 2 : 0;
    y = L.sub ? -size * 0.34 : 0;
    g.fillStyle = rgb(L.fill);
    tracked(g, text, anchor, y, track);
    if (L.sub) {
      sub = L.sub;
      subSize = Math.max(16, size * 0.58);
      g.font = "700 " + subSize + "px " + FONT;
      g.fillStyle = rgb(L.subFill || L.fill);
      sw = g.measureText(sub).width;
      subX = L.align === "left" ? -hw + sw / 2 : 0;
      g.fillText(sub, subX, y + size * 0.82);
    }
  }

  function drawBoat(g, hw, hh) {
    g.fillStyle = rgb(INK);
    g.beginPath();
    g.moveTo(-0.58 * hw, 0.28 * hh);
    g.lineTo(0.66 * hw, 0.28 * hh);
    g.lineTo(0.44 * hw, 0.7 * hh);
    g.lineTo(-0.42 * hw, 0.7 * hh);
    g.closePath();
    g.fill();
    g.fillRect(-0.03 * hw, -0.62 * hh, Math.max(3, hw * 0.07), hh * 0.95);
    g.fillStyle = rgb(PAPER);
    g.beginPath();
    g.moveTo(0.03 * hw, -0.5 * hh);
    g.lineTo(0.52 * hw, 0.22 * hh);
    g.lineTo(0.03 * hw, 0.22 * hh);
    g.closePath();
    g.fill();
    g.fillStyle = rgb(RED);
    g.beginPath();
    g.moveTo(-0.03 * hw, -0.22 * hh);
    g.lineTo(-0.4 * hw, 0.22 * hh);
    g.lineTo(-0.03 * hw, 0.22 * hh);
    g.closePath();
    g.fill();
  }

  function drawTram(g, hw, hh) {
    var r = hh * 0.16;
    var n = 4;
    var gap = hw * 0.08;
    var ww = (hw * 1.72 - gap * (n + 1)) / n;
    var i;
    g.fillStyle = rgb(MIST);
    g.beginPath();
    g.moveTo(-hw + r, -hh * 0.32);
    g.lineTo(hw - r, -hh * 0.32);
    g.arc(hw - r, -hh * 0.32 + r, r, -Math.PI / 2, 0);
    g.lineTo(hw, hh * 0.62);
    g.lineTo(-hw, hh * 0.62);
    g.lineTo(-hw, -hh * 0.32 + r);
    g.arc(-hw + r, -hh * 0.32 + r, r, Math.PI, Math.PI * 1.5);
    g.closePath();
    g.fill();
    g.fillStyle = rgb(AMBER);
    for (i = 0; i < n; i++) {
      g.fillRect(-hw * 0.86 + gap + i * (ww + gap), -hh * 0.08, ww, hh * 0.38);
    }
    g.fillStyle = rgb(INK);
    g.fillRect(-hw * 1.05, hh * 0.62, hw * 2.1, Math.max(3, hh * 0.1));
    g.fillStyle = rgb(RED);
    g.fillRect(-hw * 0.15, -hh * 0.48, hw * 0.3, hh * 0.12);
  }

  function drawKite(g, L, hw, hh) {
    g.fillStyle = rgb(L.fill);
    g.beginPath();
    g.moveTo(0, -hh);
    g.lineTo(hw * 0.72, -hh * 0.05);
    g.lineTo(0, hh * 0.82);
    g.lineTo(-hw * 0.72, -hh * 0.05);
    g.closePath();
    g.fill();
    g.strokeStyle = rgb(PAPER);
    g.lineWidth = Math.max(1, hh * 0.045);
    g.beginPath();
    g.moveTo(0, -hh);
    g.lineTo(0, hh * 0.82);
    g.moveTo(-hw * 0.72, -hh * 0.05);
    g.lineTo(hw * 0.72, -hh * 0.05);
    g.stroke();
    g.strokeStyle = rgb(INK);
    g.lineWidth = Math.max(1, hh * 0.03);
    g.beginPath();
    g.moveTo(0, hh * 0.82);
    g.quadraticCurveTo(hw * 0.45, hh * 1.25, -hw * 0.05, hh * 1.7);
    g.stroke();
  }

  function drawPhoto(g, L, hw, hh) {
    var img = L.img;
    var iw = img.width || 1;
    var ih = img.height || 1;
    var s = (hw * 2) / iw;
    var s2 = (hh * 2) / ih;
    if (s2 < s) s = s2;
    g.drawImage(img, -iw * s * 0.5, -ih * s * 0.5, iw * s, ih * s);
  }

  function drawInk(g, L, w, h) {
    var ox = L.x * w;
    var oy = L.y * h;
    var strokes = L.strokes || [];
    var s, pts, i, ddx, ddy;
    g.strokeStyle = rgb(L.fill);
    g.fillStyle = rgb(L.fill);
    g.lineCap = "round";
    g.lineJoin = "round";
    g.lineWidth = Math.max(1.5, (L.weight || 0.02) * Math.min(w, h));
    for (s = 0; s < strokes.length; s++) {
      pts = strokes[s];
      if (!pts.length) continue;
      if (pts.length === 1) {
        g.beginPath();
        g.arc(pts[0].x * w + ox, pts[0].y * h + oy, g.lineWidth * 0.45, 0, Math.PI * 2);
        g.fill();
        continue;
      }
      g.beginPath();
      g.moveTo(pts[0].x * w + ox, pts[0].y * h + oy);
      for (i = 1; i < pts.length; i++) g.lineTo(pts[i].x * w + ox, pts[i].y * h + oy);
      g.stroke();
    }
  }

  function metrics(L, w, h) {
    var m = w < h ? w : h;
    return {
      cx: L.x * w,
      cy: L.y * h,
      hw: Math.abs(L.sx) * m * 0.5,
      hh: Math.abs(L.sy) * m * 0.5
    };
  }

  function drawLayer(g, L, w, h) {
    var b;
    if (L.kind === "ink") {
      drawInk(g, L, w, h);
      return;
    }
    if (L.kind === "text") return;
    b = metrics(L, w, h);
    g.save();
    g.translate(b.cx, b.cy);
    g.rotate(L.rot || 0);
    if (L.kind === "ellipse") drawEllipse(g, L, b.hw, b.hh);
    else if (L.kind === "rect") {
      g.fillStyle = rgb(L.fill);
      g.fillRect(-b.hw, -b.hh, b.hw * 2, b.hh * 2);
    } else if (L.kind === "poly") {
      g.fillStyle = rgb(L.fill);
      tracePoly(g, L.pts, b.hw, b.hh);
      g.fill();
    } else if (L.kind === "text") drawText(g, L, b.hw, b.hh);
    else if (L.kind === "boat") drawBoat(g, b.hw, b.hh);
    else if (L.kind === "tram") drawTram(g, b.hw, b.hh);
    else if (L.kind === "kite") drawKite(g, L, b.hw, b.hh);
    else if (L.kind === "photo" && L.img) drawPhoto(g, L, b.hw, b.hh);
    g.restore();
  }

  function composite() {
    var g = plateCtx;
    var w = plate.width;
    var h = plate.height;
    var i;
    g.setTransform(1, 0, 0, 1, 0, 0);
    g.clearRect(0, 0, w, h);
    wash(g, w, h, plateId);
    for (i = 0; i < layers.length; i++) drawLayer(g, layers[i], w, h);
  }

  function toLocal(L, px, py, w, h) {
    var b = metrics(L, w, h);
    var dx = px - b.cx;
    var dy = py - b.cy;
    var c = Math.cos(-(L.rot || 0));
    var s = Math.sin(-(L.rot || 0));
    return { x: dx * c - dy * s, y: dx * s + dy * c, hw: b.hw, hh: b.hh };
  }

  function inPoly(pts, x, y, hw, hh) {
    var inside = false;
    var i, j, yi, yj, xi, xj, hit;
    for (i = 0, j = pts.length - 1; i < pts.length; j = i++) {
      yi = pts[i][1] * hh;
      yj = pts[j][1] * hh;
      xi = pts[i][0] * hw;
      xj = pts[j][0] * hw;
      hit = (yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / ((yj - yi) || 1e-6) + xi;
      if (hit) inside = !inside;
    }
    return inside;
  }

  function hitInk(L, px, py, w, h) {
    var ox = L.x * w;
    var oy = L.y * h;
    var thresh = (L.weight || 0.02) * ((w < h ? w : h)) * 1.6;
    var t2 = thresh * thresh;
    var strokes = L.strokes || [];
    var s, pts, i, dx, dy;
    for (s = 0; s < strokes.length; s++) {
      pts = strokes[s];
      for (i = 0; i < pts.length; i++) {
        dx = pts[i].x * w + ox - px;
        dy = pts[i].y * h + oy - py;
        if (dx * dx + dy * dy <= t2) return true;
      }
    }
    return false;
  }

  function hits(L, px, py, w, h) {
    var loc, nx, ny;
    if (L.kind === "ink") return hitInk(L, px, py, w, h);
    loc = toLocal(L, px, py, w, h);
    if (L.kind === "ellipse") {
      nx = loc.x / (loc.hw || 1);
      ny = loc.y / (loc.hh || 1);
      return nx * nx + ny * ny <= 1;
    }
    if (L.kind === "poly" && L.pts) return inPoly(L.pts, loc.x, loc.y, loc.hw, loc.hh);
    return Math.abs(loc.x) <= loc.hw && Math.abs(loc.y) <= loc.hh;
  }

  function hitTest(nx, ny) {
    var w = plate.width;
    var h = plate.height;
    var px = nx * w;
    var py = ny * h;
    var i;
    for (i = layers.length - 1; i >= 0; i--) {
      if (hits(layers[i], px, py, w, h)) return i;
    }
    return -1;
  }

  function spill(buf, gw, gh, x, y, er, eg, eb) {
    var o;
    if (x < 0 || y < 0 || x >= gw || y >= gh) return;
    o = (y * gw + x) * 3;
    buf[o] += er;
    buf[o + 1] += eg;
    buf[o + 2] += eb;
  }

  function ensureFrame(w, h) {
    if (!frameBuf || frameBuf.width !== w || frameBuf.height !== h) {
      frameBuf = stageCtx.createImageData(w, h);
      frameU32 = endian ? new Uint32Array(frameBuf.data.buffer, frameBuf.data.byteOffset, w * h) : null;
    }
    return frameBuf;
  }

  function dither() {
    var w = stage.width;
    var h = stage.height;
    var cell = state.dot | 0;
    var gw, gh, pal, data, n, idx, rad2, inkAt, i, r, gch, b, luma, shade, rad;
    var gain, mode, atk, scale, buf, outIdx, row, ltr, col, x0, x1, step, o, er, eg, eb, q;
    var image, d, u32, paperPack, packs, y, gyf, gy, fy, fy2, grow, base, x, gxf, gx, fx, ci;
    if (cell < 2) cell = 2;
    if (cell > 12) cell = 12;
    gw = Math.max(2, Math.round(w / cell));
    gh = Math.max(2, Math.round(h / cell));
    if (gw > w) gw = w;
    if (gh > h) gh = h;
    if (sample.width !== gw || sample.height !== gh) {
      sample.width = gw;
      sample.height = gh;
    }
    sampleCtx.setTransform(1, 0, 0, 1, 0, 0);
    sampleCtx.imageSmoothingEnabled = true;
    sampleCtx.drawImage(plate, 0, 0, gw, gh);
    data = sampleCtx.getImageData(0, 0, gw, gh).data;
    pal = paletteUnits();
    n = gw * gh;
    idx = new Uint8Array(n);
    rad2 = new Float32Array(n);
    inkAt = new Uint8Array(n);
    gain = state.gain;
    mode = state.method;
    if (mode === "floyd" || mode === "atk") {
      buf = new Float32Array(n * 3);
      for (i = 0; i < n; i++) {
        buf[i * 3] = data[i * 4] / 255;
        buf[i * 3 + 1] = data[i * 4 + 1] / 255;
        buf[i * 3 + 2] = data[i * 4 + 2] / 255;
      }
      atk = mode === "atk";
      scale = 0.55 + gain * 0.5;
      for (row = 0; row < gh; row++) {
        ltr = (row & 1) === 0;
        x0 = ltr ? 0 : gw - 1;
        x1 = ltr ? gw : -1;
        step = ltr ? 1 : -1;
        for (col = x0; col !== x1; col += step) {
          o = (row * gw + col) * 3;
          r = buf[o];
          gch = buf[o + 1];
          b = buf[o + 2];
          if (r < -0.35) r = -0.35;
          else if (r > 1.35) r = 1.35;
          if (gch < -0.35) gch = -0.35;
          else if (gch > 1.35) gch = 1.35;
          if (b < -0.35) b = -0.35;
          else if (b > 1.35) b = 1.35;
          q = nearestIndex(r, gch, b, pal);
          idx[row * gw + col] = q;
          er = (r - pal[q][0]) * scale;
          eg = (gch - pal[q][1]) * scale;
          eb = (b - pal[q][2]) * scale;
          if (atk) {
            spill(buf, gw, gh, col + step, row, er / 8, eg / 8, eb / 8);
            spill(buf, gw, gh, col + 2 * step, row, er / 8, eg / 8, eb / 8);
            spill(buf, gw, gh, col - step, row + 1, er / 8, eg / 8, eb / 8);
            spill(buf, gw, gh, col, row + 1, er / 8, eg / 8, eb / 8);
            spill(buf, gw, gh, col + step, row + 1, er / 8, eg / 8, eb / 8);
            spill(buf, gw, gh, col, row + 2, er / 8, eg / 8, eb / 8);
          } else {
            spill(buf, gw, gh, col + step, row, er * 7 / 16, eg * 7 / 16, eb * 7 / 16);
            spill(buf, gw, gh, col - step, row + 1, er * 3 / 16, eg * 3 / 16, eb * 3 / 16);
            spill(buf, gw, gh, col, row + 1, er * 5 / 16, eg * 5 / 16, eb * 5 / 16);
            spill(buf, gw, gh, col + step, row + 1, er / 16, eg / 16, eb / 16);
          }
        }
      }
    } else {
      for (i = 0; i < n; i++) {
        r = data[i * 4] / 255;
        gch = data[i * 4 + 1] / 255;
        b = data[i * 4 + 2] / 255;
        if (mode === "half") {
          luma = r * 0.299 + gch * 0.587 + b * 0.114;
          shade = 1 - luma;
          if (shade < 0) shade = 0;
          if (shade > 1) shade = 1;
          rad = Math.sqrt(shade) * (0.12 + gain * 0.5);
          if (luma < 0.55) rad += (0.55 - luma) * 0.9;
          if (rad > 0.75) rad = 0.75;
          if (rad < 0) rad = 0;
          rad2[i] = rad * rad;
          inkAt[i] = dotIndex(r, gch, b, pal);
        } else {
          y = (i / gw) | 0;
          x = i - y * gw;
          rad = (bayer8[(y & 7) * 8 + (x & 7)] + 0.5) / 64;
          idx[i] = nearestIndex(r + (rad - 0.5) * gain, gch + (rad - 0.5) * gain, b + (rad - 0.5) * gain, pal);
        }
      }
    }
    image = ensureFrame(w, h);
    d = image.data;
    u32 = frameU32;
    packs = new Uint32Array(pal.length);
    for (i = 0; i < pal.length; i++) packs[i] = packColor([byte(pal[i][0]), byte(pal[i][1]), byte(pal[i][2])]);
    paperPack = packs[0];
    if (u32) {
      for (y = 0; y < h; y++) {
        gyf = y * gh / h;
        gy = gyf | 0;
        if (gy >= gh) gy = gh - 1;
        fy = gyf - gy - 0.5;
        fy2 = fy * fy;
        grow = gy * gw;
        base = y * w;
        for (x = 0; x < w; x++) {
          gxf = x * gw / w;
          gx = gxf | 0;
          if (gx >= gw) gx = gw - 1;
          ci = grow + gx;
          if (mode === "half") {
            fx = gxf - gx - 0.5;
            u32[base + x] = (fx * fx + fy2 <= rad2[ci]) ? packs[inkAt[ci]] : paperPack;
          } else {
            u32[base + x] = packs[idx[ci]];
          }
        }
      }
    } else {
      for (y = 0; y < h; y++) {
        gyf = y * gh / h;
        gy = gyf | 0;
        if (gy >= gh) gy = gh - 1;
        fy = gyf - gy - 0.5;
        fy2 = fy * fy;
        grow = gy * gw;
        for (x = 0; x < w; x++) {
          gxf = x * gw / w;
          gx = gxf | 0;
          if (gx >= gw) gx = gw - 1;
          ci = grow + gx;
          o = (y * w + x) * 4;
          if (mode === "half") {
            fx = gxf - gx - 0.5;
            q = (fx * fx + fy2 <= rad2[ci]) ? inkAt[ci] : 0;
          } else {
            q = idx[ci];
          }
          d[o] = byte(pal[q][0]);
          d[o + 1] = byte(pal[q][1]);
          d[o + 2] = byte(pal[q][2]);
          d[o + 3] = 255;
        }
      }
    }
    stageCtx.putImageData(image, 0, 0);
    stampType();
  }

  function stampType() {
    var w = stage.width;
    var h = stage.height;
    var i, L, b;
    for (i = 0; i < layers.length; i++) {
      L = layers[i];
      if (L.kind !== "text") continue;
      b = metrics(L, w, h);
      stageCtx.save();
      stageCtx.translate(b.cx, b.cy);
      stageCtx.rotate(L.rot || 0);
      drawText(stageCtx, L, b.hw, b.hh);
      stageCtx.restore();
    }
  }

  function ringOn() {
    return !saving && (panelOpen || gesture) && selected >= 0 && layers[selected] && layers[selected].kind !== "ink" && !paintMode;
  }

  function strokeRing() {
    var L = layers[selected];
    var b = metrics(L, stage.width, stage.height);
    stageCtx.save();
    stageCtx.translate(b.cx, b.cy);
    stageCtx.rotate(L.rot || 0);
    stageCtx.lineWidth = Math.max(3, stage.width / 140);
    stageCtx.strokeStyle = "rgba(27,24,20,0.88)";
    stageCtx.strokeRect(-b.hw, -b.hh, b.hw * 2, b.hh * 2);
    stageCtx.lineWidth = Math.max(1.25, stage.width / 280);
    stageCtx.strokeStyle = "rgba(243,238,228,0.95)";
    stageCtx.strokeRect(-b.hw, -b.hh, b.hw * 2, b.hh * 2);
    stageCtx.restore();
  }

  function fallbackFrame() {
    var w = stage.width;
    var h = stage.height;
    if (w < 2 || h < 2) {
      stage.width = 390;
      stage.height = 844;
      w = 390;
      h = 844;
    }
    stageCtx.setTransform(1, 0, 0, 1, 0, 0);
    stageCtx.fillStyle = rgb(PAPER);
    stageCtx.fillRect(0, 0, w, h);
    stageCtx.fillStyle = rgb(TEAL);
    stageCtx.fillRect(0, h * 0.42, w, h * 0.12);
    stageCtx.fillStyle = rgb(INK);
    stageCtx.fillRect(0, h * 0.54, w, h * 0.1);
    stageCtx.fillStyle = rgb(RED);
    stageCtx.fillRect(w * 0.12, h * 0.08, w * 0.28, h * 0.04);
  }

  function render() {
    if (stage.width < 2 || plate.width < 2) return;
    if (plateDirty) {
      composite();
      plateDirty = false;
    }
    dither();
    if (ringOn()) strokeRing();
  }

  function requestRender() {
    if (queued) return;
    queued = true;
    requestAnimationFrame(function () {
      queued = false;
      try {
        render();
      } catch (err) {
        fallbackFrame();
      }
    });
  }

  function applySize(cssW, cssH) {
    var w = Math.max(2, Math.round(cssW));
    var h = Math.max(2, Math.round(cssH));
    var pixels = w * h;
    var limit = 420000;
    var s;
    if (pixels > limit) {
      s = Math.sqrt(limit / pixels);
      w = Math.max(2, Math.round(w * s));
      h = Math.max(2, Math.round(h * s));
    }
    if (stage.width === w && stage.height === h && plate.width === w && plate.height === h) return "same";
    stage.width = w;
    stage.height = h;
    plate.width = w;
    plate.height = h;
    plateDirty = true;
    return "changed";
  }

  function measure() {
    var r = stage.getBoundingClientRect();
    if (r.width >= 2 && r.height >= 2) return { w: r.width, h: r.height };
    if (stage.clientWidth >= 2 && stage.clientHeight >= 2) return { w: stage.clientWidth, h: stage.clientHeight };
    return null;
  }

  function armReady() {
    var n = 0;
    function tick() {
      if (readySent) return;
      n += 1;
      if (window.__gbSandbox && typeof window.__gbSandbox.ready === "function") {
        readySent = true;
        window.__gbSandbox.ready();
        return;
      }
      if (n < 40) requestAnimationFrame(tick);
    }
    requestAnimationFrame(tick);
  }

  function hintColor() {
    hint.classList.toggle("ink", plateId !== 2);
  }

  function mark(el, id) {
    var buttons = el.querySelectorAll("button");
    var i, on;
    for (i = 0; i < buttons.length; i++) {
      on = buttons[i].dataset.id === id;
      buttons[i].classList.toggle("on", on);
      buttons[i].setAttribute("aria-pressed", on ? "true" : "false");
    }
  }

  function rebuildLayers() {
    var i, b, label;
    layersEl.textContent = "";
    for (i = 0; i < layers.length; i++) {
      b = document.createElement("button");
      b.type = "button";
      b.dataset.i = String(i);
      label = layers[i].name;
      if (layers[i].text) label += " · " + layers[i].text;
      b.textContent = label;
      if (i === selected) b.classList.add("on");
      b.addEventListener("click", (function (idx) {
        return function (e) {
          e.stopPropagation();
          selected = idx;
          rebuildLayers();
          requestRender();
        };
      })(i));
      layersEl.appendChild(b);
    }
  }

  function loadPlate(i) {
    var spec, drawBtn;
    plateId = i;
    loadToken += 1;
    paintMode = false;
    drawBtn = addsEl.querySelector('[data-id="draw"]');
    if (drawBtn) drawBtn.classList.remove("on");
    toggle.classList.remove("hot");
    spec = PLATES[i].build();
    layers = spec.layers;
    selected = spec.focus || 0;
    plateDirty = true;
    mark(platesEl, PLATES[i].id);
    hintColor();
    rebuildLayers();
    if (booted) requestRender();
  }

  function setMethod(id) {
    state.method = id;
    mark(methodsEl, id);
    requestRender();
  }

  function setInk(id) {
    state.ink = id;
    mark(inksEl, id);
    requestRender();
  }

  function nextName(base) {
    var n = 1;
    var i;
    for (i = 0; i < layers.length; i++) {
      if (layers[i].name.indexOf(base) === 0) n += 1;
    }
    return n === 1 ? base : base + " " + n;
  }

  function addShape(kind) {
    var item, colors;
    if (kind === "disc") {
      colors = [RED, AMBER, TEAL, GREEN, BROWN];
      item = layer("ellipse", nextName("Disc"), 0.32 + jitter() * 0.36, 0.28 + jitter() * 0.2, 0.2, 0.2, colors[(seq >>> 4) % colors.length]);
    } else if (kind === "block") {
      item = layer("rect", nextName("Block"), 0.3 + jitter() * 0.4, 0.4 + jitter() * 0.15, 0.28, 0.16, BROWN);
    } else if (kind === "sail") {
      item = layer("poly", nextName("Sail"), 0.5, 0.42, 0.28, 0.32, RED, {
        pts: [[0, -1], [0.15, 1], [-0.9, 0.7]]
      });
    } else if (kind === "type") {
      item = layer("text", nextName("Type"), 0.5, 0.22, 0.6, 0.14, INK, { text: "INK" });
    } else {
      return;
    }
    layers.push(item);
    selected = layers.length - 1;
    plateDirty = true;
    rebuildLayers();
    requestRender();
  }

  function setPaint(on) {
    var drawBtn;
    paintMode = on;
    drawBtn = addsEl.querySelector('[data-id="draw"]');
    if (drawBtn) {
      drawBtn.classList.toggle("on", on);
      drawBtn.setAttribute("aria-pressed", on ? "true" : "false");
    }
    toggle.classList.toggle("hot", on);
  }

  function ensureInk() {
    var ink = null;
    var i;
    for (i = 0; i < layers.length; i++) {
      if (layers[i].kind === "ink") ink = layers[i];
    }
    if (!ink) {
      ink = {
        kind: "ink",
        name: "Ink",
        x: 0,
        y: 0,
        sx: 1,
        sy: 1,
        rot: 0,
        fill: INK.slice(),
        strokes: [],
        weight: 0.02,
        text: "",
        sub: ""
      };
      layers.push(ink);
    }
    selected = layers.indexOf(ink);
    return ink;
  }

  function applyWord(word) {
    var i = selected;
    var k;
    if (i < 0 || !layers[i] || layers[i].kind !== "text") {
      i = -1;
      for (k = layers.length - 1; k >= 0; k--) {
        if (layers[k].kind === "text") {
          i = k;
          break;
        }
      }
    }
    if (i < 0) {
      layers.push(layer("text", nextName("Type"), 0.5, 0.2, 0.62, 0.16, INK, { text: word }));
      selected = layers.length - 1;
    } else {
      layers[i].text = word;
      layers[i].sub = "";
      selected = i;
    }
    plateDirty = true;
    rebuildLayers();
    requestRender();
  }

  function bringFront() {
    var item;
    if (selected < 0 || !layers[selected]) return;
    item = layers.splice(selected, 1)[0];
    layers.push(item);
    selected = layers.length - 1;
    plateDirty = true;
    rebuildLayers();
    requestRender();
  }

  function removeSelected() {
    if (selected < 0 || layers.length < 2) return;
    layers.splice(selected, 1);
    if (selected >= layers.length) selected = layers.length - 1;
    plateDirty = true;
    rebuildLayers();
    requestRender();
  }

  function saveInk() {
    var url, a;
    saving = true;
    try {
      render();
      url = stage.toDataURL("image/png");
    } catch (err) {
      url = "";
    }
    saving = false;
    try { render(); } catch (err2) { fallbackFrame(); }
    if (!url) return;
    a = document.createElement("a");
    a.href = url;
    a.download = "dithr-ink.png";
    document.body.appendChild(a);
    a.click();
    a.remove();
  }

  function swallow(el) {
    var names = ["pointerdown", "pointermove", "pointerup", "pointercancel", "touchstart", "touchmove", "touchend", "mousedown", "wheel"];
    var i;
    for (i = 0; i < names.length; i++) {
      el.addEventListener(names[i], function (e) { e.stopPropagation(); });
    }
  }

  function pointOf(e) {
    var r = stage.getBoundingClientRect();
    var w = r.width || 1;
    var h = r.height || 1;
    return { x: (e.clientX - r.left) / w, y: (e.clientY - r.top) / h };
  }

  function pinchPair() {
    var a = [];
    var id;
    for (id in fingers) a.push(fingers[id]);
    return a;
  }

  function onDown(e) {
    var p, pair, dx, dy, L, ink, hit;
    if (e.button && e.button !== 0) return;
    try { stage.setPointerCapture(e.pointerId); } catch (err) {}
    p = pointOf(e);
    fingers[e.pointerId] = p;
    fingerN += 1;
    if (fingerN >= 2) {
      gesture = "pinch";
      stroke = null;
      pair = pinchPair();
      dx = pair[1].x - pair[0].x;
      dy = pair[1].y - pair[0].y;
      L = layers[selected];
      pinchBase = {
        dist: Math.sqrt(dx * dx + dy * dy) || 0.0001,
        ang: Math.atan2(dy, dx),
        sx: L ? L.sx : 1,
        sy: L ? L.sy : 1,
        rot: L ? L.rot || 0 : 0,
        weight: L && L.weight ? L.weight : 0.02
      };
    } else if (paintMode) {
      gesture = "paint";
      ink = ensureInk();
      stroke = [{ x: p.x, y: p.y }];
      ink.strokes.push(stroke);
      rebuildLayers();
      plateDirty = true;
    } else {
      gesture = "drag";
      hit = hitTest(p.x, p.y);
      if (hit >= 0) {
        selected = hit;
        dragLayer = layers[hit];
        dragDx = dragLayer.x - p.x;
        dragDy = dragLayer.y - p.y;
        lastNx = p.x;
        lastNy = p.y;
        rebuildLayers();
      } else {
        dragLayer = null;
      }
    }
    requestRender();
    e.preventDefault();
  }

  function onMove(e) {
    var p, pair, dx, dy, dist, k, L, last, ddx, ddy;
    if (!fingers[e.pointerId]) return;
    p = pointOf(e);
    fingers[e.pointerId] = p;
    if (gesture === "pinch" && fingerN >= 2 && pinchBase && layers[selected]) {
      pair = pinchPair();
      if (pair.length < 2) return;
      dx = pair[1].x - pair[0].x;
      dy = pair[1].y - pair[0].y;
      dist = Math.sqrt(dx * dx + dy * dy) || 0.0001;
      k = dist / pinchBase.dist;
      L = layers[selected];
      if (L.kind === "ink") {
        L.weight = clamp(pinchBase.weight * k, 0.008, 0.08);
      } else {
        L.sx = clamp(pinchBase.sx * k, 0.04, 1.8);
        L.sy = clamp(pinchBase.sy * k, 0.04, 1.8);
        L.rot = pinchBase.rot + (Math.atan2(dy, dx) - pinchBase.ang);
      }
      plateDirty = true;
      requestRender();
    } else if (gesture === "paint" && stroke) {
      last = stroke[stroke.length - 1];
      ddx = p.x - last.x;
      ddy = p.y - last.y;
      if (ddx * ddx + ddy * ddy > 0.000012) {
        stroke.push({ x: p.x, y: p.y });
        plateDirty = true;
        requestRender();
      }
    } else if (gesture === "drag" && dragLayer) {
      if (dragLayer.kind === "ink") {
        dragLayer.x += p.x - lastNx;
        dragLayer.y += p.y - lastNy;
      } else {
        dragLayer.x = clamp(p.x + dragDx, -0.2, 1.2);
        dragLayer.y = clamp(p.y + dragDy, -0.2, 1.2);
      }
      lastNx = p.x;
      lastNy = p.y;
      plateDirty = true;
      requestRender();
    }
    e.preventDefault();
  }

  function onUp(e) {
    if (!fingers[e.pointerId]) return;
    delete fingers[e.pointerId];
    fingerN = Math.max(0, fingerN - 1);
    if (fingerN === 0) {
      gesture = null;
      dragLayer = null;
      stroke = null;
      pinchBase = null;
      requestRender();
    } else if (fingerN === 1) {
      gesture = paintMode ? "paint" : "drag";
      pinchBase = null;
    }
  }

  function bindUi() {
    state.dot = Number(dotEl.value) || 3;
    state.gain = (Number(gainEl.value) || 72) / 100;
    METHODS.forEach(function (item) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = item.name;
      b.dataset.id = item.id;
      b.addEventListener("click", function (e) {
        e.stopPropagation();
        setMethod(item.id);
      });
      methodsEl.appendChild(b);
    });
    INKS.forEach(function (item) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = item.name;
      b.dataset.id = item.id;
      b.addEventListener("click", function (e) {
        e.stopPropagation();
        setInk(item.id);
      });
      inksEl.appendChild(b);
    });
    [
      { id: "disc", name: "Disc" },
      { id: "block", name: "Block" },
      { id: "sail", name: "Sail" },
      { id: "type", name: "Type" },
      { id: "draw", name: "Draw" }
    ].forEach(function (item) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = item.name;
      b.dataset.id = item.id;
      b.addEventListener("click", function (e) {
        e.stopPropagation();
        if (item.id === "draw") setPaint(!paintMode);
        else addShape(item.id);
      });
      addsEl.appendChild(b);
    });
    PLATES.forEach(function (item, idx) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = item.name;
      b.dataset.id = item.id;
      b.addEventListener("click", function (e) {
        e.stopPropagation();
        loadPlate(idx);
      });
      platesEl.appendChild(b);
    });
    WORDS.forEach(function (word) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = word;
      b.addEventListener("click", function (e) {
        e.stopPropagation();
        applyWord(word);
      });
      wordsEl.appendChild(b);
    });
    mark(methodsEl, state.method);
    mark(inksEl, state.ink);
    mark(platesEl, PLATES[0].id);
    dotEl.addEventListener("input", function () {
      state.dot = Number(dotEl.value) || 3;
      requestRender();
    });
    gainEl.addEventListener("input", function () {
      state.gain = (Number(gainEl.value) || 72) / 100;
      requestRender();
    });
    document.getElementById("front").addEventListener("click", function (e) {
      e.stopPropagation();
      bringFront();
    });
    document.getElementById("drop").addEventListener("click", function (e) {
      e.stopPropagation();
      removeSelected();
    });
    document.getElementById("save").addEventListener("click", function (e) {
      e.stopPropagation();
      saveInk();
    });
    fileEl.addEventListener("change", function () {
      var f = fileEl.files && fileEl.files[0];
      var url, token, img;
      fileEl.value = "";
      if (!f) return;
      url = URL.createObjectURL(f);
      token = loadToken;
      img = new Image();
      img.onload = function () {
        URL.revokeObjectURL(url);
        if (token !== loadToken) return;
        layers.push(layer("photo", nextName("Photo"), 0.5, 0.42, 0.72, 0.72, PAPER, { img: img }));
        selected = layers.length - 1;
        plateDirty = true;
        rebuildLayers();
        requestRender();
      };
      img.onerror = function () { URL.revokeObjectURL(url); };
      img.src = url;
    });
    toggle.addEventListener("click", function (e) {
      e.stopPropagation();
      panelOpen = !panelOpen;
      panel.classList.toggle("open", panelOpen);
      toggle.setAttribute("aria-expanded", panelOpen ? "true" : "false");
      requestRender();
    });
    swallow(toggle);
    swallow(panel);
    stage.addEventListener("pointerdown", onDown);
    stage.addEventListener("pointermove", onMove);
    stage.addEventListener("pointerup", onUp);
    stage.addEventListener("pointercancel", onUp);
    stage.addEventListener("contextmenu", function (e) { e.preventDefault(); });
  }

  function onResize() {
    if (!booted || !readySent) return;
    if (measure() && applySize(measure().w, measure().h) === "changed") requestRender();
  }

  function start() {
    var guard = 0;
    bindUi();
    loadPlate(0);
    function attempt() {
      var box;
      try {
        box = measure();
        if (!box) {
          guard += 1;
          if (guard < 8) {
            requestAnimationFrame(attempt);
            return;
          }
          box = { w: 390, h: 844 };
        }
        applySize(box.w, box.h);
        render();
      } catch (err) {
        try { fallbackFrame(); } catch (err2) {}
      }
      booted = true;
      armReady();
      window.addEventListener("resize", onResize);
      if (window.ResizeObserver) {
        try { new ResizeObserver(onResize).observe(stage); } catch (err3) {}
      }
    }
    attempt();
  }

  start();
})();
