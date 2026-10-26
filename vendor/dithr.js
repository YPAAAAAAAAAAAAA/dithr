/* dithr — pocket dither press.
   Layers, type, and shapes settle into e-paper and color-screen dots.
   idea after @redphx (redphx/dithr); clean-room implementation, no code copied. */
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
  var FONT = '"Noto Serif CJK SC", "Noto Serif", "DejaVu Serif", Georgia, serif';

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
  var plateCtx = plate.getContext("2d", { alpha: false });

  var state = { method: "half", ink: "press", dot: 3, gain: 0.72 };
  var layers = [];
  var selected = 0;
  var plateId = 0;
  var paintMode = false;
  var panelOpen = false;
  var plateDirty = true;
  var texDirty = true;
  var diffDirty = true;
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

  var diffW = 0;
  var diffH = 0;
  var diffPixels = null;
  var frameBuf = null;

  var glCanvas = null;
  var gl = null;
  var vbo = null;
  var glLive = false;
  var glChecked = false;
  var prog = null;
  var srcTex = null;
  var bayerTex = null;
  var loc = {};
  var palFlat = new Float32Array(24);
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
      for (var y = 0; y < size; y++) {
        for (var x = 0; x < size; x++) {
          var v = m[y * size + x];
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

  function bayerAt(x, y) {
    return (bayer8[(y & 7) * 8 + (x & 7)] + 0.5) / 64;
  }

  function paletteUnits() {
    var colors = INKS[0].colors;
    for (var i = 0; i < INKS.length; i++) {
      if (INKS[i].id === state.ink) colors = INKS[i].colors;
    }
    var out = new Array(colors.length);
    for (var c = 0; c < colors.length; c++) {
      out[c] = [colors[c][0] / 255, colors[c][1] / 255, colors[c][2] / 255];
    }
    return out;
  }

  function nearest(r, g, b, pal) {
    var best = pal[0];
    var be = 1e9;
    for (var i = 0; i < pal.length; i++) {
      var p = pal[i];
      var dr = r - p[0];
      var dg = g - p[1];
      var db = b - p[2];
      var e = dr * dr * 0.9 + dg * dg * 1.15 + db * db * 0.75;
      if (p[1] > p[0] + 0.04 && p[1] > p[2] + 0.04 && b > g + 0.02) e += 0.08;
      if (e < be) {
        be = e;
        best = p;
      }
    }
    return best;
  }

  function cellSize() {
    var css = stage.getBoundingClientRect().width;
    if (css < 2) return state.dot;
    return Math.max(1, state.dot * stage.width / css);
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
    if (extra) {
      for (var k in extra) o[k] = extra[k];
    }
    return o;
  }

  function ridge(seed, n) {
    var pts = [[-1.05, 0.42]];
    for (var i = 0; i <= n; i++) {
      var t = -1 + (2 * i) / n;
      var s = Math.sin(i * 1.35 + seed);
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
    for (var i = 0; i < spots.length; i++) {
      var s = spots[i];
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

  function disc(g, x, y, rx, ry) {
    g.beginPath();
    g.save();
    g.translate(x, y);
    g.scale(rx, ry);
    g.arc(0, 0, 1, 0, Math.PI * 2);
    g.restore();
    g.fill();
  }

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
      disc(g, w * 0.22, h * 0.16, w * 0.2, h * 0.035);
      g.globalAlpha = 1;
    }
  }

  function tracePoly(g, pts, hw, hh) {
    g.beginPath();
    g.moveTo(pts[0][0] * hw, pts[0][1] * hh);
    for (var i = 1; i < pts.length; i++) g.lineTo(pts[i][0] * hw, pts[i][1] * hh);
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

  var mask = document.createElement("canvas");
  var maskCtx = mask.getContext("2d", { willReadFrequently: true, alpha: true });

  function solidBlit(g, color, bw, bh, drawFn) {
    var mw = Math.max(2, Math.ceil(bw));
    var mh = Math.max(2, Math.ceil(bh));
    if (mask.width !== mw || mask.height !== mh) {
      mask.width = mw;
      mask.height = mh;
    }
    maskCtx.setTransform(1, 0, 0, 1, 0, 0);
    maskCtx.clearRect(0, 0, mw, mh);
    maskCtx.translate(mw / 2, mh / 2);
    maskCtx.lineJoin = "round";
    maskCtx.miterLimit = 2;
    maskCtx.fillStyle = "#000";
    maskCtx.strokeStyle = "#000";
    drawFn(maskCtx);
    var img = maskCtx.getImageData(0, 0, mw, mh);
    var d = img.data;
    var r = color[0];
    var gc = color[1];
    var b = color[2];
    for (var i = 0; i < d.length; i += 4) {
      if (d[i + 3] > 128) {
        d[i] = r;
        d[i + 1] = gc;
        d[i + 2] = b;
        d[i + 3] = 255;
      } else {
        d[i] = 0;
        d[i + 1] = 0;
        d[i + 2] = 0;
        d[i + 3] = 0;
      }
    }
    maskCtx.putImageData(img, 0, 0);
    var prev = g.imageSmoothingEnabled;
    g.imageSmoothingEnabled = false;
    g.drawImage(mask, Math.round(-mw / 2), Math.round(-mh / 2));
    g.imageSmoothingEnabled = prev;
  }

  function tracked(g, text, x, y, track) {
    if (!text) return 0;
    var widths = [];
    var total = 0;
    for (var i = 0; i < text.length; i++) {
      var w = g.measureText(text.charAt(i)).width;
      widths.push(w);
      total += w;
    }
    if (text.length > 1) total += track * (text.length - 1);
    var pen = x - total / 2;
    for (var n = 0; n < text.length; n++) {
      var cx = pen + widths[n] / 2;
      g.strokeText(text.charAt(n), cx, y);
      g.fillText(text.charAt(n), cx, y);
      pen += widths[n] + track;
    }
    return total;
  }

  function drawText(g, L, hw, hh) {
    var size = Math.max(20, hh * 1.7);
    var track = size * 0.015;
    var text = L.text || "";
    g.textAlign = "center";
    g.textBaseline = "middle";
    g.lineJoin = "round";
    g.miterLimit = 2;
    g.font = "700 " + size + "px " + FONT;
    var width = 0;
    for (var i = 0; i < text.length; i++) width += g.measureText(text.charAt(i)).width;
    if (text.length > 1) width += track * (text.length - 1);
    var limit = hw * 2 * 0.98;
    if (width > limit && width > 0) {
      size = size * (limit / width);
      track = size * 0.015;
      g.font = "700 " + size + "px " + FONT;
      width = limit;
    }
    var anchor = L.align === "left" ? -hw + width / 2 : 0;
    var y = L.sub ? -size * 0.34 : 0;
    var subSize = L.sub ? Math.max(22, size * 0.58) : 0;
    var bw = Math.max(hw * 2, width) + size;
    var bh = size * 2.6 + subSize;
    solidBlit(g, L.fill, bw, bh, function (c) {
      c.font = "700 " + size + "px " + FONT;
      c.textAlign = "center";
      c.textBaseline = "middle";
      c.lineWidth = Math.max(1.4, size * 0.04);
      tracked(c, text, anchor, y, track);
    });
    if (L.sub) {
      var sub = L.sub;
      g.font = "700 " + subSize + "px " + FONT;
      var sw = g.measureText(sub).width;
      var subX = L.align === "left" ? -hw + sw / 2 : 0;
      solidBlit(g, L.subFill || L.fill, bw, bh, function (c) {
        c.font = "700 " + subSize + "px " + FONT;
        c.textAlign = "center";
        c.textBaseline = "middle";
        c.fillText(sub, subX, y + size * 0.82);
      });
    }
  }

  function drawBoat(g, hw, hh) {
    var bw = hw * 2 + 8;
    var bh = hh * 2 + 8;
    solidBlit(g, INK, bw, bh, function (c) {
      c.beginPath();
      c.moveTo(-0.58 * hw, 0.28 * hh);
      c.lineTo(0.66 * hw, 0.28 * hh);
      c.lineTo(0.44 * hw, 0.7 * hh);
      c.lineTo(-0.42 * hw, 0.7 * hh);
      c.closePath();
      c.fill();
      c.fillRect(-0.03 * hw, -0.62 * hh, Math.max(3, hw * 0.07), hh * 0.95);
    });
    solidBlit(g, PAPER, bw, bh, function (c) {
      c.beginPath();
      c.moveTo(0.03 * hw, -0.5 * hh);
      c.lineTo(0.52 * hw, 0.22 * hh);
      c.lineTo(0.03 * hw, 0.22 * hh);
      c.closePath();
      c.fill();
    });
    solidBlit(g, RED, bw, bh, function (c) {
      c.beginPath();
      c.moveTo(-0.03 * hw, -0.22 * hh);
      c.lineTo(-0.4 * hw, 0.22 * hh);
      c.lineTo(-0.03 * hw, 0.22 * hh);
      c.closePath();
      c.fill();
    });
  }

  function drawTram(g, hw, hh) {
    var bw = hw * 2.4 + 8;
    var bh = hh * 2.4 + 8;
    var r = hh * 0.16;
    solidBlit(g, MIST, bw, bh, function (c) {
      c.beginPath();
      c.moveTo(-hw + r, -hh * 0.32);
      c.lineTo(hw - r, -hh * 0.32);
      c.arc(hw - r, -hh * 0.32 + r, r, -Math.PI / 2, 0);
      c.lineTo(hw, hh * 0.62);
      c.lineTo(-hw, hh * 0.62);
      c.lineTo(-hw, -hh * 0.32 + r);
      c.arc(-hw + r, -hh * 0.32 + r, r, Math.PI, Math.PI * 1.5);
      c.closePath();
      c.fill();
    });
    solidBlit(g, AMBER, bw, bh, function (c) {
      var n = 4;
      var gap = hw * 0.08;
      var ww = (hw * 1.72 - gap * (n + 1)) / n;
      for (var i = 0; i < n; i++) {
        c.fillRect(-hw * 0.86 + gap + i * (ww + gap), -hh * 0.08, ww, hh * 0.38);
      }
    });
    solidBlit(g, INK, bw, bh, function (c) {
      c.fillRect(-hw * 1.05, hh * 0.62, hw * 2.1, Math.max(3, hh * 0.1));
    });
    solidBlit(g, RED, bw, bh, function (c) {
      c.fillRect(-hw * 0.15, -hh * 0.48, hw * 0.3, hh * 0.12);
    });
  }

  function drawKite(g, L, hw, hh) {
    var bw = hw * 2 + 8;
    var bh = hh * 4.2 + 8;
    solidBlit(g, L.fill, bw, bh, function (c) {
      c.beginPath();
      c.moveTo(0, -hh);
      c.lineTo(hw * 0.72, -hh * 0.05);
      c.lineTo(0, hh * 0.82);
      c.lineTo(-hw * 0.72, -hh * 0.05);
      c.closePath();
      c.fill();
    });
    solidBlit(g, PAPER, bw, bh, function (c) {
      c.lineWidth = Math.max(1, hh * 0.045);
      c.beginPath();
      c.moveTo(0, -hh);
      c.lineTo(0, hh * 0.82);
      c.moveTo(-hw * 0.72, -hh * 0.05);
      c.lineTo(hw * 0.72, -hh * 0.05);
      c.stroke();
    });
    solidBlit(g, INK, bw, bh, function (c) {
      c.lineWidth = Math.max(1, hh * 0.03);
      c.beginPath();
      c.moveTo(0, hh * 0.82);
      c.quadraticCurveTo(hw * 0.45, hh * 1.25, -hw * 0.05, hh * 1.7);
      c.stroke();
    });
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
    g.strokeStyle = rgb(L.fill);
    g.fillStyle = rgb(L.fill);
    g.lineCap = "round";
    g.lineJoin = "round";
    g.lineWidth = Math.max(1.5, (L.weight || 0.02) * Math.min(w, h));
    var ox = L.x * w;
    var oy = L.y * h;
    var strokes = L.strokes || [];
    for (var s = 0; s < strokes.length; s++) {
      var pts = strokes[s];
      if (!pts.length) continue;
      if (pts.length === 1) {
        g.beginPath();
        g.arc(pts[0].x * w + ox, pts[0].y * h + oy, g.lineWidth * 0.45, 0, Math.PI * 2);
        g.fill();
        continue;
      }
      g.beginPath();
      g.moveTo(pts[0].x * w + ox, pts[0].y * h + oy);
      for (var i = 1; i < pts.length; i++) g.lineTo(pts[i].x * w + ox, pts[i].y * h + oy);
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
    if (L.kind === "ink") {
      drawInk(g, L, w, h);
      return;
    }
    var b = metrics(L, w, h);
    g.save();
    g.translate(b.cx, b.cy);
    g.rotate(L.rot || 0);
    if (L.kind === "ellipse" && L.soft) drawEllipse(g, L, b.hw, b.hh);
    else if (L.kind === "ellipse") {
      solidBlit(g, L.fill, b.hw * 2 + 6, b.hh * 2 + 6, function (c) {
        c.beginPath();
        c.save();
        c.scale(b.hw || 1, b.hh || 1);
        c.arc(0, 0, 1, 0, Math.PI * 2);
        c.restore();
        c.fill();
      });
    } else if (L.kind === "rect") {
      solidBlit(g, L.fill, b.hw * 2 + 4, b.hh * 2 + 4, function (c) {
        c.fillRect(-b.hw, -b.hh, b.hw * 2, b.hh * 2);
      });
    } else if (L.kind === "poly") {
      solidBlit(g, L.fill, b.hw * 2 + 4, b.hh * 2 + 4, function (c) {
        tracePoly(c, L.pts, b.hw, b.hh);
        c.fill();
      });
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
    g.setTransform(1, 0, 0, 1, 0, 0);
    g.fillStyle = rgb(PAPER);
    g.fillRect(0, 0, w, h);
    wash(g, w, h, plateId);
    for (var i = 0; i < layers.length; i++) drawLayer(g, layers[i], w, h);
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
    for (var i = 0, j = pts.length - 1; i < pts.length; j = i++) {
      var yi = pts[i][1] * hh;
      var yj = pts[j][1] * hh;
      var xi = pts[i][0] * hw;
      var xj = pts[j][0] * hw;
      var hit = (yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / ((yj - yi) || 1e-6) + xi;
      if (hit) inside = !inside;
    }
    return inside;
  }

  function hitInk(L, px, py, w, h) {
    var ox = L.x * w;
    var oy = L.y * h;
    var thresh = (L.weight || 0.02) * Math.min(w, h) * 1.6;
    var t2 = thresh * thresh;
    var strokes = L.strokes || [];
    for (var s = 0; s < strokes.length; s++) {
      var pts = strokes[s];
      for (var i = 0; i < pts.length; i++) {
        var dx = pts[i].x * w + ox - px;
        var dy = pts[i].y * h + oy - py;
        if (dx * dx + dy * dy <= t2) return true;
      }
    }
    return false;
  }

  function hits(L, px, py, w, h) {
    if (L.kind === "ink") return hitInk(L, px, py, w, h);
    var loc = toLocal(L, px, py, w, h);
    if (L.kind === "ellipse") {
      var nx = loc.x / (loc.hw || 1);
      var ny = loc.y / (loc.hh || 1);
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
    for (var i = layers.length - 1; i >= 0; i--) {
      if (hits(layers[i], px, py, w, h)) return i;
    }
    return -1;
  }

  function spill(buf, gw, gh, x, y, er, eg, eb) {
    if (x < 0 || y < 0 || x >= gw || y >= gh) return;
    var o = (y * gw + x) * 3;
    buf[o] += er;
    buf[o + 1] += eg;
    buf[o + 2] += eb;
  }

  function runDiffusion() {
    var w = plate.width;
    var h = plate.height;
    var cell = cellSize();
    var gw = Math.max(2, Math.round(w / cell));
    var gh = Math.max(2, Math.round(h / cell));
    var img = plateCtx.getImageData(0, 0, w, h).data;
    var n = gw * gh;
    var buf = new Float32Array(n * 3);
    for (var y = 0; y < gh; y++) {
      var sy = Math.min(h - 1, ((y + 0.5) * h / gh) | 0);
      for (var x = 0; x < gw; x++) {
        var sx = Math.min(w - 1, ((x + 0.5) * w / gw) | 0);
        var i = (sy * w + sx) * 4;
        var o = (y * gw + x) * 3;
        buf[o] = img[i] / 255;
        buf[o + 1] = img[i + 1] / 255;
        buf[o + 2] = img[i + 2] / 255;
      }
    }
    var pal = paletteUnits();
    var out = new Uint8Array(n * 4);
    var atk = state.method === "atk";
    var scale = 0.55 + state.gain * 0.5;
    for (var row = 0; row < gh; row++) {
      var ltr = (row & 1) === 0;
      var x0 = ltr ? 0 : gw - 1;
      var x1 = ltr ? gw : -1;
      var step = ltr ? 1 : -1;
      for (var col = x0; col !== x1; col += step) {
        var o = (row * gw + col) * 3;
        var r = buf[o];
        var gch = buf[o + 1];
        var b = buf[o + 2];
        if (r < -0.35) r = -0.35;
        else if (r > 1.35) r = 1.35;
        if (gch < -0.35) gch = -0.35;
        else if (gch > 1.35) gch = 1.35;
        if (b < -0.35) b = -0.35;
        else if (b > 1.35) b = 1.35;
        var q = nearest(r, gch, b, pal);
        var er = (r - q[0]) * scale;
        var eg = (gch - q[1]) * scale;
        var eb = (b - q[2]) * scale;
        var oi = (row * gw + col) * 4;
        out[oi] = byte(q[0]);
        out[oi + 1] = byte(q[1]);
        out[oi + 2] = byte(q[2]);
        out[oi + 3] = 255;
        if (atk) {
          var s = 1 / 8;
          spill(buf, gw, gh, col + step, row, er * s, eg * s, eb * s);
          spill(buf, gw, gh, col + 2 * step, row, er * s, eg * s, eb * s);
          spill(buf, gw, gh, col - step, row + 1, er * s, eg * s, eb * s);
          spill(buf, gw, gh, col, row + 1, er * s, eg * s, eb * s);
          spill(buf, gw, gh, col + step, row + 1, er * s, eg * s, eb * s);
          spill(buf, gw, gh, col, row + 2, er * s, eg * s, eb * s);
        } else {
          spill(buf, gw, gh, col + step, row, er * 7 / 16, eg * 7 / 16, eb * 7 / 16);
          spill(buf, gw, gh, col - step, row + 1, er * 3 / 16, eg * 3 / 16, eb * 3 / 16);
          spill(buf, gw, gh, col, row + 1, er * 5 / 16, eg * 5 / 16, eb * 5 / 16);
          spill(buf, gw, gh, col + step, row + 1, er * 1 / 16, eg * 1 / 16, eb * 1 / 16);
        }
      }
    }
    diffW = gw;
    diffH = gh;
    diffPixels = out;
  }

  function ensureFrame(w, h) {
    if (!frameBuf || frameBuf.width !== w || frameBuf.height !== h) {
      frameBuf = stageCtx.createImageData(w, h);
    }
    return frameBuf;
  }

  function sampleCell(src, w, h, gx, gy, gw, gh) {
    var sx = Math.min(w - 1, ((gx + 0.5) * w / gw) | 0);
    var sy = Math.min(h - 1, ((gy + 0.5) * h / gh) | 0);
    var i = (sy * w + sx) * 4;
    return [src[i] / 255, src[i + 1] / 255, src[i + 2] / 255];
  }

  function cpuPaint() {
    var w = stage.width;
    var h = stage.height;
    if (w < 2 || h < 2 || plate.width !== w || plate.height !== h) return;
    var src = plateCtx.getImageData(0, 0, w, h).data;
    var image = ensureFrame(w, h);
    var d = image.data;
    var pal = paletteUnits();
    var cell = cellSize();
    var gain = state.gain;
    var mode = state.method;
    if (mode === "floyd" || mode === "atk") {
      if (!diffPixels || diffDirty) runDiffusion();
      var gw = diffW;
      var gh = diffH;
      for (var y = 0; y < h; y++) {
        var gy = Math.min(gh - 1, (y * gh / h) | 0);
        for (var x = 0; x < w; x++) {
          var gx = Math.min(gw - 1, (x * gw / w) | 0);
          var s = (gy * gw + gx) * 4;
          var o = (y * w + x) * 4;
          d[o] = diffPixels[s];
          d[o + 1] = diffPixels[s + 1];
          d[o + 2] = diffPixels[s + 2];
          d[o + 3] = 255;
        }
      }
    } else {
      var gw2 = Math.max(1, Math.round(w / cell));
      var gh2 = Math.max(1, Math.round(h / cell));
      var paper = pal[0];
      var cellInk = new Uint8Array(gw2 * gh2 * 3);
      var cellRad = new Float32Array(gw2 * gh2);
      for (var cy = 0; cy < gh2; cy++) {
        for (var cx = 0; cx < gw2; cx++) {
          var c = sampleCell(src, w, h, cx, cy, gw2, gh2);
          var oi = (cy * gw2 + cx) * 3;
          if (mode === "half") {
            var luma = c[0] * 0.299 + c[1] * 0.587 + c[2] * 0.114;
            var shade = 1 - luma;
            if (shade < 0) shade = 0;
            if (shade > 1) shade = 1;
            var rad = Math.sqrt(shade) * (0.12 + gain * 0.5);
            if (luma < 0.55) rad += (0.55 - luma) * 0.9;
            cellRad[cy * gw2 + cx] = rad;
            var ink = nearest(c[0], c[1], c[2], pal);
            cellInk[oi] = byte(ink[0]);
            cellInk[oi + 1] = byte(ink[1]);
            cellInk[oi + 2] = byte(ink[2]);
          } else {
            var t = bayerAt(cx, cy);
            var pick = nearest(c[0] + (t - 0.5) * gain, c[1] + (t - 0.5) * gain, c[2] + (t - 0.5) * gain, pal);
            cellInk[oi] = byte(pick[0]);
            cellInk[oi + 1] = byte(pick[1]);
            cellInk[oi + 2] = byte(pick[2]);
          }
        }
      }
      var pr = byte(paper[0]);
      var pg = byte(paper[1]);
      var pb = byte(paper[2]);
      for (var y2 = 0; y2 < h; y2++) {
        var gy2 = Math.min(gh2 - 1, (y2 * gh2 / h) | 0);
        var fy = (y2 * gh2 / h) - gy2 - 0.5;
        var row = gy2 * gw2;
        for (var x2 = 0; x2 < w; x2++) {
          var gx2 = Math.min(gw2 - 1, (x2 * gw2 / w) | 0);
          var o2 = (y2 * w + x2) * 4;
          var srcI = (row + gx2) * 3;
          if (mode === "half") {
            var fx = (x2 * gw2 / w) - gx2 - 0.5;
            var rad = cellRad[row + gx2];
            if (fx * fx + fy * fy <= rad * rad) {
              d[o2] = cellInk[srcI];
              d[o2 + 1] = cellInk[srcI + 1];
              d[o2 + 2] = cellInk[srcI + 2];
            } else {
              d[o2] = pr;
              d[o2 + 1] = pg;
              d[o2 + 2] = pb;
            }
          } else {
            d[o2] = cellInk[srcI];
            d[o2 + 1] = cellInk[srcI + 1];
            d[o2 + 2] = cellInk[srcI + 2];
          }
          d[o2 + 3] = 255;
        }
      }
    }
    stageCtx.putImageData(image, 0, 0);
    stage.dataset.engine = "cpu";
  }

  var VERT = "#version 300 es\nin vec2 a;\nout vec2 vUv;\nvoid main(){\n  vUv=a*0.5+0.5;\n  gl_Position=vec4(a,0.0,1.0);\n}\n";
  var FRAG = [
    "#version 300 es",
    "precision highp float;",
    "uniform sampler2D uSrc;",
    "uniform sampler2D uBayer;",
    "uniform vec2 uRes;",
    "uniform float uCell;",
    "uniform float uGain;",
    "uniform int uMode;",
    "uniform int uPalN;",
    "uniform vec3 uPal[8];",
    "in vec2 vUv;",
    "out vec4 o;",
    "vec3 snap(vec3 c){",
    "  vec3 best=uPal[0];",
    "  float be=1e9;",
    "  for(int i=0;i<8;i++){",
    "    float live=i<uPalN?1.0:0.0;",
    "    vec3 d=c-uPal[i];",
    "    float e=dot(d,vec3(0.9,1.15,0.75)*d)+(1.0-live)*1e4;",
    "    float greenInk=step(uPal[i].r+0.04,uPal[i].g)*step(uPal[i].b+0.04,uPal[i].g);",
    "    e+=greenInk*step(c.g+0.02,c.b)*0.08;",
    "    if(e<be){be=e;best=uPal[i];}",
    "  }",
    "  return best;",
    "}",
    "void main(){",
    "  if(uMode==2){o=vec4(texture(uSrc,vUv).rgb,1.0);return;}",
    "  vec2 pix=vUv*uRes;",
    "  float cell=max(uCell,1.0);",
    "  vec2 q=(floor(pix/cell)+0.5)*cell;",
    "  vec3 c=texture(uSrc,q/uRes).rgb;",
    "  if(uMode==1){",
    "    vec2 f=fract(pix/cell)-0.5;",
    "    float luma=dot(c,vec3(0.299,0.587,0.114));",
    "    float shade=clamp(1.0-luma,0.0,1.0);",
    "    float rad=sqrt(shade)*(0.12+uGain*0.5);",
    "    if(luma<0.55) rad+=(0.55-luma)*0.9;",
    "    vec3 ink=snap(c);",
    "    float on=step(length(f),rad);",
    "    o=vec4(mix(uPal[0],ink,on),1.0);",
    "    return;",
    "  }",
    "  vec2 bp=floor(pix/cell);",
    "  float t=texture(uBayer,(mod(bp,8.0)+0.5)/8.0).r;",
    "  o=vec4(snap(clamp(c+(t-0.5)*uGain,0.0,1.0)),1.0);",
    "}"
  ].join("\n");

  function compile(type, src) {
    var sh = gl.createShader(type);
    gl.shaderSource(sh, src);
    gl.compileShader(sh);
    if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS)) {
      gl.deleteShader(sh);
      return null;
    }
    return sh;
  }

  function initGL() {
    glCanvas = document.createElement("canvas");
    gl = glCanvas.getContext("webgl2", {
      alpha: false,
      antialias: false,
      depth: false,
      stencil: false,
      preserveDrawingBuffer: true,
      premultipliedAlpha: false
    });
    if (!gl) return;
    var vs = compile(gl.VERTEX_SHADER, VERT);
    var fs = compile(gl.FRAGMENT_SHADER, FRAG);
    if (!vs || !fs) {
      gl = null;
      return;
    }
    prog = gl.createProgram();
    gl.attachShader(prog, vs);
    gl.attachShader(prog, fs);
    gl.bindAttribLocation(prog, 0, "a");
    gl.linkProgram(prog);
    if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
      gl = null;
      return;
    }
    vbo = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 1, -1, -1, 1, 1, 1]), gl.STATIC_DRAW);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);
    srcTex = gl.createTexture();
    bayerTex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, bayerTex);
    var bytes = new Uint8Array(64);
    for (var i = 0; i < 64; i++) bytes[i] = byte((bayer8[i] + 0.5) / 64);
    gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.R8, 8, 8, 0, gl.RED, gl.UNSIGNED_BYTE, bytes);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
    if (gl.getError() !== gl.NO_ERROR) {
      gl = null;
      return;
    }
    gl.bindTexture(gl.TEXTURE_2D, srcTex);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    loc.src = gl.getUniformLocation(prog, "uSrc");
    loc.bayer = gl.getUniformLocation(prog, "uBayer");
    loc.res = gl.getUniformLocation(prog, "uRes");
    loc.cell = gl.getUniformLocation(prog, "uCell");
    loc.gain = gl.getUniformLocation(prog, "uGain");
    loc.mode = gl.getUniformLocation(prog, "uMode");
    loc.pal = gl.getUniformLocation(prog, "uPal");
    loc.palN = gl.getUniformLocation(prog, "uPalN");
    gl.disable(gl.DEPTH_TEST);
    gl.disable(gl.BLEND);
    glLive = true;
  }

  function modeId() {
    if (state.method === "floyd" || state.method === "atk") return 2;
    if (state.method === "half") return 1;
    return 0;
  }

  function paintGL() {
    if (!glLive || !gl || glCanvas.width < 2) return false;
    if ((state.method === "floyd" || state.method === "atk") && diffDirty) {
      runDiffusion();
      diffDirty = false;
      texDirty = true;
    }
    gl.useProgram(prog);
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);
    gl.viewport(0, 0, glCanvas.width, glCanvas.height);
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, srcTex);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);
    if (texDirty) {
      if (state.method === "floyd" || state.method === "atk") {
        gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, diffW, diffH, 0, gl.RGBA, gl.UNSIGNED_BYTE, diffPixels);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
      } else {
        gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, plate);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
      }
      texDirty = false;
    }
    gl.activeTexture(gl.TEXTURE1);
    gl.bindTexture(gl.TEXTURE_2D, bayerTex);
    var pal = paletteUnits();
    for (var i = 0; i < 8; i++) {
      var p = pal[i < pal.length ? i : pal.length - 1];
      palFlat[i * 3] = p[0];
      palFlat[i * 3 + 1] = p[1];
      palFlat[i * 3 + 2] = p[2];
    }
    gl.uniform1i(loc.src, 0);
    gl.uniform1i(loc.bayer, 1);
    gl.uniform2f(loc.res, glCanvas.width, glCanvas.height);
    gl.uniform1f(loc.cell, cellSize());
    gl.uniform1f(loc.gain, state.gain);
    gl.uniform1i(loc.mode, modeId());
    gl.uniform3fv(loc.pal, palFlat);
    gl.uniform1i(loc.palN, pal.length);
    gl.clearColor(PAPER[0] / 255, PAPER[1] / 255, PAPER[2] / 255, 1);
    gl.clear(gl.COLOR_BUFFER_BIT);
    gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
    stageCtx.imageSmoothingEnabled = false;
    stageCtx.drawImage(glCanvas, 0, 0, stage.width, stage.height);
    stage.dataset.engine = "gl";
    return true;
  }

  function stageHasInk() {
    var w = stage.width;
    var h = stage.height;
    if (w < 8 || h < 8) return false;
    var pts = [[w >> 1, h >> 1], [8, 8], [w - 8, 8], [8, h - 8], [w - 8, h - 8], [w >> 1, 24], [(w * 0.2) | 0, (h * 0.7) | 0]];
    var mn = 9999;
    var mx = 0;
    for (var i = 0; i < pts.length; i++) {
      var p = stageCtx.getImageData(pts[i][0], pts[i][1], 1, 1).data;
      if (p[3] < 200) return false;
      var L = p[0] + p[1] + p[2];
      if (L < mn) mn = L;
      if (L > mx) mx = L;
    }
    return mx - mn > 18;
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

  var saving = false;

  function render() {
    if (stage.width < 2 || plate.width < 2) return;
    if (plateDirty) {
      composite();
      plateDirty = false;
      texDirty = true;
      diffDirty = true;
    }
    var used = false;
    if (glLive) {
      used = paintGL();
      if (used && !glChecked) {
        glChecked = true;
        if (!stageHasInk()) {
          glLive = false;
          used = false;
        }
      }
      if (!used) glLive = false;
    }
    if (!glLive || !used) cpuPaint();
    if (ringOn()) strokeRing();
  }

  function requestRender() {
    if (queued) return;
    queued = true;
    requestAnimationFrame(function () {
      queued = false;
      render();
    });
  }

  function fit() {
    var r = stage.getBoundingClientRect();
    var cssW = r.width;
    var cssH = r.height;
    if (cssW < 2 || cssH < 2) return false;
    var dpr = Math.min(window.devicePixelRatio || 1, 1.5);
    var w = Math.max(2, Math.round(cssW * dpr));
    var h = Math.max(2, Math.round(cssH * dpr));
    if (h > 1000) {
      w = Math.max(2, Math.round(w * 1000 / h));
      h = 1000;
    }
    if (stage.width === w && stage.height === h && plate.width === w) return "same";
    stage.width = w;
    stage.height = h;
    plate.width = w;
    plate.height = h;
    if (glCanvas) {
      glCanvas.width = w;
      glCanvas.height = h;
    }
    plateDirty = true;
    texDirty = true;
    diffDirty = true;
    return "changed";
  }

  function forceSize() {
    stage.width = 390;
    stage.height = 844;
    plate.width = 390;
    plate.height = 844;
    if (glCanvas) {
      glCanvas.width = 390;
      glCanvas.height = 844;
    }
    plateDirty = true;
    texDirty = true;
    diffDirty = true;
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
    for (var i = 0; i < buttons.length; i++) {
      var on = buttons[i].dataset.id === id;
      buttons[i].classList.toggle("on", on);
      buttons[i].setAttribute("aria-pressed", on ? "true" : "false");
    }
  }

  function rebuildLayers() {
    layersEl.textContent = "";
    for (var i = 0; i < layers.length; i++) {
      var b = document.createElement("button");
      b.type = "button";
      b.dataset.i = String(i);
      var label = layers[i].name;
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
    plateId = i;
    loadToken += 1;
    paintMode = false;
    var drawBtn = addsEl.querySelector('[data-id="draw"]');
    if (drawBtn) drawBtn.classList.remove("on");
    toggle.classList.remove("hot");
    var spec = PLATES[i].build();
    layers = spec.layers;
    selected = spec.focus || 0;
    plateDirty = true;
    diffDirty = true;
    texDirty = true;
    mark(platesEl, PLATES[i].id);
    hintColor();
    rebuildLayers();
    if (booted) requestRender();
  }

  function setMethod(id) {
    state.method = id;
    diffDirty = true;
    texDirty = true;
    mark(methodsEl, id);
    requestRender();
  }

  function setInk(id) {
    state.ink = id;
    diffDirty = true;
    mark(inksEl, id);
    requestRender();
  }

  function nextName(base) {
    var n = 1;
    for (var i = 0; i < layers.length; i++) {
      if (layers[i].name.indexOf(base) === 0) n += 1;
    }
    return n === 1 ? base : base + " " + n;
  }

  function addShape(kind) {
    var item;
    if (kind === "disc") {
      var colors = [RED, AMBER, TEAL, GREEN, BROWN];
      item = layer("ellipse", nextName("Disc"), 0.32 + jitter() * 0.36, 0.28 + jitter() * 0.2, 0.2, 0.2, colors[(seq >>> 4) % colors.length]);
    } else if (kind === "block") {
      item = layer("rect", nextName("Block"), 0.3 + jitter() * 0.4, 0.4 + jitter() * 0.15, 0.28, 0.16, BROWN);
    } else if (kind === "sail") {
      item = layer("poly", nextName("Sail"), 0.5, 0.42, 0.28, 0.32, PAPER, {
        pts: [[0, -1], [0.15, 1], [-0.9, 0.7]],
        fill: RED.slice()
      });
      item.fill = RED.slice();
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
    paintMode = on;
    var drawBtn = addsEl.querySelector('[data-id="draw"]');
    if (drawBtn) {
      drawBtn.classList.toggle("on", on);
      drawBtn.setAttribute("aria-pressed", on ? "true" : "false");
    }
    toggle.classList.toggle("hot", on);
  }

  function ensureInk() {
    var ink = null;
    for (var i = 0; i < layers.length; i++) {
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
    if (i < 0 || !layers[i] || layers[i].kind !== "text") {
      i = -1;
      for (var k = layers.length - 1; k >= 0; k--) {
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
    if (selected < 0 || !layers[selected]) return;
    var item = layers.splice(selected, 1)[0];
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
    saving = true;
    render();
    var url;
    try {
      url = stage.toDataURL("image/png");
    } catch (err) {
      url = "";
    }
    saving = false;
    render();
    if (!url) return;
    var a = document.createElement("a");
    a.href = url;
    a.download = "dithr-ink.png";
    document.body.appendChild(a);
    a.click();
    a.remove();
  }

  function swallow(el) {
    var names = ["pointerdown", "pointermove", "pointerup", "pointercancel", "touchstart", "touchmove", "touchend", "mousedown", "wheel"];
    for (var i = 0; i < names.length; i++) {
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
    for (var id in fingers) a.push(fingers[id]);
    return a;
  }

  function onDown(e) {
    if (e.button && e.button !== 0) return;
    try { stage.setPointerCapture(e.pointerId); } catch (err) {}
    var p = pointOf(e);
    fingers[e.pointerId] = p;
    fingerN += 1;
    if (fingerN >= 2) {
      gesture = "pinch";
      stroke = null;
      var pair = pinchPair();
      var dx = pair[1].x - pair[0].x;
      var dy = pair[1].y - pair[0].y;
      var L = layers[selected];
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
      var ink = ensureInk();
      stroke = [{ x: p.x, y: p.y }];
      ink.strokes.push(stroke);
      rebuildLayers();
      plateDirty = true;
    } else {
      gesture = "drag";
      var hit = hitTest(p.x, p.y);
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
    if (!fingers[e.pointerId]) return;
    var p = pointOf(e);
    fingers[e.pointerId] = p;
    if (gesture === "pinch" && fingerN >= 2 && pinchBase && layers[selected]) {
      var pair = pinchPair();
      if (pair.length < 2) return;
      var dx = pair[1].x - pair[0].x;
      var dy = pair[1].y - pair[0].y;
      var dist = Math.sqrt(dx * dx + dy * dy) || 0.0001;
      var k = dist / pinchBase.dist;
      var L = layers[selected];
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
      var last = stroke[stroke.length - 1];
      var ddx = p.x - last.x;
      var ddy = p.y - last.y;
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
    state.gain = (Number(gainEl.value) || 62) / 100;
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
    var adds = [
      { id: "disc", name: "Disc" },
      { id: "block", name: "Block" },
      { id: "sail", name: "Sail" },
      { id: "type", name: "Type" },
      { id: "draw", name: "Draw" }
    ];
    adds.forEach(function (item) {
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
      diffDirty = true;
      requestRender();
    });
    gainEl.addEventListener("input", function () {
      state.gain = (Number(gainEl.value) || 62) / 100;
      diffDirty = true;
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
      fileEl.value = "";
      if (!f) return;
      var url = URL.createObjectURL(f);
      var token = loadToken;
      var img = new Image();
      img.onload = function () {
        URL.revokeObjectURL(url);
        if (token !== loadToken) return;
        var item = layer("photo", nextName("Photo"), 0.5, 0.42, 0.72, 0.72, PAPER, { img: img });
        layers.push(item);
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
    if (!booted) return;
    if (fit() === "changed") requestRender();
  }

  function start() {
    bindUi();
    initGL();
    loadPlate(0);
    var guard = 0;
    function attempt() {
      var sized = fit();
      if (sized === false) {
        guard += 1;
        if (guard < 30) {
          requestAnimationFrame(attempt);
          return;
        }
        forceSize();
      }
      plateDirty = true;
      texDirty = true;
      render();
      booted = true;
      armReady();
      window.addEventListener("resize", onResize);
      if (window.ResizeObserver) new ResizeObserver(onResize).observe(stage);
    }
    attempt();
  }

  start();
})();
