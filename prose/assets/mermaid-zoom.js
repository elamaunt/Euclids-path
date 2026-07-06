/* assets/mermaid-zoom.js
 *
 * Interactive pan + zoom for the navigator map on 00_Overview §3 (and its EN
 * mirror /en/00_Overview/), under Material for MkDocs.
 *
 * WHY A PRE-RENDERED INLINE SVG (not the live mermaid fence):
 *   Material renders a ```mermaid fence into a div whose SVG sits in a CLOSED
 *   shadow root, and its labels are HTML in <foreignObject>. Chrome RASTERISES
 *   foreignObject under a CSS transform, so zooming blurred the edge labels and
 *   the shadow SVG was unreachable for anything better. Instead we ship a
 *   pre-rendered SVG whose labels are native SVG <text> (htmlLabels:false): it
 *   stays razor-crisp at any zoom, lives in the light DOM, and is theme-neutral
 *   (self-contained dark chips + mid-grey edges read on light and dark pages).
 *
 * The page carries <img class="nav-map" src="assets/navigator.<loc>.svg"> — the
 * src is resolved to the correct URL by MkDocs, and the <img> is the graceful
 * fallback (a crisp static image) if this script or the fetch does not run.
 * When it does run, we fetch that SVG, inline it, and drive a self-contained
 * transform pan/zoom (wheel, drag, +/-/reset buttons, keyboard). No library.
 */
(function () {
  "use strict";
  if (typeof window === "undefined") return;

  var GUARD = "mzoom";
  var MIN = 0.15, MAX = 20, BTN = 1.45, WHEEL_BASE = 1.0018;
  var live = [], mo = null;

  function isRu() {
    var l = (document.documentElement.getAttribute("lang") || "en").toLowerCase();
    return l.indexOf("ru") === 0;
  }
  function captionText() {
    return isRu()
      ? "Колесо мыши — масштаб, перетаскивание — панорама; кнопки справа: увеличить, уменьшить, сбросить."
      : "Scroll to zoom, drag to pan; buttons at right: zoom in, zoom out, reset.";
  }
  function labels() {
    return isRu()
      ? { in: "Увеличить", out: "Уменьшить", reset: "Сбросить вид" }
      : { in: "Zoom in", out: "Zoom out", reset: "Reset view" };
  }

  function svgNaturalSize(svg) {
    var w = parseFloat(svg.getAttribute("width"));
    var h = parseFloat(svg.getAttribute("height"));
    if (w && h) return { w: w, h: h };
    var vb = (svg.getAttribute("viewBox") || "").split(/[ ,]+/).map(Number);
    if (vb.length === 4 && vb[2] && vb[3]) return { w: vb[2], h: vb[3] };
    var r = svg.getBoundingClientRect();
    return { w: r.width || 1000, h: r.height || 500 };
  }

  function enhance(img) {
    if (!img || img.dataset[GUARD] === "1") return;
    var src = img.currentSrc || img.getAttribute("src");
    var parent = img.parentNode;
    if (!src || !parent) return;
    img.dataset[GUARD] = "1";

    fetch(src).then(function (r) {
      if (!r.ok) throw new Error("fetch " + r.status);
      return r.text();
    }).then(function (svgText) {
      if (img.dataset[GUARD] !== "1" || !img.parentNode) return; // torn down meanwhile

      var frame = document.createElement("div");
      frame.className = "mzoom-frame";
      frame.setAttribute("tabindex", "0");
      frame.setAttribute("role", "group");
      frame.setAttribute("aria-label", isRu() ? "Интерактивная карта-навигатор" : "Interactive navigator map");

      var inner = document.createElement("div");
      inner.className = "mzoom-inner";
      inner.innerHTML = svgText;
      var svg = inner.querySelector("svg");
      if (!svg) throw new Error("no svg");
      svg.style.display = "block";
      svg.style.maxWidth = "none";
      svg.removeAttribute("style"); // drop any mermaid max-width; keep width/height attrs
      svg.style.display = "block";

      // place the frame where the image was; keep the <img> as hidden fallback source
      parent.insertBefore(frame, img);
      frame.appendChild(inner);
      img.style.display = "none";

      var lbl = labels();
      var nav = document.createElement("div");
      nav.className = "mzoom-nav";
      nav.innerHTML =
        '<button type="button" class="mzoom-btn mzoom-in" title="' + lbl.in + '" aria-label="' + lbl.in + '">+</button>' +
        '<button type="button" class="mzoom-btn mzoom-out" title="' + lbl.out + '" aria-label="' + lbl.out + '">−</button>' +
        '<button type="button" class="mzoom-btn mzoom-reset" title="' + lbl.reset + '" aria-label="' + lbl.reset + '">⤡</button>';
      frame.appendChild(nav);

      var caption = document.createElement("p");
      caption.className = "mzoom-caption";
      caption.textContent = captionText();
      if (frame.nextSibling) parent.insertBefore(caption, frame.nextSibling);
      else parent.appendChild(caption);

      var nat = svgNaturalSize(svg);
      var w0 = nat.w, h0 = nat.h;
      var st = { scale: 1, tx: 0, ty: 0 };
      function apply() {
        inner.style.transform = "translate(" + st.tx + "px," + st.ty + "px) scale(" + st.scale + ")";
      }
      function clamp(s) { return Math.max(MIN, Math.min(MAX, s)); }
      function fit() {
        var fw = frame.clientWidth, fh = frame.clientHeight;
        if (!fw || !fh || !w0 || !h0) return;
        var s = clamp(Math.min(fw / w0, fh / h0) * 0.98);
        st.scale = s; st.tx = (fw - w0 * s) / 2; st.ty = (fh - h0 * s) / 2; apply();
      }
      function zoomAt(px, py, factor) {
        var ns = clamp(st.scale * factor);
        if (ns === st.scale) return;
        var k = ns / st.scale;
        st.tx = px - k * (px - st.tx); st.ty = py - k * (py - st.ty); st.scale = ns; apply();
      }
      function toFrame(cx, cy) { var r = frame.getBoundingClientRect(); return { x: cx - r.left, y: cy - r.top }; }
      function centerZoom(f) { zoomAt(frame.clientWidth / 2, frame.clientHeight / 2, f); }

      function onWheel(e) { e.preventDefault(); var p = toFrame(e.clientX, e.clientY); zoomAt(p.x, p.y, Math.pow(WHEEL_BASE, -e.deltaY)); }
      frame.addEventListener("wheel", onWheel, { passive: false });

      var dragging = false, lastX = 0, lastY = 0, pid = null;
      function onDown(e) {
        if (e.target && e.target.closest && e.target.closest(".mzoom-nav")) return;
        dragging = true; lastX = e.clientX; lastY = e.clientY; pid = e.pointerId;
        if (e.pointerType !== "touch" && frame.setPointerCapture) { try { frame.setPointerCapture(e.pointerId); } catch (_) {} }
        frame.classList.add("mzoom-grabbing");
      }
      function onMove(e) { if (!dragging) return; st.tx += e.clientX - lastX; st.ty += e.clientY - lastY; lastX = e.clientX; lastY = e.clientY; apply(); }
      function onUp() { if (!dragging) return; dragging = false; frame.classList.remove("mzoom-grabbing"); if (pid != null && frame.releasePointerCapture) { try { frame.releasePointerCapture(pid); } catch (_) {} } pid = null; }
      frame.addEventListener("pointerdown", onDown);
      frame.addEventListener("pointermove", onMove);
      frame.addEventListener("pointerup", onUp);
      frame.addEventListener("pointercancel", onUp);
      frame.addEventListener("pointerleave", onUp);

      nav.querySelector(".mzoom-in").addEventListener("click", function () { centerZoom(BTN); });
      nav.querySelector(".mzoom-out").addEventListener("click", function () { centerZoom(1 / BTN); });
      nav.querySelector(".mzoom-reset").addEventListener("click", fit);

      function onKey(e) {
        var pan = 60;
        switch (e.key) {
          case "+": case "=": centerZoom(BTN); break;
          case "-": case "_": centerZoom(1 / BTN); break;
          case "0": fit(); break;
          case "ArrowLeft": st.tx += pan; apply(); break;
          case "ArrowRight": st.tx -= pan; apply(); break;
          case "ArrowUp": st.ty += pan; apply(); break;
          case "ArrowDown": st.ty -= pan; apply(); break;
          default: return;
        }
        e.preventDefault();
      }
      frame.addEventListener("keydown", onKey);

      fit();
      var settle = setTimeout(fit, 200);
      function onResize() { fit(); }
      window.addEventListener("resize", onResize);

      live.push({ img: img, frame: frame, caption: caption, parent: parent, onResize: onResize, settle: settle });
    }).catch(function () {
      // leave the <img> visible as the static fallback
      img.dataset[GUARD] = "";
    });
  }

  function teardown() {
    live.forEach(function (i) {
      try { clearTimeout(i.settle); } catch (_) {}
      try { window.removeEventListener("resize", i.onResize); } catch (_) {}
      try {
        if (i.img) { i.img.style.display = ""; delete i.img.dataset[GUARD]; }
        if (i.frame) i.frame.remove();
        if (i.caption) i.caption.remove();
      } catch (_) {}
    });
    live = [];
    if (mo) { try { mo.disconnect(); } catch (_) {} mo = null; }
  }

  function scan() {
    document.querySelectorAll("img.nav-map").forEach(function (img) {
      if (img.dataset[GUARD] !== "1") enhance(img);
    });
  }

  function onPage() {
    teardown();
    scan();
    var root = document.querySelector(".md-content") || document.body;
    var stopped = false;
    mo = new MutationObserver(function () { if (!stopped) scan(); });
    mo.observe(root, { childList: true, subtree: true });
    setTimeout(function () { stopped = true; if (mo) { try { mo.disconnect(); } catch (_) {} } scan(); }, 4000);
  }

  if (window.document$ && typeof window.document$.subscribe === "function") {
    window.document$.subscribe(onPage);
  } else if (document.readyState !== "loading") {
    onPage();
  } else {
    document.addEventListener("DOMContentLoaded", onPage);
  }
})();
