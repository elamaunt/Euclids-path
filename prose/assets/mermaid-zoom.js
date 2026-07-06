/* assets/mermaid-zoom.js
 *
 * Interactive pan + zoom for the wide navigator flowchart on 00_Overview §3
 * (and its EN mirror /en/00_Overview/), under Material for MkDocs 9.7.
 *
 * WHY IT IS BUILT THIS WAY (verified empirically against the shipped site):
 *   Material renders the ```mermaid fence into <div class="mermaid"> whose SVG
 *   lives inside a CLOSED shadow root. The inner <svg> is unreachable from page
 *   JS and page CSS, so svg-pan-zoom / d3-zoom on the svg is impossible. The one
 *   lever we have is a CSS transform on the light-DOM host, which the browser
 *   applies to the closed-shadow subtree visually (and, being vector, stays
 *   crisp at any zoom). Pointer and wheel events raised on the shadow SVG are
 *   composed, so they bubble to a light-DOM wrapper — meaning a wrapper-level
 *   transform pan/zoom needs NO external library at all.
 *
 * Guarantees:
 *   - RU (/) and EN (/en/): keys off the DOM, not the URL.
 *   - Light + dark palettes: all colours come from Material CSS variables (CSS).
 *   - Survives Material instant navigation: one document$ subscription, full
 *     teardown (unwrap + listener removal) on every emission, idempotency guard.
 *   - Degrades gracefully: if this script does not run, mermaid.css keeps the
 *     natural-size horizontal-scroll fallback; nothing here throws.
 *   - Non-hostile on touch: touch-action:pan-y (CSS) keeps vertical page scroll;
 *     the +/-/reset buttons zoom without a wheel.
 */
(function () {
  "use strict";
  if (typeof window === "undefined") return;

  var GUARD = "mzoom";          // host.dataset.mzoom === "1" once wrapped
  var MIN = 0.25, MAX = 16;     // zoom range
  var BTN = 1.45;               // per-click / per-key zoom factor
  var WHEEL_BASE = 1.0018;      // wheel sensitivity (factor = base^-deltaY)
  var live = [];                // active instances, for teardown
  var mo = null;                // MutationObserver for async render

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

  function enhance(host) {
    if (!host || host.dataset[GUARD] === "1") return;
    // Must be laid out (closed-shadow graph has non-zero box) or fit math is NaN.
    var w0 = host.offsetWidth, h0 = host.offsetHeight;
    if (!w0 || !h0) return;                 // retry later via the observer
    var parent = host.parentNode;
    if (!parent) return;
    host.dataset[GUARD] = "1";

    // ---- build frame > inner > host, plus controls + caption ----
    var frame = document.createElement("div");
    frame.className = "mzoom-frame";
    frame.setAttribute("tabindex", "0");
    frame.setAttribute("role", "group");
    frame.setAttribute("aria-label", isRu() ? "Интерактивная карта-навигатор" : "Interactive navigator map");

    var inner = document.createElement("div");
    inner.className = "mzoom-inner";

    parent.insertBefore(frame, host);
    inner.appendChild(host);
    frame.appendChild(inner);

    // Pin the host to its measured natural size so the closed-shadow SVG
    // (max-width:100%) resolves stably once it is out of the document flow.
    host.style.margin = "0";
    host.style.display = "block";
    host.style.width = w0 + "px";
    host.style.height = h0 + "px";
    host.style.maxWidth = "none";

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

    // ---- transform state ----
    var st = { scale: 1, tx: 0, ty: 0 };
    function apply() {
      inner.style.transform =
        "translate(" + st.tx + "px," + st.ty + "px) scale(" + st.scale + ")";
    }
    function clamp(s) { return Math.max(MIN, Math.min(MAX, s)); }

    function fit() {
      var fw = frame.clientWidth, fh = frame.clientHeight;
      if (!fw || !fh || !w0 || !h0) return;
      var s = clamp(Math.min(fw / w0, fh / h0) * 0.98);
      st.scale = s;
      st.tx = (fw - w0 * s) / 2;
      st.ty = (fh - h0 * s) / 2;
      apply();
    }

    // Zoom keeping the frame-space point (px,py) fixed under the pointer.
    function zoomAt(px, py, factor) {
      var ns = clamp(st.scale * factor);
      if (ns === st.scale) return;
      var k = ns / st.scale;
      st.tx = px - k * (px - st.tx);
      st.ty = py - k * (py - st.ty);
      st.scale = ns;
      apply();
    }
    function toFrame(clientX, clientY) {
      var r = frame.getBoundingClientRect();
      return { x: clientX - r.left, y: clientY - r.top };
    }
    function centerZoom(factor) { zoomAt(frame.clientWidth / 2, frame.clientHeight / 2, factor); }

    // ---- wheel zoom ----
    function onWheel(e) {
      e.preventDefault();
      var p = toFrame(e.clientX, e.clientY);
      zoomAt(p.x, p.y, Math.pow(WHEEL_BASE, -e.deltaY));
    }
    frame.addEventListener("wheel", onWheel, { passive: false });

    // ---- drag pan (pointer events; skip when starting on a control) ----
    var dragging = false, lastX = 0, lastY = 0, pid = null;
    function onDown(e) {
      if (e.target && e.target.closest && e.target.closest(".mzoom-nav")) return;
      dragging = true; lastX = e.clientX; lastY = e.clientY; pid = e.pointerId;
      if (e.pointerType !== "touch" && frame.setPointerCapture) {
        try { frame.setPointerCapture(e.pointerId); } catch (_) {}
      }
      frame.classList.add("mzoom-grabbing");
    }
    function onMove(e) {
      if (!dragging) return;
      st.tx += e.clientX - lastX; st.ty += e.clientY - lastY;
      lastX = e.clientX; lastY = e.clientY; apply();
    }
    function onUp() {
      if (!dragging) return;
      dragging = false; frame.classList.remove("mzoom-grabbing");
      if (pid != null && frame.releasePointerCapture) {
        try { frame.releasePointerCapture(pid); } catch (_) {}
      }
      pid = null;
    }
    frame.addEventListener("pointerdown", onDown);
    frame.addEventListener("pointermove", onMove);
    frame.addEventListener("pointerup", onUp);
    frame.addEventListener("pointercancel", onUp);
    frame.addEventListener("pointerleave", onUp);

    // ---- buttons ----
    nav.querySelector(".mzoom-in").addEventListener("click", function () { centerZoom(BTN); });
    nav.querySelector(".mzoom-out").addEventListener("click", function () { centerZoom(1 / BTN); });
    nav.querySelector(".mzoom-reset").addEventListener("click", fit);

    // ---- keyboard (frame focused): +/- zoom, arrows pan, 0 reset ----
    function onKey(e) {
      var pan = 60;
      switch (e.key) {
        case "+": case "=": centerZoom(BTN); break;
        case "-": case "_": centerZoom(1 / BTN); break;
        case "0": fit(); break;
        case "ArrowLeft":  st.tx += pan; apply(); break;
        case "ArrowRight": st.tx -= pan; apply(); break;
        case "ArrowUp":    st.ty += pan; apply(); break;
        case "ArrowDown":  st.ty -= pan; apply(); break;
        default: return;
      }
      e.preventDefault();
    }
    frame.addEventListener("keydown", onKey);

    // ---- fit now and once more after fonts/layout settle ----
    fit();
    var settle = setTimeout(fit, 200);
    function onResize() { fit(); }
    window.addEventListener("resize", onResize);

    live.push({ host: host, frame: frame, parent: parent, caption: caption, onResize: onResize, settle: settle });
  }

  function teardown() {
    live.forEach(function (i) {
      try { clearTimeout(i.settle); } catch (_) {}
      try { window.removeEventListener("resize", i.onResize); } catch (_) {}
      try {
        i.host.style.margin = ""; i.host.style.display = ""; i.host.style.width = "";
        i.host.style.height = ""; i.host.style.maxWidth = ""; i.host.style.transform = "";
        delete i.host.dataset[GUARD];
        if (i.parent && i.frame && i.frame.parentNode === i.parent) i.parent.insertBefore(i.host, i.frame);
        if (i.frame) i.frame.remove();
        if (i.caption) i.caption.remove();
      } catch (_) {}
    });
    live = [];
    if (mo) { try { mo.disconnect(); } catch (_) {} mo = null; }
  }

  function scan() {
    var hosts = document.querySelectorAll(".md-typeset div.mermaid, .md-content div.mermaid");
    hosts.forEach(function (h) { if (h.dataset[GUARD] !== "1") enhance(h); });
  }

  function onPage() {
    teardown();
    scan();
    var root = document.querySelector(".md-content") || document.body;
    var stopped = false;
    mo = new MutationObserver(function () { if (!stopped) scan(); });
    mo.observe(root, { childList: true, subtree: true });
    // Mermaid renders a tick (or more) after document$; stop watching once settled.
    setTimeout(function () { stopped = true; if (mo) { try { mo.disconnect(); } catch (_) {} } scan(); }, 4000);
  }

  if (window.document$ && typeof window.document$.subscribe === "function") {
    window.document$.subscribe(onPage);          // fires on load AND instant-nav
  } else if (document.readyState !== "loading") {
    onPage();
  } else {
    document.addEventListener("DOMContentLoaded", onPage);
  }
})();
