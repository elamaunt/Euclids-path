window.MathJax = {
  tex: {
    inlineMath: [["\\(", "\\)"]],
    displayMath: [["\\[", "\\]"]],
    processEscapes: true,
    processEnvironments: true
  },
  options: {
    ignoreHtmlClass: ".*|",
    processHtmlClass: "arithmatex"
  }
};

// Re-typeset math after Material's instant navigation swaps the page body.
// Each step is guarded: if one call is unavailable in the loaded MathJax build
// and throws, the others (crucially typesetPromise) must still run — otherwise
// the whole page's math silently fails to render.
document$.subscribe(() => {
  if (!window.MathJax || !MathJax.typesetPromise) return;
  try { MathJax.startup.output.clearCache(); } catch (e) {}
  try { MathJax.typesetClear(); } catch (e) {}
  try { MathJax.texReset(); } catch (e) {}
  MathJax.typesetPromise();
});
