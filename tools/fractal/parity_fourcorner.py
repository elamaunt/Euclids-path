"""
Parity-sign oscillation and four-corner sign figures (English labels, repo convention).

  parity_oscillation()  -> out/parity_sign_oscillation.png
      Liouville / rank-parity sign  L(x) = sum_{n<=x} lambda(n),  lambda(n)=(-1)^Omega(n),
      shown at three scales: the negative Polya drift, the +-1 oscillation, and L(x)/sqrt(x)
      inside the sqrt(x) envelope (the Riemann wall). This is the "sign passing through 0"
      object: it looks sign-stable but provably crosses 0 (Haselgrove 1958, first flip at
      x = 906,150,257) -- so the engine "no passing through 0" bypass cannot grip it.

  four_corner_sign()    -> out/four_corner_sign.png
      The actual four-corner sign of chapter 51 (prose/51_NumericalEvidence.md, exact old-free
      sieve): B5 = N00 - N33 > 0 with a wide margin, R_fc = N00*N33/(N03*N30) < 1 pointwise,
      and the parity wall in numbers: the margin 1 - R_fc -> 0+ (the estimate must be uniform,
      not per-block). Same rank-parity object as L(x) above via lambda = (-1)^rank.
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = os.path.join(os.path.dirname(__file__), "out")
os.makedirs(OUT, exist_ok=True)
BG = "#05060a"


def _liouville_L(X):
    """L(x) = sum_{n<=x} lambda(n) for x = 0..X, via a smallest-prime-factor sieve."""
    spf = np.zeros(X + 1, dtype=np.int64)
    for i in range(2, X + 1):
        if spf[i] == 0:
            col = spf[i::i]
            spf[i::i] = np.where(col == 0, i, col)
    Om = np.zeros(X + 1, dtype=np.int64)
    for n in range(2, X + 1):
        Om[n] = Om[n // spf[n]] + 1
    lam = np.where(Om % 2 == 0, 1, -1)
    lam[0] = 0
    lam[1] = 1
    return np.cumsum(lam)


def parity_oscillation(X=2_000_000):
    L = _liouville_L(X)
    xs = np.arange(X + 1)
    fig = plt.figure(figsize=(15, 9.5), facecolor=BG)
    gs = fig.add_gridspec(2, 2, height_ratios=[1.15, 1.0], hspace=0.28, wspace=0.20)

    axA = fig.add_subplot(gs[0, :], facecolor=BG)
    step = max(1, X // 24000)
    axA.plot(xs[::step], L[::step], color="#5bd6ff", lw=0.9)
    axA.axhline(0, color="#ffd24a", lw=1.2, alpha=0.85)
    axA.fill_between(xs[::step], L[::step], 0, where=(L[::step] < 0), color="#5bd6ff", alpha=0.10)
    imin = int(np.argmin(L))
    axA.scatter([imin], [L[imin]], s=26, color="#ff5d6c", zorder=5)
    axA.annotate(f"min L = {int(L[imin])} at x={imin:,}", (imin, L[imin]),
                 textcoords="offset points", xytext=(10, -4), color="#ff9aa4", fontsize=9)
    axA.set_title("Rank-parity sign  L(x) = sum lambda(n),  lambda(n)=(-1)^Omega(n)   "
                  "-   stays NEGATIVE on all of [1, 2e6] (Polya region)", color="#cfe", fontsize=13)
    axA.set_xlabel("x", color="#aab"); axA.set_ylabel("L(x)", color="#aab")
    axA.tick_params(colors="#778"); [s.set_color("#334") for s in axA.spines.values()]
    axA.text(0.015, 0.06,
             "looks sign-stable here - but L(x) provably crosses 0 (Haselgrove 1958),\n"
             "first flip at x = 906,150,257.  Four-corner data reaches only 2^27=134M, 2^28=268M - both BELOW the flip.",
             transform=axA.transAxes, color="#ffd24a", fontsize=9.5,
             bbox=dict(boxstyle="round", fc="#0a0c14", ec="#665", alpha=0.85))

    axB = fig.add_subplot(gs[1, 0], facecolor=BG)
    axB.plot(xs[1:4000], L[1:4000], color="#7cf29a", lw=1.0)
    axB.axhline(0, color="#ffd24a", lw=1.0, alpha=0.7)
    axB.set_title("zoom x in [1,4000]: the +-1 walk - genuine up/down OSCILLATION", color="#cfe", fontsize=11)
    axB.set_xlabel("x", color="#aab"); axB.set_ylabel("L(x)", color="#aab")
    axB.tick_params(colors="#778"); [s.set_color("#334") for s in axB.spines.values()]

    axC = fig.add_subplot(gs[1, 1], facecolor=BG)
    xr = np.arange(100, X + 1, step)
    axC.plot(xr, L[xr] / np.sqrt(xr), color="#c79bff", lw=0.9)
    axC.axhline(0, color="#ffd24a", lw=1.0, alpha=0.7)
    axC.set_title("L(x)/sqrt(x) - oscillation inside the sqrt(x) envelope  ( |L(x)|=O(sqrt x) <=> Riemann wall )",
                  color="#cfe", fontsize=10.5)
    axC.set_xlabel("x", color="#aab"); axC.set_ylabel("L(x)/sqrt(x)", color="#aab")
    axC.tick_params(colors="#778"); [s.set_color("#334") for s in axC.spines.values()]

    fig.suptitle("The parity-sign oscillation - why the 'engine forbids passing through 0' bypass cannot grip",
                 color="#e8eef8", fontsize=14.5, y=0.98)
    p = os.path.join(OUT, "parity_sign_oscillation.png")
    fig.savefig(p, dpi=155, bbox_inches="tight", facecolor=BG)
    plt.close(fig)
    print("parity_sign_oscillation.png  (min L =", int(L.min()), ")")


def four_corner_sign():
    # Chapter 51 table (prose/51_NumericalEvidence.md), exact old-free sieve, blocks N = 2^k.
    k = np.array([21, 22, 23, 24, 25, 26, 27, 28])
    N00 = np.array([59382, 109168, 202492, 375236, 698496, 1302736, 2435911, 4566323], float)
    N33 = np.array([745, 1213, 2816, 4796, 9596, 18721, 33386, 72230], float)
    Rfc = np.array([0.876, 0.918, 0.920, 0.976, 0.951, 0.962, 0.972, 0.977])
    B5 = N00 - N33
    margin = 1.0 - Rfc

    fig = plt.figure(figsize=(15, 5.6), facecolor=BG)
    gs = fig.add_gridspec(1, 3, wspace=0.30)

    # Panel A: N00 (twins) vs N33 -> B5 = N00 - N33 > 0 with a wide margin
    axA = fig.add_subplot(gs[0, 0], facecolor=BG)
    axA.semilogy(k, N00, "o-", color="#ffd24a", lw=1.6, ms=5, label="N00 = twin centers")
    axA.semilogy(k, N33, "s-", color="#ff5d6c", lw=1.4, ms=4, label="N33 = both sides spoiled")
    axA.fill_between(k, N33, N00, color="#ffd24a", alpha=0.08)
    axA.set_title("B5 = N00 - N33 > 0  (N33 ~ 1.1-1.6% of N00)", color="#cfe", fontsize=11)
    axA.set_xlabel("block  k  (N = 2^k)", color="#aab"); axA.set_ylabel("count (log)", color="#aab")
    axA.tick_params(colors="#778"); [s.set_color("#334") for s in axA.spines.values()]
    axA.legend(loc="upper left", framealpha=0.25, facecolor="#0a0c14", edgecolor="#334", labelcolor="#cda", fontsize=8.5)

    # Panel B: R_fc < 1 pointwise but climbing toward 1
    axB = fig.add_subplot(gs[0, 1], facecolor=BG)
    axB.plot(k, Rfc, "o-", color="#5bd6ff", lw=1.6, ms=5)
    axB.axhline(1.0, color="#ffd24a", lw=1.2, alpha=0.85)
    axB.text(21.2, 1.003, "R_fc = 1  (independence / wall)", color="#ffd24a", fontsize=8.5)
    axB.set_ylim(0.83, 1.02)
    axB.set_title("R_fc = N00*N33/(N03*N30) < 1  on every block", color="#cfe", fontsize=11)
    axB.set_xlabel("block  k", color="#aab"); axB.set_ylabel("R_fc", color="#aab")
    axB.tick_params(colors="#778"); [s.set_color("#334") for s in axB.spines.values()]

    # Panel C: the parity wall in numbers - margin 1 - R_fc -> 0+
    axC = fig.add_subplot(gs[0, 2], facecolor=BG)
    axC.semilogy(k, margin, "o", color="#c79bff", ms=6, label="measured  1 - R_fc")
    # log-linear trend of the measured margin (honest fit to the 8 points)
    b, a = np.polyfit(k, np.log(margin), 1)
    axC.semilogy(k, np.exp(a + b * k), "--", color="#7cf29a", lw=1.3,
                 label=f"trend  ~ exp({b:.2f}*k)  -> 0+")
    axC.set_title("PARITY WALL:  margin 1 - R_fc -> 0+  (must be uniform, not per-block)", color="#cfe", fontsize=10.5)
    axC.set_xlabel("block  k", color="#aab"); axC.set_ylabel("1 - R_fc  (log)", color="#aab")
    axC.tick_params(colors="#778"); [s.set_color("#334") for s in axC.spines.values()]
    axC.text(0.03, 0.06, "prose exploratory fit:\n1 - R_fc ~ 12.12 * A^(-1.161),  alpha>0 -> 0+ smoothly,\nnever crossing 0 at finite A",
             transform=axC.transAxes, color="#ffd24a", fontsize=8.0,
             bbox=dict(boxstyle="round", fc="#0a0c14", ec="#665", alpha=0.85))
    axC.legend(loc="upper right", framealpha=0.25, facecolor="#0a0c14", edgecolor="#334", labelcolor="#cda", fontsize=8.5)

    fig.suptitle("Four-corner sign (chapter 51): B5>0 and R_fc<1 hold pointwise to 2^28 - but the margin melts (the parity wall)",
                 color="#e8eef8", fontsize=13, y=1.02)
    p = os.path.join(OUT, "four_corner_sign.png")
    fig.savefig(p, dpi=155, bbox_inches="tight", facecolor=BG)
    plt.close(fig)
    print("four_corner_sign.png  (margin trend slope in log:", round(float(b), 3), ")")


if __name__ == "__main__":
    parity_oscillation()
    four_corner_sign()
    print("done ->", OUT)
