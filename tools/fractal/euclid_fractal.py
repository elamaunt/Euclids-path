"""
Euclid fractal: visual structure of primes via the twin-program objects.
Each view comes from a real object: centers 6m+-1, ranks, old-peel descent, the engine.
Output: PNG files in out/ (English labels, with colorbars / legends / axes).
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
import matplotlib as mpl
import math, os

OUT = os.path.join(os.path.dirname(__file__), "out")
os.makedirs(OUT, exist_ok=True)
mpl.rcParams["font.size"] = 11

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

# ---------------------------------------------------------------------------
# (1) OLD-PEEL DESCENT FOREST — the engine fractal (brighter, with colorbar).
# ---------------------------------------------------------------------------
def old_peel_tree(A=200):
    P = primes_upto(A*A*4); small = [p for p in P if 3 < p <= A]; isprime = set(int(x) for x in P)
    segs, cols = [], []
    def peel(n, eps, d, x0):
        if d > 7 or n < 2: return
        a = 6*n + eps
        if a <= A or a not in isprime: return
        other = 6*n - eps
        if other < 2: return
        p = next((q for q in small if other % q == 0), None)
        if p is None: return
        co = other // p
        delta = 1 if co % 6 == 1 else (-1 if co % 6 == 5 else 0)
        if delta == 0: return
        t = (co - delta)//6
        if t <= 0: return
        y0, y1 = math.log10(n+1), math.log10(t+1)
        x1 = x0 + eps*0.55/(d+1)
        segs.append([(x0, y0), (x1, y1)]); cols.append(d)
        peel(t, 1, d+1, x1); peel(t, -1, d+1, x1)
    xs = np.linspace(-30, 30, 460)
    n0 = A*A//6
    for i, x in enumerate(xs):
        peel(n0 + i*7, 1, 0, x); peel(n0 + i*7, -1, 0, x)
    fig, ax = plt.subplots(figsize=(13, 9), facecolor="#05060a")
    lc = LineCollection(segs, array=np.array(cols), cmap="turbo", linewidths=1.1, alpha=0.92)
    ax.add_collection(lc); ax.set_facecolor("#05060a"); ax.autoscale()
    ax.set_xlabel("lateral spread  (sign of each descent step  ε = ±1)", color="#aab")
    ax.set_ylabel("height  log10(center m)", color="#aab")
    ax.tick_params(colors="#778"); [s.set_color("#334") for s in ax.spines.values()]
    cb = fig.colorbar(lc, ax=ax, pad=0.01, fraction=0.035)
    cb.set_label("old-peel depth (descent step number)", color="#aab"); cb.ax.yaxis.set_tick_params(color="#778")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#aab")
    ax.set_title("Euclid fractal · old-peel descent forest of primes (the engine)", color="#cfe", fontsize=14)
    fig.savefig(os.path.join(OUT, "1_old_peel_tree.png"), dpi=160, bbox_inches="tight", facecolor="#05060a")
    plt.close(fig); print("1_old_peel_tree.png")

# ---------------------------------------------------------------------------
# (2) RANK / CHARGE FIELD — r-(m) - r+(m) over centers 6m+-1 (with colorbar).
# ---------------------------------------------------------------------------
def rank_field(A=60, W=900):
    P = primes_upto(A*A); layer = [int(p) for p in P if A < p <= A*A]
    N = W*W
    rm = np.zeros(N, dtype=np.int16); rp = np.zeros(N, dtype=np.int16)
    base = 1
    for p in layer:
        i6 = pow(6, -1, p)
        for s, arr in ((1, rp), (-1, rm)):
            r = (s*i6) % p; st = (r - base) % p
            arr[st::p] += 1
    img = (rm.astype(np.float32) - rp.astype(np.float32)).reshape(W, W)
    fig, ax = plt.subplots(figsize=(11.5, 10), facecolor="#000")
    im = ax.imshow(img, cmap="twilight_shifted", interpolation="nearest", origin="lower")
    ax.set_xlabel("center index  m  (column)", color="#aab")
    ax.set_ylabel("center index  m  (row · width)", color="#aab")
    ax.tick_params(colors="#778"); [s.set_color("#334") for s in ax.spines.values()]
    cb = fig.colorbar(im, ax=ax, pad=0.01, fraction=0.046)
    cb.set_label("charge   r₋(m) − r₊(m)   (left minus right prime-rank)", color="#aab")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#aab"); cb.ax.yaxis.set_tick_params(color="#778")
    ax.set_title("Euclid fractal · charge field  r₋−r₊  of centers 6m±1", color="#ccd", fontsize=14)
    fig.savefig(os.path.join(OUT, "2_rank_field.png"), dpi=150, bbox_inches="tight", facecolor="#000")
    plt.close(fig); print("2_rank_field.png")

# ---------------------------------------------------------------------------
# (3) GOLDEN SPIRAL OF TWINS — with legend.
# ---------------------------------------------------------------------------
def twin_spiral(M=60000):
    P = primes_upto(6*M+2); isp = set(int(x) for x in P)
    m = np.arange(1, M)
    th = m * (math.pi*(3-5**0.5))
    r = np.sqrt(m)
    lo = np.array([(6*k-1) in isp for k in m]); hi = np.array([(6*k+1) in isp for k in m])
    twin = lo & hi
    x, y = r*np.cos(th), r*np.sin(th)
    fig, ax = plt.subplots(figsize=(11, 11), facecolor="#02030a")
    ax.scatter(x[lo|hi], y[lo|hi], s=0.6, c="#2a3a66", alpha=0.5, label="one side prime (6m−1 or 6m+1)")
    ax.scatter(x[twin], y[twin], s=5.0, c="#ffd24a", alpha=0.95, edgecolors="none", label="twin center (both prime)")
    ax.set_aspect("equal"); ax.set_facecolor("#02030a")
    ax.set_xlabel("x = √m · cos(m·φ)", color="#aab"); ax.set_ylabel("y = √m · sin(m·φ)", color="#aab")
    ax.tick_params(colors="#667"); [s.set_color("#223") for s in ax.spines.values()]
    leg = ax.legend(loc="upper right", framealpha=0.25, facecolor="#0a0c14", edgecolor="#334", labelcolor="#cda")
    ax.set_title("Euclid fractal · golden spiral of centers; twins are golden doubles  (φ = golden angle)", color="#cda", fontsize=13)
    fig.savefig(os.path.join(OUT, "3_twin_spiral.png"), dpi=160, bbox_inches="tight", facecolor="#02030a")
    plt.close(fig); print("3_twin_spiral.png")

# ---------------------------------------------------------------------------
# (4) DESCENT-HEIGHT LANDSCAPE — fixed: accumulate true peel depth with deeper chains.
# ---------------------------------------------------------------------------
def descent_landscape(side=620, B=12):
    """Euclidean smoothness landscape: for each center m, the TOTAL small-prime load
       Omega(6m-1)+Omega(6m+1) (number of prime factors, with multiplicity, up to bound B-smooth).
       Twin centers = load 0 valleys. Self-similar CRT relief, always non-trivial."""
    span = side*side
    sp = [int(p) for p in primes_upto(10000) if p >= 5][:B]   # first B primes >=5
    load = np.zeros(span, dtype=np.float32)
    m = np.arange(span, dtype=np.int64)
    for side_sign in (-1, 1):
        val = 6*m + side_sign       # the side 6m-1 or 6m+1
        for p in sp:
            # count multiplicity of p in each val (vectorized over a few powers)
            pk = p
            while pk <= (6*span+1):
                load += (val % pk == 0)
                if pk > (6*span)//p + 1: break
                pk *= p
    img = load.reshape(side, side)
    vmax = max(1.0, np.percentile(load, 99))
    fig, ax = plt.subplots(figsize=(11.5, 10), facecolor="#000")
    im = ax.imshow(img, cmap="inferno", interpolation="nearest", origin="lower", vmin=0, vmax=vmax)
    ax.set_xlabel("center index  m  (column)", color="#ecc")
    ax.set_ylabel("center index  m  (row · side)", color="#ecc")
    ax.tick_params(colors="#977"); [s.set_color("#422") for s in ax.spines.values()]
    cb = fig.colorbar(im, ax=ax, pad=0.01, fraction=0.046)
    cb.set_label(f"small-prime load  Ω(6m−1)+Ω(6m+1)  (first {B} primes ≥5)   —   dark valleys = twin candidates", color="#ecc")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#ecc"); cb.ax.yaxis.set_tick_params(color="#977")
    ax.set_title("Euclid fractal · prime-load landscape of centers 6m±1   (valleys = twins)", color="#ecc", fontsize=14)
    fig.savefig(os.path.join(OUT, "4_descent_landscape.png"), dpi=150, bbox_inches="tight", facecolor="#000")
    plt.close(fig)
    print(f"4_descent_landscape.png  (load: mean={load.mean():.2f}, max={int(load.max())}, zero-valleys={100*np.mean(load==0):.2f}%)")

# ---------------------------------------------------------------------------
# (5) THE LINE — centers on one axis; twins flank it on both sides;
#     old-peel genealogies run ALONG the line as arcs, one Euclid prime per step.
# ---------------------------------------------------------------------------
def _peel_step(k, isp, euclid_primes):
    """One old-peel genealogy step from center k: peel the composite side
       6k∓1 = p·(6t±1) by its smallest Euclid prime p. Returns (t, p) or None."""
    for eps in (-1, 1):
        val = 6*k + eps
        if val in isp:
            continue
        p = next((q for q in euclid_primes if val % q == 0), None)
        if p is None:
            continue
        co = val // p
        d = 1 if co % 6 == 1 else (-1 if co % 6 == 5 else 0)
        if d == 0:
            continue
        t = (co - d) // 6
        if 1 <= t < k:
            return t, p
    return None

def _peel_step_side(k, isp, euclid_primes):
    """As _peel_step, but also returns the side eps of the peeled composite 6k+eps
       (so an ornament can place each step on the side it came from)."""
    for eps in (-1, 1):
        val = 6*k + eps
        if val in isp:
            continue
        p = next((q for q in euclid_primes if val % q == 0), None)
        if p is None:
            continue
        co = val // p
        d = 1 if co % 6 == 1 else (-1 if co % 6 == 5 else 0)
        if d == 0:
            continue
        t = (co - d) // 6
        if 1 <= t < k:
            return t, p, eps
    return None

def twin_line_genealogy(M=2400, PMAX=97):
    """The line of centers m. Above the line: 6m+1, below: 6m-1 (prime = spark).
       Twin centers = golden double sparks flanking the line symmetrically.
       On the line itself: descent genealogy arcs m -> t of the old-peel step
       6m∓1 = p·(6t±1); each arc is colored by its Euclid prime p (the witness
       prime of the peel). Twins live OFF the line, the genealogy lives ON it."""
    P = primes_upto(6*M + 2); isp = set(int(x) for x in P)
    euclid_primes = [int(p) for p in P if 5 <= p <= PMAX]
    m = np.arange(1, M + 1)
    lo = np.array([(6*k - 1) in isp for k in m])
    hi = np.array([(6*k + 1) in isp for k in m])
    twin = lo & hi

    segs, cols, n_arcs = [], [], 0
    def arc(x0, x1, npts=36):
        cx, span = (x0 + x1) / 2.0, abs(x1 - x0)
        h = 0.06 * span ** 0.85 + 0.4
        t = np.linspace(0.0, math.pi, npts)
        xs = cx + (span / 2.0) * np.cos(t) * (1 if x1 < x0 else -1)
        return np.column_stack([xs, h * np.sin(t)])
    for k in range(1, M + 1):
        st = _peel_step(k, isp, euclid_primes)
        if st is None: continue
        t_, p = st
        pts = arc(k, t_)
        segs.extend(np.stack([pts[:-1], pts[1:]], axis=1))
        cols.extend([math.log(p)] * (len(pts) - 1))
        n_arcs += 1

    fig, ax = plt.subplots(figsize=(16, 7.5), facecolor="#04050c")
    ax.set_facecolor("#04050c")
    ax.axhline(0.0, color="#9aa7d8", lw=1.0, alpha=0.85, zorder=3)
    lc = LineCollection(segs, array=np.array(cols), cmap="turbo",
                        linewidths=0.7, alpha=0.55, zorder=2)
    ax.add_collection(lc)
    wing = 0.9 + 0.25 * np.sqrt(m / M)
    ax.scatter(m[hi],  wing[hi], s=2.2, c="#33518f", alpha=0.55, edgecolors="none",
               zorder=4, label="6m+1 prime (above the line)")
    ax.scatter(m[lo], -wing[lo], s=2.2, c="#2f7d6d", alpha=0.55, edgecolors="none",
               zorder=4, label="6m−1 prime (below the line)")
    tw, wt = m[twin], wing[twin]
    ax.vlines(tw, -wt, wt, colors="#ffd24a", lw=0.55, alpha=0.35, zorder=5)
    ax.scatter(tw,  wt, s=9.0, c="#ffd24a", alpha=0.95, edgecolors="none", zorder=6,
               label="twin center (both sides prime)")
    ax.scatter(tw, -wt, s=9.0, c="#ffd24a", alpha=0.95, edgecolors="none", zorder=6)
    ax.set_xlim(0, M + 1)
    ax.set_ylim(-2.4, 0.06 * M ** 0.85 + 1.4)
    ax.set_xlabel("center m on the line (sides are 6m−1 / 6m+1)", color="#aab")
    ax.set_ylabel("twins flank the line · genealogy arcs run along it", color="#aab")
    ax.tick_params(colors="#778"); [s.set_color("#334") for s in ax.spines.values()]
    cb = fig.colorbar(lc, ax=ax, pad=0.01, fraction=0.03)
    cb.set_label("Euclid prime p of the peel step  6m∓1 = p·(6t±1)", color="#aab")
    cb.ax.yaxis.set_tick_params(color="#778")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#aab")
    tick_ps = [q for q in (5, 7, 13, 23, 43, 79) if q <= PMAX]
    cb.set_ticks([math.log(q) for q in tick_ps]); cb.set_ticklabels([str(q) for q in tick_ps])
    ax.legend(loc="upper right", framealpha=0.25, facecolor="#0a0c14",
              edgecolor="#334", labelcolor="#cda", markerscale=2.5)
    ax.set_title("Euclid fractal · the line of centers: twins flank it on both sides, "
                 "old-peel genealogies (one Euclid prime per step) run along the line",
                 color="#cfe", fontsize=13.5)
    fig.savefig(os.path.join(OUT, "5_twin_line_genealogy.png"), dpi=160,
                bbox_inches="tight", facecolor="#04050c")
    plt.close(fig)
    print(f"5_twin_line_genealogy.png  (arcs={n_arcs}, twins={int(twin.sum())})")

# ---------------------------------------------------------------------------
# (6) GENEALOGY ORNAMENT — full descent genealogies as a chord rose:
#     centers on a circle, every peel step is a chord colored by its Euclid prime.
# ---------------------------------------------------------------------------
def genealogy_ornament(M=4200, PMAX=97, DEPTH=10):
    """Ornament woven from the genealogies themselves. Centers 1..M sit on a
       circle (angle 2π·m/M). For every center the FULL old-peel genealogy
       m -> t1 -> t2 -> ... (up to DEPTH) is drawn: each step is a Bezier chord
       pulled toward the middle, colored by the Euclid prime p of that step.
       CRT periodicity of the small primes weaves the rosette; twins sit on the
       rim as golden points (their genealogy is empty: nothing to peel)."""
    P = primes_upto(6*M + 2); isp = set(int(x) for x in P)
    euclid_primes = [int(p) for p in P if 5 <= p <= PMAX]
    def pos(k):
        th = 2*math.pi * k / M
        return np.array([math.cos(th), math.sin(th)])
    segs, cols = [], []
    def chord(a, b, npts=30):
        P0, P1 = pos(a), pos(b)
        dth = abs(a - b) / M
        pull = 1.0 - min(2*dth, 1.0) * 0.92          # long chords dive deeper
        C = (P0 + P1) / 2.0 * pull
        u = np.linspace(0, 1, npts)[:, None]
        return (1-u)**2 * P0 + 2*u*(1-u) * C + u**2 * P1
    n_steps = 0
    for k0 in range(2, M + 1):
        k = k0
        for _ in range(DEPTH):
            st = _peel_step(k, isp, euclid_primes)
            if st is None: break
            t_, p = st
            pts = chord(k, t_)
            segs.extend(np.stack([pts[:-1], pts[1:]], axis=1))
            cols.extend([math.log(p)] * (len(pts) - 1))
            n_steps += 1
            k = t_
    m = np.arange(1, M + 1)
    twin = np.array([((6*k - 1) in isp) and ((6*k + 1) in isp) for k in m])
    tw_pts = np.array([pos(int(k)) for k in m[twin]])

    fig, ax = plt.subplots(figsize=(13, 13), facecolor="#03040a")
    ax.set_facecolor("#03040a")
    th = np.linspace(0, 2*math.pi, 720)
    ax.plot(np.cos(th), np.sin(th), color="#2a3350", lw=0.8, alpha=0.8, zorder=1)
    lc = LineCollection(segs, array=np.array(cols), cmap="turbo",
                        linewidths=0.45, alpha=0.34, zorder=2)
    ax.add_collection(lc)
    ax.scatter(tw_pts[:, 0], tw_pts[:, 1], s=7.5, c="#ffd24a", alpha=0.95,
               edgecolors="none", zorder=5, label="twin center (empty genealogy)")
    ax.set_aspect("equal"); ax.set_xticks([]); ax.set_yticks([])
    [s.set_visible(False) for s in ax.spines.values()]
    cb = fig.colorbar(lc, ax=ax, pad=0.01, fraction=0.035)
    cb.set_label("Euclid prime p of each genealogy step  6m∓1 = p·(6t±1)", color="#aab")
    cb.ax.yaxis.set_tick_params(color="#778")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#aab")
    tick_ps = [q for q in (5, 7, 13, 23, 43, 79) if q <= PMAX]
    cb.set_ticks([math.log(q) for q in tick_ps]); cb.set_ticklabels([str(q) for q in tick_ps])
    ax.legend(loc="lower right", framealpha=0.25, facecolor="#0a0c14",
              edgecolor="#334", labelcolor="#cda", markerscale=2.0)
    ax.set_title("Euclid fractal · genealogy ornament: full old-peel descent of every center,\n"
                 "woven as chords on the circle of centers (color = Euclid prime of the step)",
                 color="#cfe", fontsize=13.5)
    fig.savefig(os.path.join(OUT, "6_genealogy_ornament.png"), dpi=160,
                bbox_inches="tight", facecolor="#03040a")
    plt.close(fig)
    print(f"6_genealogy_ornament.png  (steps={n_steps}, twins={int(twin.sum())})")

# ---------------------------------------------------------------------------
# (9) ASCENDING TWIN ORNAMENT — vertical sibling of the genealogy ornament:
#     genealogies rise the axis bottom->top; each peel step is a petal on the
#     side of the composite it came from (6k+1 -> right, 6k-1 -> left).
# ---------------------------------------------------------------------------
def ascending_twin_ornament(M=3000, PMAX=97, DEPTH=14):
    """Centers 1..M ascend the axis x=0 (height = m). Every old-peel step
       6k∓1 = p·(6t±1) is a semicircular petal on the SIDE of the composite that
       was peeled (6k+1 -> right, 6k-1 -> left), colored by its Euclid prime p.
       Each petal is clipped to a circle of radius M/2, so the whole ornament
       fills a SPHERE around the ascending twin meridian; twin centers (empty
       genealogy: both sides prime) are golden double sparks flanking the axis."""
    P = primes_upto(6*M + 2); isp = set(int(x) for x in P)
    euclid_primes = [int(p) for p in P if 5 <= p <= PMAX]
    band = 0.55 * M; bulge = 1.8; R = 0.5 * M                # R = sphere radius (the envelope)
    def petal(k, t, side, npts=30):
        yc, a = 0.5 * (k + t), 0.5 * (k - t)                 # a > 0 since t < k
        mag = band * math.tanh(bulge * a / band)             # smooth saturation
        wc = math.sqrt(max(0.0, R * R - (yc - R) ** 2))      # circle half-width at this height
        b = side * min(mag, 0.985 * wc)                      # clip each petal -> ornament fills a sphere
        th = np.linspace(-math.pi / 2, math.pi / 2, npts)    # bottom (t) -> top (k)
        return np.column_stack([b * np.cos(th), yc + a * np.sin(th)])
    segs, cols, n_steps = [], [], 0
    for k0 in range(2, M + 1):
        k = k0
        for _ in range(DEPTH):
            st = _peel_step_side(k, isp, euclid_primes)
            if st is None: break
            t_, p, eps = st
            pts = petal(k, t_, 1.0 if eps == 1 else -1.0)
            segs.extend(np.stack([pts[:-1], pts[1:]], axis=1))
            cols.extend([math.log(p)] * (len(pts) - 1))
            n_steps += 1; k = t_
    m = np.arange(1, M + 1)
    twin = np.array([((6 * k - 1) in isp) and ((6 * k + 1) in isp) for k in m])
    tw = m[twin]

    fig, ax = plt.subplots(figsize=(13.5, 14.5), facecolor="#03040a")
    ax.set_facecolor("#03040a")
    ax.plot([0, 0], [1, M], color="#2a3350", lw=0.7, alpha=0.6, zorder=1)
    lc = LineCollection(segs, array=np.array(cols), cmap="turbo",
                        linewidths=0.42, alpha=0.30, zorder=2)
    ax.add_collection(lc)
    off = 0.010 * M
    ax.hlines(tw, -off, off, colors="#ffd24a", lw=0.4, alpha=0.35, zorder=4)
    ax.scatter(np.full(tw.shape, off), tw, s=6.5, c="#ffd24a", alpha=0.95,
               edgecolors="none", zorder=5, label="twin center (both sides prime)")
    ax.scatter(np.full(tw.shape, -off), tw, s=6.5, c="#ffd24a", alpha=0.95,
               edgecolors="none", zorder=5)
    ax.set_xlim(-R * 1.03, R * 1.03); ax.set_ylim(0, M + 1); ax.set_aspect("equal")
    ax.set_xticks([]); ax.set_yticks([])
    [s.set_visible(False) for s in ax.spines.values()]
    cb = fig.colorbar(lc, ax=ax, pad=0.01, fraction=0.045)
    cb.set_label("Euclid prime p of each genealogy step  6m∓1 = p·(6t±1)", color="#aab")
    cb.ax.yaxis.set_tick_params(color="#778")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#aab")
    ticks = [q for q in (5, 7, 13, 23, 43, 79) if q <= PMAX]
    cb.set_ticks([math.log(q) for q in ticks]); cb.set_ticklabels([str(q) for q in ticks])
    ax.legend(loc="lower right", framealpha=0.25, facecolor="#0a0c14",
              edgecolor="#334", labelcolor="#cda", markerscale=2.0)
    ax.set_title("Euclid fractal · ascending twin ornament\n"
                 "genealogies rise the axis; each peel petal on its own side (6m±1), colored by the Euclid prime",
                 color="#cfe", fontsize=12.5)
    fig.savefig(os.path.join(OUT, "9_ascending_twin_ornament.png"), dpi=160,
                bbox_inches="tight", facecolor="#03040a")
    plt.close(fig)
    print(f"9_ascending_twin_ornament.png  (steps={n_steps}, twins={int(twin.sum())})")

if __name__ == "__main__":
    twin_spiral()
    rank_field()
    old_peel_tree()
    descent_landscape()
    twin_line_genealogy()
    genealogy_ornament()
    ascending_twin_ornament()
    print("done ->", OUT)
