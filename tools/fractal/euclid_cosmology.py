"""
Euclid fractal · COSMOLOGICAL views built on the REAL old-peel genealogy (not sketches).

The real fractal is the old-peel descent: every center k peels to a smaller center t by
    6k∓1 = p·(6t±1),   p = Euclid prime of the step,
so each center has a genealogy chain  k → t1 → t2 → … → base  (twin centers = empty chain).
Both views below draw THAT structure — mathematically the same object as views 1,5,6 —
just placed for the cosmological reading:

  (7) observer at the centre: centers placed radially by height (radius = √(k/M)); the real
      genealogy chords flow INWARD (k → t, t<k, smaller radius) toward the observer at the
      root; event horizon circle; arrowheads on real edges = the arrow of time inward.
  (8) the time-sphere: centers placed on a sphere, small centers at the 0-pole (start of
      time · singularity 0), large centers at the antipodal observer pole; the real genealogy
      steps are great-circle arcs, so the fractal EMANATES from the 0-pole across the surface.

Output: 7_observer_horizon.png, 8_time_sphere.png in out/.  Reuses primes_upto + _peel_step
so the drawn edges are exactly the peel steps of euclid_fractal.py (no decorative scatter).
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
from matplotlib.colors import Normalize
import matplotlib as mpl
import math, os

OUT = os.path.join(os.path.dirname(__file__), "out")
os.makedirs(OUT, exist_ok=True)
mpl.rcParams["font.size"] = 11
GOLD = math.pi * (3 - 5 ** 0.5)          # golden angle

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def _peel_step(k, isp, euclid_primes):
    """One old-peel step from center k: 6k∓1 = p·(6t±1). Returns (t, p) or None.
       Identical rule to euclid_fractal.py — these are the real fractal edges."""
    for eps in (-1, 1):
        val = 6 * k + eps
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

def _chains(M, PMAX, DEPTH):
    """Return (isp, euclid_primes, twin_mask, steps) where steps is a list of (k, t, logp)
       for every old-peel step of every center's full genealogy chain."""
    P = primes_upto(6 * M + 2); isp = set(int(x) for x in P)
    euclid_primes = [int(p) for p in P if 5 <= p <= PMAX]
    m = np.arange(1, M + 1)
    lo = np.array([(6 * k - 1) in isp for k in m])
    hi = np.array([(6 * k + 1) in isp for k in m])
    twin = lo & hi
    steps = []
    for k0 in range(2, M + 1):
        k = k0
        for _ in range(DEPTH):
            st = _peel_step(k, isp, euclid_primes)
            if st is None:
                break
            t, p = st
            steps.append((k, t, math.log(p)))
            k = t
    return isp, euclid_primes, twin, steps

# ---------------------------------------------------------------------------
# (7) OBSERVER · HORIZON · the real genealogy flowing INWARD to the centre.
# ---------------------------------------------------------------------------
def observer_horizon(M=9000, PMAX=97, DEPTH=9):
    isp, ep, twin, steps = _chains(M, PMAX, DEPTH)
    m = np.arange(1, M + 1)

    # radial placement by height: radius grows with center k, angle = golden spiral.
    rad = np.sqrt(m / M)                         # k small -> near centre (the root/observer)
    ang = m * GOLD
    px, py = rad * np.cos(ang), rad * np.sin(ang)

    def curve(a, b, npts=16):
        # quadratic Bezier from center a to center b, control pulled toward the centre
        P0 = np.array([px[a - 1], py[a - 1]]); P1 = np.array([px[b - 1], py[b - 1]])
        C = (P0 + P1) / 2.0 * 0.72               # pull toward origin -> inward-diving arc
        u = np.linspace(0, 1, npts)[:, None]
        return (1 - u) ** 2 * P0 + 2 * u * (1 - u) * C + u ** 2 * P1

    segs, cols = [], []
    for (k, t, lp) in steps:
        pts = curve(k, t)
        segs.extend(np.stack([pts[:-1], pts[1:]], axis=1)); cols.extend([lp] * (len(pts) - 1))

    fig, ax = plt.subplots(figsize=(11.5, 11.5), facecolor="#02030a")
    ax.set_facecolor("#02030a"); ax.set_aspect("equal")

    lc = LineCollection(segs, array=np.array(cols), cmap="turbo",
                        norm=Normalize(math.log(5), math.log(PMAX)),
                        linewidths=0.5, alpha=0.42, zorder=2)
    ax.add_collection(lc)

    # arrowheads on real first-steps: the arrow of time pointing INWARD (k -> t, smaller radius)
    firsts = [(k, t) for (k, t, lp) in steps if rad[k - 1] > 0.30]
    for k, t in firsts[::max(1, len(firsts) // 240)]:
        x0, y0 = px[k - 1], py[k - 1]; x1, y1 = px[t - 1], py[t - 1]
        xm, ym = 0.55 * x0 + 0.45 * x1, 0.55 * y0 + 0.45 * y1
        ax.annotate("", xy=(0.985 * xm, 0.985 * ym), xytext=(x0, y0),
                    arrowprops=dict(arrowstyle="-|>", color="#ff9a5c", lw=0.7, alpha=0.5), zorder=3)

    # twin centers = golden points (empty genealogy) on the real spiral
    ax.scatter(px[twin], py[twin], s=4.5, c="#ffd24a", alpha=0.9, edgecolors="none", zorder=4)

    # event horizon of the observer
    for r_, al in ((0.66, 0.9), (0.34, 0.5)):
        ax.add_patch(plt.Circle((0, 0), r_, fill=False, ls=(0, (6, 5)),
                                 ec="#7fd0ff", lw=1.1, alpha=al, zorder=5))
    ax.text(0.0, 0.70, "event horizon", color="#7fd0ff", ha="center", va="bottom",
            fontsize=10.5, alpha=0.9, zorder=6)

    # the observer at the root (present) — where every genealogy flows in
    ax.scatter([0], [0], s=560, c="#fff2cc", alpha=0.16, edgecolors="none", zorder=6)
    ax.scatter([0], [0], s=72, c="#ffffff", alpha=0.97, edgecolors="none", zorder=7)
    ax.text(0.045, -0.015, "observer  (now)", color="#ffe9b0", ha="left", va="center",
            fontsize=11, zorder=7)

    L = 1.02
    ax.set_xlim(-L, L); ax.set_ylim(-L, L); ax.set_xticks([]); ax.set_yticks([])
    [s.set_visible(False) for s in ax.spines.values()]
    cb = fig.colorbar(lc, ax=ax, pad=0.01, fraction=0.035)
    cb.set_label("Euclid prime p of the genealogy step  6k∓1 = p·(6t±1)", color="#aab")
    cb.ax.yaxis.set_tick_params(color="#778")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#aab")
    tick_ps = [q for q in (5, 7, 13, 23, 43, 79) if q <= PMAX]
    cb.set_ticks([math.log(q) for q in tick_ps]); cb.set_ticklabels([str(q) for q in tick_ps])
    ax.set_title("Euclid fractal · thought experiment: the observer at the root, the event horizon,\n"
                 "and the real old-peel genealogy flowing inward (the arrow of time) from all sides",
                 color="#cfe", fontsize=13)
    fig.savefig(os.path.join(OUT, "7_observer_horizon.png"), dpi=160,
                bbox_inches="tight", facecolor="#02030a")
    plt.close(fig); print("7_observer_horizon.png  (steps=%d, twins=%d)" % (len(steps), int(twin.sum())))

# ---------------------------------------------------------------------------
# (8) THE TIME-SPHERE: the real genealogy emanating from the 0-pole across the sphere.
# ---------------------------------------------------------------------------
def time_sphere(M=7000, PMAX=97, DEPTH=9):
    isp, ep, twin, steps = _chains(M, PMAX, DEPTH)
    m = np.arange(1, M + 1)

    # spherical placement: center k -> unit vector. k=1 at the 0-pole (bottom, z=-1),
    # k=M at the observer pole (top, z=+1); golden-angle longitude (equal-area spiral).
    z = -1.0 + 2.0 * (m - 1) / (M - 1)
    rho = np.sqrt(np.clip(1 - z * z, 0, 1))
    phi = m * GOLD
    V = np.column_stack([rho * np.cos(phi), rho * np.sin(phi), z])   # (M,3) unit vectors

    tilt = math.radians(20.0)
    ca, sa = math.cos(tilt), math.sin(tilt)
    def proj(P):                      # P:(...,3) -> screen (x, y) and depth toward viewer
        x = P[..., 0]; y = P[..., 1]; zc = P[..., 2]
        yy = y * ca - zc * sa         # rotate about x-axis
        zz = y * sa + zc * ca
        return x, zz, yy              # screen_x, screen_y, depth(front if >0)

    def slerp(a, b, n=18):
        d = float(np.clip(np.dot(a, b), -1, 1)); om = math.acos(d)
        u = np.linspace(0, 1, n)
        if om < 1e-6:
            return (1 - u)[:, None] * a + u[:, None] * b
        so = math.sin(om)
        return (np.sin((1 - u) * om)[:, None] * a + np.sin(u * om)[:, None] * b) / so

    fseg, fcol, bseg, bcol = [], [], [], []
    for (k, t, lp) in steps:
        arc = slerp(V[k - 1], V[t - 1])
        sx, sy, dep = proj(arc)
        pts = np.column_stack([sx, sy])
        seg = np.stack([pts[:-1], pts[1:]], axis=1)
        if dep.mean() >= -0.02:
            fseg.extend(seg); fcol.extend([lp] * len(seg))
        else:
            bseg.extend(seg); bcol.extend([lp] * len(seg))

    fig, ax = plt.subplots(figsize=(11.5, 12), facecolor="#03040a")
    ax.set_facecolor("#03040a"); ax.set_aspect("equal")
    norm = Normalize(math.log(5), math.log(PMAX))

    # sphere body + faint lat/long grid (front half brighter)
    ax.add_patch(plt.Circle((0, 0), 1.0, fc="#070a14", ec="#243050", lw=1.0, zorder=0))
    th = np.linspace(0, 2 * math.pi, 400)
    for lat in np.linspace(-0.8, 0.8, 7):                 # latitude rings
        r = math.sqrt(max(0, 1 - lat * lat))
        ring = np.column_stack([r * np.cos(th), r * np.sin(th), np.full_like(th, lat)])
        sx, sy, dep = proj(ring); vis = dep >= 0
        ax.plot(np.where(vis, sx, np.nan), np.where(vis, sy, np.nan),
                color="#1b2640", lw=0.5, alpha=0.7, zorder=1)
    for lon in np.linspace(0, 2 * math.pi, 12, endpoint=False):   # meridians
        tt = np.linspace(-math.pi / 2, math.pi / 2, 120)
        mer = np.column_stack([np.cos(tt) * math.cos(lon), np.cos(tt) * math.sin(lon), np.sin(tt)])
        sx, sy, dep = proj(mer); vis = dep >= 0
        ax.plot(np.where(vis, sx, np.nan), np.where(vis, sy, np.nan),
                color="#141d33", lw=0.4, alpha=0.6, zorder=1)

    # real genealogy net: back hemisphere faint, front hemisphere bright
    ax.add_collection(LineCollection(bseg, array=np.array(bcol), cmap="turbo", norm=norm,
                                     linewidths=0.4, alpha=0.13, zorder=2))
    lcf = LineCollection(fseg, array=np.array(fcol), cmap="turbo", norm=norm,
                         linewidths=0.5, alpha=0.5, zorder=4)
    ax.add_collection(lcf)

    # a few meridian guides with arrowheads: generative arrow of time 0-pole -> observer
    for lon in np.linspace(0, 2 * math.pi, 6, endpoint=False):
        tt = np.linspace(-math.pi / 2 + 0.05, math.pi / 2 - 0.05, 60)
        mer = np.column_stack([np.cos(tt) * math.cos(lon), np.cos(tt) * math.sin(lon), np.sin(tt)])
        sx, sy, dep = proj(mer); vis = dep >= 0
        if vis.sum() < 6:
            continue
        idx = np.where(vis)[0]; j = idx[int(len(idx) * 0.62)]
        ax.annotate("", xy=(sx[j + 2], sy[j + 2]), xytext=(sx[j], sy[j]),
                    arrowprops=dict(arrowstyle="-|>", color="#ff9a5c", lw=0.8, alpha=0.45), zorder=3)

    # twin centers as golden points (front bright, back faint)
    sxT, syT, depT = proj(V[twin])
    fr = depT >= 0
    ax.scatter(sxT[~fr], syT[~fr], s=2.0, c="#8a7420", alpha=0.35, edgecolors="none", zorder=3)
    ax.scatter(sxT[fr], syT[fr], s=4.2, c="#ffd24a", alpha=0.92, edgecolors="none", zorder=5)

    # the two poles
    bx, by, _ = proj(np.array([0, 0, -1.0]))              # 0-pole (start of time) bottom
    tx, ty, _ = proj(np.array([0, 0, 1.0]))               # observer pole top
    ax.scatter([tx], [ty], s=460, c="#fff2cc", alpha=0.16, edgecolors="none", zorder=6)
    ax.scatter([tx], [ty], s=64, c="#ffffff", alpha=0.97, edgecolors="none", zorder=7)
    ax.text(tx + 0.04, ty + 0.03, "observer  (now)", color="#ffe9b0", ha="left", va="bottom",
            fontsize=11, zorder=7)
    ax.scatter([bx], [by], s=320, c="#bfe4ff", alpha=0.16, edgecolors="none", zorder=6)
    ax.scatter([bx], [by], s=58, c="#eaf5ff", alpha=0.95, edgecolors="none", zorder=7)
    ax.text(bx + 0.04, by - 0.03, "start of time  ·  singularity 0", color="#bfe4ff",
            ha="left", va="top", fontsize=10.5, alpha=0.9, zorder=7)

    ax.set_xlim(-1.12, 1.12); ax.set_ylim(-1.18, 1.2); ax.set_xticks([]); ax.set_yticks([])
    [s.set_visible(False) for s in ax.spines.values()]
    cb = fig.colorbar(lcf, ax=ax, pad=0.01, fraction=0.035)
    cb.set_label("Euclid prime p of the genealogy step  6k∓1 = p·(6t±1)", color="#aab")
    cb.ax.yaxis.set_tick_params(color="#778")
    plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color="#aab")
    tick_ps = [q for q in (5, 7, 13, 23, 43, 79) if q <= PMAX]
    cb.set_ticks([math.log(q) for q in tick_ps]); cb.set_ticklabels([str(q) for q in tick_ps])
    ax.set_title("Euclid fractal · thought experiment: the time-sphere — the real old-peel genealogy\n"
                 "emanating from the 0-pole (start of time) across the surface to the observer at the antipode",
                 color="#cfe", fontsize=12.5)
    fig.savefig(os.path.join(OUT, "8_time_sphere.png"), dpi=160,
                bbox_inches="tight", facecolor="#03040a")
    plt.close(fig)
    print("8_time_sphere.png  (steps=%d, front=%d, twins=%d)"
          % (len(steps), len(fseg), int(twin.sum())))

if __name__ == "__main__":
    observer_horizon()
    time_sphere()
    print("done ->", OUT)
