"""
Euclid fractal · COSMOLOGICAL thought-experiment views (conceptual, not data-proofs).
Two overlays on the REAL twin-center substrate:
  (7) observer at the centre, event horizon, arrow of time winding INWARD from all sides;
  (8) the time-sphere: observer at one pole, the start of time (singularity 0) at the antipode,
      the genealogy fractal wrapping the sphere, meridian arrows = the arrow of time.
These are mental pictures of the coda's reading, drawn on the true golden spiral of centers.
Output: 7_observer_horizon.png, 8_time_sphere.png in out/.
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
import matplotlib as mpl
import math, os

OUT = os.path.join(os.path.dirname(__file__), "out")
os.makedirs(OUT, exist_ok=True)
mpl.rcParams["font.size"] = 11
PHI = math.pi * (3 - 5 ** 0.5)          # golden angle

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def twin_mask(M):
    P = primes_upto(6 * M + 2); isp = set(int(x) for x in P)
    m = np.arange(1, M)
    lo = np.array([(6 * k - 1) in isp for k in m])
    hi = np.array([(6 * k + 1) in isp for k in m])
    return m, lo, hi, (lo & hi)

# ---------------------------------------------------------------------------
# (7) OBSERVER · HORIZON · ARROW OF TIME WINDING INWARD
#     The contracting (inward-winding) fractal: the observer sits at the centre,
#     an event horizon circles them, and the arrow of time spirals in from every
#     side. Conceptual overlay on the real golden spiral of twin centres.
# ---------------------------------------------------------------------------
def observer_horizon(M=42000):
    m, lo, hi, twin = twin_mask(M)
    th = m * PHI
    r = np.sqrt(m)
    r = r / r.max()                       # normalise so the disc is the cosmos
    x, y = r * np.cos(th), r * np.sin(th)

    fig, ax = plt.subplots(figsize=(11, 11), facecolor="#02030a")
    ax.set_facecolor("#02030a"); ax.set_aspect("equal")

    # real substrate: faint one-side primes, golden twins (the winding genealogy)
    side = lo | hi
    ax.scatter(x[side], y[side], s=0.5, c="#243356", alpha=0.45, edgecolors="none", zorder=1)
    ax.scatter(x[twin], y[twin], s=4.5, c="#ffd24a", alpha=0.9, edgecolors="none", zorder=4)

    # arrow of time: logarithmic spirals winding INWARD to the observer, from all sides
    b = 0.30
    for a0 in np.linspace(0, 2 * math.pi, 24, endpoint=False):
        t = np.linspace(0, 5.2, 300)
        rr = 1.02 * np.exp(-b * t)
        aa = a0 + t
        sx, sy = rr * np.cos(aa), rr * np.sin(aa)
        ax.plot(sx, sy, color="#ff7a3c", lw=0.7, alpha=0.33, zorder=2)
        # arrowhead pointing inward, partway along
        k = 150
        ax.annotate("", xy=(sx[k + 8], sy[k + 8]), xytext=(sx[k], sy[k]),
                    arrowprops=dict(arrowstyle="-|>", color="#ff9a5c", lw=0.8, alpha=0.55), zorder=3)

    # event horizon of the observer
    for rad, al in ((0.62, 0.9), (0.30, 0.5)):
        ax.add_patch(plt.Circle((0, 0), rad, fill=False, ls=(0, (6, 5)),
                                 ec="#7fd0ff", lw=1.1, alpha=al, zorder=5))
    ax.text(0.0, 0.66, "event horizon", color="#7fd0ff", ha="center", va="bottom",
            fontsize=10.5, alpha=0.9, zorder=6)

    # the observer at the centre (the present; the arrow of time converges here)
    ax.scatter([0], [0], s=520, c="#fff2cc", alpha=0.16, edgecolors="none", zorder=6)
    ax.scatter([0], [0], s=70, c="#ffffff", alpha=0.95, edgecolors="none", zorder=7)
    ax.text(0.045, -0.02, "observer  (now)", color="#ffe9b0", ha="left", va="center",
            fontsize=11, zorder=7)

    lim = 1.06
    ax.set_xlim(-lim, lim); ax.set_ylim(-lim, lim)
    ax.set_xticks([]); ax.set_yticks([])
    [s.set_visible(False) for s in ax.spines.values()]
    ax.set_title("Euclid fractal · thought experiment: the observer at the centre,\n"
                 "the event horizon, and the arrow of time winding inward from all sides",
                 color="#cfe", fontsize=13)
    fig.savefig(os.path.join(OUT, "7_observer_horizon.png"), dpi=160,
                bbox_inches="tight", facecolor="#02030a")
    plt.close(fig); print("7_observer_horizon.png  (twins=%d)" % int(twin.sum()))

# ---------------------------------------------------------------------------
# (8) THE TIME-SPHERE: observer at one pole, start of time (0) at the antipode.
#     Spherical-Fibonacci genealogy wrapping the sphere; meridian arrows = the
#     arrow of time running from the singularity pole to the observer pole.
# ---------------------------------------------------------------------------
def time_sphere(M=26000):
    m, lo, hi, twin = twin_mask(M)
    N = len(m)
    # spherical Fibonacci: index 0 = bottom pole (start of time), N = top pole (observer)
    z = 1.0 - 2.0 * (np.arange(N) + 0.5) / N          # +1 (top) .. -1 (bottom)
    rad = np.sqrt(np.clip(1 - z * z, 0, 1))
    ang = np.arange(N) * PHI
    X = rad * np.cos(ang); Y = rad * np.sin(ang); Z = z
    # view tilted slightly; project to (X, Z'), depth = Y' for fake 3-D shading
    tilt = math.radians(18)
    Zp = Z * math.cos(tilt) - Y * math.sin(tilt)
    Yp = Z * math.sin(tilt) + Y * math.cos(tilt)      # depth toward viewer
    front = Yp >= -0.05

    fig, ax = plt.subplots(figsize=(11, 11.4), facecolor="#03040a")
    ax.set_facecolor("#03040a"); ax.set_aspect("equal")

    # sphere disc + faint lat/long grid
    th = np.linspace(0, 2 * math.pi, 400)
    ax.add_patch(plt.Circle((0, 0), 1.0, fc="#070a14", ec="#243050", lw=1.0, alpha=1.0, zorder=0))
    for lat in np.linspace(-0.8, 0.8, 7):
        rr = math.sqrt(1 - lat * lat)
        cx = rr * np.cos(th); cz = lat * math.cos(tilt) - rr * np.sin(th) * math.sin(tilt)
        cy = lat * math.sin(tilt) + rr * np.sin(th) * math.cos(tilt)
        vis = cy >= -0.02
        ax.plot(np.where(vis, cx, np.nan), np.where(vis, cz, np.nan),
                color="#1b2640", lw=0.5, alpha=0.7, zorder=1)

    # substrate points (front hemisphere): one-side faint, twins golden
    side = (lo | hi) & front
    ax.scatter(X[side], Zp[side], s=0.6, c="#2a3a63",
               alpha=0.42, edgecolors="none", zorder=2)
    tw = twin & front
    ax.scatter(X[tw], Zp[tw], s=4.2, c="#ffd24a", alpha=0.9, edgecolors="none", zorder=4)

    # meridian arrows: the arrow of time from the singularity pole (bottom) to the observer pole (top)
    for lon in np.linspace(0, 2 * math.pi, 10, endpoint=False):
        tt = np.linspace(-math.pi / 2 + 0.06, math.pi / 2 - 0.06, 120)
        mx = np.cos(tt) * math.cos(lon)
        my = np.cos(tt) * math.sin(lon)
        mz = np.sin(tt)
        pz = mz * math.cos(tilt) - my * math.sin(tilt)
        py = mz * math.sin(tilt) + my * math.cos(tilt)
        vis = py >= 0.0
        if vis.sum() < 6: continue
        ax.plot(np.where(vis, mx, np.nan), np.where(vis, pz, np.nan),
                color="#ff7a3c", lw=0.7, alpha=0.30, zorder=3)
        idx = np.where(vis)[0]
        j = idx[int(len(idx) * 0.6)]
        ax.annotate("", xy=(mx[j + 3], pz[j + 3]), xytext=(mx[j], pz[j]),
                    arrowprops=dict(arrowstyle="-|>", color="#ff9a5c", lw=0.8, alpha=0.5), zorder=3)

    # the two poles
    # top pole (observer, now)
    ax.scatter([0], [math.cos(tilt)], s=430, c="#fff2cc", alpha=0.16, edgecolors="none", zorder=5)
    ax.scatter([0], [math.cos(tilt)], s=60, c="#ffffff", alpha=0.95, edgecolors="none", zorder=6)
    ax.text(0.05, math.cos(tilt) + 0.04, "observer  (now)", color="#ffe9b0",
            ha="left", va="bottom", fontsize=11, zorder=6)
    # bottom pole (start of time, singularity 0) — on the far side, shown faint
    zb = -math.cos(tilt)
    ax.scatter([0], [zb], s=260, c="#bfe4ff", alpha=0.12, edgecolors="none", zorder=1)
    ax.scatter([0], [zb], s=42, c="#dff0ff", alpha=0.7, edgecolors="none", zorder=1)
    ax.text(0.05, zb - 0.04, "start of time  ·  singularity 0", color="#bfe4ff",
            ha="left", va="top", fontsize=10.5, alpha=0.85, zorder=1)

    ax.set_xlim(-1.12, 1.12); ax.set_ylim(-1.2, 1.2)
    ax.set_xticks([]); ax.set_yticks([])
    [s.set_visible(False) for s in ax.spines.values()]
    ax.set_title("Euclid fractal · thought experiment: the time-sphere — observer at one pole,\n"
                 "the start of time (singularity 0) at the antipode; meridians are the arrow of time",
                 color="#cfe", fontsize=13)
    fig.savefig(os.path.join(OUT, "8_time_sphere.png"), dpi=160,
                bbox_inches="tight", facecolor="#03040a")
    plt.close(fig); print("8_time_sphere.png  (twins on front=%d)" % int((twin & front).sum()))

if __name__ == "__main__":
    observer_horizon()
    time_sphere()
    print("done ->", OUT)
