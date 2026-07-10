# packing_walk_harness.py -- P0 gate (packing walk): census of the centered triple
# (L, C, R) = (6m-1, 6m, 6m+1) in the DISTINCT-prime dimension omega, plus the
# EXACT truncated per-q layer and the pre-registered foil-v2 escalation.
#
# CRASH RESILIENCE: every stage is a separate argv mode run as its own python
# invocation appending to tools/packing_walk_run1.log -- partial progress survives:
#   w1  centered dimension walk: joint omega tables clipped 1..6, MI(center;wings)
#       with permutation nulls, transition matrices along n and along m,
#       return-to-(Omega=1) times of the wings vs shuffled null;
#   w2  additive shift correlations: Erdos-Kac u(n) = (omega(n)-lnln n)/sqrt(lnln n),
#       corr(u(n),u(n+2)) at n <= 6e7; wing/center correlations at 1e7/1e9/1e12
#       (1e12 confirmatory only), each vs permutation null; scale trend;
#   w3  twin-collision census: E[omega(C)|twin] - E[omega(C)|no-twin] vs the exact
#       truncated prediction sum_{5<=q<=B}(1/(q-2) - 1/q) at B=31; same on
#       survivors A in {13,31}; v2(C)/v3(C) twin vs not; mirror asymmetry;
#   w4  EXACT truncated layer (fractions.Fraction, no scanning): joint pgf of
#       (d_B(L), d_B(C), d_B(R)) with identities E1-E4, survivor-conditioned pgf,
#       FULL-period enumeration cross-check at B=7 (35) and B=13 (5005),
#       kernel census constants 48 / 15 / 1485;
#   w5  foil-v2 (pre-registered): candidates C1..C5 on grid A in {13,31,101} x
#       X in {1e6,1e9}, H=50, NW=3000/1000, loads S / S0 (self-excluded) /
#       S'' (split-window), independence null exactly as in
#       gain_complex_harness.gate_g3 (lambda resampled from pooled empirical).
#
# Per-q competition law (exact, the spine of the stage): for every prime q >= 5
# the residue classes of m mod q split 1 / 1 / 1 / (q-3):
#   q | L  at  m ==  inv6 (mod q);   q | R  at  m == -inv6 (mod q);
#   q | C  at  m ==  0    (mod q);   the remaining q-3 classes are neutral
# (inv6 = 6^{-1} mod q; the three special classes are pairwise distinct for q >= 5).
#
# DISCLOSURE: omega = # DISTINCT prime factors, so omega = 1 includes prime
# powers (25, 49, ...);  Omega = 1 <=> prime;  twin <=> Omega_L = Omega_R = 1.
#
# House style: numpy, RNG seed 20260710, N_PERM = 200, fixed-width tables
# (matches tools/wing_grade_harness.py and tools/gain_complex_harness.py).
# The omega sieve to 6e7+2 is cached in $PACKING_WALK_CACHE (default: system
# temp dir) so stages w1/w2/w3 share it across separate invocations.

import math
import os
import sys
import tempfile
import time
from fractions import Fraction

import numpy as np

SEED = 20260710
N_PERM = 200
RNG = np.random.default_rng(SEED)

N_BIG = 6 * 10**7 + 2          # omega-sieve ceiling: wings/center of m <= 1e7
M_MED = 10**7                  # main m-scale of the walk
M_RET = 10**6                  # return-time scale (Omega = 1 <=> prime wing)
TRIPLE_WINDOWS = [(10**9, 10**6), (10**12, 2 * 10**5)]   # (X, W) in m
CACHE_DIR = os.environ.get("PACKING_WALK_CACHE", tempfile.gettempdir())

CLIP_LABELS = ["1", "2", "3", "4", "5", ">=6"]
FOLD3_LABELS = ["1", "2", ">=3"]
Q31 = (5, 7, 11, 13, 17, 19, 23, 29, 31)


# ---------- sieves ----------

def prime_sieve(n):
    """Boolean array is_prime[0..n]."""
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def primes_upto(n):
    return [int(p) for p in np.flatnonzero(prime_sieve(n))]


def omega_sieve(n):
    """int8 array over 0..n: number of DISTINCT prime factors (each prime once)."""
    lit = np.zeros(n + 1, dtype=np.int8)
    isp = prime_sieve(n)
    for p in np.flatnonzero(isp):
        p = int(p)
        lit[p::p] += 1
    return lit


def omega_cached():
    """omega(n) for n <= N_BIG, cached across the separate stage invocations."""
    path = os.path.join(CACHE_DIR, "packing_walk_omega_6e7.npy")
    if os.path.exists(path):
        lit = np.load(path)
        if lit.size == N_BIG + 1:
            print(f"[omega sieve] loaded cache {path}")
            return lit
    t0 = time.time()
    lit = omega_sieve(N_BIG)
    print(f"[omega sieve] built omega(n), n <= {N_BIG} in {time.time()-t0:.1f}s")
    try:
        np.save(path, lit)
        print(f"[omega sieve] cached to {path}")
    except OSError:
        print("[omega sieve] cache write failed (non-fatal)")
    return lit


def window_triple(X, W, want_center=True):
    """Segmented exact (Omega, omega) for the triple over m in [X, X+W).

    Returns dict off -> (big, lit) for off in {-1, 0, +1} (0 only if wanted).
    Adapted from gain_complex_harness.omega_range, counting DISTINCT factors:
    lit incremented ONCE per prime, powers still divided out of the remainder
    so the leftover-prime detection (rem > 1) stays exact.
    """
    lim = int(math.isqrt(6 * (X + W) + 2)) + 1
    ps = primes_upto(lim)
    out = {}
    offs = (-1, 1, 0) if want_center else (-1, 1)
    t0 = time.time()
    for off in offs:
        vals = 6 * (X + np.arange(W, dtype=np.int64)) + off
        rem = vals.copy()
        big = np.zeros(W, dtype=np.int16)
        lit = np.zeros(W, dtype=np.int16)
        for p in ps:
            if p < 5:
                if off != 0:
                    continue               # 2, 3 never divide the wings
                idx = np.arange(W)         # ... and always divide the center
            else:
                if off == 0:
                    r = 0                  # q | 6m  <=>  m == 0 (mod q)
                else:
                    inv6 = pow(6, -1, p)
                    r = inv6 if off == -1 else (p - inv6) % p
                first = (r - X) % p
                if first >= W:
                    continue
                idx = np.arange(first, W, p)
            lit[idx] += 1
            rem[idx] //= p
            big[idx] += 1
            cur = idx[rem[idx] % p == 0]
            while cur.size:
                rem[cur] //= p
                big[cur] += 1
                cur = cur[rem[cur] % p == 0]
        left = rem > 1
        big[left] += 1
        lit[left] += 1
        out[off] = (big.astype(np.int32), lit.astype(np.int32))
    print(f"[window X={X:.1e} W={W:.0e}] exact triple grades in {time.time()-t0:.1f}s "
          f"(primes to {ps[-1]})")
    return out


def survivor_mask_of(m_arr, A):
    """Clean(A, m): no prime q in [5, A] divides either wing."""
    ok = np.ones(m_arr.size, dtype=bool)
    for q in primes_upto(A):
        if q < 5:
            continue
        inv6 = pow(6, -1, q)
        r = m_arr % q
        ok &= (r != inv6) & (r != (q - inv6) % q)
    return ok


# ---------- info-theory / statistics helpers ----------

def clip6(a):
    return np.minimum(np.maximum(a.astype(np.int64), 1), 6)


def fold3(a):
    return np.minimum(a.astype(np.int64), 3)


def mi_bits(x, y, nx, ny):
    """Plug-in MI (bits) of int arrays with alphabets 0..nx-1 / 0..ny-1."""
    joint = np.bincount(x * ny + y, minlength=nx * ny).astype(np.float64)
    joint = joint.reshape(nx, ny)
    joint /= joint.sum()
    px = joint.sum(1, keepdims=True)
    py = joint.sum(0, keepdims=True)
    nz = joint > 0
    return float((joint[nz] * np.log2(joint[nz] / (px @ py)[nz])).sum())


def mi_named(x, y, nx, ny, label, n_perm=N_PERM):
    x = x.astype(np.int64)
    y = y.astype(np.int64)
    mi = mi_bits(x, y, nx, ny)
    xs = x.copy()
    null = np.empty(n_perm)
    for i in range(n_perm):
        RNG.shuffle(xs)
        null[i] = mi_bits(xs, y, nx, ny)
    mu, sd = null.mean(), null.std() + 1e-15
    print(f"  MI {label:<46} = {mi:.6f} bits  null {mu:.6f}+/-{sd:.6f}  "
          f"z = {(mi - mu) / sd:+9.1f}  (n={x.size})")
    return mi, (mi - mu) / sd


def corr_named(x, y, label, n_perm=N_PERM):
    """Pearson r with permutation null (one series reshuffled n_perm times)."""
    mx, sx = float(x.mean(dtype=np.float64)), float(x.std(dtype=np.float64))
    my, sy = float(y.mean(dtype=np.float64)), float(y.std(dtype=np.float64))
    xs = ((x - mx) / (sx + 1e-30)).astype(np.float64)
    ys = ((y - my) / (sy + 1e-30)).astype(np.float64)
    n = xs.size
    r = float(np.dot(xs, ys)) / n
    null = np.empty(n_perm)
    for i in range(n_perm):
        RNG.shuffle(xs)
        null[i] = float(np.dot(xs, ys)) / n
    mu, sd = null.mean(), null.std() + 1e-15
    z = (r - mu) / sd
    print(f"  corr {label:<44} = {r:+.6f}  null {mu:+.6f}+/-{sd:.6f}  "
          f"z = {z:+9.1f}  (n={n})")
    return r, z


def print_joint(a, b, title):
    """6x6 percentage table of two arrays already clipped to 1..6."""
    k = 6
    tab = np.bincount((a - 1) * k + (b - 1), minlength=k * k).astype(np.float64)
    tab = tab.reshape(k, k)
    tot = tab.sum()
    print(f"\n  joint {title}  [rows=first, cols=second, n={int(tot)}, %]")
    print("        " + "".join(f"{c:>8}" for c in CLIP_LABELS))
    for i in range(k):
        print(f"  {CLIP_LABELS[i]:>5} " +
              "".join(f"{100 * tab[i, j] / tot:8.3f}" for j in range(k)))


def print_transition(cnt, labels, title):
    k = len(labels)
    rs = cnt.sum(1).astype(np.float64)
    print(f"\n  transition {title}  [rows -> cols, row-stochastic]")
    print("            " + "".join(f"{c:>8}" for c in labels))
    for i in range(k):
        print(f"  {labels[i]:>9} " +
              "".join(f"{cnt[i, j] / max(rs[i], 1):8.4f}" for j in range(k)))
    marg = cnt.sum(1) / cnt.sum()
    print("    marginal " + " ".join(f"{labels[i]}:{marg[i]:.4f}" for i in range(k)))


# ---------- stage W1: centered dimension walk ----------

def transition_chunked(arr8, lo, hi, k=6):
    """Counts of clip6 transitions n -> n+1 for n in [lo, hi-1] (chunked)."""
    cnt = np.zeros(k * k, dtype=np.int64)
    step = 10**7
    for a in range(lo, hi, step):
        b = min(a + step, hi)
        x = clip6(arr8[a:b]) - 1
        y = clip6(arr8[a + 1:b + 1]) - 1
        cnt += np.bincount(x * k + y, minlength=k * k)
    return cnt.reshape(k, k)


def return_report(mask, name):
    idx = np.flatnonzero(mask)
    gaps = np.diff(idx)

    def stats(g):
        return np.array([g.mean(), g.std(), (g == 1).mean(),
                         (g >= 10).mean(), float(g.max())])

    def hist(g):
        h = [(g == kk).mean() for kk in range(1, 13)]
        h.append((g >= 13).mean())
        return np.array(h)

    act_s, act_h = stats(gaps), hist(gaps)
    null_s = np.empty((N_PERM, 5))
    null_h = np.empty((N_PERM, 13))
    ms = mask.copy()
    for i in range(N_PERM):
        RNG.shuffle(ms)
        gi = np.diff(np.flatnonzero(ms))
        null_s[i], null_h[i] = stats(gi), hist(gi)
    print(f"\n  return-to-(Omega=1) times, wing {name}, m <= {M_RET:.0e}: "
          f"{idx.size} prime wings, {gaps.size} gaps  (null: {N_PERM} shuffles)")
    print("     gap    actual%     null%       sd%         z")
    labs = [str(kk) for kk in range(1, 13)] + [">=13"]
    for kk in range(13):
        mu, sd = null_h[:, kk].mean(), null_h[:, kk].std() + 1e-15
        print(f"    {labs[kk]:>4} {100*act_h[kk]:10.4f} {100*mu:10.4f} "
              f"{100*sd:10.4f} {(act_h[kk]-mu)/sd:+9.1f}")
    for j, nm in enumerate(["mean", "sd", "P(gap=1)", "P(gap>=10)", "max"]):
        mu, sd = null_s[:, j].mean(), null_s[:, j].std() + 1e-15
        print(f"    stat {nm:<10} actual {act_s[j]:10.4f}  "
              f"null {mu:10.4f}+/-{sd:8.4f}  z {(act_s[j]-mu)/sd:+9.1f}")


def w1_block(wL, wC, wR, title):
    """Joint tables + the four named MIs for one data set."""
    cL, cC, cR = clip6(wL), clip6(wC), clip6(wR)
    print(f"\n-- {title} --")
    print(f"  mean omega: L {wL.mean():.4f}   C {wC.mean():.4f}   R {wR.mean():.4f}"
          f"   (C carries 2 and 3 for every center: +2 exactly)")
    print_joint(cL, cR, "(omega_L, omega_R) clipped 1..6")
    print_joint(cC, cL, "(omega_C, omega_L) clipped 1..6")
    print_joint(cC, cR, "(omega_C, omega_R) clipped 1..6")
    pair = (cL - 1) * 6 + (cR - 1)
    mi_named(cC - 1, pair, 6, 36, "(omega_C ; (omega_L, omega_R))")
    mi_named(cL - 1, cR - 1, 6, 6, "(omega_L ; omega_R)  [reference]")
    sel = wC <= 3
    mi_named((cL - 1)[sel], (cR - 1)[sel], 6, 6,
             "(omega_L ; omega_R | omega_C in {2,3})")
    sel = wC >= 4
    mi_named((cL - 1)[sel], (cR - 1)[sel], 6, 6,
             "(omega_L ; omega_R | omega_C >= 4)")


def stage_w1():
    lit = omega_cached()
    m = np.arange(1, M_MED + 1, dtype=np.int64)
    wL = lit[6 * m - 1].astype(np.int64)
    wC = lit[6 * m].astype(np.int64)
    wR = lit[6 * m + 1].astype(np.int64)

    w1_block(wL, wC, wR, f"main scale m <= {M_MED:.0e} (exhaustive sieve)")

    print("\n-- transition structure (main scale) --")
    tr_n = transition_chunked(lit, 2, N_BIG)
    print_transition(tr_n, CLIP_LABELS,
                     f"clip6(omega(n)) -> clip6(omega(n+1)), n in [2, {N_BIG}]")
    s = (fold3(wL) - 1) * 3 + (fold3(wR) - 1)
    tr_m = np.bincount(s[:-1] * 9 + s[1:], minlength=81).reshape(9, 9)
    pair_labels = [f"({a},{b})" for a in FOLD3_LABELS for b in FOLD3_LABELS]
    print_transition(tr_m, pair_labels,
                     "wing pair (fold3 omega_L, fold3 omega_R), m -> m+1"
                     "  [fold3 = clip to 1,2,>=3]")

    print("\n-- return times of the wings (Omega = 1 <=> prime) --")
    isp = prime_sieve(6 * M_RET + 1)
    mr = np.arange(1, M_RET + 1, dtype=np.int64)
    return_report(isp[6 * mr - 1], "L = 6m-1")
    return_report(isp[6 * mr + 1], "R = 6m+1")

    for X, W in TRIPLE_WINDOWS:
        g = window_triple(X, W, want_center=True)
        w1_block(g[-1][1].astype(np.int64), g[0][1].astype(np.int64),
                 g[1][1].astype(np.int64),
                 f"window [{X:.0e}, +{W:.0e}) (segmented exact)")


# ---------- stage W2: additive shift correlations ----------

def ek_u(cnts, vals):
    """Erdos-Kac normalized u = (omega - lnln)/sqrt(lnln); requires vals >= 3."""
    ll = np.log(np.log(vals.astype(np.float64)))
    return (cnts.astype(np.float64) - ll) / np.sqrt(ll)


def u_line(lit, nmax):
    """u(n) for n = 0..nmax as float32 (entries n < 3 are 0 and never used)."""
    u = np.zeros(nmax + 1, dtype=np.float32)
    step = 10**7
    for lo in range(3, nmax + 1, step):
        hi = min(lo + step - 1, nmax)
        v = np.arange(lo, hi + 1, dtype=np.float64)
        ll = np.log(np.log(v))
        u[lo:hi + 1] = ((lit[lo:hi + 1] - ll) / np.sqrt(ll)).astype(np.float32)
    return u


def stage_w2():
    lit = omega_cached()
    print("\nErdos-Kac u(n) = (omega(n) - lnln n)/sqrt(lnln n), n >= 3;"
          " every corr vs its own permutation null (N_PERM shuffles)")

    print(f"\n-- shift-2 correlation on the full line, n <= {N_BIG} --")
    u = u_line(lit, N_BIG)
    corr_named(u[3:N_BIG - 1], u[5:N_BIG + 1], f"(u(n), u(n+2)), n <= {N_BIG:.0e}")
    del u

    trend = {}
    print(f"\n-- triple correlations at m <= {M_MED:.0e} --")
    m = np.arange(1, M_MED + 1, dtype=np.int64)
    L, C, R = 6 * m - 1, 6 * m, 6 * m + 1
    uL, uC, uR = ek_u(lit[L], L), ek_u(lit[C], C), ek_u(lit[R], R)
    trend[("L-R", 10**7)] = corr_named(uL, uR, "(u_L, u_R) at 1e7")[0]
    trend[("C-L", 10**7)] = corr_named(uC, uL, "(u_C, u_L) at 1e7")[0]
    trend[("C-R", 10**7)] = corr_named(uC, uR, "(u_C, u_R) at 1e7")[0]
    del uL, uC, uR, L, C, R, m

    for X, W in TRIPLE_WINDOWS:
        tag = "confirmatory only" if X == 10**12 else "segmented exact"
        print(f"\n-- triple correlations, window [{X:.0e}, +{W:.0e}) ({tag}) --")
        g = window_triple(X, W, want_center=True)
        i = np.arange(W, dtype=np.int64)
        vL, vC, vR = 6 * (X + i) - 1, 6 * (X + i), 6 * (X + i) + 1
        uL, uC, uR = ek_u(g[-1][1], vL), ek_u(g[0][1], vC), ek_u(g[1][1], vR)
        trend[("L-R", X)] = corr_named(uL, uR, f"(u_L, u_R) at {X:.0e}")[0]
        trend[("C-L", X)] = corr_named(uC, uL, f"(u_C, u_L) at {X:.0e}")[0]
        trend[("C-R", X)] = corr_named(uC, uR, f"(u_C, u_R) at {X:.0e}")[0]

    print("\n-- scale trend of r (addresses the L1 open decay-form goal) --")
    print("    pair        1e7          1e9          1e12(confirm)")
    for pr in ("L-R", "C-L", "C-R"):
        print(f"    {pr:<6} " + "".join(
            f"{trend[(pr, X)]:+12.6f} " for X in (10**7, 10**9, 10**12)))


# ---------- stage W3: twin-collision census ----------

def valuation(vals, p):
    v = np.zeros(vals.size, dtype=np.int64)
    cur = vals.copy()
    idx = np.flatnonzero(cur % p == 0)
    while idx.size:
        v[idx] += 1
        cur[idx] //= p
        idx = idx[cur[idx] % p == 0]
    return v


def contrast_report(wC, twin, title, preds):
    n1, n2 = int(twin.sum()), int((~twin).sum())
    m1, m2 = float(wC[twin].mean()), float(wC[~twin].mean())
    s1, s2 = float(wC[twin].std()), float(wC[~twin].std())
    d = m1 - m2
    z = d / math.sqrt(s1 * s1 / n1 + s2 * s2 / n2)
    print(f"\n  center contrast {title}:")
    print(f"    E[omega_C | twin]    = {m1:.6f}   (n_twin = {n1})")
    print(f"    E[omega_C | no-twin] = {m2:.6f}   (n = {n2})")
    print(f"    contrast = {d:+.6f}   z = {z:+8.2f}")
    for lab, val in preds:
        print(f"    prediction {lab:<28} = {val:+.6f}")
    return d, z


def vdist_report(v, twin, p, title):
    vv = np.clip(v, 1, 6)
    labs = ["1", "2", "3", "4", "5", ">=6"]
    print(f"\n  v_{p}(C) distribution {title}  [% within group]")
    for grp, sel in (("twin", twin), ("no-twin", ~twin)):
        h = np.bincount(vv[sel] - 1, minlength=6).astype(np.float64)
        h /= h.sum()
        row = " ".join(f"{labs[k]}:{100 * h[k]:7.4f}" for k in range(6))
        print(f"    {grp:>8}: {row}  mean={v[sel].mean():.6f}")
    n1, n2 = int(twin.sum()), int((~twin).sum())
    m1, m2 = float(v[twin].mean()), float(v[~twin].mean())
    s1, s2 = float(v[twin].std()), float(v[~twin].std())
    z = (m1 - m2) / math.sqrt(s1 * s1 / n1 + s2 * s2 / n2)
    print(f"    mean diff (twin - no-twin) = {m1 - m2:+.6f}   z = {z:+.2f}")


def mirror_report(dL, dR, title):
    D = dL.astype(np.float64) - dR.astype(np.float64)
    n = D.size
    mean, sd = float(D.mean()), float(D.std())
    z_mean = mean / (sd / math.sqrt(n))
    m3 = float(((D - mean) ** 3).mean())
    skew = m3 / sd**3
    z_skew = skew / math.sqrt(6.0 / n)
    c = np.clip(D, -4, 4).astype(np.int64) + 4
    h = np.bincount(c, minlength=9).astype(np.float64) / n
    print(f"\n  mirror asymmetry {title}: distribution of omega_L - omega_R [%]")
    print("    " + "".join(f"{k:>8}" for k in
                           ["<=-4", "-3", "-2", "-1", "0", "+1", "+2", "+3", ">=+4"]))
    print("    " + "".join(f"{100 * h[k]:8.3f}" for k in range(9)))
    print(f"    mean = {mean:+.6f}  z_mean = {z_mean:+7.2f}   "
          f"skew = {skew:+.6f}  z_skew = {z_skew:+7.2f}   (n={n})")


def prime_state_table(primeL, primeR, wL, wR, title):
    fL, fR = fold3(wL), fold3(wR)
    print(f"\n  P(wing prime | opposite-wing state) {title}"
          "   [state = fold3(omega_opposite); two-proportion z]")
    print("    state      n_L    P(L prime|st_R)      n_R    P(R prime|st_L)"
          "       diff        z")
    for s in (1, 2, 3):
        selL = fR == s
        selR = fL == s
        n1, n2 = int(selL.sum()), int(selR.sum())
        p1 = float(primeL[selL].mean())
        p2 = float(primeR[selR].mean())
        pp = (float(primeL[selL].sum()) + float(primeR[selR].sum())) / (n1 + n2)
        se = math.sqrt(max(pp * (1 - pp) * (1.0 / n1 + 1.0 / n2), 1e-30))
        print(f"    {FOLD3_LABELS[s-1]:>5} {n1:9d} {p1:18.6f} {n2:9d} "
              f"{p2:18.6f} {p1 - p2:+10.6f} {(p1 - p2) / se:+9.2f}")


def enrichment_partial(a, b, ps):
    """sum over primes a < q <= b of (1/(q-2) - 1/q), float."""
    return sum(1.0 / (q - 2) - 1.0 / q for q in ps if a < q <= b)


def stage_w3():
    lit = omega_cached()
    isp = prime_sieve(N_BIG)
    ps_ref = primes_upto(10**5)
    pred31 = sum(Fraction(1, q - 2) - Fraction(1, q) for q in Q31)
    print(f"\nexact truncated prediction sum_(5<=q<=31)(1/(q-2) - 1/q) "
          f"= {pred31} = {float(pred31):.6f}")
    print(f"reference partial sums: B=101: {enrichment_partial(4, 101, ps_ref):.6f}"
          f"   B=1e3: {enrichment_partial(4, 10**3, ps_ref):.6f}"
          f"   B=1e5: {enrichment_partial(4, 10**5, ps_ref):.6f}")

    m = np.arange(1, M_MED + 1, dtype=np.int64)
    L, C, R = 6 * m - 1, 6 * m, 6 * m + 1
    wC = lit[C].astype(np.float64)
    wL8, wR8 = lit[L].astype(np.int64), lit[R].astype(np.int64)
    twin = isp[L] & isp[R]
    print(f"\n-- m <= {M_MED:.0e} (exhaustive; twin <=> both wings prime) --")
    contrast_report(wC, twin, f"all centers, m <= {M_MED:.0e}",
                    [("truncated B=31 (exact)", float(pred31)),
                     ("all q <= 1e5 (reference)",
                      enrichment_partial(4, 10**5, ps_ref))])
    for A in (13, 31):
        s = survivor_mask_of(m, A)
        contrast_report(wC[s], twin[s], f"survivors A={A}, m <= {M_MED:.0e}",
                        [(f"tail {A}<q<=31 (truncated)",
                          enrichment_partial(A, 31, ps_ref)),
                         (f"tail {A}<q<=1e5 (reference)",
                          enrichment_partial(A, 10**5, ps_ref))])

    for p in (2, 3):
        vdist_report(1 + valuation(m, p), twin, p, f"(m <= {M_MED:.0e})")

    mirror_report(wL8, wR8, f"m <= {M_MED:.0e}")
    prime_state_table(isp[L], isp[R], wL8, wR8, f"m <= {M_MED:.0e}")

    X, W = TRIPLE_WINDOWS[0]
    print(f"\n-- window [{X:.0e}, +{W:.0e}) (segmented exact; twin <=> Omega=1 both) --")
    g = window_triple(X, W, want_center=True)
    bigL, litL = g[-1]
    bigC, litC = g[0]
    bigR, litR = g[1]
    twinw = (bigL == 1) & (bigR == 1)
    contrast_report(litC.astype(np.float64), twinw, f"window [{X:.0e}, +{W:.0e})",
                    [("truncated B=31 (exact)", float(pred31)),
                     ("all q <= 1e5 (reference)",
                      enrichment_partial(4, 10**5, ps_ref))])
    i = X + np.arange(W, dtype=np.int64)
    for p in (2, 3):
        vdist_report(1 + valuation(i, p), twinw, p, f"(window {X:.0e})")
    mirror_report(litL, litR, f"window [{X:.0e}, +{W:.0e})")
    prime_state_table(bigL == 1, bigR == 1, litL, litR,
                      f"window [{X:.0e}, +{W:.0e})")


# ---------- stage W4: EXACT truncated layer (fractions, no scanning) ----------

def qs_upto(B):
    return [q for q in Q31 if q <= B]


def pgf_joint(B):
    """dict (i,j,k) -> Fraction: joint pgf coeffs of (d_B(L), d_B(C), d_B(R)),
    center counting only q >= 5;  product over q of ((q-3) + x + y + z)/q."""
    poly = {(0, 0, 0): Fraction(1)}
    for q in qs_upto(B):
        new = {}
        for (i, j, k), c in poly.items():
            for key, w in (((i, j, k), q - 3), ((i + 1, j, k), 1),
                           ((i, j + 1, k), 1), ((i, j, k + 1), 1)):
                new[key] = new.get(key, Fraction(0)) + c * Fraction(w, q)
        poly = new
    return poly


def stage_w4():
    print("\nEXACT layer over fractions.Fraction -- no scanning, no floats in the")
    print("assertions.  Joint pgf of (d_B(L), d_B(C), d_B(R)) with the center")
    print("counting ONLY q >= 5:  P_B(x,y,z) = prod_(5<=q<=B) ((q-3) + x + y + z)/q,")
    print("driven by the exact 1/1/1/(q-3) residue-class split of m mod q.")
    all_ok = True

    for B in (7, 13, 31):
        qs = qs_upto(B)
        poly = pgf_joint(B)
        print(f"\n-- B = {B}  (primes {qs}, {len(poly)} pgf terms) --")

        e1 = [sum(c * t[d] for t, c in poly.items()) for d in range(3)]
        t1 = sum(Fraction(1, q) for q in qs)
        ok1 = all(e == t1 for e in e1)
        all_ok &= ok1
        print(f"  E1 marginal means: E[d(L)] = E[d(C)] = E[d(R)] = {t1} "
              f"= {float(t1):.6f}   sum 1/q: {'PASS' if ok1 else 'FAIL'}")

        t2 = -sum(Fraction(1, q * q) for q in qs)
        ok2 = True
        for a, b, nm in ((0, 1, "L,C"), ((0), 2, "L,R"), (1, 2, "C,R")):
            eab = sum(c * t[a] * t[b] for t, c in poly.items())
            cov = eab - e1[a] * e1[b]
            ok2 &= (cov == t2)
        all_ok &= ok2
        print(f"  E2/E3 covariances: cov(d_L,d_C) = cov(d_L,d_R) = cov(d_C,d_R) = "
              f"{t2} = {float(t2):.8f}   -sum 1/q^2: {'PASS' if ok2 else 'FAIL'}")

        pclean = sum(c for t, c in poly.items() if t[0] == 0 and t[2] == 0)
        tclean = Fraction(1)
        for q in qs:
            tclean *= Fraction(q - 2, q)
        ec = sum(c * t[1] for t, c in poly.items()
                 if t[0] == 0 and t[2] == 0) / pclean
        enrich = ec - e1[1]
        t4 = sum(Fraction(1, q - 2) - Fraction(1, q) for q in qs)
        ok4 = (pclean == tclean) and (enrich == t4)
        all_ok &= ok4
        print(f"  E4 clean-center layer: P(clean) = {pclean} = {float(pclean):.6f} "
              f"(prod (q-2)/q)")
        print(f"     E[d(C)|clean] - E[d(C)] = {enrich} = {float(enrich):.6f} "
              f"= sum(1/(q-2) - 1/q): {'PASS' if ok4 else 'FAIL'}")

        cond = {}
        for t, c in poly.items():
            if t[0] == 0 and t[2] == 0:
                cond[t[1]] = cond.get(t[1], Fraction(0)) + c / pclean
        direct = {0: Fraction(1)}
        for q in qs:
            new = {}
            for j, c in direct.items():
                new[j] = new.get(j, Fraction(0)) + c * Fraction(q - 3, q - 2)
                new[j + 1] = new.get(j + 1, Fraction(0)) + c * Fraction(1, q - 2)
            direct = new
        ok5 = cond == direct
        all_ok &= ok5
        print(f"     survivor-conditioned pgf = prod((q-3) + y)/(q-2): "
              f"{'PASS' if ok5 else 'FAIL'}   coeffs "
              + " ".join(f"y^{j}:{c}" for j, c in sorted(direct.items())))

    print("\n-- FULL-period enumeration cross-check (assert EXACT equality) --")
    for B, period in ((7, 35), (13, 5005)):
        qs = qs_upto(B)
        poly = pgf_joint(B)
        counts = {}
        for mm in range(1, period + 1):
            t = (sum(1 for q in qs if (6 * mm - 1) % q == 0),
                 sum(1 for q in qs if (6 * mm) % q == 0),
                 sum(1 for q in qs if (6 * mm + 1) % q == 0))
            counts[t] = counts.get(t, 0) + 1
        same_keys = set(counts) == set(poly)
        exact = same_keys and all(Fraction(counts[t], period) == poly[t]
                                  for t in counts)
        all_ok &= exact
        print(f"  B={B:>2} period={period:>5}: {len(counts)} occupied cells, "
              f"pgf == enumeration EXACTLY: {'PASS' if exact else 'FAIL'}")

    c210 = sum(1 for r in range(210) if all(r % p for p in (2, 3, 5, 7)))
    c35 = sum(1 for mm in range(1, 36)
              if all((6 * mm - 1) % q and (6 * mm + 1) % q for q in (5, 7)))
    c5005 = sum(1 for mm in range(1, 5006)
                if all((6 * mm - 1) % q and (6 * mm + 1) % q
                       for q in (5, 7, 11, 13)))
    okc = (c210, c35, c5005) == (48, 15, 1485)
    all_ok &= okc
    print("\n" + "=" * 74)
    print("  KERNEL CENSUS CONSTANTS (targets for the Lean layer):")
    print(f"    #{{r < 210    : truncDim(7, r) = 0}}       = {c210:>5}   "
          f"(predicted 48)   {'PASS' if c210 == 48 else 'FAIL'}")
    print(f"    #{{m in [1,35]   : both wings d_7  = 0}}   = {c35:>5}   "
          f"(predicted 15)   {'PASS' if c35 == 15 else 'FAIL'}")
    print(f"    #{{m in [1,5005] : both wings d_13 = 0}}   = {c5005:>5}   "
          f"(predicted 1485) {'PASS' if c5005 == 1485 else 'FAIL'}")
    print("  NOTE: truncDim(B, n) counts ALL primes q <= B dividing n, INCLUDING")
    print("  2 and 3 (Lean def uses range(B+1) over all primes).  For the")
    print("  210-census that is exactly the residues coprime to 2*3*5*7, so the")
    print("  count is phi(210) = 48.  For the WING censuses 2 and 3 never divide")
    print("  6m+-1, so counting q >= 5 is equivalent to the full truncDim.")
    print("=" * 74)
    print(f"\n  W4 VERDICT: {'ALL EXACT CHECKS PASS' if all_ok else 'FAILURES PRESENT'}")


# ---------- stage W5: foil-v2 (pre-registered) ----------

def per_window_mi(scope, cells, NW):
    """Plug-in MI (bits) per window over 3x3 folded cells; <2 samples -> 0."""
    w = np.nonzero(scope)[0]
    cv = cells[scope]
    cnt = np.bincount(w * 9 + cv, minlength=NW * 9).astype(np.float64)
    cnt = cnt.reshape(NW, 3, 3)
    tot = cnt.sum(axis=(1, 2))
    p = cnt / np.maximum(tot, 1)[:, None, None]
    px = p.sum(2, keepdims=True)
    py = p.sum(1, keepdims=True)
    ratio = np.divide(p, px * py, out=np.ones_like(p), where=cnt > 0)
    mi = (p * np.log2(ratio)).sum(axis=(1, 2))
    mi[tot < 2] = 0.0
    return mi


def stage_w5():
    rng = np.random.default_rng(SEED)
    e_d13c = sum(Fraction(1, q - 2) for q in (5, 7, 11, 13))
    print("\nPRE-REGISTRATION (fixed before any measurement below):")
    print("  grid A in {13,31,101} x X in {1e6,1e9}; H = 50; NW = 3000 (1e6) /")
    print("  1000 (1e9); N_PERM = 200.  Loads per window:")
    print("    S   = sum of lambda_L*lambda_R over ALL survivors of the window;")
    print("    S0  = self-excluded: survivors NOT read by the invariant")
    print("          (C5: the counted twins are removed from the load);")
    print("    S'' = split-window: invariant on the LEFT half (pos 0..24),")
    print("          load = survivor lambda-sum of the RIGHT half (pos 25..49).")
    print("  Independence null sigma_I exactly as gain_complex_harness.gate_g3:")
    print("  lambda resampled from the pooled survivor empirical, load recomputed,")
    print("  z_I = (R - mean_null)/sd_null; z_W = R/sd(perm of I).")
    print("  Candidates and PRIMARY loads:")
    print("    C1  counts per folded dim-class floor((Omega_L-1)/2) in {0,1,2+}")
    print("        among LEFT-half survivors -> S'' (three class rows; candidate")
    print("        verdict = best class, all three reported);")
    print("    C2  per-window plug-in MI(omega_L; omega_R) over survivors, folded")
    print("        alphabet floor((omega-1)/2) clipped to {0,1,2+} -> PRIMARY S''")
    print("        (left-half MI vs right-half load; full-window MI vs S is")
    print("        reported as SECONDARY: the MI reads survivors whose lambda")
    print("        enters S, so S alone is self-contaminated);")
    print("    C3  frustration density = #(lambda_L*lambda_R = -1, non-top")
    print("        survivors)/#non-top on the LEFT half -> S'' ONLY (the")
    print("        self-excluded load degenerates: it would remove every read");
    print("    C4  sum over survivors of d13(C) minus nsurv * E_exact[d13(C)|clean]")
    print(f"        with E_exact = sum(1/(q-2), q<=13) = {e_d13c} = {float(e_d13c):.6f}")
    print("        -> S primary (residues of m only: lambda-blind by construction).")
    print("        NOTE: the literal d13(L)+d13(R) is IDENTICALLY 0 on survivors")
    print("        for A >= 13 (degenerate), so the registered non-degenerate")
    print("        lambda-blind form is the CENTER residual from the W4 pgf;")
    print("    C5  twin-transit count (twins among survivors) -> S0 (the counted")
    print("        twins are excluded from the load).")
    print("  VERDICT RULE (no threshold adjustments): MANAGED-PASS iff")
    print("  min|z_I| >= 5 over the 6 grid cells on the primary load AND")
    print("  |R(101)/R(13)| >= 1/3 at each X with |R(13)| > 1e-9;")
    print("  SOFT-PASS iff min|z_I| >= 3; else PARITY-BLIND-UNDER-ESCALATION-v2.")

    ef = float(e_d13c)
    results = {}
    for X, NW in ((10**6, 3000), (10**9, 1000)):
        n = 50 * NW
        g = window_triple(X, n, want_center=False)
        OL, wLd = g[-1]
        OR, wRd = g[1]
        m_arr = X + np.arange(n, dtype=np.int64)
        lam = (1 - 2 * ((OL + OR) & 1)).astype(np.int64)
        twin = (OL == 1) & (OR == 1)
        d13C = np.zeros(n, dtype=np.int64)
        for q in (5, 7, 11, 13):
            d13C += (m_arr % q == 0)
        foldO = np.minimum((OL - 1) // 2, 2).reshape(NW, 50)
        cells = (np.minimum((wLd - 1) // 2, 2) * 3 +
                 np.minimum((wRd - 1) // 2, 2)).astype(np.int64).reshape(NW, 50)
        pos = np.arange(50)
        leftM = (pos < 25)[None, :]
        for A in (13, 31, 101):
            cleanm = survivor_mask_of(m_arr, A)
            cl = cleanm.reshape(NW, 50)
            lm = np.where(cl, lam.reshape(NW, 50), 0)
            tw = cl & twin.reshape(NW, 50)
            clL = cl & leftM
            loads = {
                "S": lm.sum(1).astype(np.float64),
                "S2": np.where(leftM, 0, lm).sum(1).astype(np.float64),
                "S0": np.where(tw, 0, lm).sum(1).astype(np.float64),
            }
            topL = np.where(clL, pos[None, :], -1).max(1)
            nontopL = clL & (pos[None, :] != topL[:, None])
            dnm = nontopL.sum(1)
            i_c3 = np.where(dnm > 0,
                            ((lm == -1) & nontopL).sum(1) / np.maximum(dnm, 1),
                            0.0)
            d13w = np.where(cl, d13C.reshape(NW, 50), 0)
            rows = [
                ("C1[c0]", ((clL & (foldO == 0)).sum(1)).astype(np.float64), "S2"),
                ("C1[c1]", ((clL & (foldO == 1)).sum(1)).astype(np.float64), "S2"),
                ("C1[c2]", ((clL & (foldO == 2)).sum(1)).astype(np.float64), "S2"),
                ("C2", per_window_mi(clL, cells, NW), "S2"),
                ("C2sec", per_window_mi(cl, cells, NW), "S"),
                ("C3", i_c3, "S2"),
                ("C4", d13w.sum(1) - cl.sum(1) * ef, "S"),
                ("C5", tw.sum(1).astype(np.float64), "S0"),
            ]
            pool = lam[cleanm]
            nsurv = int(cl.sum())
            print(f"\n  [X={X:.0e} A={A:>3}] survivors {nsurv}/{n} "
                  f"(density {nsurv / n:.4f}), twins {int(tw.sum())}", flush=True)
            for name, inv, lname in rows:
                ld = loads[lname]
                if inv.std() < 1e-12 or ld.std() < 1e-12:
                    results[(name, X, A)] = (lname, 0.0, 0.0, 0.0)
                    print(f"    {name:<7} vs {lname:<3}: DEGENERATE "
                          f"(zero variance)")
                    continue
                r = float(np.corrcoef(inv, ld)[0, 1])
                ic = inv.copy()
                perm = np.empty(N_PERM)
                for t in range(N_PERM):
                    rng.shuffle(ic)
                    perm[t] = np.corrcoef(ic, ld)[0, 1]
                nulls = np.empty(N_PERM)
                lmat = np.zeros((NW, 50), dtype=np.float64)
                for t in range(N_PERM):
                    lmat[:] = 0.0
                    lmat[cl] = rng.choice(pool, size=nsurv)
                    if lname == "S":
                        ln = lmat.sum(1)
                    elif lname == "S2":
                        ln = np.where(leftM, 0.0, lmat).sum(1)
                    else:
                        ln = np.where(tw, 0.0, lmat).sum(1)
                    nulls[t] = 0.0 if ln.std() < 1e-12 else \
                        float(np.corrcoef(inv, ln)[0, 1])
                z_w = r / (perm.std() + 1e-15)
                z_i = (r - nulls.mean()) / (nulls.std() + 1e-15)
                results[(name, X, A)] = (lname, r, z_w, z_i)
                print(f"    {name:<7} vs {lname:<3}: R = {r:+.4f}  "
                      f"zW = {z_w:+7.1f}  zI = {z_i:+7.1f}", flush=True)

    print("\n" + "=" * 74)
    print("FOIL-v2 MATRIX (R / z_I on each candidate's registered load)")
    hdr = "  cand     load "
    for X in (10**6, 10**9):
        for A in (13, 31, 101):
            hdr += f"  X{X:.0e},A={A:<3}"
    print(hdr)
    names = ["C1[c0]", "C1[c1]", "C1[c2]", "C2", "C2sec", "C3", "C4", "C5"]
    for name in names:
        lname = results[(name, 10**6, 13)][0]
        line = f"  {name:<7} {lname:<4}"
        for X in (10**6, 10**9):
            for A in (13, 31, 101):
                _, r, _, z_i = results[(name, X, A)]
                line += f" {r:+.3f}/{z_i:+6.1f}"
        print(line)

    def sub_verdict(name):
        zs = [abs(results[(name, X, A)][3])
              for X in (10**6, 10**9) for A in (13, 31, 101)]
        ratio_ok = True
        for X in (10**6, 10**9):
            r13 = results[(name, X, 13)][1]
            r101 = results[(name, X, 101)][1]
            if abs(r13) > 1e-9 and abs(r101) < abs(r13) / 3.0:
                ratio_ok = False
        minz = min(zs)
        if minz >= 5 and ratio_ok:
            v = "MANAGED-PASS"
        elif minz >= 3:
            v = "SOFT-PASS"
        else:
            v = "PARITY-BLIND-UNDER-ESCALATION-v2"
        return minz, ratio_ok, v

    print("\nVERDICTS (primary loads; rule as pre-registered above):")
    c1_best = None
    for cls in ("C1[c0]", "C1[c1]", "C1[c2]"):
        minz, rok, v = sub_verdict(cls)
        print(f"  {cls}: min|z_I| = {minz:5.1f}  ratio_ok = {rok}  -> {v}")
        if c1_best is None or minz > c1_best[1]:
            c1_best = (cls, minz, rok, v)
    print(f"  C1 (best class {c1_best[0]}): min|z_I| = {c1_best[1]:5.1f}  "
          f"ratio_ok = {c1_best[2]}  -> {c1_best[3]}")
    for name in ("C2", "C3", "C4", "C5"):
        minz, rok, v = sub_verdict(name)
        print(f"  {name}: min|z_I| = {minz:5.1f}  ratio_ok = {rok}  -> {v}")
    minz, rok, v = sub_verdict("C2sec")
    print(f"  [info] C2 secondary (full-window MI vs S): min|z_I| = {minz:5.1f}"
          f"  ratio_ok = {rok}  -> {v} (NOT a verdict load)")


# ---------- main ----------

STAGES = {
    "w1": ("centered dimension walk (STATISTICAL)", stage_w1),
    "w2": ("additive shift correlations (STATISTICAL)", stage_w2),
    "w3": ("twin-collision census (STATISTICAL, law candidates)", stage_w3),
    "w4": ("EXACT truncated layer (fractions.Fraction)", stage_w4),
    "w5": ("foil-v2 (STATISTICAL, pre-registered)", stage_w5),
}


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in STAGES:
        print("usage: python tools/packing_walk_harness.py {w1|w2|w3|w4|w5}")
        print("       each stage is a separate invocation; append stdout to")
        print("       tools/packing_walk_run1.log")
        sys.exit(2)
    title, fn = STAGES[mode]
    t0 = time.time()
    print("=" * 78)
    print(f"PACKING-WALK P0 -- stage {mode}: {title}")
    print(f"  seed={SEED}  N_PERM={N_PERM}  numpy={np.__version__}  "
          f"{time.strftime('%Y-%m-%d %H:%M:%S')}")
    print("  DISCLOSURE: omega = # DISTINCT primes -> omega=1 includes prime")
    print("  powers (25, 49, ...); Omega=1 <=> prime; twin <=> Omega_L=Omega_R=1.")
    print("=" * 78, flush=True)
    fn()
    print(f"\n[{mode} done in {time.time() - t0:.1f}s]", flush=True)


if __name__ == "__main__":
    main()
