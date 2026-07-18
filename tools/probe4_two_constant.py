"""PROBE W4-3: the two-constant law for the Omega<=2 transition
(re-registered).  Evolves tools/probe3_zstar_scaling.py.

Wave-3 (tools/probe3_zstar_scaling.py) found that BOTH mechanism-level
indicators of the LFU purity-to-structure transition scale as the cube
root of X with the SAME fitted exponent (0.3414):

  z_dich(X) = first z on a geometric grid with
              mean_windows frac(Omega <= 2 within R) >= 0.999;
  z_lock(X) = first z with Pearson corr across windows between the
              per-window max rational peak max_{a/q}|F(a/q)|/sqrt|R|
              and |S-P|/sqrt|R| reaching >= 0.99;

with z_dich within 5% of (0.75X)^(1/3) and z_lock at the same exponent
but a constant ~0.6x (peaks lock onto the proven wing bias S-P BEFORE
full Omega<=2 purity).  Wave-3 used a coarse grid (ratio 1.3), so the
lock constant was quantization-noisy (0.562/0.745/0.583).

This probe re-registers the two-constant law on a finer grid over four
decades: X = 10^6 (H = 10^4), 10^7 (3*10^4), 10^8 (10^5), 10^9
(3*10^5); windows x ~ U[X/2, X], NWIN = 50 (same windows reused at
every z); z-grid geometric with ratio 1.15.  Grid floor lowered from
50 to 30 (sole change to the wave-3 measurement besides grid ratio /
NWIN / decades): at X = 10^6 the predicted lock point ~0.6*(0.75X)^(1/3)
= 55 sits at the old floor and would be left-censored.  Thresholds
(0.999 / 0.99), the Farey grid q <= 48, the window statistics and the
trial-division arithmetic are identical to wave 3.

PRE-REGISTERED CLAUSES (recorded before the run):
  (1) z_dich = c_d * (0.75X)^(1/3) with c_d in [0.90, 1.05] at EVERY
      decade;
  (2) z_lock = c_l * (0.75X)^(1/3) with c_l stable across decades:
      every c_l within +-20 percent of its four-decade mean;
  (3) both fitted slopes of log z* vs log X in [0.31, 0.36].

PRE-REGISTERED VERDICTS (mechanical):
  signal    = all three clauses hold;
  killed    = either fitted slope outside [0.28, 0.39] (exponent
              break), or c_l varying by more than a factor 2 across
              decades (max c_l / min c_l > 2);
  ambiguous = otherwise (including any indicator never reaching its
              threshold on the grid at some decade).
"""

import numpy as np
import time
from math import gcd

rng = np.random.default_rng(2026071804)
t0 = time.time()

CONFIGS = [(10 ** 6, 10_000), (10 ** 7, 30_000),
           (10 ** 8, 100_000), (10 ** 9, 300_000)]
NWIN = 50
RATIO = 1.15
ZMIN = 30.0
FRAC_THRESH = 0.999
CORR_THRESH = 0.99

# Farey fractions a/q, q <= 48, gcd(a,q)=1 (same grid as waves 1-3)
QS = list(range(2, 49))
AS_BY_Q = {q: [a for a in range(1, q) if gcd(a, q) == 1] for q in QS}
ROOTS = {q: np.exp(2j * np.pi * np.arange(q) / q) for q in QS}
IDX = {q: {a: (a * np.arange(q)) % q for a in AS_BY_Q[q]} for q in QS}
NFAREY = sum(len(AS_BY_Q[q]) for q in QS)


def zgrid(X):
    zmax = 3.0 * X ** (1.0 / 3.0)
    zs, z = [], ZMIN
    while z <= zmax:
        zi = int(round(z))
        if not zs or zi > zs[-1]:
            zs.append(zi)
        z *= RATIO
    return zs


def primes_upto(limit):
    sv = np.ones(limit + 1, dtype=bool)
    sv[:2] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if sv[i]:
            sv[i * i:: i] = False
    return np.nonzero(sv)[0].astype(np.int64)


def window_arrays(x, H, PRIMES):
    """lambda(n) (int8), minFac(n) (int32, sentinel 2^31-1 for primes)
    and Omega(n) (int16, with multiplicity) for n in (x, x+H] by trial
    division.  Identical arithmetic to waves 1-3."""
    n0 = x + 1
    size = H
    rem = np.arange(n0, n0 + size, dtype=np.int64)
    omega = np.zeros(size, dtype=np.int16)
    minf = np.zeros(size, dtype=np.int64)
    for p in PRIMES:
        p = int(p)
        if p * p > n0 + size:
            break
        start = ((n0 + p - 1) // p) * p
        idx = np.arange(start - n0, size, p, dtype=np.int64)
        if idx.size == 0:
            continue
        first = minf[idx] == 0
        minf[idx[first]] = p
        sub = idx
        while sub.size:
            div = rem[sub] % p == 0
            sub = sub[div]
            rem[sub] //= p
            omega[sub] += 1
    left = rem > 1
    omega[left] += 1  # remaining cofactor is a single prime > sqrt
    minf[minf == 0] = 2 ** 31 - 1
    lam = (1 - 2 * (omega & 1)).astype(np.int8)
    return lam, minf.astype(np.int32), omega


print("PROBE W4-3: two-constant law for z_dich / z_lock "
      f"(NWIN={NWIN}, z-grid ratio {RATIO} from {ZMIN:.0f} to 3*X^(1/3))")
print(f"Farey fractions q<=48: {NFAREY}")
print(f"thresholds: frac(Omega<=2) >= {FRAC_THRESH}, corr >= {CORR_THRESH}")
print("registered: c_d in [0.90,1.05] each decade; c_l within +-20% of "
      "4-decade mean; slopes in [0.31,0.36]")

results = {}  # X -> dict with z-rows, z_dich, z_lock, pred
for (X, H) in CONFIGS:
    pred = (0.75 * X) ** (1.0 / 3.0)
    ZS = zgrid(X)
    ROOT = int((X + 2 * H) ** 0.5) + 1
    PRIMES = primes_upto(ROOT)
    print(f"\n########## X = {X:.0e}  H = {H}  "
          f"pred z* = (0.75X)^(1/3) = {pred:.0f} ##########")
    print(f"trial-division primes up to {ROOT} (count {PRIMES.size}); "
          f"z-grid ({len(ZS)} pts): {ZS}")

    windows = []
    for w in range(NWIN):
        x = int(rng.integers(X // 2, X))
        lam, minf, omega = window_arrays(x, H, PRIMES)
        windows.append((x, lam, minf, omega))
    print(f"[{time.time()-t0:7.1f}s] {NWIN} windows sieved "
          f"(x in [{X//2:.2e}, {X:.2e}])")

    rows = []
    z_dich, z_lock = None, None
    for z in ZS:
        peaks, sp_norm, sizes, frac_om2 = [], [], [], []
        for (x, lam, minf, omega) in windows:
            R = np.nonzero(minf > z)[0]
            if R.size < 50:
                continue
            n_int = (x + 1 + R).astype(np.int64)
            lamR = lam[R].astype(np.float64)
            omR = omega[R]
            sp = int((omR == 2).sum()) - int((omR == 1).sum())
            sqrtR = np.sqrt(R.size)
            wmax = 0.0
            for q in QS:
                r = n_int % q
                S = np.bincount(r, weights=lamR, minlength=q)
                roots = ROOTS[q]
                for a in AS_BY_Q[q]:
                    Fv = abs((S * roots[IDX[q][a]]).sum()) / sqrtR
                    if Fv > wmax:
                        wmax = Fv
            peaks.append(wmax)
            sp_norm.append(abs(sp) / sqrtR)
            sizes.append(R.size)
            frac_om2.append((omR <= 2).sum() / R.size)
        peaks = np.array(peaks)
        sp_norm = np.array(sp_norm)
        fmean = float(np.mean(frac_om2))
        if peaks.std() > 0 and sp_norm.std() > 0:
            corr = float(np.corrcoef(peaks, sp_norm)[0, 1])
        else:
            corr = float("nan")
        if z_dich is None and fmean >= FRAC_THRESH:
            z_dich = z
        if z_lock is None and not np.isnan(corr) and corr >= CORR_THRESH:
            z_lock = z
        rows.append((z, np.mean(sizes), fmean, corr, len(sizes)))
        print(f"  z={z:5d}  mean|R|={np.mean(sizes):8.0f}  "
              f"fracOm<=2={fmean:.5f}  corr(peak,|SP|)={corr:6.3f}  "
              f"windows={len(sizes)}  [{time.time()-t0:7.1f}s]")
    print(f"X={X:.0e}: z_dich = {z_dich}  z_lock = {z_lock}  "
          f"pred = {pred:.0f}")
    results[X] = dict(rows=rows, z_dich=z_dich, z_lock=z_lock, pred=pred)

# ---------- summary + mechanical verdict ----------
print("\n=== SUMMARY: two-constant law z* = c * (0.75X)^(1/3) ===")
print("      X        pred   z_dich      c_d   z_lock      c_l")
for (X, H) in CONFIGS:
    r = results[X]
    cd = (r["z_dich"] / r["pred"]) if r["z_dich"] else float("nan")
    cl = (r["z_lock"] / r["pred"]) if r["z_lock"] else float("nan")
    zd = r["z_dich"] if r["z_dich"] else -1
    zl = r["z_lock"] if r["z_lock"] else -1
    print(f"{X:11.0e}  {r['pred']:7.0f}  {zd:7d}  {cd:7.3f}  "
          f"{zl:7d}  {cl:7.3f}")

XS = [X for (X, H) in CONFIGS]
logX = np.log([float(X) for X in XS])


def fit_slope(key):
    vals = [results[X][key] for X in XS]
    if any(v is None for v in vals):
        return None
    return float(np.polyfit(logX, np.log(vals), 1)[0])


slope_d = fit_slope("z_dich")
slope_l = fit_slope("z_lock")
print(f"\nfit slope log z_dich vs log X : "
      f"{'undefined' if slope_d is None else f'{slope_d:.4f}'}"
      f"  (cube root = 0.3333; registered [0.31, 0.36]; "
      f"kill outside [0.28, 0.39])")
print(f"fit slope log z_lock vs log X : "
      f"{'undefined' if slope_l is None else f'{slope_l:.4f}'}")

cds = [results[X]["z_dich"] / results[X]["pred"]
       if results[X]["z_dich"] else None for X in XS]
cls = [results[X]["z_lock"] / results[X]["pred"]
       if results[X]["z_lock"] else None for X in XS]
all_defined = all(v is not None for v in cds + cls)

clause1 = all_defined and all(0.90 <= c <= 1.05 for c in cds)
if all_defined:
    cl_mean = float(np.mean(cls))
    cl_dev = max(abs(c - cl_mean) / cl_mean for c in cls)
    clause2 = cl_dev <= 0.20
    cl_spread = max(cls) / min(cls)
else:
    cl_mean, cl_dev, clause2, cl_spread = float("nan"), float("nan"), \
        False, float("nan")
clause3 = (slope_d is not None and slope_l is not None and
           0.31 <= slope_d <= 0.36 and 0.31 <= slope_l <= 0.36)

kill_slope = ((slope_d is not None and not (0.28 <= slope_d <= 0.39)) or
              (slope_l is not None and not (0.28 <= slope_l <= 0.39)))
kill_cl = all_defined and cl_spread > 2.0

print("\n=== PRE-REGISTERED VERDICT ===")
print(f"  both indicators defined at all four X  : {all_defined}")
print(f"  clause 1: c_d in [0.90, 1.05] each dec : {clause1}  "
      f"(c_d = {[None if c is None else round(c, 3) for c in cds]})")
print(f"  clause 2: c_l within +-20% of mean     : {clause2}  "
      f"(c_l = {[None if c is None else round(c, 3) for c in cls]}, "
      f"mean = {cl_mean:.3f}, max dev = {cl_dev:.3f})")
print(f"  clause 3: both slopes in [0.31, 0.36]  : {clause3}  "
      f"(slope_d = {slope_d}, slope_l = {slope_l})")
print(f"  kill: slope outside [0.28, 0.39]       : {kill_slope}")
print(f"  kill: c_l spread factor > 2            : {kill_cl}  "
      f"(spread = {cl_spread:.3f})")
if kill_slope or kill_cl:
    verdict = "KILLED"
elif clause1 and clause2 and clause3:
    verdict = "SIGNAL"
else:
    verdict = "AMBIGUOUS"
print(f"  VERDICT: {verdict}")
print(f"[{time.time()-t0:7.1f}s] done")
