"""PROBE W3-3 (queue item (iii)): the z*(X) cube-root scaling law.

Wave-2 (tools/probe2_lfu_zscan.py, X ~ 10^8) localized the LFU
purity-to-structure transition mechanically: on rough windows
R = {n in (x, x+H] : minFac(n) > z} the set becomes pure Omega <= 2
exactly at z* = (x+H)^(1/3), and from that point on the per-window max
rational Fourier peak of lambda restricted to R is a deterministic
function of the proven wing bias S - P (Pearson corr 1.000).

This probe tests whether BOTH mechanism-level indicators obey the
cube-root scaling law across three decades:

  z_dich(X) = first z on a geometric grid with
              mean_windows frac(Omega <= 2 within R) >= 0.999;
  z_lock(X) = first z with Pearson corr across windows between the
              per-window max rational peak max_{a/q}|F(a/q)|/sqrt|R|
              and |S-P|/sqrt|R| reaching >= 0.99.

Decades: X = 10^7 (H = 3*10^4), X = 10^8 (H = 10^5), X = 10^9
(H = 3*10^5); windows x ~ U[X/2, X], NWIN = 40 (same windows reused at
every z -- window arrays are z-independent); z-grid geometric with
ratio 1.3 from 50 up to 3*X^(1/3).  Windows are sieved by trial
division with primes up to sqrt(x_max + 2H) only (no global sieve;
~32000 for X = 10^9).

Prediction: both indicators track (x+H)^(1/3) at the typical window
x ~ 0.75X, i.e. z* ~ (0.75X)^(1/3): 196 / 422 / 909.

PRE-REGISTERED VERDICTS (operationalized before the run):
  killed    = either indicator scales with a visibly different
              exponent: least-squares slope of log z* vs log X outside
              [0.28, 0.39].
  signal    = not killed AND both indicators within one grid step
              (factor 1.3) of the cube-root prediction (0.75X)^(1/3)
              at ALL three X, i.e. z*/pred in [1/1.3, 1.3].
  ambiguous = otherwise (including any indicator never reaching its
              threshold on the grid).
"""

import numpy as np
import time
from math import gcd

rng = np.random.default_rng(2026071803)
t0 = time.time()

CONFIGS = [(10 ** 7, 30_000), (10 ** 8, 100_000), (10 ** 9, 300_000)]
NWIN = 40
RATIO = 1.3
ZMIN = 50.0
FRAC_THRESH = 0.999
CORR_THRESH = 0.99

# Farey fractions a/q, q <= 48, gcd(a,q)=1 (same grid as waves 1-2)
QS = list(range(2, 49))
AS_BY_Q = {q: [a for a in range(1, q) if gcd(a, q) == 1] for q in QS}
ROOTS = {q: np.exp(2j * np.pi * np.arange(q) / q) for q in QS}
IDX = {q: {a: (a * np.arange(q)) % q for a in AS_BY_Q[q]} for q in QS}
NFAREY = sum(len(AS_BY_Q[q]) for q in QS)


def zgrid(X):
    zmax = 3.0 * X ** (1.0 / 3.0)
    zs, z = [], ZMIN
    while z <= zmax:
        zs.append(int(round(z)))
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
    division.  Identical arithmetic to waves 1-2."""
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


print("PROBE W3-3: z*(X) cube-root scaling law "
      f"(NWIN={NWIN}, z-grid ratio {RATIO} from {ZMIN:.0f} to 3*X^(1/3))")
print(f"Farey fractions q<=48: {NFAREY}")
print(f"thresholds: frac(Omega<=2) >= {FRAC_THRESH}, corr >= {CORR_THRESH}")

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
print("\n=== SUMMARY: z*(X) vs cube-root prediction ===")
print("      X        pred   z_dich  ratio_d   z_lock  ratio_l")
for (X, H) in CONFIGS:
    r = results[X]
    rd = (r["z_dich"] / r["pred"]) if r["z_dich"] else float("nan")
    rl = (r["z_lock"] / r["pred"]) if r["z_lock"] else float("nan")
    zd = r["z_dich"] if r["z_dich"] else -1
    zl = r["z_lock"] if r["z_lock"] else -1
    print(f"{X:11.0e}  {r['pred']:7.0f}  {zd:7d}  {rd:7.3f}  "
          f"{zl:7d}  {rl:7.3f}")

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
      f"  (cube root = 0.3333; kill range outside [0.28, 0.39])")
print(f"fit slope log z_lock vs log X : "
      f"{'undefined' if slope_l is None else f'{slope_l:.4f}'}")

within = []
for X in XS:
    r = results[X]
    for key in ("z_dich", "z_lock"):
        v = r[key]
        ok = v is not None and (1.0 / RATIO) <= v / r["pred"] <= RATIO
        within.append(ok)
all_within = all(within)
all_defined = all(results[X][k] is not None
                  for X in XS for k in ("z_dich", "z_lock"))
killed = ((slope_d is not None and not (0.28 <= slope_d <= 0.39)) or
          (slope_l is not None and not (0.28 <= slope_l <= 0.39)))

print("\n=== PRE-REGISTERED VERDICT ===")
print(f"  both indicators defined at all three X : {all_defined}")
print(f"  all z*/pred within [1/1.3, 1.3]        : {all_within}  "
      f"({[round(results[X][k] / results[X]['pred'], 3) if results[X][k] else None for X in XS for k in ('z_dich', 'z_lock')]})")
print(f"  slope outside [0.28, 0.39] (kill)      : {killed}")
if killed:
    verdict = "KILLED"
elif all_defined and all_within:
    verdict = "SIGNAL"
else:
    verdict = "AMBIGUOUS"
print(f"  VERDICT: {verdict}")
print(f"[{time.time()-t0:7.1f}s] done")
