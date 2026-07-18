"""PROBE W2-2 (A3 rough-lfu): purity-to-structure transition in z.

Wave-1 (tools/probe_rough_lfu.py) measured, on short windows W=(x, x+H] with
rough set R = {n in W : minFac(n) > z}:
  F(alpha) = sum_{n in R} lambda(n) e(n alpha),
  rho      = q95 |F at Farey rationals (q<=48)| / q95 |F at random alpha|
(both normalized by sqrt|R|).  Result: rho ~ 1 at z=100 (lambda kills the
sieve's rational peaks cleanly), rho = 1.5/3.9 at z=3000 -- explained
structurally: once z^3 > x+H the rough set has Omega <= 2, lambda becomes
1 - 2*1_prime, and the rational peaks are the proven wing bias S - P in
Fourier clothing, not a defect of local Fourier uniformity.

This probe scans z at fixed H = 100000, x uniform in [5*10^7, 10^8],
NWIN = 60 windows (the same 60 windows are evaluated at every z: the window
arrays lambda/minFac/Omega are z-independent, so this is exact and gives a
cleaner transition curve), z in {30, 100, 200, 300, 400, 500, 700, 1000,
2000, 5000}.  The Omega<=2 dichotomy threshold z*^3 = x + H gives
z* ~ 465 for x ~ 10^8.

Additionally per window: SP = (#semiprimes in R) - (#primes in R)
(Omega counted with multiplicity), and at each z the Pearson correlation
across windows between the per-window max rational peak
max_{a/q} |F(a/q)|/sqrt|R| and |SP|/sqrt|R|.

PRE-REGISTERED VERDICTS (operationalized before the run):
  signal    = rho(z) ~ 1 for z <= 300, i.e. rho(z) <= 1.35 for all
              z in {30,100,200,300};
              AND the first z with rho(z) >= 2.0 lies within a factor 2 of
              z* ~ 465, i.e. in (232, 930) -- on this grid {300,400,500,700};
              AND Pearson corr(peak, |SP|/sqrt|R|) > 0.6 at every
              z in {1000, 2000, 5000}.
  killed    = rho(z) > 3 already at some z <= 100.
  ambiguous = otherwise.
"""

import numpy as np
import time
from math import gcd

rng = np.random.default_rng(2026071802)
t0 = time.time()

H = 100_000
NWIN = 60
XLO, XHI = 5 * 10 ** 7, 10 ** 8
ZLIST = [30, 100, 200, 300, 400, 500, 700, 1000, 2000, 5000]
ZSTAR = round((XHI + H) ** (1.0 / 3.0))  # ~465

# primes up to sqrt(max n) with margin
ROOT = int((XHI + 2 * H) ** 0.5) + 1
sv = np.ones(ROOT + 1, dtype=bool)
sv[:2] = False
for i in range(2, int(ROOT ** 0.5) + 1):
    if sv[i]:
        sv[i * i:: i] = False
PRIMES = np.nonzero(sv)[0].astype(np.int64)

# Farey fractions a/q, q <= 48, gcd(a,q)=1 (same grid as wave 1)
QS = list(range(2, 49))
AS_BY_Q = {q: [a for a in range(1, q) if gcd(a, q) == 1] for q in QS}
ROOTS = {q: np.exp(2j * np.pi * np.arange(q) / q) for q in QS}
IDX = {q: {a: (a * np.arange(q)) % q for a in AS_BY_Q[q]} for q in QS}
NFAREY = sum(len(AS_BY_Q[q]) for q in QS)
NRAND = 40
RAND_ALPHA = rng.random(NRAND)


def window_arrays(x, H):
    """lambda(n) (int8), minFac(n) (int32, sentinel 2^31-1 for primes) and
    Omega(n) (int16, with multiplicity) for n in (x, x+H] by trial division.
    Identical arithmetic to wave-1 window_lambda_minfac, plus Omega."""
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
    omega[left] += 1  # remaining cofactor is a prime > ROOT threshold
    minf[minf == 0] = 2 ** 31 - 1  # no factor <= sqrt(n): n itself is prime
    lam = (1 - 2 * (omega & 1)).astype(np.int8)
    return lam, minf.astype(np.int32), omega


print(f"PROBE W2-2: LFU purity-to-structure z-scan  "
      f"(H={H}, NWIN={NWIN}, x in [{XLO:.0e},{XHI:.0e}])")
print(f"Omega<=2 dichotomy threshold z* = (x+H)^(1/3) ~ {ZSTAR}")
print(f"Farey fractions q<=48: {NFAREY}; random alphas per window: {NRAND}")

windows = []
for w in range(NWIN):
    x = int(rng.integers(XLO, XHI))
    lam, minf, omega = window_arrays(x, H)
    windows.append((x, lam, minf, omega))
print(f"[{time.time()-t0:7.1f}s] {NWIN} windows sieved")

rows = []
for z in ZLIST:
    Fr_all, Fn_all = [], []
    peaks, sp_norm, sp_raw, sizes, frac_om2 = [], [], [], [], []
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
            r = (n_int % q)
            S = np.bincount(r, weights=lamR, minlength=q)
            roots = ROOTS[q]
            for a in AS_BY_Q[q]:
                Fv = abs((S * roots[IDX[q][a]]).sum()) / sqrtR
                Fr_all.append(Fv)
                if Fv > wmax:
                    wmax = Fv
        n_f = n_int.astype(np.float64)
        for al in RAND_ALPHA:
            ph = np.exp(2j * np.pi * ((al * n_f) % 1.0))
            Fn_all.append(abs((lamR * ph).sum()) / sqrtR)
        peaks.append(wmax)
        sp_raw.append(sp)
        sp_norm.append(abs(sp) / sqrtR)
        sizes.append(R.size)
        frac_om2.append((omR <= 2).sum() / R.size)
    Fr = np.array(Fr_all)
    Fn = np.array(Fn_all)
    peaks = np.array(peaks)
    sp_norm = np.array(sp_norm)
    rho = np.quantile(Fr, 0.95) / np.quantile(Fn, 0.95)
    if peaks.std() > 0 and sp_norm.std() > 0:
        corr = float(np.corrcoef(peaks, sp_norm)[0, 1])
    else:
        corr = float("nan")
    rows.append((z, np.mean(sizes), rho, np.quantile(Fr, 0.95),
                 np.quantile(Fn, 0.95), corr, np.mean(sp_norm),
                 np.mean(frac_om2), len(sizes)))
    print(f"\n=== z={z}  (windows used {len(sizes)}, mean |R| = "
          f"{np.mean(sizes):.0f}, mean frac Omega<=2 in R = "
          f"{np.mean(frac_om2):.3f}) ===")
    print(f"  F rational : median {np.median(Fr):.3f}  "
          f"q95 {np.quantile(Fr, 0.95):.3f}  max {Fr.max():.3f}")
    print(f"  F random   : median {np.median(Fn):.3f}  "
          f"q95 {np.quantile(Fn, 0.95):.3f}  max {Fn.max():.3f}")
    print(f"  rho = {rho:.3f}")
    print(f"  per-window peak vs |SP|/sqrt|R|: Pearson r = {corr:.3f}  "
          f"(mean |SP|/sqrt|R| = {np.mean(sp_norm):.3f}, "
          f"mean SP = {np.mean(sp_raw):.1f})")
    print(f"  [{time.time()-t0:7.1f}s]")

print("\n=== SUMMARY TABLE ===")
print("   z     mean|R|   rho    q95Frat  q95Frnd  corr(peak,SP)  "
      "mean|SP|/sqrtR  fracOm<=2")
for (z, mR, rho, qr, qn, corr, msp, fo, nw) in rows:
    print(f"{z:6d}  {mR:8.0f}  {rho:6.3f}  {qr:7.3f}  {qn:7.3f}  "
          f"{corr:12.3f}  {msp:13.3f}  {fo:9.3f}")

# --- mechanical verdict per pre-registered rules ---
rho_by_z = {z: rho for (z, _, rho, *_ ) in rows}
corr_by_z = {z: c for (z, _, _, _, _, c, *_ ) in rows}
low_ok = all(rho_by_z[z] <= 1.35 for z in (30, 100, 200, 300))
killed = any(rho_by_z[z] > 3 for z in (30, 100))
first_rise = next((z for z in ZLIST if rho_by_z[z] >= 2.0), None)
rise_ok = first_rise is not None and 232 < first_rise < 930
corr_ok = all(corr_by_z[z] > 0.6 for z in (1000, 2000, 5000))
print("\n=== PRE-REGISTERED VERDICT ===")
print(f"  rho <= 1.35 for z in {{30,100,200,300}} : {low_ok}  "
      f"({[round(rho_by_z[z], 3) for z in (30, 100, 200, 300)]})")
print(f"  first z with rho >= 2.0               : {first_rise}  "
      f"(in (232,930): {rise_ok})")
print(f"  corr > 0.6 at z in {{1000,2000,5000}}   : {corr_ok}  "
      f"({[round(corr_by_z[z], 3) for z in (1000, 2000, 5000)]})")
print(f"  rho > 3 at some z <= 100 (kill)       : {killed}")
if killed:
    verdict = "KILLED"
elif low_ok and rise_ok and corr_ok:
    verdict = "SIGNAL"
else:
    verdict = "AMBIGUOUS"
print(f"  VERDICT: {verdict}")
print(f"[{time.time()-t0:7.1f}s] done")
