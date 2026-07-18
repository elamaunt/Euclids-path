"""PROBE A3 (rough-lfu): does lambda kill the rational Fourier peaks of the
sieve weight?

For a window W=(x, x+H], roughness z: R = {n in W : minFac(n) > z}.
  G(alpha) = sum_{n in R} e(n alpha)         (sieve weight alone)
  F(alpha) = sum_{n in R} lambda(n) e(n alpha)
At rationals a/q (q z-smooth, squarefree) G has structural peaks ~|R|/phi(q).
Question: does F inherit them (killed) or sit at noise sqrt(|R|) (signal)?

Pre-registered verdict rules:
  signal    = rho = q95|F(rational)|/q95|F(random)| <= 2 for all (H,z) combos,
  killed    = rho >= 10 persistently,
  ambiguous = otherwise.
"""

import numpy as np
import time

rng = np.random.default_rng(20260718)
t0 = time.time()

XBASE = 10 ** 8
NWIN = 100
COMBOS = [(10_000, 100), (10_000, 3000), (100_000, 100), (100_000, 3000)]

# primes up to sqrt(XBASE + max H + margin)
ROOT = int((XBASE + 200_000) ** 0.5) + 1
sv = np.ones(ROOT + 1, dtype=bool)
sv[:2] = False
for i in range(2, int(ROOT ** 0.5) + 1):
    if sv[i]:
        sv[i * i:: i] = False
PRIMES = np.nonzero(sv)[0].astype(np.int64)

# Farey fractions a/q, q <= 48, gcd(a,q)=1, 0 < a < q
from math import gcd
FAREY = [(a, q) for q in range(2, 49) for a in range(1, q) if gcd(a, q) == 1]
NRAND = 200
RAND_ALPHA = rng.random(NRAND)


def window_lambda_minfac(x, H):
    """lambda(n) and minFac(n) for n in (x, x+H] via trial division."""
    n0 = x + 1
    size = H
    rem = np.arange(n0, n0 + size, dtype=np.int64)
    omega = np.zeros(size, dtype=np.int16)
    minf = np.full(size, 0, dtype=np.int64)
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
    omega[left] += 1
    minf[(minf == 0) & left] = 10 ** 18  # the number itself is prime (> root)
    minf[minf == 0] = 10 ** 18
    lam = (1 - 2 * (omega & 1)).astype(np.float64)
    return lam, minf


results = {}
for (H, z) in COMBOS:
    ratF_rat, ratF_rnd, ratG_rat = [], [], []
    sizes = []
    for w in range(NWIN):
        x = int(rng.integers(XBASE // 2, XBASE))
        lam, minf = window_lambda_minfac(x, H)
        rough = minf > z
        R = np.nonzero(rough)[0]
        if R.size < 50:
            continue
        n_val = (x + 1 + R).astype(np.float64)
        lamR = lam[R]
        sizes.append(R.size)
        sqrtR = np.sqrt(R.size)
        # rationals
        for (a, q) in FAREY:
            ph = np.exp(2j * np.pi * ((a / q) * n_val % 1.0))
            Fv = np.abs((lamR * ph).sum())
            Gv = np.abs(ph.sum())
            ratF_rat.append(Fv / sqrtR)
            ratG_rat.append(Gv / R.size)
        # random alphas (a subset per window to keep cost even)
        for al in RAND_ALPHA[:40]:
            ph = np.exp(2j * np.pi * ((al * n_val) % 1.0))
            ratF_rnd.append(np.abs((lamR * ph).sum()) / sqrtR)
    Fr = np.array(ratF_rat)
    Fn = np.array(ratF_rnd)
    Gr = np.array(ratG_rat)
    rho = np.quantile(Fr, 0.95) / np.quantile(Fn, 0.95)
    results[(H, z)] = (Fr, Fn, Gr, rho, np.mean(sizes))
    print(f"\n=== H={H}, z={z}  (mean |R| = {np.mean(sizes):.0f}) ===")
    print(f"  G at rationals   : median |G|/|R| = {np.median(Gr):.4f}  "
          f"q95 = {np.quantile(Gr, 0.95):.4f}   (structural peaks present)")
    print(f"  F at rationals   : median |F|/sqrt|R| = {np.median(Fr):.3f}  "
          f"q95 = {np.quantile(Fr, 0.95):.3f}  max = {Fr.max():.3f}")
    print(f"  F at random alpha: median = {np.median(Fn):.3f}  "
          f"q95 = {np.quantile(Fn, 0.95):.3f}  max = {Fn.max():.3f}")
    print(f"  rho = q95(F rational)/q95(F random) = {rho:.3f}")
    print(f"  [{time.time()-t0:7.1f}s]")

print("\n=== SUMMARY ===")
for k, (_, _, _, rho, _) in results.items():
    print(f"  H={k[0]:6d} z={k[1]:5d}: rho = {rho:.3f}")
