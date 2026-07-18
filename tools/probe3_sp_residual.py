"""PROBE W3-2 (A3 rough-lfu, wave-3 queue item (ii)): SP-subtracted LFU residual.

Wave 2 (tools/probe2_lfu_zscan.py) established: above the Omega<=2 dichotomy
z* = (x+H)^(1/3), the per-window correlation between the max rational peak of
F(alpha) = sum_{n in R} lambda(n) e(n alpha), R = {n in (x, x+H] : minFac > z},
and |S-P|/sqrt|R| equals 1.000.  This probe is the quantitative form: subtract
the structural (per-class prime/semiprime counting) model and measure what is
left at rationals.

MODEL.  On R with z^3 > x+H every n in R has Omega(n) <= 2, hence
lambda(n) = 1 - 2*1_prime(n) on R.  The pre-registered structured model
replaces 1_prime(n) by its window average over the residue class of n mod q:
    M'(alpha; q) = sum_{n in R} (1 - 2*P_c(n)/N_c(n)) e(n alpha),
with N_c, P_c = rough / prime counts of class c mod q in the window; i.e.
    M'(a/q) = sum_c (N_c - 2*P_c) * (class average of e(n a/q)).

DEGENERACY, DISCOVERED AT IMPLEMENTATION TIME (before the run, recorded here
for honesty).  At an EXACT rational alpha = a/q the phase e(n a/q) is constant
on each class c mod q, so
    F(a/q) = sum_c e(ca/q) * (sum of lambda over R cap class c)
           = sum_c e(ca/q) * (N_c - 2*P_c) = M'(a/q)
IDENTICALLY, for every window and every z above the dichotomy.  The
pre-registered residual is zero by algebra: "per-class S-P counting is the
ONLY rational structure" is a THEOREM on Omega<=2 windows, not an empirical
question.  The pre-registered verdict rule is still applied mechanically to
this arm (Arm A), whose run documents the identity at machine precision; any
verdict from Arm A is VACUOUS as an empirical finding and is flagged as such.
Two non-degenerate completions run as supplementary arms, clearly labelled
NOT PRE-REGISTERED (numbers reported, no verdict claims):

  Arm B (global model, exact rationals): replace 1_prime by its GLOBAL window
    average pbar = P/|R| (class-blind).  Residual
    F - M_glob = -2 * sum_{n in R} (1_prime(n) - pbar) e(n a/q)
    measures per-class structure of the prime/semiprime split beyond global
    counting -- the honest quantitative sharpening of wave-2's corr = 1.000
    (which used the GLOBAL S-P).

  Arm C (displaced rationals): the SAME pre-registered per-class model M',
    evaluated at alpha = a/q + delta, delta in {0.5/H, 2/H} (Farey-arc
    scale), where the class exponential average no longer collapses:
    measures positional structure of primes within classes beyond counting.
    Baseline stays q95|F| at random alphas (a displaced random alpha is
    another random alpha).

All quantities are normalized by sqrt|R| per window, as in waves 1-2.
  rho_resid_X(z) = q95 |residual at rationals| / q95 |F at random alphas|.

PRE-REGISTERED VERDICTS (applied mechanically to Arm A):
  signal    = rho_resid <= 1.35 at every z in {700, 1000, 2000, 5000};
  killed    = rho_resid >= 3 persistently (operationalized before the run:
              at >= 3 of the 4 z values);
  ambiguous = otherwise.
"""

import numpy as np
import time
from math import gcd

rng = np.random.default_rng(2026071803)
t0 = time.time()

H = 100_000
NWIN = 60
XLO, XHI = 5 * 10 ** 7, 10 ** 8
ZLIST = [700, 1000, 2000, 5000]
DELTAS = [0.5 / H, 2.0 / H]
# dichotomy guard: z^3 > x+H for all z in ZLIST (700^3 = 3.43e8 > 1.0001e8)
assert min(ZLIST) ** 3 > XHI + H

# primes up to sqrt(max n) with margin (same arithmetic as waves 1-2)
ROOT = int((XHI + 2 * H) ** 0.5) + 1
sv = np.ones(ROOT + 1, dtype=bool)
sv[:2] = False
for i in range(2, int(ROOT ** 0.5) + 1):
    if sv[i]:
        sv[i * i:: i] = False
PRIMES = np.nonzero(sv)[0].astype(np.int64)

# Farey fractions a/q, q <= 48, gcd(a,q)=1 (same grid as waves 1-2)
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
    Identical arithmetic to wave-2 window_arrays."""
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
    omega[left] += 1  # remaining cofactor is a prime
    minf[minf == 0] = 2 ** 31 - 1  # no factor <= sqrt(n): n itself is prime
    lam = (1 - 2 * (omega & 1)).astype(np.int8)
    return lam, minf.astype(np.int32), omega


def cbincount(r, w, q):
    """Complex-weighted bincount."""
    return (np.bincount(r, weights=w.real, minlength=q)
            + 1j * np.bincount(r, weights=w.imag, minlength=q))


print("PROBE W3-2: SP-subtracted LFU residual  "
      f"(H={H}, NWIN={NWIN}, x in [{XLO:.0e},{XHI:.0e}])")
print(f"z list {ZLIST} (all above Omega<=2 dichotomy z* ~ "
      f"{round((XHI + H) ** (1.0 / 3.0))})")
print(f"Farey fractions q<=48: {NFAREY}; random alphas per window: {NRAND}; "
      f"deltas for Arm C: {[f'{d * H:g}/H' for d in DELTAS]}")
print("NOTE: Arm A (pre-registered, exact rationals) is an algebraic identity"
      " on Omega<=2 windows -- see module docstring; its run documents the"
      " identity at machine precision.")

windows = []
for w in range(NWIN):
    x = int(rng.integers(XLO, XHI))
    lam, minf, omega = window_arrays(x, H)
    windows.append((x, lam, minf, omega))
print(f"[{time.time()-t0:7.1f}s] {NWIN} windows sieved")

rows = []
for z in ZLIST:
    Frat, Frand = [], []
    RA, RB = [], []
    RC = {d: [] for d in DELTAS}
    sizes, pfracs = [], []
    maxdev = 0.0  # max |F - M'_class| / sqrt|R| over all rationals (Arm A)
    used = 0
    for (x, lam, minf, omega) in windows:
        R = np.nonzero(minf > z)[0]
        if R.size < 50:
            continue
        used += 1
        n_int = (x + 1 + R).astype(np.int64)
        lamR = lam[R].astype(np.float64)
        omR = omega[R]
        assert omR.max() <= 2, "Omega<=2 dichotomy violated"
        isP = omR == 1
        P = int(isP.sum())
        sz = R.size
        sqrtR = np.sqrt(sz)
        pbar = P / sz
        sizes.append(sz)
        pfracs.append(pbar)
        n_f = n_int.astype(np.float64)
        # random-alpha baseline
        for al in RAND_ALPHA:
            ph = np.exp(2j * np.pi * ((al * n_f) % 1.0))
            Frand.append(abs((lamR * ph).sum()) / sqrtR)
        # per-delta window phases for Arm C
        phs = {d: np.exp(2j * np.pi * ((n_f * d) % 1.0)) for d in DELTAS}
        for q in QS:
            r = (n_int % q).astype(np.int64)
            Nc = np.bincount(r, minlength=q).astype(np.float64)
            Pc = np.bincount(r[isP], minlength=q).astype(np.float64)
            Sc = np.bincount(r, weights=lamR, minlength=q)
            mval = np.zeros(q)
            nzc = Nc > 0
            mval[nzc] = (Nc[nzc] - 2 * Pc[nzc]) / Nc[nzc]
            roots = ROOTS[q]
            # class sums for displaced rationals (Arm C)
            Td, Ud = {}, {}
            for d in DELTAS:
                ph = phs[d]
                Td[d] = cbincount(r, lamR * ph, q)
                Ud[d] = mval * cbincount(r, ph + 0j, q)
            Mclass_c = Nc - 2 * Pc  # = Sc identically (Omega<=2 identity)
            Mglob_c = (1 - 2 * pbar) * Nc
            for a in AS_BY_Q[q]:
                rot = roots[IDX[q][a]]
                Fv = (Sc * rot).sum()
                Frat.append(abs(Fv) / sqrtR)
                dA = abs(Fv - (Mclass_c * rot).sum()) / sqrtR
                RA.append(dA)
                if dA > maxdev:
                    maxdev = dA
                RB.append(abs(Fv - (Mglob_c * rot).sum()) / sqrtR)
                for d in DELTAS:
                    RC[d].append(abs(((Td[d] - Ud[d]) * rot).sum()) / sqrtR)
    Frat = np.array(Frat)
    Frand = np.array(Frand)
    RA = np.array(RA)
    RB = np.array(RB)
    q95rand = np.quantile(Frand, 0.95)
    q95rat = np.quantile(Frat, 0.95)
    rho_w2 = q95rat / q95rand
    rhoA = np.quantile(RA, 0.95) / q95rand
    rhoB = np.quantile(RB, 0.95) / q95rand
    rhoC = {d: np.quantile(np.array(RC[d]), 0.95) / q95rand for d in DELTAS}
    rows.append((z, np.mean(sizes), np.mean(pfracs), rho_w2,
                 rhoA, rhoB, rhoC, maxdev, used, q95rat, q95rand))
    print(f"\n=== z={z}  (windows {used}, mean |R| = {np.mean(sizes):.0f}, "
          f"mean prime fraction in R = {np.mean(pfracs):.3f}) ===")
    print(f"  q95 |F| rationals {q95rat:.3f}   q95 |F| random {q95rand:.3f}"
          f"   rho(wave-2 style) = {rho_w2:.3f}")
    print(f"  Arm A (PRE-REG, per-class model, exact rationals): "
          f"rho_resid = {rhoA:.3e}   max|F-M'|/sqrtR = {maxdev:.3e}"
          f"   [identity: expected 0]")
    print(f"  Arm B (suppl., global model, exact rationals):     "
          f"rho_resid = {rhoB:.3f}")
    for d in DELTAS:
        print(f"  Arm C (suppl., per-class model, a/q + {d * H:g}/H):     "
              f"rho_resid = {rhoC[d]:.3f}")
    print(f"  [{time.time()-t0:7.1f}s]")

print("\n=== SUMMARY TABLE ===")
head = ("   z    mean|R|  pfrac  rho_w2   rhoA(prereg)  rhoB(glob)"
        + "".join(f"  rhoC({d * H:g}/H)" for d in DELTAS) + "   maxdevA")
print(head)
for (z, mR, pf, rw2, rA, rB, rC, mdev, used, qr, qn) in rows:
    line = (f"{z:6d}  {mR:7.0f}  {pf:5.3f}  {rw2:6.3f}   {rA:12.3e}  "
            f"{rB:10.3f}")
    for d in DELTAS:
        line += f"  {rC[d]:11.3f}"
    line += f"  {mdev:9.3e}"
    print(line)

# --- mechanical verdict per pre-registered rules (Arm A) ---
rhoA_by_z = {row[0]: row[4] for row in rows}
sig = all(rhoA_by_z[z] <= 1.35 for z in ZLIST)
kill = sum(1 for z in ZLIST if rhoA_by_z[z] >= 3) >= 3
print("\n=== PRE-REGISTERED VERDICT (Arm A, mechanical) ===")
print(f"  rho_resid <= 1.35 at every z : {sig}  "
      f"({[f'{rhoA_by_z[z]:.2e}' for z in ZLIST]})")
print(f"  rho_resid >= 3 at >= 3 of 4 z (kill) : {kill}")
if kill:
    verdict = "KILLED"
elif sig:
    verdict = "SIGNAL"
else:
    verdict = "AMBIGUOUS"
print(f"  VERDICT: {verdict}")
print("  HONESTY FLAG: Arm A residual is zero by an algebraic identity on"
      " Omega<=2 windows (F(a/q) = M'(a/q) exactly, since e(n a/q) is"
      " constant on classes mod q). The pre-registered 'signal' is therefore"
      " VACUOUS as an empirical finding: it holds as a theorem, in the"
      " strongest possible form (residual exactly 0, not merely <= 1.35)."
      " Empirical content lives in the supplementary Arms B and C above,"
      " which carry NO pre-registered verdict.")
print(f"[{time.time()-t0:7.1f}s] done")
