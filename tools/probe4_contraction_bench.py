"""PROBE W4-5 (dependence-aware contraction benchmark; wave-4 queue item (v)).

Background (wave 3, tools/probe3_opened_sieve.py): the opened pair sieve
  Lx(z) = Sum_{d | P(z)} mu(d) * S_roots(d),
    S_roots(d) = Sum_{a: 36a^2=1 mod d} Sum_{m = a mod d, m <= X} F(m),
    F(m) = lambda(6m-1) * lambda(6m+1),
was verified integer-exactly at X = 10^8, and the centered partial sums
  err(k) = Sum_{k smallest d} mu(d) * (S_roots(d) - 2^omega(d) * full / d)
landed 5-7x BELOW the independent-noise floor sqrt(Sum 2^om X/d) -- an
anti-adversarial over-cancellation that the independence benchmark cannot
rationalize.  This probe re-registers the SAME measured object against two
dependence-aware benchmarks:

 (a) V-model (identity-consistent residual scale): the exact identity forces
     the full opened sum to equal the pair-rough restricted sum Lx(z), whose
     natural sqrt-scale is sqrt(V(z) * X) with
         V(z) = prod_{5 <= p <= z} (1 - 2/p)
     (the pair-rough density; primes 2, 3 never divide 36m^2-1).  Benchmark
     at truncation k uses z_k = largest prime dividing any of the k smallest
     moduli: bench_V(k) = sqrt(V(z_k) * X).

 (b) Permutation baseline (dependence destroyed, magnitudes kept): 1000
     random sign vectors eps_d in {+-1} applied to the CENTERED terms
     c_d = mu(d) * (S_roots(d) - 2^om(d) * full / d), with the d = 1 term
     kept fixed (c_1 = 0 identically); rebuild partial sums over the same
     d-ordering; benchmark = per-k 95th percentile of |err_perm(k)|.

Report |err(k)| / benchmark for both at octiles k = 32, 64, ..., 256.

PRE-REGISTERED VERDICTS (mechanical):
  signal    = |err(k)|/bench_V in [0.2, 3] at ALL octiles
              OR |err(k)| <= perm-95th(k) at ALL octiles
              (either benchmark rationalizes the observed contraction);
  killed    = at some octile |err(k)| > 3 * bench_V(k)
              AND |err(k)| > 3 * perm-95th(k)  (unmodeled conspiracy);
  ambiguous = otherwise.
Validity gate: the z=30 identity must reproduce LHS = RHS = 1149 exactly
(else BLOCKED: code bug).
"""

import numpy as np
import time
from itertools import combinations

X = 100_000_000
N = 6 * X + 1
SEG = 10_000_000
PRIMES_Z = [5, 7, 11, 13, 17, 19, 23, 29]
OCTILES = [32, 64, 96, 128, 160, 192, 224, 256]
NPERM = 1000
RNG = np.random.default_rng(20260718)

t0 = time.time()


def log(msg):
    print(f"[{time.time()-t0:8.1f}s] {msg}", flush=True)


def lambda_sieve(N, SEG):
    """Liouville lambda(n) for 0..N via segmented Omega-parity
    (same routine as wave-1/wave-3 probes)."""
    lam = np.ones(N + 1, dtype=np.int8)
    root = int(N ** 0.5) + 1
    small = np.ones(root + 1, dtype=bool)
    small[:2] = False
    for i in range(2, int(root ** 0.5) + 1):
        if small[i]:
            small[i * i:: i] = False
    primes = np.nonzero(small)[0]
    for lo in range(0, N + 1, SEG):
        hi = min(lo + SEG, N + 1)
        size = hi - lo
        omega = np.zeros(size, dtype=np.int8)
        rem = np.arange(lo, hi, dtype=np.int64)
        if lo == 0:
            rem[0] = 1  # n=0 unused
        for p in primes:
            pk = int(p)
            while pk <= N:
                start = ((lo + pk - 1) // pk) * pk
                if start >= hi:
                    break
                idx = np.arange(start - lo, size, pk, dtype=np.int64)
                omega[idx] += 1
                rem[idx] //= p
                pk *= p
        omega[rem > 1] += 1
        lam[lo:hi] = 1 - 2 * (omega & 1)
    return lam


log(f"sieving lambda up to N={N} ...")
lam = lambda_sieve(N, SEG)
log("sieve done")
assert lam[2] == -1 and lam[4] == 1 and lam[12] == -1 and lam[36] == 1
assert lam[30] == -1 and lam[8] == -1 and lam[9] == 1

Fm = np.empty(X, dtype=np.int8)
for lo in range(0, X, SEG):
    hi = min(lo + SEG, X)
    a = lam[6 * lo + 5: 6 * hi: 6].astype(np.int16)
    b = lam[6 * lo + 7: 6 * hi + 2: 6].astype(np.int16)
    Fm[lo:hi] = (a * b).astype(np.int8)
del lam, a, b
log("F(m) built, lambda array freed")

anchor6 = int(Fm[:1_000_000].sum(dtype=np.int64))
anchor7 = int(Fm[:30_000_000].sum(dtype=np.int64))
full = int(Fm.sum(dtype=np.int64))
log(f"anchor: sum F(m), m<=1e6  = {anchor6}   (wave-1 value: 236)")
log(f"anchor: sum F(m), m<=3e7  = {anchor7}   (wave-1 value: 3918)")
log(f"full:   sum F(m), m<=1e8  = {full}   sqrt(X) = {X**0.5:.0f}")
assert anchor6 == 236, "ANCHOR MISMATCH at 1e6 -> BLOCKED (sieve bug)"
assert anchor7 == 3918, "ANCHOR MISMATCH at 3e7 -> BLOCKED (sieve bug)"


def crt_roots(primes_sub):
    """(d, roots): all a in [0,d) with 36 a^2 = 1 (mod d), d squarefree."""
    d = 1
    roots = [0]
    for p in primes_sub:
        inv6 = pow(6, -1, p)
        dinv = pow(d % p, -1, p)
        new = []
        for r in roots:
            for s in (inv6, p - inv6):
                t = ((s - r) * dinv) % p
                new.append(r + d * t)
        roots = new
        d *= p
    return d, roots


def root_class_sum(d, roots):
    """Exact integer Sum over roots a of Sum_{m = a (mod d), 1<=m<=X} F(m)."""
    if d == 1:
        return full
    s = 0
    for a in roots:
        if a - 1 < X:
            s += int(Fm[a - 1:: d].sum(dtype=np.int64))
    return s


_d, _r = crt_roots([5, 7])
assert _d == 35 and sorted(_r) == sorted(
    a for a in range(35) if (36 * a * a - 1) % 35 == 0)

# ------------------------------------------- validity gate: z=30 identity
log("validity gate: exact pair-rough LHS at z=30 via trial division")
LHS30 = 0
for lo in range(0, X, SEG):
    hi = min(lo + SEG, X)
    mv = np.arange(lo + 1, hi + 1, dtype=np.int64)
    wm = 6 * mv - 1
    wp = wm + 2
    bad = np.zeros(hi - lo, dtype=bool)
    for p in PRIMES_Z:
        bad |= (wm % p == 0) | (wp % p == 0)
    LHS30 += int(Fm[lo:hi][~bad].sum(dtype=np.int64))
del mv, wm, wp, bad
log(f"    LHS(z=30) = {LHS30}   (wave-3 value: 1149)")

# --------------------------------------- exact opened terms, 256 moduli
log("opened terms: all 256 squarefree d | P(30), t_d = mu(d)*S_roots(d)")
records = []  # d, mu, om, maxp, S
for k in range(len(PRIMES_Z) + 1):
    for sub in combinations(PRIMES_Z, k):
        d, roots = crt_roots(list(sub))
        S = root_class_sum(d, roots)
        records.append(dict(d=d, mu=(-1) ** k, om=k,
                            maxp=(max(sub) if sub else 0), S=S))
log(f"    {len(records)} moduli done (largest d = "
    f"{max(r['d'] for r in records)})")

RHS30 = sum(r["mu"] * r["S"] for r in records)
identity_ok = (LHS30 == RHS30 == 1149)
print(f"\n--- VALIDITY GATE ---\n  z=30: LHS = {LHS30}   RHS = {RHS30}   "
      f"wave-3 = 1149   EXACT MATCH: {identity_ok}", flush=True)

# ------------------------------- centered terms and observed partial sums
recs = sorted(records, key=lambda r: r["d"])
c = np.array([r["mu"] * (r["S"] - (2 ** r["om"]) * full / r["d"])
              for r in recs])                       # centered terms, d=1 -> 0
assert abs(c[0]) < 1e-9, "d=1 term not centered to 0"
err = np.cumsum(c)                                  # err(k) at k = 1..256
maxp_cum = np.maximum.accumulate(np.array([r["maxp"] for r in recs]))

# ---------------------------------------------- benchmark (a): V-model
V_at = {}
prod = 1.0
for p in PRIMES_Z:
    prod *= (1.0 - 2.0 / p)
    V_at[p] = prod
bench_V = np.array([(V_at[maxp_cum[k - 1]] * X) ** 0.5 if maxp_cum[k - 1] > 0
                    else float("inf") for k in range(1, 257)])

# --------------------------------------- benchmark (b): permutation 95th
log(f"permutation baseline: {NPERM} random sign-flips on centered terms "
    f"(d=1 fixed)")
eps = RNG.choice(np.array([-1.0, 1.0]), size=(NPERM, len(c)))
eps[:, 0] = 1.0                                     # keep d = 1 term fixed
perm_err = np.cumsum(eps * c[None, :], axis=1)      # (NPERM, 256)
perm95 = np.quantile(np.abs(perm_err), 0.95, axis=0)

# ----------------------------------------------------------- report table
print("\n--- (b) DEPENDENCE-AWARE CONTRACTION BENCHMARKS "
      "(z=30, 256 moduli ordered by d) ---", flush=True)
print("    k    d_k        z_k      err(k)     bench_V   err/V "
      "   perm95   err/perm95", flush=True)
ratio_V, ratio_P = {}, {}
for k in OCTILES:
    i = k - 1
    rV = abs(err[i]) / bench_V[i]
    rP = abs(err[i]) / perm95[i] if perm95[i] > 0 else float("inf")
    ratio_V[k] = rV
    ratio_P[k] = rP
    print(f"  {k:3d}  {recs[i]['d']:10d}  {maxp_cum[i]:3d}  "
          f"{err[i]:10.1f}  {bench_V[i]:10.1f}  {rV:6.3f}  "
          f"{perm95[i]:9.1f}  {rP:8.3f}", flush=True)

# ------------------------------------------------------------- verdict
print("\n--- PRE-REGISTERED VERDICT (mechanical) ---", flush=True)
cond_V = all(0.2 <= ratio_V[k] <= 3.0 for k in OCTILES)
cond_P = all(ratio_P[k] <= 1.0 for k in OCTILES)
cond_kill = any(ratio_V[k] > 3.0 and ratio_P[k] > 3.0 for k in OCTILES)

print(f"  validity gate (z=30 identity):      {identity_ok}", flush=True)
print(f"  err/V-model in [0.2,3] all octiles: {cond_V}   "
      f"({['%.3f' % ratio_V[k] for k in OCTILES]})", flush=True)
print(f"  err <= perm-95th at all octiles:    {cond_P}   "
      f"({['%.3f' % ratio_P[k] for k in OCTILES]})", flush=True)
print(f"  kill (err > 3x BOTH somewhere):     {cond_kill}", flush=True)

if not identity_ok:
    verdict = "BLOCKED (identity gate failed -> code bug suspected)"
elif cond_V or cond_P:
    verdict = "SIGNAL"
elif cond_kill:
    verdict = "KILLED"
else:
    verdict = "AMBIGUOUS"
print(f"\nVERDICT: {verdict}", flush=True)
log("done")
