"""PROBE W3-1 (opened pair sieve + kappa contraction; queue items (i)+(v)).

Objects: F(m) = lambda(6m-1)*lambda(6m+1) = lambda(36m^2-1), m <= X.
P(z) = product of primes in [5, z].  For squarefree d | P(z) the congruence
36 a^2 = 1 (mod d) has exactly 2^omega(d) roots (CRT: a = +-inv6 per factor).

Structural identity under test (inclusion-exclusion unroll of PAIR roughness):
  Lx(z) := Sum_{m<=X, both 6m-1 and 6m+1 z-rough} F(m)
         = Sum_{d | P(z)} mu(d) * Sum_{a: 36a^2=1 mod d} Sum_{m=a mod d, m<=X} F(m).

Parts:
 (a) EXACT identity check for z in {10, 20, 30}: LHS by trial division of
     6m+-1 by primes <= z (independent path), RHS by root-class strided sums.
 (b) Contraction: order d | P(30) by size, accumulated error
     err(k) = Sum_{k smallest d} mu(d)*(S_roots(d) - 2^omega(d)*full/d)
     against noise scale sqrt(Sum_{k smallest d} 2^omega(d)*X/d); ratio at
     k-quartiles (64, 128, 192, 256).
 (c) Composite E(d) scan: ALL squarefree d coprime to 6, d <= 10^4, r(d) =
     |E(d)|/sqrt(2^omega(d)*X/d), stats binned by omega(d).

PRE-REGISTERED VERDICTS (mechanical):
  signal    = identity EXACT for all three z
              AND contraction ratio in [0.3, 3] at all quartiles
              AND r-means for omega = 2, 3 within [0.5, 1.2];
  killed    = identity mismatch (blocked if code bug suspected),
              OR r-mean for omega >= 2 exceeding 2,
              OR contraction ratio > 10;
  ambiguous = otherwise.
"""

import numpy as np
import time
from itertools import combinations

X = 100_000_000
N = 6 * X + 1
SEG = 10_000_000
DMAX_C = 10_000
PRIMES_Z = [5, 7, 11, 13, 17, 19, 23, 29]
ZLISTS = {10: [5, 7], 20: [5, 7, 11, 13, 17, 19], 30: PRIMES_Z}

t0 = time.time()


def log(msg):
    print(f"[{time.time()-t0:8.1f}s] {msg}", flush=True)


def lambda_sieve(N, SEG):
    """Liouville lambda(n) for 0..N (lam[0] = lam[1] = +1 convention;
    only n >= 5 used downstream), via segmented Omega-parity.
    Same routine as wave-1 tools/probe_ed_scan.py."""
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

# F(m), m = 1..X  ->  Fm[m-1], built in chunks to keep memory low
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


# ---------------------------------------------------------------- helpers
def crt_roots(primes_sub):
    """(d, roots) with roots = all a in [0,d) satisfying 36 a^2 = 1 (mod d),
    d = prod(primes_sub) squarefree, built by CRT: a = +-inv6 per factor."""
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


# sanity of crt_roots on d = 35
_d, _r = crt_roots([5, 7])
assert _d == 35 and sorted(_r) == sorted(
    a for a in range(35) if (36 * a * a - 1) % 35 == 0)

# ------------------------------------------------- (a) LHS: trial division
log("(a) LHS: exact pair-rough sums via trial division, z in {10,20,30}")
LHS = {10: 0, 20: 0, 30: 0}
for lo in range(0, X, SEG):
    hi = min(lo + SEG, X)
    mv = np.arange(lo + 1, hi + 1, dtype=np.int64)
    wm = 6 * mv - 1
    wp = wm + 2
    divmask = {}
    for p in PRIMES_Z:
        divmask[p] = (wm % p == 0) | (wp % p == 0)
    seg = Fm[lo:hi]
    for z, pl in ZLISTS.items():
        bad = np.zeros(hi - lo, dtype=bool)
        for p in pl:
            bad |= divmask[p]
        LHS[z] += int(seg[~bad].sum(dtype=np.int64))
del mv, wm, wp, divmask, bad, seg
for z in (10, 20, 30):
    log(f"    LHS(z={z}) = {LHS[z]}")

# ------------------------------------- (a) RHS: 256 moduli, root classes
log("(a) RHS: enumerating all 256 squarefree d | P(30) with root sums")
records = []  # dicts: d, mu, om, maxp, S (exact int root-class sum)
for k in range(len(PRIMES_Z) + 1):
    for sub in combinations(PRIMES_Z, k):
        d, roots = crt_roots(list(sub))
        S = root_class_sum(d, roots)
        records.append(dict(d=d, mu=(-1) ** k, om=k,
                            maxp=(max(sub) if sub else 0), S=S))
log(f"    {len(records)} moduli done (largest d = {max(r['d'] for r in records)})")

RHS = {z: sum(r["mu"] * r["S"] for r in records if r["maxp"] <= z)
       for z in (10, 20, 30)}

print("\n--- (a) EXACT IDENTITY CHECK ---", flush=True)
identity_ok = True
for z in (10, 20, 30):
    nmod = sum(1 for r in records if r["maxp"] <= z)
    match = (LHS[z] == RHS[z])
    identity_ok &= match
    print(f"  z={z:2d}: LHS = {LHS[z]:10d}   RHS = {RHS[z]:10d}   "
          f"moduli = {nmod:3d}   EXACT MATCH: {match}", flush=True)

# ------------------------------------------------- (b) contraction, z=30
print("\n--- (b) CONTRACTION MEASUREMENT (z=30, 256 moduli ordered by d) ---",
      flush=True)
recs = sorted(records, key=lambda r: r["d"])
cum_err = 0.0
cum_var_incl = 0.0   # literal pre-registered formula (includes d=1 term X)
cum_var_excl = 0.0   # variant excluding d=1 (E(1)=0 deterministically)
traj = []
for i, rec in enumerate(recs, 1):
    E = rec["S"] - (2 ** rec["om"]) * full / rec["d"]
    cum_err += rec["mu"] * E
    v = (2 ** rec["om"]) * X / rec["d"]
    cum_var_incl += v
    if rec["d"] > 1:
        cum_var_excl += v
    traj.append((i, rec["d"], cum_err, cum_var_incl, cum_var_excl))

quartile_ratios = []
print("    k    d_k          err(k)      noise(k)   ratio   ratio_no_d1",
      flush=True)
for i, dk, err, vi, ve in traj:
    if i in (32, 64, 96, 128, 160, 192, 224, 256):
        ni = vi ** 0.5
        ne = ve ** 0.5 if ve > 0 else float("nan")
        ratio = abs(err) / ni
        ratio_e = abs(err) / ne if ve > 0 else float("nan")
        tag = ""
        if i in (64, 128, 192, 256):
            quartile_ratios.append(ratio)
            tag = "  <- quartile"
        print(f"  {i:3d}  {dk:9d}  {err:12.1f}  {ni:12.1f}  {ratio:6.3f}"
              f"   {ratio_e:6.3f}{tag}", flush=True)

# --------------------------------------------- (c) composite E(d) scan
log("(c) composite scan: all squarefree (d,6)=1, d <= 10^4")
spf = list(range(DMAX_C + 1))
for i in range(2, int(DMAX_C ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, DMAX_C + 1, i):
            if spf[j] == j:
                spf[j] = i

targets = []
for d in range(5, DMAX_C + 1):
    if d % 2 == 0 or d % 3 == 0:
        continue
    n, fs, sqfree = d, [], True
    while n > 1:
        p = spf[n]
        n //= p
        if n % p == 0:
            sqfree = False
            break
        fs.append(p)
    if sqfree:
        targets.append((d, fs))
log(f"    {len(targets)} moduli; workload Sum 2^om/d = "
    f"{sum(2**len(fs)/d for d, fs in targets):.2f} passes over X")

by_om = {}
done = 0
for d, fs in targets:
    dd, roots = crt_roots(fs)
    assert dd == d
    om = len(fs)
    S = root_class_sum(d, roots)
    E = S - (2 ** om) * full / d
    r = abs(E) / ((2 ** om) * X / d) ** 0.5
    by_om.setdefault(om, []).append(r)
    done += 1
    if done % 1000 == 0:
        log(f"    ... {done}/{len(targets)} moduli")
log("    composite scan done")

print("\n--- (c) COMPOSITE E(d) SCAN: r(d) = |E(d)|/sqrt(2^om X/d) by omega ---",
      flush=True)
print("  (Gaussian-pure benchmark: E|N(0,1)| = 0.798)", flush=True)
r_means = {}
for om in sorted(by_om):
    arr = np.array(by_om[om])
    r_means[om] = float(arr.mean())
    print(f"  omega={om}: n={len(arr):5d}  mean={arr.mean():.3f}  "
          f"median={np.median(arr):.3f}  q95={np.quantile(arr, 0.95):.3f}  "
          f"max={arr.max():.3f}", flush=True)

# ------------------------------------------------------------- verdict
print("\n--- PRE-REGISTERED VERDICT (mechanical) ---", flush=True)
cond_identity = identity_ok
cond_contract_sig = all(0.3 <= q <= 3.0 for q in quartile_ratios)
cond_contract_kill = any(q > 10.0 for q in quartile_ratios)
m2, m3 = r_means.get(2, float("nan")), r_means.get(3, float("nan"))
cond_r_sig = (0.5 <= m2 <= 1.2) and (0.5 <= m3 <= 1.2)
cond_r_kill = (m2 > 2.0) or (m3 > 2.0)

print(f"  identity exact (all z):        {cond_identity}", flush=True)
print(f"  quartile ratios:               "
      f"{['%.3f' % q for q in quartile_ratios]}", flush=True)
print(f"  contraction in [0.3,3] all q:  {cond_contract_sig}"
      f"   (kill >10: {cond_contract_kill})", flush=True)
print(f"  r-mean omega=2: {m2:.3f}  omega=3: {m3:.3f}  "
      f"in [0.5,1.2]: {cond_r_sig}   (kill >2: {cond_r_kill})", flush=True)

if not cond_identity:
    verdict = "KILLED (identity mismatch; check for code bug -> blocked)"
elif cond_contract_kill or cond_r_kill:
    verdict = "KILLED"
elif cond_contract_sig and cond_r_sig:
    verdict = "SIGNAL"
else:
    verdict = "AMBIGUOUS"
print(f"\nVERDICT: {verdict}", flush=True)
log("done")
