"""PROBE A1 (wf-bv-chowla-in-aps): E(d)-scan of the twin cross-correlation
in progressions.

Objects: F(m) = lambda(6m-1)*lambda(6m+1) = lambda(36m^2-1), m <= X.
For a prime d > 3 the congruence 36 a^2 = 1 (mod d) has exactly the two
root classes a = +inv6, -inv6 (mod d) with inv6 = 6^{-1} mod d.
  S+(d), S-(d) = sums of F(m) over the two root classes,
  E(d) = S+(d) + S-(d) - (2/d) * FullSum.

Pre-registered verdict rules (probe ledger, binary-cancellation program):
  signal    = r(d) = |E(d)|/sqrt(2X/d) flat O(1) in dyadic d-bins
              AND |corr(S+, S-)| < 0.3
              AND |T(D)|/X stays below ~0.001 scale,
  killed    = r(d) grows systematically with d, OR corr > 0.7,
              OR T(D) reaches main-term size,
  ambiguous = otherwise.
"""

import numpy as np
import sys
import time

X = 30_000_000
N = 6 * X + 1
SEG = 10_000_000
DMAX = 30_000

t0 = time.time()


def lambda_sieve(N, SEG):
    """Liouville lambda(n) for 0..N (lam[0] = lam[1] = +1 convention;
    only n >= 5 used downstream), via segmented Omega-parity."""
    lam = np.ones(N + 1, dtype=np.int8)
    root = int(N ** 0.5) + 1
    # primes up to sqrt(N) by simple sieve
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
            rem[0] = 1  # avoid zero-division bookkeeping; n=0 unused
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


print(f"[{time.time()-t0:7.1f}s] sieving lambda up to N={N} ...")
lam = lambda_sieve(N, SEG)
print(f"[{time.time()-t0:7.1f}s] sieve done")

# sanity: lambda(2)=-1, lambda(4)=+1, lambda(12)=-1, lambda(36)=+1
assert lam[2] == -1 and lam[4] == 1 and lam[12] == -1 and lam[36] == 1

# F(m), m = 1..X  ->  Fm[m-1]
Fm = (lam[5: 6 * X: 6].astype(np.int32) * lam[7: 6 * X + 2: 6]).astype(np.int8)
assert Fm.shape[0] == X

anchor6 = int(Fm[:1_000_000].astype(np.int64).sum())
full = int(Fm.astype(np.int64).sum())
print(f"anchor: sum F(m), m<=1e6  = {anchor6}   (prospecting claimed 236)")
print(f"full:   sum F(m), m<=X={X:.0e} = {full}   sqrt(X) = {X**0.5:.0f}")

# primes 3 < d <= DMAX
sv = np.ones(DMAX + 1, dtype=bool)
sv[:2] = False
for i in range(2, int(DMAX ** 0.5) + 1):
    if sv[i]:
        sv[i * i:: i] = False
ds = [int(d) for d in np.nonzero(sv)[0] if d > 3]
print(f"[{time.time()-t0:7.1f}s] scanning {len(ds)} prime moduli d <= {DMAX}")

Fi64 = Fm.astype(np.int64)
Sp = np.zeros(len(ds))
Sm = np.zeros(len(ds))
Ed = np.zeros(len(ds))
for j, d in enumerate(ds):
    inv6 = pow(6, -1, d)
    ap = inv6 % d
    am = (-inv6) % d
    # m runs 1..X ; class m = a (mod d): indices a-1, a-1+d, ... (a in 1..d;
    # a = 0 impossible since 36*0-1 = -1 not divisible)
    sp = int(Fi64[ap - 1:: d].sum()) if ap >= 1 else int(Fi64[d - 1:: d].sum())
    sm = int(Fi64[am - 1:: d].sum()) if am >= 1 else int(Fi64[d - 1:: d].sum())
    Sp[j], Sm[j] = sp, sm
    Ed[j] = sp + sm - 2.0 * full / d

r = np.abs(Ed) / np.sqrt(2.0 * X / np.array(ds))

print("\n--- (i) normalized r(d) = |E(d)|/sqrt(2X/d), dyadic bins ---")
lo = 5
while lo <= DMAX:
    hi = min(2 * lo, DMAX + 1)
    mask = (np.array(ds) >= lo) & (np.array(ds) < hi)
    if mask.sum() > 0:
        rb = r[mask]
        print(f"  d in [{lo:6d},{hi:6d}): n={mask.sum():5d}  "
              f"mean={rb.mean():.3f}  median={np.median(rb):.3f}  "
              f"q95={np.quantile(rb, 0.95):.3f}  max={rb.max():.3f}")
    lo = hi

print("\n--- (ii) conjugate-root correlation ---")
cc = np.corrcoef(Sp, Sm)[0, 1]
print(f"  Pearson corr(S+, S-) over d: {cc:+.4f}")
# also correlation of the fluctuation parts (subtract common mean term)
Ep = Sp - full / np.array(ds)
Em = Sm - full / np.array(ds)
ccf = np.corrcoef(Ep, Em)[0, 1]
print(f"  Pearson corr of fluctuations E+(d), E-(d): {ccf:+.4f}")

print("\n--- (iii) toy opened sieve: T(D) = sum_(3<d<=D) mu(d)(S+ + S-) ---")
T = -np.cumsum(Sp + Sm)  # mu(prime) = -1
Ds = np.array(ds)
for Dcut in [100, 300, 1000, 3000, 10000, 30000]:
    k = np.searchsorted(Ds, Dcut, side="right") - 1
    if k >= 0:
        sqrt_scale = np.sqrt((2.0 * X / Ds[: k + 1]).sum())
        print(f"  D={Dcut:6d}: T(D)={T[k]:12.0f}  |T|/X={abs(T[k])/X:.6f}  "
              f"sqrt-scale/X={sqrt_scale/X:.6f}")

print(f"\n[{time.time()-t0:7.1f}s] done")
