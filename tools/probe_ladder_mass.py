"""PROBE A4 (ladder-entropy-chowla-transfer): coefficient mass of the
roughness-peeling ladder + dilated correlations.

(1) EXACT depth-1 minFac-fibered identity at X = 10^6:
      FullSum = Lx(z) + sum_{5<=p<=z} N_p
    where N_p = sum of F(m) over m whose product (6m-1)(6m+1) has smallest
    prime factor exactly p.  Must match exactly (else status=blocked).
(2) Mass ledger:
      - fibered ladder: the tree is a PARTITION at every level => l1 mass = 1
        identically (verified at depth 1 numerically); price: nodes carry
        rough-CONSTRAINED correlations.
      - inclusion-exclusion unroll to UNconstrained correlations:
        M_IE(z) = prod_{5<=p<=z} (1 + 2/p)  (exact rational) -> c log^2 z.
      - hybrid: fiber to w, I-E the band (w, z]: per-node inflation
        prod_{w<p<=z}(1+2/p).
(3) Dilated correlations (the objects the ladder produces at its nodes,
    UNconstrained version -- Tao's averaging target):
      D(p) = sum_{k<=K} lambda(k) lambda(p k + 2),  normalized by sqrt K.

Pre-registered verdict rules: signal = mass bounded (or single log) with
signed mass bounded; killed = clean log^2 for every organization; the
identity in (1) must pass exactly or blocked.
"""

import numpy as np
from fractions import Fraction
import time

t0 = time.time()

# ---------- lambda + minFac sieve up to N ----------
X1 = 10 ** 6
KMAX = 10 ** 7
PMAXD = 100
N = max(6 * X1 + 2, PMAXD * KMAX + 2)


def sieve_lam_minf(N):
    root = int(N ** 0.5) + 1
    sv = np.ones(root + 1, dtype=bool)
    sv[:2] = False
    for i in range(2, int(root ** 0.5) + 1):
        if sv[i]:
            sv[i * i:: i] = False
    primes = np.nonzero(sv)[0]
    lam = np.ones(N + 1, dtype=np.int8)
    minf = np.zeros(N + 1, dtype=np.int32)
    SEG = 10 ** 7
    for lo in range(0, N + 1, SEG):
        hi = min(lo + SEG, N + 1)
        size = hi - lo
        omega = np.zeros(size, dtype=np.int8)
        rem = np.arange(lo, hi, dtype=np.int64)
        if lo == 0:
            rem[0] = 1
        mfs = np.zeros(size, dtype=np.int32)
        for p in primes:
            p = int(p)
            start = ((lo + p - 1) // p) * p
            if start >= hi:
                continue
            idx = np.arange(start - lo, size, p, dtype=np.int64)
            first = mfs[idx] == 0
            mfs[idx[first]] = p
            pk = p
            while pk <= N:
                s2 = ((lo + pk - 1) // pk) * pk
                if s2 >= hi:
                    break
                idx2 = np.arange(s2 - lo, size, pk, dtype=np.int64)
                omega[idx2] += 1
                pk *= p
        left = rem_gt = None
        # remaining prime factor > root
        remv = np.arange(lo, hi, dtype=np.int64)
        if lo == 0:
            remv[0] = 1
        # divide out counted primes cheaply: recompute via omega is enough for
        # lambda parity only if we count the large factor: n has at most one
        # prime factor > root; detect it via full division tracking:
        # (redo with rem tracking for correctness)
        rem2 = np.arange(lo, hi, dtype=np.int64)
        if lo == 0:
            rem2[0] = 1
        for p in primes:
            p = int(p)
            start = ((lo + p - 1) // p) * p
            if start >= hi:
                continue
            sub = np.arange(start - lo, size, p, dtype=np.int64)
            while sub.size:
                div = rem2[sub] % p == 0
                sub = sub[div]
                rem2[sub] //= p
        big = rem2 > 1
        omega[big] += 1
        mfs[(mfs == 0) & big] = 2 ** 31 - 1  # prime beyond root
        lam[lo:hi] = 1 - 2 * (omega & 1)
        minf[lo:hi] = mfs
    return lam, minf


print(f"[{time.time()-t0:6.1f}s] sieving lam+minFac to N={N} ...")
lam, minf = sieve_lam_minf(N)
print(f"[{time.time()-t0:6.1f}s] sieve done")
assert lam[2] == -1 and lam[4] == 1 and lam[15] == 1 and minf[15] == 3

# ---------- (1) exact depth-1 fibered identity ----------
m = np.arange(1, X1 + 1, dtype=np.int64)
a = 6 * m - 1
b = 6 * m + 1
F = (lam[a].astype(np.int32) * lam[b]).astype(np.int32)
mf_pair = np.minimum(minf[a], minf[b])
full = int(F.sum())
print(f"\n(1) exact fibered identity at X={X1}: FullSum = {full}")
for z in [10, 30, 100]:
    rough = mf_pair > z
    Lx = int(F[rough].sum())
    ps = [p for p in range(5, z + 1)
          if all(p % q for q in range(2, int(p ** 0.5) + 1))]
    parts = {p: int(F[mf_pair == p].sum()) for p in ps}
    rhs = Lx + sum(parts.values())
    ok = "EXACT MATCH" if rhs == full else f"MISMATCH ({rhs})"
    A = int(rough.sum())
    print(f"  z={z:4d}: Lx={Lx:8d}  A={A:8d}  Lx/A={Lx/max(A,1):+.4f}  "
          f"sum nodes={sum(parts.values()):8d}  identity: {ok}")

# ---------- (2) mass ledger ----------
print("\n(2) mass ledger:")
print("  fibered ladder: partition at every level -> l1 mass == 1 (exact).")
print("  I-E unroll to unconstrained sums: M_IE(z) = prod_(5<=p<=z)(1+2/p):")
zs = [10, 30, 100, 300, 1000, 3000, 10000, 30000]
sv2 = np.ones(max(zs) + 1, dtype=bool)
sv2[:2] = False
for i in range(2, int(max(zs) ** 0.5) + 1):
    if sv2[i]:
        sv2[i * i:: i] = False
allp = np.nonzero(sv2)[0]
rows = []
for z in zs:
    Mie = Fraction(1)
    for p in allp[(allp >= 5) & (allp <= z)]:
        Mie *= Fraction(int(p) + 2, int(p))
    lg = np.log(z)
    rows.append((z, float(Mie), float(Mie) / lg, float(Mie) / lg ** 2))
    print(f"  z={z:6d}: M_IE={float(Mie):9.3f}   M/log z={float(Mie)/lg:7.3f}"
          f"   M/log^2 z={float(Mie)/lg**2:7.4f}")
r_llog = np.corrcoef([np.log(np.log(r[0])) for r in rows],
                     [np.log(r[1]) for r in rows])[0, 1]
print(f"  (M/log^2 z stabilizing => clean log^2 growth for the I-E organization)")

# ---------- (3) dilated correlations ----------
print(f"\n(3) dilated correlations D(p) = sum_(k<=K) lam(k) lam(pk+2), "
      f"K={KMAX:.0e}:")
lamf = lam.astype(np.int32)
k = np.arange(1, KMAX + 1, dtype=np.int64)
lk = lamf[k]
res = []
for p in [1, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 53, 71, 97]:
    D = int((lk * lamf[p * k + 2]).sum())
    res.append((p, D, D / KMAX ** 0.5))
    print(f"  p={p:3d}: D(p)={D:8d}   D/sqrt(K)={D/KMAX**0.5:+7.3f}")
avg = np.mean([r[1] for r in res[1:]])
print(f"  p-average over dilations (p>1): {avg:.0f}   "
      f"normalized {avg/KMAX**0.5:+.3f}")
print(f"\n[{time.time()-t0:6.1f}s] done")
