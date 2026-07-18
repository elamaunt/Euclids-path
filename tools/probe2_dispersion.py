"""PROBE W2-1 (wf-bv-chowla-in-aps, wave 2): toy dispersion E(d1,d2) over
prime-pair moduli.

Objects: F(m) = lambda(6m-1)*lambda(6m+1) = lambda(36m^2-1), m <= X.
For primes d1 < d2 (both > 3) the joint root classes are the 4 CRT classes
  m = e1*inv6 (mod d1)  AND  m = e2*inv6 (mod d2),   e1, e2 in {+1,-1},
i.e. 4 residues a mod q, q = d1*d2.  Define
  S(d1,d2) = sum of F(m) over the union of the 4 classes,
  E(d1,d2) = S(d1,d2) - 4*FullSum/q.

Dyadic ranges D in {30, 100, 300, 1000}: all pairs d1 < d2 in [D, 2D).

Metrics (per dyadic D):
  (i)   r2 = |E|/sqrt(4X/q) distribution (mean/median/q95);
        Gaussian-noise prediction: mean = E|N(0,1)| = 0.798.
  (ii)  shared-modulus correlation: mean absolute pairwise Pearson
        correlation between rows E(d1, .) of the (symmetric) pair matrix
        (computed on raw E rows for the verdict, and on normalized
        z = E/sqrt(4X/q) rows as a heteroscedasticity check).
  (iii) Delta(D) = sum of E^2 over pairs vs noise prediction sum 4X/q.

Pre-registered verdict rules (probe ledger, binary-cancellation program):
  signal    = r2 mean in [0.5, 1.2] across all D
              AND mean |row correlation| < 0.2
              AND Delta(D)/noise in [0.5, 2] for all D;
  killed    = r2 mean grows beyond 2 with D,
              OR mean |row corr| > 0.5,
              OR Delta/noise > 5;
  ambiguous = otherwise.
"""

import numpy as np
import time

X = 30_000_000
N = 6 * X + 1
SEG = 10_000_000
DYADIC = [30, 100, 300, 1000]

t0 = time.time()


def lambda_sieve(N, SEG):
    """Liouville lambda(n) for 0..N (lam[0] = lam[1] = +1 convention;
    only n >= 5 used downstream), via segmented Omega-parity.
    Identical construction to tools/probe_ed_scan.py."""
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
print(f"anchor: sum F(m), m<=1e6  = {anchor6}   (wave-1 ledger: 236)")
print(f"full:   sum F(m), m<=X={X:.0e} = {full}   (wave-1 ledger: 3918)   "
      f"sqrt(X) = {X**0.5:.0f}")
assert anchor6 == 236, "construction drifted from probe_ed_scan"
assert full == 3918, "construction drifted from probe_ed_scan"

Fi64 = Fm.astype(np.int64)


def primes_in(lo, hi):
    sv = np.ones(hi, dtype=bool)
    sv[:2] = False
    for i in range(2, int(hi ** 0.5) + 1):
        if sv[i]:
            sv[i * i:: i] = False
    return [int(p) for p in np.nonzero(sv)[0] if lo <= p < hi]


def row_abs_corrs(M, n):
    """Pairwise Pearson correlations between rows i,k of symmetric matrix M
    (diagonal undefined), over the common columns j != i, j != k."""
    out = []
    for i in range(n):
        for k in range(i + 1, n):
            cols = np.array([j for j in range(n) if j != i and j != k])
            x = M[i, cols]
            y = M[k, cols]
            xc = x - x.mean()
            yc = y - y.mean()
            den = np.sqrt((xc * xc).sum() * (yc * yc).sum())
            out.append(float(xc.dot(yc) / den) if den > 0 else 0.0)
    return np.abs(np.array(out))


summary = {}
pooled_corr = []
pooled_corr_z = []

for D in DYADIC:
    ps = primes_in(D, 2 * D)
    n = len(ps)
    npairs = n * (n - 1) // 2
    print(f"\n===== D = {D}: {n} primes in [{D},{2*D}), {npairs} pairs =====")
    inv6 = {p: pow(6, -1, p) for p in ps}

    Emat = np.full((n, n), np.nan)
    Zmat = np.full((n, n), np.nan)
    E_list = []
    z_list = []
    noise_list = []
    for i in range(n):
        d1 = ps[i]
        for j in range(i + 1, n):
            d2 = ps[j]
            q = d1 * d2
            m1 = pow(d2, -1, d1)   # d2^{-1} mod d1
            m2 = pow(d1, -1, d2)   # d1^{-1} mod d2
            s = 0
            for e1 in (1, -1):
                r1 = (e1 * inv6[d1]) % d1
                for e2 in (1, -1):
                    r2 = (e2 * inv6[d2]) % d2
                    a = (r1 * d2 * m1 + r2 * d1 * m2) % q
                    # a in 1..q-1 (a=0 impossible: 36*0^2-1 = -1 mod d)
                    s += int(Fi64[a - 1:: q].sum())
            E = s - 4.0 * full / q
            sd = np.sqrt(4.0 * X / q)
            Emat[i, j] = Emat[j, i] = E
            Zmat[i, j] = Zmat[j, i] = E / sd
            E_list.append(E)
            z_list.append(E / sd)
            noise_list.append(4.0 * X / q)

    z = np.array(z_list)
    r2 = np.abs(z)
    E_arr = np.array(E_list)
    noise = np.array(noise_list)

    # (i) r2 distribution
    print(f"  (i)  r2 = |E|/sqrt(4X/(d1*d2)):  mean={r2.mean():.3f}  "
          f"median={np.median(r2):.3f}  q95={np.quantile(r2, 0.95):.3f}  "
          f"max={r2.max():.3f}   [Gaussian pred: mean 0.798]")
    print(f"       signed z: mean={z.mean():+.4f}  (bias check; "
          f"noise scale 1/sqrt(npairs) = {1/np.sqrt(npairs):.4f})")

    # (ii) shared-modulus row correlations
    ac = row_abs_corrs(Emat, n)
    ac_z = row_abs_corrs(Zmat, n)
    ncols = n - 2
    base = np.sqrt(2.0 / (np.pi * max(ncols - 1, 1)))
    print(f"  (ii) mean |row corr| (raw E rows): {ac.mean():.3f}  "
          f"(max {ac.max():.3f}, {len(ac)} row pairs, {ncols} common cols; "
          f"pure-noise baseline E|r| ~ {base:.3f})")
    print(f"       mean |row corr| (normalized z rows): {ac_z.mean():.3f}  "
          f"(max {ac_z.max():.3f})")
    pooled_corr.extend(ac.tolist())
    pooled_corr_z.extend(ac_z.tolist())

    # (iii) Delta vs noise
    Delta = float((E_arr ** 2).sum())
    noise_pred = float(noise.sum())
    ratio = Delta / noise_pred
    print(f"  (iii) Delta(D) = sum E^2 = {Delta:.1f}   "
          f"noise pred = {noise_pred:.1f}   ratio = {ratio:.3f}")

    summary[D] = dict(n=n, npairs=npairs, r2_mean=float(r2.mean()),
                      r2_med=float(np.median(r2)),
                      r2_q95=float(np.quantile(r2, 0.95)),
                      corr_mean=float(ac.mean()),
                      corr_mean_z=float(ac_z.mean()),
                      corr_baseline=float(base),
                      delta_ratio=ratio)
    print(f"  [{time.time()-t0:7.1f}s] D={D} done")

pooled = float(np.mean(pooled_corr))
pooled_z = float(np.mean(pooled_corr_z))

print("\n===== SUMMARY =====")
print(f"{'D':>6} {'npairs':>7} {'r2_mean':>8} {'r2_med':>8} {'r2_q95':>8} "
      f"{'|corr|':>7} {'|corr|z':>8} {'base':>6} {'Dlt/nse':>8}")
for D in DYADIC:
    s = summary[D]
    print(f"{D:>6} {s['npairs']:>7} {s['r2_mean']:>8.3f} {s['r2_med']:>8.3f} "
          f"{s['r2_q95']:>8.3f} {s['corr_mean']:>7.3f} "
          f"{s['corr_mean_z']:>8.3f} {s['corr_baseline']:>6.3f} "
          f"{s['delta_ratio']:>8.3f}")
print(f"pooled mean |row corr| over all D (raw E): {pooled:.3f}   "
      f"(normalized z: {pooled_z:.3f})")

# ----- pre-registered verdict, applied mechanically -----
r2_means = [summary[D]['r2_mean'] for D in DYADIC]
ratios = [summary[D]['delta_ratio'] for D in DYADIC]
corr_means = [summary[D]['corr_mean'] for D in DYADIC]

sig_r2 = all(0.5 <= m <= 1.2 for m in r2_means)
sig_corr = pooled < 0.2
sig_delta = all(0.5 <= r <= 2.0 for r in ratios)

kill_r2 = (max(r2_means) > 2.0 and r2_means[-1] == max(r2_means))
kill_corr = pooled > 0.5
kill_delta = max(ratios) > 5.0

print("\n===== PRE-REGISTERED VERDICT =====")
print(f"  signal conds: r2 mean in [0.5,1.2] all D: {sig_r2} "
      f"(means {['%.3f' % m for m in r2_means]})")
print(f"                mean |row corr| < 0.2:      {sig_corr} "
      f"(pooled {pooled:.3f}; per-D {['%.3f' % c for c in corr_means]})")
print(f"                Delta/noise in [0.5,2] all D: {sig_delta} "
      f"(ratios {['%.3f' % r for r in ratios]})")
print(f"  kill conds:   r2 mean grows beyond 2:     {kill_r2}")
print(f"                mean |row corr| > 0.5:      {kill_corr}")
print(f"                Delta/noise > 5:            {kill_delta}")

if kill_r2 or kill_corr or kill_delta:
    verdict = "KILLED"
elif sig_r2 and sig_corr and sig_delta:
    verdict = "SIGNAL"
else:
    verdict = "AMBIGUOUS"
print(f"\nVERDICT: {verdict}")
print(f"[{time.time()-t0:7.1f}s] done")
