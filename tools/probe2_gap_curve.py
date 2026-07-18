"""PROBE W2-3 (expander-gap-on-rough-graph, wave 2): gap(z) curve up to
z ~ X^{1/3} for the HR-style divisibility graph at M = 10^8 (window
6M ~ 6*10^8).  PURE NUMPY (no scipy) -- machinery reused VERBATIM from
tools/probe_expander_gap.py (components_bipartite, spectral_gap with
BOTH +-1 deflation).

Construction (minus wing): vertices = pairs (p, k), p prime in (z, 2z],
k prime in (z, (6M-1)/p], with p*k = 5 (mod 6); vertex m = (p*k+1)/6.
Moves: change p keeping k (k-block) or change k keeping p (p-block) --
realized as the bipartite vertex-block graph.  Mixing metric: spectral
gap 1 - sigma_2 of the normalized adjacency on the giant component.
RESTRICTED graph keeps vertices with 6m+1 = p*k+2 also z-rough.

Wave-2 scaling: we do NOT sieve minFac to 6e8.  IS_PRIME is a plain
boolean sieve to 6e8/100 = 6e6 (covers all k since kmax <= (6M-1)/101).
Pair-roughness minFac(p*k+2) > z is tested by TRIAL DIVISION with the
primes 5 <= q <= z (at most 146 primes for z <= 843; p*k+2 is coprime
to 6 automatically since p*k = 5 mod 6), vectorized on the p*k+2 array.

z grid: {100, 200, 300, 450, 600, 750, 843}, 843 ~ (6e8)^(1/3).

Pre-registered verdict rules (applied mechanically at the end):
  signal    = g(z) = gap_restricted/gap_full >= 0.5 on the WHOLE grid
              including z=843 AND restricted giant fraction equals the
              full giant fraction within 0.02 (structural 1/2
              strike-sector split expected in BOTH),
  killed    = g(z) below 0.2 approaching X^(1/3) or restricted giant
              collapses,
  ambiguous = otherwise.
"""

import numpy as np
import time

t0 = time.time()
M = 10 ** 8
LIMIT = 6 * M            # window 6M ~ 6*10^8
SIEVE_TO = LIMIT // 100  # 6*10^6: covers kmax = (6M-1)//(z+1) for z >= 100


def sieve_is_prime(N):
    isp = np.ones(N + 1, dtype=bool)
    isp[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if isp[p]:
            isp[p * p:: p] = False
    return isp


print(f"[{time.time()-t0:6.1f}s] plain IS_PRIME sieve to {SIEVE_TO} ...")
IS_PRIME = sieve_is_prime(SIEVE_TO)
PRIMES = np.nonzero(IS_PRIME)[0].astype(np.int64)
print(f"[{time.time()-t0:6.1f}s] sieve done ({PRIMES.size} primes)")


def components_bipartite(pidx, kidx, nb_p, nb_k):
    """Connected components of the vertex-block bipartite graph via
    iterative scatter-min label propagation.  Returns vertex labels."""
    n = pidx.size
    vlab = np.arange(n, dtype=np.int64)
    plab = np.full(nb_p, -1, dtype=np.int64)
    klab = np.full(nb_k, -1, dtype=np.int64)
    pl = np.full(nb_p, np.iinfo(np.int64).max, dtype=np.int64)
    kl = np.full(nb_k, np.iinfo(np.int64).max, dtype=np.int64)
    for it in range(300):
        pl.fill(np.iinfo(np.int64).max)
        kl.fill(np.iinfo(np.int64).max)
        np.minimum.at(pl, pidx, vlab)
        np.minimum.at(kl, kidx, vlab)
        new = np.minimum(vlab, np.minimum(pl[pidx], kl[kidx]))
        if np.array_equal(new, vlab):
            break
        vlab = new
    return vlab


def spectral_gap(pidx, kidx, nb_p, nb_k, iters=800):
    """1 - sigma_2 of the normalized adjacency of the bipartite
    vertex-block graph (vertices deg 2; blocks deg = multiplicity),
    matrix-free power iteration deflated against the top pair."""
    n = pidx.size
    dp = np.bincount(pidx, minlength=nb_p).astype(np.float64)
    dk = np.bincount(kidx, minlength=nb_k).astype(np.float64)
    dv = np.full(n, 2.0)
    sp_ = np.sqrt(np.maximum(dp, 1e-300))
    sk_ = np.sqrt(np.maximum(dk, 1e-300))
    sv_ = np.sqrt(dv)

    def apply_An(xv, xp, xk):
        # A: vertex i -- pblock pidx[i], kblock kidx[i]
        yv = xp[pidx] / (sv_ * sp_[pidx]) + xk[kidx] / (sv_ * sk_[kidx])
        yp = np.bincount(pidx, weights=xv / sv_, minlength=nb_p) / sp_
        yk = np.bincount(kidx, weights=xv / sv_, minlength=nb_k) / sk_
        return yv, yp, yk

    # top eigenvectors: bipartite spectrum is symmetric, deflate BOTH
    # +1 (sqrt deg) and -1 (sqrt deg with block side negated)
    tv, tp, tk = sv_.copy(), sp_.copy(), sk_.copy()
    tp[dp == 0] = 0.0
    tk[dk == 0] = 0.0
    tnorm = np.sqrt((tv ** 2).sum() + (tp ** 2).sum() + (tk ** 2).sum())
    tv, tp, tk = tv / tnorm, tp / tnorm, tk / tnorm
    uv, up, uk = tv.copy(), -tp, -tk
    rng = np.random.default_rng(1)
    xv = rng.standard_normal(n)
    xp = rng.standard_normal(nb_p)
    xk = rng.standard_normal(nb_k)
    xp[dp == 0] = 0.0
    xk[dk == 0] = 0.0
    sigma = 0.0
    for it in range(iters):
        # deflate both top vectors
        c = (xv * tv).sum() + (xp * tp).sum() + (xk * tk).sum()
        xv -= c * tv
        xp -= c * tp
        xk -= c * tk
        c2 = (xv * uv).sum() + (xp * up).sum() + (xk * uk).sum()
        xv -= c2 * uv
        xp -= c2 * up
        xk -= c2 * uk
        yv, yp, yk = apply_An(xv, xp, xk)
        # bipartite spectrum is symmetric +-sigma: use two steps (An^2)
        yv, yp, yk = apply_An(yv, yp, yk)
        nrm = np.sqrt((yv ** 2).sum() + (yp ** 2).sum() + (yk ** 2).sum())
        if nrm == 0:
            return 1.0
        yv, yp, yk = yv / nrm, yp / nrm, yk / nrm
        sigma_new = np.sqrt(nrm) if False else nrm  # An^2 eigval = sigma^2
        if it > 50 and abs(sigma_new - sigma) < 1e-9:
            sigma = sigma_new
            break
        sigma = sigma_new
        xv, xp, xk = yv, yp, yk
    sigma2 = np.sqrt(max(sigma, 0.0))  # eigenvalue of An
    return 1.0 - sigma2


def build_pairs(z):
    """(p, k) grid for level z, chunked over p to bound meshgrid size;
    returns Pv, Kv (valid pairs) and rough_other (trial-division test
    minFac(p*k+2) > z using primes 5 <= q <= z only)."""
    ps = PRIMES[(PRIMES > z) & (PRIMES <= 2 * z)]
    kmax = (6 * M - 1) // (z + 1)
    ks = PRIMES[(PRIMES > z) & (PRIMES <= kmax)]
    tdiv = PRIMES[(PRIMES >= 5) & (PRIMES <= z)]
    max_cells = 10 ** 8
    pchunk = max(1, max_cells // max(ks.size, 1))
    Pv_l, Kv_l, rough_l = [], [], []
    for i0 in range(0, ps.size, pchunk):
        pc = ps[i0:i0 + pchunk]
        P, K = np.meshgrid(pc, ks, indexing="ij")
        prod = (P * K).ravel()
        Pf = P.ravel()
        Kf = K.ravel()
        valid = (prod % 6 == 5) & (prod <= 6 * M - 1)
        Pv_c, Kv_c = Pf[valid], Kf[valid]
        other = Pv_c * Kv_c + 2  # = 1 mod 6, coprime to 6 automatically
        rough = np.ones(other.size, dtype=bool)
        for q in tdiv:
            rough &= (other % q) != 0
        Pv_l.append(Pv_c)
        Kv_l.append(Kv_c)
        rough_l.append(rough)
    Pv = np.concatenate(Pv_l)
    Kv = np.concatenate(Kv_l)
    rough_other = np.concatenate(rough_l)
    return ps, ks, Pv, Kv, rough_other, tdiv.size


def analyze(z):
    ps, ks, Pv, Kv, rough_other, ntd = build_pairs(z)
    print(f"[{time.time()-t0:6.1f}s] z={z}: |p-list|={ps.size}, "
          f"|k-list|={ks.size}, pairs={Pv.size}, "
          f"trial-division primes={ntd}")
    out = {}
    for tag, mask in [("full", np.ones(Pv.size, dtype=bool)),
                      ("restricted", rough_other)]:
        Pm, Km = Pv[mask], Kv[mask]
        n = Pm.size
        if n < 100:
            out[tag] = (n, 0.0, float("nan"))
            continue
        pidx = np.searchsorted(ps, Pm)
        kidx = np.searchsorted(ks, Km)
        vlab = components_bipartite(pidx, kidx, ps.size, ks.size)
        uniq, counts = np.unique(vlab, return_counts=True)
        giant_lab = uniq[counts.argmax()]
        giant = counts.max() / n
        keep = vlab == giant_lab
        gap = spectral_gap(pidx[keep], kidx[keep], ps.size, ks.size)
        out[tag] = (n, giant, gap)
    return out


print("\n z | graph      | vertices | giant frac | gap 1-sigma2")
summary = {}
ZGRID = [100, 200, 300, 450, 600, 750, 843]
for z in ZGRID:
    res = analyze(z)
    for tag in ["full", "restricted"]:
        n, giant, gap = res[tag]
        print(f" {z:5d} | {tag:10s} | {n:8d} | {giant:10.4f} | {gap:.6f}"
              f"   [{time.time()-t0:6.1f}s]")
    fn, fg, fgap = res["full"]
    rn, rg, rgap = res["restricted"]
    ratio = rgap / fgap if fgap and fgap > 0 else float("nan")
    summary[z] = (rn / fn if fn else 0, fg, rg, ratio)
    print(f"        -> kept fraction {summary[z][0]:.3f}, "
          f"giant full/restricted = {fg:.4f}/{rg:.4f}, "
          f"gap ratio g(z) = {ratio:.3f}")

print("\n=== SUMMARY (M = 10^8, window 6M ~ 6e8, X^(1/3) ~ 843) ===")
for z, (kf, fg, rg, ratio) in summary.items():
    print(f"  z={z:5d}: kept={kf:.3f}  giant full={fg:.4f}  "
          f"giant restricted={rg:.4f}  gap-ratio g(z)={ratio:.3f}")

# --- mechanical application of the pre-registered verdict rules ---
ratios = [summary[z][3] for z in ZGRID]
giant_dev = max(abs(summary[z][2] - summary[z][1]) for z in ZGRID)
min_ratio = min(ratios)
r843 = summary[843][3]
giant_collapse = any(summary[z][2] < 0.30 for z in ZGRID)
if min_ratio >= 0.5 and giant_dev <= 0.02:
    verdict = "SIGNAL"
elif r843 < 0.2 or giant_collapse:
    verdict = "KILLED"
else:
    verdict = "AMBIGUOUS"
print(f"\nmin g(z) over grid = {min_ratio:.3f}; g(843) = {r843:.3f}; "
      f"max |giant_restr - giant_full| = {giant_dev:.4f}; "
      f"restricted giant collapse (<0.30): {giant_collapse}")
print(f"PRE-REGISTERED VERDICT: {verdict}")
print(f"[{time.time()-t0:6.1f}s] done")
