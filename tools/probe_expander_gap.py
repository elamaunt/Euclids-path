"""PROBE A5 (expander-gap-on-rough-graph): spectral gap of the HR-style
divisibility graph restricted to pair-rough vertices.  PURE NUMPY
(no scipy: matrix-free power iteration + scatter-min components).

Construction (minus wing): vertices = pairs (p, k), p prime in (z, 2z],
k prime in (z, (6M-1)/p], with p*k = 5 (mod 6); vertex m = (p*k+1)/6.
Moves: change p keeping k (k-block) or change k keeping p (p-block) --
realized as the bipartite vertex-block graph.  Mixing metric: spectral
gap 1 - sigma_2 of the normalized adjacency on the giant component.
RESTRICTED graph keeps vertices with 6m+1 = p*k+2 also z-rough.

Pre-registered verdict rules:
  signal    = restricted keeps giant component (>80%) AND
              g(z) = gap_restricted/gap_full >= 0.5 across z,
  killed    = restricted shatters (giant < 30%) or g(z) -> 0,
  ambiguous = otherwise.
"""

import numpy as np
import time

t0 = time.time()
M = 10 ** 7
N = 6 * M + 2


def sieve_minfac(N):
    minf = np.zeros(N + 1, dtype=np.int32)
    root = int(N ** 0.5) + 1
    for p in range(2, root + 1):
        if minf[p] == 0:
            sl = minf[p * p:: p]
            sl[sl == 0] = p
            minf[p] = p
    rest = np.nonzero(minf == 0)[0]
    minf[rest] = rest
    minf[0] = minf[1] = 1
    return minf


print(f"[{time.time()-t0:6.1f}s] minFac sieve to N={N} ...")
MF = sieve_minfac(N)
print(f"[{time.time()-t0:6.1f}s] sieve done")
IS_PRIME = MF == np.arange(N + 1)
IS_PRIME[:2] = False


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


def analyze(z):
    plist = [p for p in range(z + 1, 2 * z + 1) if IS_PRIME[p]]
    kmax = (6 * M - 1) // (z + 1)
    klist = [k for k in range(z + 1, kmax + 1) if IS_PRIME[k]]
    ps = np.array(plist, dtype=np.int64)
    ks = np.array(klist, dtype=np.int64)
    P, K = np.meshgrid(ps, ks, indexing="ij")
    prod = (P * K).ravel()
    Pf = P.ravel()
    Kf = K.ravel()
    valid = (prod % 6 == 5) & (prod <= 6 * M - 1)
    Pv, Kv = Pf[valid], Kf[valid]
    other = Pv * Kv + 2
    rough_other = MF[other] > z
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
for z in [300, 1000, 3000]:
    res = analyze(z)
    for tag in ["full", "restricted"]:
        n, giant, gap = res[tag]
        print(f" {z:5d} | {tag:10s} | {n:8d} | {giant:10.4f} | {gap:.6f}"
              f"   [{time.time()-t0:6.1f}s]")
    fn, fg, fgap = res["full"]
    rn, rg, rgap = res["restricted"]
    ratio = rgap / fgap if fgap and fgap > 0 else float("nan")
    summary[z] = (rn / fn if fn else 0, rg, ratio)
    print(f"        -> kept fraction {summary[z][0]:.3f}, "
          f"gap ratio g(z) = {ratio:.3f}")

print("\n=== SUMMARY ===")
for z, (kf, rg, ratio) in summary.items():
    print(f"  z={z:5d}: kept={kf:.3f}  restricted-giant={rg:.3f}  "
          f"gap-ratio={ratio:.3f}")
print(f"[{time.time()-t0:6.1f}s] done")
