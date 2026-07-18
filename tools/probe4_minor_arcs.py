"""PROBE W4-4 (A3 rough-lfu, wave-4 queue item (iv)): large q and minor arcs,
with the S-P (Arm B) model subtracted -- the untouched LFU territory.

CONTEXT.  Waves 1-3 established: on Omega<=2 windows (z^3 > x+H) every
rational-point structure of F(alpha) = sum_{n in R} lambda(n) e(n alpha),
R = {n in (x, x+H] : minFac(n) > z}, at exact rationals a/q is EXACTLY the
per-class S-P counting (Arm A identity, residual 0 by algebra), and the
class-blind global model (Arm B of tools/probe3_sp_residual.py)
    M_B(alpha) = (1 - 2*pbar) * sum_{n in R} e(n alpha),  pbar = P/|R|,
leaves a residual
    F - M_B = -2 * sum_{n in R} (1_prime(n) - pbar) e(n alpha)
that sat on/below the noise floor for q <= 48.  Wave 3 never looked at
LARGE q (48 < q <= 316) or at MINOR arcs (alphas far from all rationals
with small q).  This probe covers exactly that territory.

DESIGN (fixed before the run):
  x ~ U[5*10^7, 10^8], H = 10^5, NWIN = 50, z in {1000, 3000}
  (both above the Omega<=2 dichotomy: 1000^3 = 10^9 > x+H, so
  lambda = 1 - 2*1_prime on R exactly and M_B is well-defined).
  Frequency sets, freshly sampled per window (shared between the two z):
    (a) rationals a/q, gcd(a,q) = 1, q in dyadic bands
        B1 = [50,100), B2 = [100,180), B3 = [180,316]; 300 fractions
        per band per window (q uniform in band, a uniform coprime);
    (b) 200 MINOR alphas per window: alpha ~ U(0,1) rejection-sampled to
        satisfy  min_a |alpha - a/q| > 1/(320*q^2)  for ALL q <= 316
        (equivalently ||alpha*q|| > 1/(320*q) for all q <= 316);
    (c) 40 generic random alphas per window as the noise reference
        (unconditioned, as in waves 1-3).
  Rational phases are computed EXACTLY via residues mod q and roots of
  unity (no float phase error); minor/generic phases in float64
  (phase error <= (x+H)*2^-53 ~ 1e-8, negligible).

STATISTIC.  At every frequency: resid = |F - M_B| / sqrt|R|.  Per band
(B1, B2, B3, MINOR) and per z:
    q95_resid(band)  and the VARIANCE-ADJUSTED ratio
    ratio(band) = q95_resid(band) / q95_resid(generic),
where the generic reference is the SAME subtracted statistic at the 40
unconditioned random alphas (so numerator and denominator share the
variance 4*pbar*(1-pbar)*|R| of the subtracted weight, unlike the raw
wave-2 rho which compares against |F| ~ sqrt|R|).  Raw wave-2-style
rho = q95|F|(band)/q95|F|(generic) is also reported for context only.

PRE-REGISTERED VERDICTS (mechanical, operationalized BEFORE the run):
  signal    = variance-adjusted ratio <= 1.5 in ALL four bands
              (B1, B2, B3, MINOR) at BOTH z;
  killed    = some (band, z) has aggregate ratio >= 3 PERSISTENTLY across
              windows, operationalized as: aggregate ratio >= 3 AND the
              per-window ratio (window q95 band resid / window q95 generic
              resid) >= 3 in >= 50% of used windows.  This would be hidden
              structure at large q / on minor arcs -- report loudly,
              genuinely new;
  ambiguous = otherwise.
NEVER claims the parity wall moved: a signal only says the un-averaging
gap's Fourier side stays noise-pure on the last unexplored frequency
ranges; the wall (Chowla2LogHypothesis -> Chowla2Hypothesis) is untouched.
"""

import numpy as np
import time
from math import gcd

rng = np.random.default_rng(2026071804)
t0 = time.time()

H = 100_000
NWIN = 50
XLO, XHI = 5 * 10 ** 7, 10 ** 8
ZLIST = [1000, 3000]
BANDS = [("B1[50,100)", 50, 99), ("B2[100,180)", 100, 179),
         ("B3[180,316]", 180, 316)]
NFRAC = 300      # fractions per band per window
NMINOR = 200     # minor-arc alphas per window
NRAND = 40       # generic noise-reference alphas per window
QMAX_MINOR = 316
MINOR_C = 320.0  # ||alpha*q|| > 1/(MINOR_C*q) for all q <= QMAX_MINOR
RATIO_SIG = 1.5
RATIO_KILL = 3.0

# Omega<=2 dichotomy guard
assert min(ZLIST) ** 3 > XHI + H

# primes up to sqrt(max n) with margin (same arithmetic as waves 1-3)
ROOT = int((XHI + 2 * H) ** 0.5) + 1
sv = np.ones(ROOT + 1, dtype=bool)
sv[:2] = False
for i in range(2, int(ROOT ** 0.5) + 1):
    if sv[i]:
        sv[i * i:: i] = False
PRIMES = np.nonzero(sv)[0].astype(np.int64)

ROOTS = {}  # q -> exp(2 pi i c / q), c = 0..q-1  (filled lazily)


def window_arrays(x, H):
    """lambda, minFac, Omega for n in (x, x+H] (identical to waves 2-3)."""
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
    omega[left] += 1
    minf[minf == 0] = 2 ** 31 - 1
    lam = (1 - 2 * (omega & 1)).astype(np.int8)
    return lam, minf.astype(np.int32), omega


def sample_fractions(qlo, qhi, nfrac):
    """nfrac pairs (a, q), q uniform in [qlo, qhi], a uniform coprime."""
    out = []
    while len(out) < nfrac:
        q = int(rng.integers(qlo, qhi + 1))
        a = int(rng.integers(1, q))
        if gcd(a, q) == 1:
            out.append((a, q))
    return out


QARR = np.arange(1, QMAX_MINOR + 1, dtype=np.float64)
MINOR_THRESH = 1.0 / (MINOR_C * QARR)


def sample_minor(nminor):
    """alphas with ||alpha*q|| > 1/(320*q) for all q <= 316."""
    out = []
    while len(out) < nminor:
        cand = rng.random(2 * nminor)
        t = cand[:, None] * QARR[None, :]
        dist = np.abs(t - np.round(t))
        ok = (dist > MINOR_THRESH[None, :]).all(axis=1)
        out.extend(cand[ok].tolist())
    return np.array(out[:nminor])


print("PROBE W4-4: large-q and minor-arc LFU with Arm-B model subtracted")
print(f"  H={H}, NWIN={NWIN}, x in [{XLO:.0e},{XHI:.0e}], z in {ZLIST}"
      f"  (Omega<=2 guard: {min(ZLIST)}^3 = {min(ZLIST)**3:.1e} >"
      f" {XHI + H:.4e})")
print(f"  bands: {[b[0] for b in BANDS]} with {NFRAC} fractions each;"
      f" {NMINOR} minor alphas (||aq|| > 1/({MINOR_C:.0f}q), q <="
      f" {QMAX_MINOR}); {NRAND} generic alphas (reference)")
print(f"  verdict rules: signal = all variance-adjusted ratios <="
      f" {RATIO_SIG}; kill = some band ratio >= {RATIO_KILL} aggregate AND"
      f" in >= 50% of windows")

# ---- sieve windows ----
windows = []
for wi in range(NWIN):
    x = int(rng.integers(XLO, XHI))
    lam, minf, omega = window_arrays(x, H)
    fracs = [sample_fractions(qlo, qhi, NFRAC) for (_, qlo, qhi) in BANDS]
    minor = sample_minor(NMINOR)
    gener = rng.random(NRAND)
    windows.append((x, lam, minf, omega, fracs, minor, gener))
    if (wi + 1) % 10 == 0:
        print(f"[{time.time()-t0:7.1f}s] {wi + 1}/{NWIN} windows sieved")

BANDNAMES = [b[0] for b in BANDS] + ["MINOR"]
results = {}   # z -> dict with aggregates
for z in ZLIST:
    agg_resid = {b: [] for b in BANDNAMES}
    agg_raw = {b: [] for b in BANDNAMES}
    agg_resid_gen, agg_raw_gen = [], []
    perwin_ratio = {b: [] for b in BANDNAMES}
    sizes, pfracs = [], []
    used = 0
    for (x, lam, minf, omega, fracs, minor, gener) in windows:
        R = np.nonzero(minf > z)[0]
        if R.size < 500:
            continue
        used += 1
        n_int = (x + 1 + R).astype(np.int64)
        lamR = lam[R].astype(np.float64)
        omR = omega[R]
        assert omR.max() <= 2, "Omega<=2 dichotomy violated"
        isP = omR == 1
        sz = R.size
        sqrtR = np.sqrt(sz)
        pbar = float(isP.sum()) / sz
        sizes.append(sz)
        pfracs.append(pbar)
        # subtracted weight: lam - (1-2pbar) = -2(1_prime - pbar), mean 0
        w = lamR - (1.0 - 2.0 * pbar)
        n_f = n_int.astype(np.float64)

        # generic + minor alphas: direct float64 phases, chunked
        def eval_alphas(alphas):
            res_r, res_f = [], []
            for lo in range(0, len(alphas), 64):
                al = np.asarray(alphas[lo:lo + 64])
                ph = np.exp(2j * np.pi * ((al[:, None] * n_f[None, :]) % 1.0))
                res_r.append(np.abs(ph @ w) / sqrtR)
                res_f.append(np.abs(ph @ lamR) / sqrtR)
            return np.concatenate(res_r), np.concatenate(res_f)

        gen_res, gen_raw = eval_alphas(gener)
        min_res, min_raw = eval_alphas(minor)
        agg_resid_gen.append(gen_res)
        agg_raw_gen.append(gen_raw)
        agg_resid["MINOR"].append(min_res)
        agg_raw["MINOR"].append(min_raw)
        g95 = np.quantile(gen_res, 0.95)
        perwin_ratio["MINOR"].append(np.quantile(min_res, 0.95) / g95)

        # rational bands: exact residue phases, grouped by q
        for (bname, _, _), frs in zip(BANDS, fracs):
            byq = {}
            for (a, q) in frs:
                byq.setdefault(q, []).append(a)
            res_r, res_f = [], []
            for q, alist in byq.items():
                if q not in ROOTS:
                    ROOTS[q] = np.exp(2j * np.pi * np.arange(q) / q)
                roots = ROOTS[q]
                r = (n_int % q).astype(np.int64)
                Wc = np.bincount(r, weights=w, minlength=q)
                Sc = np.bincount(r, weights=lamR, minlength=q)
                cc = np.arange(q)
                for a in alist:
                    rot = roots[(a * cc) % q]
                    res_r.append(abs((Wc * rot).sum()) / sqrtR)
                    res_f.append(abs((Sc * rot).sum()) / sqrtR)
            res_r = np.array(res_r)
            res_f = np.array(res_f)
            agg_resid[bname].append(res_r)
            agg_raw[bname].append(res_f)
            perwin_ratio[bname].append(np.quantile(res_r, 0.95) / g95)

    gen_res_all = np.concatenate(agg_resid_gen)
    gen_raw_all = np.concatenate(agg_raw_gen)
    q95_gen = np.quantile(gen_res_all, 0.95)
    q95_gen_raw = np.quantile(gen_raw_all, 0.95)
    print(f"\n=== z={z}  (windows {used}, mean |R| = {np.mean(sizes):.0f}, "
          f"mean prime fraction = {np.mean(pfracs):.3f}) ===")
    print(f"  generic reference: q95 resid = {q95_gen:.3f}   "
          f"q95 raw |F| = {q95_gen_raw:.3f}   "
          f"(sqrt(4*pbar*(1-pbar)) = "
          f"{np.sqrt(4*np.mean(pfracs)*(1-np.mean(pfracs))):.3f})")
    zrow = {}
    for b in BANDNAMES:
        res_all = np.concatenate(agg_resid[b])
        raw_all = np.concatenate(agg_raw[b])
        q95b = np.quantile(res_all, 0.95)
        ratio = q95b / q95_gen
        raw_rho = np.quantile(raw_all, 0.95) / q95_gen_raw
        pw = np.array(perwin_ratio[b])
        frac_ge3 = float((pw >= RATIO_KILL).mean())
        med_pw = float(np.median(pw))
        zrow[b] = (q95b, ratio, raw_rho, frac_ge3, med_pw)
        print(f"  {b:13s} q95 resid = {q95b:.3f}  VAR-ADJ RATIO = "
              f"{ratio:.3f}  (raw rho = {raw_rho:.3f}; per-window ratio: "
              f"median {med_pw:.3f}, frac >= {RATIO_KILL:.0f}: "
              f"{frac_ge3:.2f})")
    results[z] = zrow
    print(f"  [{time.time()-t0:7.1f}s]")

print("\n=== SUMMARY TABLE (variance-adjusted q95 ratios band/generic) ===")
head = "   z  " + "".join(f"  {b:>13s}" for b in BANDNAMES)
print(head)
for z in ZLIST:
    line = f"{z:5d} "
    for b in BANDNAMES:
        line += f"  {results[z][b][1]:13.3f}"
    print(line)

# ---- mechanical verdict per pre-registered rules ----
all_ok = all(results[z][b][1] <= RATIO_SIG
             for z in ZLIST for b in BANDNAMES)
kills = [(z, b) for z in ZLIST for b in BANDNAMES
         if results[z][b][1] >= RATIO_KILL and results[z][b][3] >= 0.5]
print("\n=== PRE-REGISTERED VERDICT (mechanical) ===")
print(f"  all ratios <= {RATIO_SIG} (both z, all bands incl MINOR): "
      f"{all_ok}")
print(f"  kill list (aggregate >= {RATIO_KILL} AND >= 50% windows): "
      f"{kills if kills else 'empty'}")
if kills:
    verdict = "KILLED"
elif all_ok:
    verdict = "SIGNAL"
else:
    verdict = "AMBIGUOUS"
print(f"  VERDICT: {verdict}")
print("  Scope note: this verdict concerns ONLY the Fourier purity of the"
      " Arm-B residual at large-q rationals and on minor arcs. It does NOT"
      " move the parity wall (Chowla2LogHypothesis -> Chowla2Hypothesis).")
print(f"[{time.time()-t0:7.1f}s] done")
