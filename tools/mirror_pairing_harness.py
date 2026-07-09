# mirror_pairing_harness.py -- Line A recon: can a phase-mirror involution
# kill the killed sector?
#
# Setting: wings L = 6m-1, R = 6m+1.  A prime q in [5, A] strikes L at
# m == a_L := inv6 (mod q) and strikes R at m == a_R := q - a_L (mod q).
# Killed(A, m) = some q in [5, A] strikes a wing; the least such q is the
# label q(m), with a phase side s(m) in {L, R}.  wingSign(m) =
# (-1)^(Omega(L)+Omega(R)) = lambda(L) lambda(R).
#
# The assault needs an involution `pair` on killed centers that
#   (a) maps killed -> killed,   (b) preserves the least-killer label,
#   (c) is fixed-point-free,     (d) FLIPS wingSign (sign m + sign pair m = 0).
# Three concrete phase-mirror candidates are tested; all swap the two struck
# residues a_L <-> a_R of the least killer q = q(m):
#   V1 block-mirror: m' = (2b+1)q - m, b = m // q   (reflection in the midpoint
#      of the q-block [bq, bq+q-1] containing m; stays inside the block);
#   V2 phase-shift:  m' = m + d on the L-phase, m' = m - d on the R-phase,
#      d = (a_R - a_L) mod q;
#   V3 near-shift:   m' = m + d - q on the L-phase, m' = m - d + q on the
#      R-phase (the opposite representative of the same shift class).
# All three send phase a_L <-> a_R (mod q), hence pair(m) is ALWAYS struck by
# the same q -- metric (i) is 100% by construction (up to range clipping); the
# content sits in label preservation (ii), sign flip (iii), involutivity (iv).
#
# Graded signs g = (-1)^f are scored for flip rate; the A-rough variant
# f = Omega(A-rough part of L*R) (divide out all primes <= A first) is the
# theoretically motivated one: the killer q <= A contributes deterministically
# to Omega and the mirror changes which side carries q.
# Any variant with flip rate EXACTLY 100% (or 0%) over the full range is gold;
# exactness is tested and counterexamples are listed otherwise.
# Nulls: iid random +-1 signs; Selberg foils 1 +/- lambda_L lambda_R as
# source-center weights.
#
# Output: fixed-width console tables. Feeds tools/LAWS_ordered_exponent.md.

import numpy as np
import math
import time

M = 10**6                 # exhaustive range of centers m
SCALES_A = [13, 31, 101]  # killed-sector scales
RNG = np.random.default_rng(20260710)


# ---------- sieves ----------

def prime_sieve(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def build_grades(n):
    """Omega (with multiplicity) and omega (distinct) arrays over 0..n."""
    t0 = time.time()
    isp = prime_sieve(n)
    big = np.zeros(n + 1, dtype=np.int8)
    lit = np.zeros(n + 1, dtype=np.int8)
    for p in np.flatnonzero(isp):
        p = int(p)
        lit[p::p] += 1
        pk = p
        while pk <= n:
            big[pk::pk] += 1
            pk *= p
    print(f"[grades] Omega/omega arrays to {n} built in {time.time()-t0:.1f}s")
    return big, lit


def small_omega_snapshots(n, scales):
    """cnt_A[x] = multiplicity of primes in [5, A] dividing x; one snapshot
    per A in scales (scales assumed prime, ascending)."""
    cnt = np.zeros(n + 1, dtype=np.int8)
    primes = [int(q) for q in np.flatnonzero(prime_sieve(max(scales))) if q >= 5]
    remaining = sorted(scales)
    out = {}
    for q in primes:
        while remaining and q > remaining[0]:
            out[remaining.pop(0)] = cnt.copy()
        pk = q
        while pk <= n:
            cnt[pk::pk] += 1
            pk *= q
    while remaining:
        out[remaining.pop(0)] = cnt.copy()
    return out


def least_killer(Mmax, A):
    """lk[m] = least prime q in [5, A] striking a wing of m (0 if clean);
    sideL[m] = True iff that least killer strikes the LEFT wing."""
    lk = np.zeros(Mmax + 1, dtype=np.int32)
    sideL = np.zeros(Mmax + 1, dtype=bool)
    for q in [int(q) for q in np.flatnonzero(prime_sieve(A)) if q >= 5]:
        aL = pow(6, -1, q)
        aR = (q - aL) % q
        for a, isL in ((aL, True), (aR, False)):
            idx = np.arange(a, Mmax + 1, q)
            fresh = idx[lk[idx] == 0]
            lk[fresh] = q
            if isL:
                sideL[fresh] = True
    lk[0] = 0
    return lk, sideL


# ---------- pairing variants ----------

VARIANTS = ["V1-block-mirror", "V2-phase-shift", "V3-near-shift"]


def build_pairs(lk, sideL, Mmax, A):
    """For each variant: full pair array P (size Mmax+1, int64, -1 where
    undefined or out of range), plus the killed index list."""
    killed = np.flatnonzero(lk)
    q = lk[killed].astype(np.int64)
    mm = killed.astype(np.int64)
    inv6_of = np.zeros(A + 1, dtype=np.int64)
    for p in [int(p) for p in np.flatnonzero(prime_sieve(A)) if p >= 5]:
        inv6_of[p] = pow(6, -1, p)
    aL = inv6_of[q]
    d = (q - 2 * aL) % q            # (a_R - a_L) mod q, a_R = q - a_L
    r = mm % q
    b = mm // q
    onL = sideL[killed]
    # sanity: the recorded phase matches the residue
    assert np.all(np.where(onL, r == aL, r == q - aL)), "phase bookkeeping broken"
    cand = {
        "V1-block-mirror": (2 * b + 1) * q - mm,
        "V2-phase-shift":  np.where(onL, mm + d, mm - d),
        "V3-near-shift":   np.where(onL, mm + d - q, mm - d + q),
    }
    pairs = {}
    for name, p in cand.items():
        P = np.full(Mmax + 1, -1, dtype=np.int64)
        ok = (p >= 1) & (p <= Mmax)
        P[mm[ok]] = p[ok]
        pairs[name] = P
    return pairs, killed


# ---------- metrics ----------

def rate_se(k, n):
    p = k / max(n, 1)
    return p, math.sqrt(max(p * (1 - p), 1e-30) / max(n, 1))


def flip_rate(signs, mm, pp, weights=None):
    """Weighted fraction of pairs with signs[pp] == -signs[mm]."""
    flip = signs[pp] == -signs[mm]
    if weights is None:
        return flip.mean(), flip
    w = weights[mm].astype(np.float64)
    tot = w.sum()
    return (w * flip).sum() / max(tot, 1e-30), flip


def failure_structure(OL, OR, mm, pp, flip, title):
    """Among pairs failing the sign flip: joint clipped total grades of m vs
    pair(m)  (T = Omega_L + Omega_R - 2, clipped to 0..6)."""
    fail = ~flip
    if fail.sum() == 0:
        print(f"  {title}: no failures")
        return
    Tm = np.clip(OL[mm[fail]] + OR[mm[fail]] - 2, 0, 6)
    Tp = np.clip(OL[pp[fail]] + OR[pp[fail]] - 2, 0, 6)
    tab = np.zeros((7, 7))
    np.add.at(tab, (Tm, Tp), 1)
    tot = tab.sum()
    print(f"  {title}: joint clipped total grade T(m) rows vs T(pair m) cols "
          f"among {int(tot)} sign-flip FAILURES, %:")
    print("        " + "".join(f"{j:>7}" for j in range(6)) + f"{'>=6':>7}")
    for i in range(7):
        lab = f"{i}" if i < 6 else ">=6"
        print(f"   {lab:>4} " + "".join(f"{100*tab[i, j]/tot:7.3f}" for j in range(7)))
    okm = mm[flip]
    print(f"  mean T among successes: m {np.mean(OL[okm]+OR[okm]-2):.3f} / "
          f"pair {np.mean(OL[pp[flip]]+OR[pp[flip]]-2):.3f};  among failures: "
          f"m {np.mean(OL[mm[fail]]+OR[mm[fail]]-2):.3f} / "
          f"pair {np.mean(OL[pp[fail]]+OR[pp[fail]]-2):.3f}")


def exactness_check(name, flip, mm, n_show=3):
    n = flip.size
    k = int(flip.sum())
    if k == n:
        print(f"  *** GOLD: {name} flips EXACTLY 100% ({k}/{n}) ***")
    elif k == 0:
        print(f"  *** GOLD (anti): {name} preserves sign EXACTLY 100% "
              f"(0/{n} flips -- exact NON-flip) ***")
    else:
        ce = mm[~flip][:n_show]
        return k, n, [int(x) for x in ce]
    return k, n, []


# ---------- main ----------

def main():
    print("=" * 78)
    print("MIRROR PAIRING HARNESS -- Line A recon (phase-mirror involution)")
    print(f"M = {M:.0e}, scales A = {SCALES_A}")
    print("=" * 78)

    n = 6 * M + 1
    big, lit = build_grades(n)
    m_all = np.arange(0, M + 1, dtype=np.int64)
    L = 6 * m_all - 1
    L[0] = 1  # dummy for m=0 (never used)
    R = 6 * m_all + 1
    OL = big[L].astype(np.int32)
    OR = big[R].astype(np.int32)
    wLd = lit[L].astype(np.int32)
    wRd = lit[R].astype(np.int32)
    sm_omega = small_omega_snapshots(n, SCALES_A)

    wing_sign = 1 - 2 * ((OL + OR) & 1)     # (-1)^(Omega_L + Omega_R)
    rand_sign = RNG.choice(np.array([-1, 1], dtype=np.int32), size=M + 1)

    for A in SCALES_A:
        print("\n" + "=" * 78)
        print(f"A = {A}")
        print("=" * 78)
        lk, sideL = least_killer(M, A)
        clean = int((lk[1:] == 0).sum())
        qs = [int(q) for q in np.flatnonzero(prime_sieve(A)) if q >= 5]
        crt = 1.0
        for q in qs:
            crt *= (q - 2) / q
        print(f"clean {clean} ({clean/M:.6f}, CRT product {crt:.6f})  "
              f"killed {M - clean}")

        pairs, killed = build_pairs(lk, sideL, M, A)

        # graded sign variants (A-dependent rough parts)
        sA_L = sm_omega[A][L].astype(np.int32)
        sA_R = sm_omega[A][R].astype(np.int32)
        rough_L = OL - sA_L                  # Omega of A-rough part of L
        rough_R = OR - sA_R
        sign_variants = {
            "wingSign":  wing_sign,
            "leftSign":  1 - 2 * (OL & 1),
            "rightSign": 1 - 2 * (OR & 1),
            "roughLR":   1 - 2 * ((rough_L + rough_R) & 1),
            "roughL":    1 - 2 * (rough_L & 1),
            "roughR":    1 - 2 * (rough_R & 1),
            "omegaLR":   1 - 2 * ((wLd + wRd) & 1),
        }

        stats = {}
        print(f"\n{'variant':<17}{'n_valid':>9}{'oor':>6}{'(i)killed':>11}"
              f"{'(ii)label':>11}{'(iii)flip':>10}{'+-se':>8}{'z':>7}"
              f"{'(iv)invol':>11}{'fixpts':>7}")
        for name in VARIANTS:
            P = pairs[name]
            valid = P[killed] >= 1
            mm = killed[valid]
            pp = P[mm]
            nv = mm.size
            oor = killed.size - nv
            r_killed = float((lk[pp] > 0).mean())
            r_label = float((lk[pp] == lk[mm]).mean())
            fr, flip = flip_rate(wing_sign, mm, pp)
            se = math.sqrt(fr * (1 - fr) / nv)
            z = (fr - 0.5) / se
            back = P[pp]
            r_inv = float((back == mm).mean())
            fixpts = int((pp == mm).sum())
            stats[name] = dict(mm=mm, pp=pp, flip=flip, fr=fr, se=se,
                               nv=nv, label=r_label, inv=r_inv)
            print(f"{name:<17}{nv:>9}{oor:>6}{r_killed:>11.6f}"
                  f"{r_label:>11.6f}{fr:>10.5f}{se:>8.5f}{z:>+7.1f}"
                  f"{r_inv:>11.6f}{fixpts:>7}")

        # graded-sign flip table with independence nulls.
        # null = p_src*(1-p_tgt) + (1-p_src)*p_tgt from the +1-marginals of
        # the sign at sources / at pair targets: a pure marginal-bias artifact
        # gives obs == null; only excess = obs - null is pairing structure.
        print("\ngraded-sign flip rates vs independence null "
              "(excess = obs - null; z approx):")
        print(f"  {'sign':<10}{'pairing':<17}{'p_src':>8}{'p_tgt':>8}"
              f"{'null':>9}{'obs':>9}{'excess':>9}{'z':>8}")
        for sname, sarr in sign_variants.items():
            for vname in VARIANTS:
                st = stats[vname]
                fr, flip = flip_rate(sarr, st["mm"], st["pp"])
                p_src = float((sarr[st["mm"]] == 1).mean())
                p_tgt = float((sarr[st["pp"]] == 1).mean())
                null = p_src * (1 - p_tgt) + (1 - p_src) * p_tgt
                se = math.sqrt(max(fr * (1 - fr), 1e-30) / st["nv"])
                z = (fr - null) / se
                print(f"  {sname:<10}{vname:<17}{p_src:>8.4f}{p_tgt:>8.4f}"
                      f"{null:>9.5f}{fr:>9.5f}{fr-null:>+9.5f}{z:>+8.1f}")

        # exactness audit for every (sign, variant) cell
        print("\nexactness audit (flip == 100% or 0% exactly?):")
        any_gold = False
        worst_dev = (-1.0, "", "", 0, 1, [])
        for sname, sarr in sign_variants.items():
            for vname in VARIANTS:
                st = stats[vname]
                _, flip = flip_rate(sarr, st["mm"], st["pp"])
                k, ntot, ce = exactness_check(f"{sname}/{vname}", flip, st["mm"])
                if not ce and (k == ntot or k == 0):
                    any_gold = True
                dev = abs(k / ntot - 0.5)
                if dev > worst_dev[0]:
                    worst_dev = (dev, sname, vname, k, ntot, ce)
        if not any_gold:
            dev, sname, vname, k, ntot, ce = worst_dev
            print(f"  no exact variant. farthest from coin-flip: {sname}/{vname} "
                  f"rate {k/ntot:.5f} ({k}/{ntot}); first non-conforming "
                  f"centers m = {ce}")

        # failure structure for the sign-best pairing at the base sign
        vbest = max(VARIANTS, key=lambda v: abs(stats[v]["fr"] - 0.5))
        st = stats[vbest]
        print(f"\nfailure structure, base wingSign, pairing {vbest}:")
        failure_structure(OL, OR, st["mm"], st["pp"], st["flip"],
                          f"A={A} {vbest}")

        # nulls: random sign, Selberg foils
        print(f"\nnull calibration (pairing {vbest}):")
        fr_r, _ = flip_rate(rand_sign, st["mm"], st["pp"])
        print(f"  iid random +-1 sign: flip rate {fr_r:.5f} (base ~0.5)")
        w_plus = (1 + wing_sign).astype(np.float64)
        w_minus = (1 - wing_sign).astype(np.float64)
        fr_t = st["fr"]
        fr_p, _ = flip_rate(wing_sign, st["mm"], st["pp"], weights=w_plus)
        fr_m, _ = flip_rate(wing_sign, st["mm"], st["pp"], weights=w_minus)
        print(f"  wingSign flip: truth {fr_t:.5f}  foil+ {fr_p:.5f}  "
              f"foil- {fr_m:.5f}")
        # label preservation under foils (parity-blindness of the pairing metric)
        lab = lk[st["pp"]] == lk[st["mm"]]
        for wname, w in (("truth", None), ("foil+", w_plus), ("foil-", w_minus)):
            if w is None:
                v = lab.mean()
            else:
                ww = w[st["mm"]]
                v = (ww * lab).sum() / max(ww.sum(), 1e-30)
            print(f"  label preservation under {wname}: {v:.5f}")

    print("\ndone.")


if __name__ == "__main__":
    main()
