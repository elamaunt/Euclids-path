# wing_grade_harness.py — Phase 0 baseline census of the two wings 6m-1, 6m+1.
#
# Measures (exhaustive small scale + segmented large-scale windows):
#   * grade vectors of both wings: Omega (with multiplicity), omega (distinct),
#     PowDef = Omega - omega, GapDef = hull(prime-index support) - omega;
#   * joint distribution of (Omega_L - 1, Omega_R - 1), overall and conditioned on
#     survival at scale A (no prime 5..A divides either wing), vs independence null;
#   * sign walk signPair(m) = ((-1)^Omega_L, (-1)^Omega_R): corner frequencies,
#     transition matrix, lag autocorrelations, Chowla-type cross moment E[lam_L*lam_R];
#   * GapDef relevance gate: conditional mutual information
#     I(GapDef ; survivor | Omega, minFac-bucket) against a permutation null;
#   * parity-foil snapshot: grade census under Selberg weights 1 +/- lam_L*lam_R;
#   * twin counts vs Hardy-Littlewood 2*C2*6M/(ln 6M)^2.
#
# Output: fixed-width console tables. Feeds tools/LAWS_ordered_exponent.md.
# Cross-checks the Lean layer Engine/Step00OrderedExponentGeometry.lean (Phase 1).

import numpy as np
import math
import sys
import time

M_SMALL = 10**6          # exhaustive census with GapDef (arrays over 6*M+2)
M_MED = 10**7            # Omega/omega census only (no GapDef; int8 arrays)
LARGE_WINDOWS = [(10**9, 10**6), (10**12, 2 * 10**5)]  # (start center M0, width W)
SCALES_A = [5, 13, 31, 101]
N_PERM = 200             # permutation-null resamples for MI tests
RNG = np.random.default_rng(20260710)


# ---------- sieves ----------

def prime_sieve(n):
    """Boolean array is_prime[0..n]."""
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def grade_arrays(n, want_gapdef):
    """Arrays over 0..n: big Omega, little omega, and (optionally) min/max prime rank."""
    isp = prime_sieve(n)
    primes = np.flatnonzero(isp)
    big = np.zeros(n + 1, dtype=np.int8)
    lit = np.zeros(n + 1, dtype=np.int8)
    if want_gapdef:
        minr = np.full(n + 1, np.iinfo(np.int32).max, dtype=np.int32)
        maxr = np.full(n + 1, -1, dtype=np.int32)
    for i, p in enumerate(primes):
        p = int(p)
        lit[p::p] += 1
        pk = p
        while pk <= n:
            big[pk::pk] += 1
            pk *= p
        if want_gapdef:
            minr[p::p] = np.minimum(minr[p::p], i)
            maxr[p::p] = np.maximum(maxr[p::p], i)
    if want_gapdef:
        return primes, big, lit, minr, maxr
    return primes, big, lit, None, None


def survivor_mask(M, A):
    """survivor[m] for m in 0..M: no prime q in [5, A] divides 6m-1 or 6m+1."""
    mask = np.ones(M + 1, dtype=bool)
    isp = prime_sieve(A)
    for q in np.flatnonzero(isp):
        q = int(q)
        if q < 5:
            continue
        inv6 = pow(6, -1, q)
        mask[inv6::q] = False              # q | 6m-1  (6m == 1 mod q)
        mask[(q - inv6) % q::q] = False    # q | 6m+1  (6m == -1 mod q)
    mask[0] = False
    return mask


# ---------- info-theory helpers ----------

def mutual_info(x, y, nx, ny):
    """Plug-in MI (bits) of two int arrays with alphabets 0..nx-1, 0..ny-1."""
    joint = np.zeros((nx, ny))
    np.add.at(joint, (x, y), 1.0)
    joint /= joint.sum()
    px = joint.sum(1, keepdims=True)
    py = joint.sum(0, keepdims=True)
    nzero = joint > 0
    return float((joint[nzero] * np.log2(joint[nzero] / (px @ py)[nzero])).sum())


def mi_with_null(x, y, nx, ny, n_perm=N_PERM):
    mi = mutual_info(x, y, nx, ny)
    null = np.empty(n_perm)
    xs = x.copy()
    for i in range(n_perm):
        RNG.shuffle(xs)
        null[i] = mutual_info(xs, y, nx, ny)
    mu, sd = null.mean(), null.std() + 1e-15
    return mi, mu, sd, (mi - mu) / sd


# ---------- small/medium-scale census ----------

def census(M, want_gapdef):
    t0 = time.time()
    n = 6 * M + 1
    primes, big, lit, minr, maxr = grade_arrays(n, want_gapdef)
    m = np.arange(1, M + 1)
    L = 6 * m - 1
    R = 6 * m + 1
    OL, OR = big[L].astype(np.int32), big[R].astype(np.int32)
    wL, wR = lit[L].astype(np.int32), lit[R].astype(np.int32)
    powL, powR = OL - wL, OR - wR
    if want_gapdef:
        gapL = (maxr[L] - minr[L] + 1 - wL).astype(np.int32)
        gapR = (maxr[R] - minr[R] + 1 - wR).astype(np.int32)
    else:
        gapL = gapR = None
    print(f"[census M={M:.0e}] sieves+grades built in {time.time()-t0:.1f}s")
    return dict(M=M, m=m, L=L, R=R, OL=OL, OR=OR, wL=wL, wR=wR,
                powL=powL, powR=powR, gapL=gapL, gapR=gapR)


def print_joint_omega(c, cond=None, title=""):
    OL, OR = c["OL"], c["OR"]
    if cond is not None:
        OL, OR = OL[cond], OR[cond]
    K = 5
    a = np.clip(OL - 1, 0, K)
    b = np.clip(OR - 1, 0, K)
    tab = np.zeros((K + 1, K + 1))
    np.add.at(tab, (a, b), 1)
    tot = tab.sum()
    print(f"\n  joint (Omega_L-1, Omega_R-1) {title}  [rows=L, cols=R, {int(tot)} centers, %]")
    hdr = "        " + "".join(f"{j:>8}" for j in range(K)) + f"{'>=' + str(K):>8}"
    print(hdr)
    for i in range(K + 1):
        lab = f"{i}" if i < K else f">={K}"
        print(f"  {lab:>5} " + "".join(f"{100*tab[i, j]/tot:8.3f}" for j in range(K + 1)))
    mi, mu, sd, z = mi_with_null(a.astype(np.int64), b.astype(np.int64), K + 1, K + 1, 60)
    print(f"  MI(L;R) = {mi:.6f} bits   perm-null {mu:.6f} +/- {sd:.6f}   z = {z:+.1f}")
    lamL = np.where((OL & 1) == 1, -1, 1)   # (-1)^Omega: odd Omega -> -1
    lamR = np.where((OR & 1) == 1, -1, 1)
    print(f"  Chowla cross moment E[lam_L*lam_R] = {np.mean(lamL*lamR):+.6f}"
          f"   (n={lamL.size}, se~{1/np.sqrt(lamL.size):.6f})")


def sign_walk(c, cond=None, title=""):
    OL, OR = c["OL"], c["OR"]
    if cond is not None:
        OL, OR = OL[cond], OR[cond]
    lamL = 1 - 2 * (OL & 1)
    lamR = 1 - 2 * (OR & 1)
    corner = (lamL < 0).astype(np.int64) * 2 + (lamR < 0).astype(np.int64)
    names = ["(+,+)", "(+,-)", "(-,+)", "(-,-)"]
    freq = np.bincount(corner, minlength=4) / corner.size
    print(f"\n  sign walk {title}: corner freq " +
          " ".join(f"{names[i]}={freq[i]:.4f}" for i in range(4)))
    trans = np.zeros((4, 4))
    np.add.at(trans, (corner[:-1], corner[1:]), 1)
    trans /= np.maximum(trans.sum(1, keepdims=True), 1)
    print("  transition matrix (rows -> cols):")
    for i in range(4):
        print(f"    {names[i]} " + "".join(f"{trans[i, j]:8.4f}" for j in range(4)))
    for lag in (1, 2, 3, 6):
        aL = np.mean(lamL[:-lag] * lamL[lag:])
        aR = np.mean(lamR[:-lag] * lamR[lag:])
        x = lamL[:-lag] * lamR[lag:]
        print(f"    lag {lag}: auto_L={aL:+.5f} auto_R={aR:+.5f} cross_LR={np.mean(x):+.5f}")


def gapdef_gate(c, surv, A):
    """CMI(GapDef ; survivor | Omega-bucket, minFac-bucket) with permutation null."""
    OL, gapL, L = c["OL"], c["gapL"], c["L"]
    g = np.clip(gapL, 0, 3).astype(np.int64)
    s = surv[c["m"]].astype(np.int64)
    om = np.clip(OL, 1, 4).astype(np.int64) - 1
    # minFac bucket: 0 if L divisible by 5/7/11/13, else 1 (survivors all land in 1)
    small = np.zeros(L.size, dtype=np.int64)
    for q in (5, 7, 11, 13):
        small |= (L % q == 0)
    bucket = om * 2 + small
    cmi = 0.0
    weights = 0.0
    parts = []
    for b in range(8):
        sel = bucket == b
        nb = int(sel.sum())
        if nb < 1000 or s[sel].min() == s[sel].max():
            continue
        mi, mu, sd, z = mi_with_null(g[sel], s[sel], 4, 2, 100)
        parts.append((b, nb, mi, mu, z))
        cmi += nb * max(mi - mu, 0.0)
        weights += nb
    print(f"\n  GapDef gate (A={A}), left wing: CMI-excess = {cmi/max(weights,1):.3e} bits")
    for b, nb, mi, mu, z in parts:
        print(f"    bucket {b} (n={nb}): MI={mi:.2e} null={mu:.2e} z={z:+.1f}")


def foil_snapshot(c, surv):
    OL, OR = c["OL"], c["OR"]
    lam = (1 - 2 * (OL & 1)) * (1 - 2 * (OR & 1))
    s = surv[c["m"]]
    for name, w in (("truth", np.ones_like(lam)),
                    ("foil+", 1 + lam), ("foil-", 1 - lam)):
        wS = w[s].sum()
        if wS == 0:
            print(f"  {name}: zero survivor mass")
            continue
        mean_grade = ((OL + OR - 2)[s] * w[s]).sum() / wS
        twin_mass = (w[s & (OL == 1) & (OR == 1)]).sum() / wS
        print(f"  {name}: survivor mass={w[s].sum():>10.0f}  "
              f"mean grade={mean_grade:.4f}  twin mass frac={twin_mass:.6f}")


# ---------- segmented large-scale window ----------

def window_grades(M0, W):
    """Cleaner exact segmented factor-count: returns OL, OR arrays for the window."""
    lim = int(math.isqrt(6 * (M0 + W) + 2)) + 1
    primes = np.flatnonzero(prime_sieve(lim))
    out = {}
    t0 = time.time()
    for side, off in (("L", -1), ("R", +1)):
        vals = 6 * (M0 + np.arange(W, dtype=np.int64)) + off
        rem = vals.copy()
        big = np.zeros(W, dtype=np.int16)
        lit = np.zeros(W, dtype=np.int16)
        for p in primes:
            p = int(p)
            if p < 5:
                continue
            inv6 = pow(6, -1, p)
            r = (inv6 if off == -1 else (p - inv6) % p)
            first = (r - M0) % p
            if first >= W:
                continue
            idx = np.arange(first, W, p)
            lit[idx] += 1
            rem[idx] //= p
            big[idx] += 1
            cur = idx[rem[idx] % p == 0]
            while cur.size:
                rem[cur] //= p
                big[cur] += 1
                cur = cur[rem[cur] % p == 0]
        left = rem > 1
        big[left] += 1
        lit[left] += 1
        out[side] = (big.astype(np.int32), lit.astype(np.int32))
    print(f"[window M0={M0:.1e} W={W:.0e}] exact grades in {time.time()-t0:.1f}s "
          f"(primes to {primes[-1]})")
    return out


def report_window(M0, W):
    g = window_grades(M0, W)
    OL, wLd = g["L"]
    OR, wRd = g["R"]
    c = dict(OL=OL, OR=OR, m=np.arange(W))
    print_joint_omega(c, title=f"window [{M0:.1e}, +{W:.0e})")
    sign_walk(c, title=f"window [{M0:.1e}, +{W:.0e})")
    powL = (OL - wLd)
    print(f"  PowDef_L distribution: " + " ".join(
        f"{k}:{np.mean(powL == k):.4f}" for k in range(4)))
    twins = int(((OL == 1) & (OR == 1)).sum())
    x = 6 * (M0 + W / 2)
    hl = 2 * 0.6601618158 * 6 * W / math.log(x) ** 2
    print(f"  twins in window: {twins}   HL prediction ~ {hl:.1f}")


# ---------- main ----------

def main():
    print("=" * 78)
    print("WING GRADE CENSUS — Phase 0 baseline (ordered exponent geometry)")
    print("=" * 78)

    c = census(M_SMALL, want_gapdef=True)
    surv = {A: survivor_mask(M_SMALL, A) for A in SCALES_A}

    dens_expected = {}
    for A in SCALES_A:
        qs = [int(q) for q in np.flatnonzero(prime_sieve(A)) if q >= 5]
        d = 1.0
        for q in qs:
            d *= (q - 2) / q
        dens_expected[A] = d

    print(f"\n-- small scale M = {M_SMALL:.0e} (exhaustive, exact) --")
    twins = (c["OL"] == 1) & (c["OR"] == 1)
    hl = 2 * 0.6601618158 * 6 * M_SMALL / math.log(6 * M_SMALL) ** 2
    print(f"twin centers: {int(twins.sum())}   HL ~ {hl:.0f}")
    for A in SCALES_A:
        s = surv[A][c["m"]]
        print(f"A={A:>4}: survivor density {np.mean(s):.6f}  "
              f"product law prod(q-2)/q = {dens_expected[A]:.6f}  "
              f"ratio {np.mean(s)/dens_expected[A]:.4f}   "
              f"twin|survivor = {np.mean(twins[s]):.5f}")

    print_joint_omega(c, title="(all centers)")
    for A in (13, 101):
        print_joint_omega(c, surv[A][c["m"]], title=f"(survivors A={A})")

    sign_walk(c, title="(all centers)")
    sign_walk(c, surv[13][c["m"]], title="(survivors A=13)")

    print("\n-- PowDef / GapDef marginals (left wing) --")
    for name, arr in (("PowDef_L", c["powL"]), ("GapDef_L", c["gapL"])):
        print(f"  {name}: " + " ".join(
            f"{k}:{np.mean(arr == k):.4f}" for k in range(5)) +
            f"  >=5:{np.mean(arr >= 5):.4f}  mean={arr.mean():.3f}")

    for A in (13, 101):
        gapdef_gate(c, surv[A], A)

    print("\n-- parity-foil snapshot (A=13) --")
    foil_snapshot(c, surv[13])

    print(f"\n-- medium scale M = {M_MED:.0e} (Omega/omega only) --")
    cm = census(M_MED, want_gapdef=False)
    twins_m = (cm["OL"] == 1) & (cm["OR"] == 1)
    hl_m = 2 * 0.6601618158 * 6 * M_MED / math.log(6 * M_MED) ** 2
    print(f"twin centers: {int(twins_m.sum())}   HL ~ {hl_m:.0f}")
    print_joint_omega(cm, title="(all centers, M=1e7)")
    sign_walk(cm, title="(all centers, M=1e7)")

    print("\n-- large-scale windows (segmented, exact) --")
    for M0, W in LARGE_WINDOWS:
        report_window(M0, W)

    print("\ndone.")


if __name__ == "__main__":
    main()
