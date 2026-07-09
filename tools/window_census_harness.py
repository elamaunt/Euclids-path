# window_census_harness.py — Phase 2 census of signed window sums
#     S(W) = sum_{m in W} lam(6m-1) lam(6m+1),   lam = Liouville = (-1)^Omega.
#
# Empirical face of the planned estimate field `window_sum_ne_zero` with
# sign(m) = wingSign(m) = lam(L) lam(R) in {+1, -1} (Lean: wingSign,
# wingSign_of_twin — twins contribute +1; EuclidsPath/Engine/Step00OrderedExponentGeometry.lean).
# Question: which window families give ROBUST nonzero S(W)?  CLT null: S ~ +-sqrt(|W|).
#
# Window families over m <= 10^7 (full ranges, no reduction):
#   (a) plain intervals [M0 + i*H, M0 + (i+1)*H), H in {1e3, 1e4, 1e5},
#       M0 in {1e5, 1e6, 5e6}, N_INST disjoint instances each;
#   (b) the same intervals intersected with survivors at A in {13, 31}
#       (no prime clock 5..A strikes either wing);
#   (c) primorial-anchored progressions m = k*P, P = 5005 = 5*7*11*13 and
#       P = 85085 = 5*7*11*13*17 — automatically clean at A = 13 / 17 (verified);
#   (d) admissible-class windows: m in a fixed residue class mod 385 = 5*7*11
#       that survives all three clocks (135 = 3*5*9 such classes exist).
#
# Per family: instance-by-instance S, |W|, S/sqrt(|W|); sign stability across the
# disjoint instances (flip rate = minority-sign fraction); twin-corner decomposition
# S = N(+1) - N(-1) with the twin share of N(+1); plus the survivor-conditioned mean
# E[lam_L lam_R | survivor A] vs E[lam_L lam_R] and its scale dependence.
#
# Output: fixed-width console tables -> tools/window_census_run1.log.
# Feeds tools/LAWS_ordered_exponent.md (L7+).

import numpy as np
import math
import time

M_MAX = 10**7                    # census range of centers m
H_LIST = [10**3, 10**4, 10**5]   # plain window widths
M0_LIST = [10**5, 10**6, 5 * 10**6]
N_INST = 10                      # disjoint instances per plain/survivor family
A_SURV = [13, 31]                # survivor scales for family (b)
PRIMORIALS = [(5005, 13, 6), (85085, 17, 3)]   # (P, clean scale A, #instances)
ADM_MOD = 385                    # 5*7*11 for family (d)
ADM_N_INST = 8
MEAN_SCALES = [10**5, 10**6, 10**7]


# ---------- sieves ----------

def prime_sieve(n):
    """Boolean array is_prime[0..n]."""
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def omega_array(n):
    """Omega (number of prime factors with multiplicity) for 0..n, int8."""
    isp = prime_sieve(n)
    big = np.zeros(n + 1, dtype=np.int8)
    for p in np.flatnonzero(isp):
        p = int(p)
        pk = p
        while pk <= n:
            big[pk::pk] += 1
            pk *= p
    return big


def survivor_mask(M, A):
    """survivor[m] for m in 0..M: no prime q in [5, A] divides 6m-1 or 6m+1."""
    mask = np.ones(M + 1, dtype=bool)
    isp = prime_sieve(A)
    for q in np.flatnonzero(isp):
        q = int(q)
        if q < 5:
            continue
        inv6 = pow(6, -1, q)
        mask[inv6::q] = False              # q | 6m-1
        mask[(q - inv6) % q::q] = False    # q | 6m+1
    mask[0] = False
    return mask


# ---------- family evaluation ----------

def family_report(name, instances, sgn, twin):
    """Print one family block; return a summary row for the final verdict table."""
    S_list, n_list = [], []
    for ms in instances:
        S_list.append(int(sgn[ms].sum(dtype=np.int64)))
        n_list.append(int(ms.size))
    allm = np.concatenate(instances)
    n = int(allm.size)
    S = int(sgn[allm].sum(dtype=np.int64))
    npos = int((sgn[allm] == 1).sum())
    nneg = n - npos
    ntw = int(twin[allm].sum())
    pos_i = sum(1 for s in S_list if s > 0)
    neg_i = sum(1 for s in S_list if s < 0)
    zer_i = len(S_list) - pos_i - neg_i
    flip = min(pos_i, neg_i) / max(len(S_list), 1)
    verdict = "STABLE" if (pos_i == 0 or neg_i == 0) else "FLIPS"
    norm = S / math.sqrt(n) if n else 0.0
    print(f"\n-- {name}  ({len(instances)} disjoint instances) --")
    print("   inst S      : " + " ".join(f"{s:+d}" for s in S_list))
    print("   inst S/sqrt : " + " ".join(
        f"{s / math.sqrt(k):+.2f}" if k else "  n/a" for s, k in zip(S_list, n_list)))
    print(f"   agg  |W| = {n:>8}   S = {S:+8d}   S/sqrt|W| = {norm:+7.3f}   "
          f"inst signs {pos_i}+/{neg_i}-/{zer_i}0   flip-rate {flip:.2f}  -> {verdict}")
    print(f"   corners: N(+1) = {npos}   N(-1) = {nneg}   twins = {ntw}   "
          f"twin share of N(+1) = {ntw / max(npos, 1):.4f}")
    return dict(name=name, n=n, S=S, norm=norm, pos=pos_i, neg=neg_i,
                flip=flip, verdict=verdict, twin_share=ntw / max(npos, 1))


# ---------- main ----------

def main():
    print("=" * 78)
    print("WINDOW CENSUS - Phase 2 signed window sums S(W) = sum wingSign(m)")
    print("=" * 78)
    t0 = time.time()
    big = omega_array(6 * M_MAX + 1)
    mm = np.arange(1, M_MAX + 1, dtype=np.int64)
    OL = big[6 * mm - 1]
    OR = big[6 * mm + 1]
    sgn = np.zeros(M_MAX + 1, dtype=np.int8)       # indexed by m; m = 0 unused
    sgn[1:] = (1 - 2 * (OL & 1)).astype(np.int8) * (1 - 2 * (OR & 1)).astype(np.int8)
    twin = np.zeros(M_MAX + 1, dtype=bool)
    twin[1:] = (OL == 1) & (OR == 1)
    surv = {A: survivor_mask(M_MAX, A) for A in sorted(set(A_SURV) | {a for _, a, _ in PRIMORIALS})}
    print(f"[build] Omega to {6 * M_MAX + 1}, wingSign, twin mask, survivor masks "
          f"A={sorted(surv)} in {time.time() - t0:.1f}s")
    print(f"sanity: wingSign(twin) = +1 for all {int(twin.sum())} twins: "
          f"{'OK' if (sgn[twin] == 1).all() else 'FAIL'}")

    rows = []

    # (a) plain intervals
    print("\n" + "=" * 78)
    print("(a) plain intervals [M0 + i*H, M0 + (i+1)*H)")
    for M0 in M0_LIST:
        for H in H_LIST:
            inst = [np.arange(M0 + i * H, M0 + (i + 1) * H, dtype=np.int64)
                    for i in range(N_INST)]
            rows.append(family_report(f"plain    M0={M0:.0e} H={H:.0e}", inst, sgn, twin))

    # (b) survivor-restricted intervals
    print("\n" + "=" * 78)
    print("(b) survivor-restricted intervals (same intervals ^ survivors at A)")
    for A in A_SURV:
        sv = surv[A]
        for M0 in M0_LIST:
            for H in H_LIST:
                inst = []
                for i in range(N_INST):
                    lo, hi = M0 + i * H, M0 + (i + 1) * H
                    inst.append(np.flatnonzero(sv[lo:hi]).astype(np.int64) + lo)
                rows.append(family_report(
                    f"surv A={A:<2} M0={M0:.0e} H={H:.0e}", inst, sgn, twin))

    # (c) primorial-anchored progressions
    print("\n" + "=" * 78)
    print("(c) primorial-anchored progressions m = k*P (auto-clean at scale A)")
    for P, A, n_inst in PRIMORIALS:
        kmax = M_MAX // P
        ms = P * np.arange(1, kmax + 1, dtype=np.int64)
        clean = bool(surv[A][ms].all())
        print(f"\n   P = {P} (clean scale A = {A}): k = 1..{kmax}, "
              f"all m = k*P survive at A = {A}: {'OK' if clean else 'FAIL'}")
        inst = [blk for blk in np.array_split(ms, n_inst)]
        rows.append(family_report(f"primor   P={P} A={A}", inst, sgn, twin))

    # (d) admissible-class windows mod 385
    print("\n" + "=" * 78)
    print(f"(d) admissible residue classes mod {ADM_MOD} = 5*7*11")
    adm = []
    for r in range(ADM_MOD):
        ok = True
        for q in (5, 7, 11):
            inv6 = pow(6, -1, q)
            if r % q == inv6 or r % q == (q - inv6) % q:
                ok = False
                break
        if ok:
            adm.append(r)
    print(f"   admissible classes: {len(adm)} (expect (5-2)(7-2)(11-2) = 135)  "
          f"first = {adm[0]}, mid = {adm[len(adm) // 2]}, last = {adm[-1]}")
    for r in (adm[0], adm[len(adm) // 2]):
        ms = np.arange(r, M_MAX + 1, ADM_MOD, dtype=np.int64)
        if ms.size and ms[0] == 0:
            ms = ms[1:]
        inst = [blk for blk in np.array_split(ms, ADM_N_INST)]
        rows.append(family_report(f"admcls   r={r} mod {ADM_MOD}", inst, sgn, twin))

    # survivor conditioning of the mean
    print("\n" + "=" * 78)
    print("mean E[lam_L lam_R] vs survivor conditioning (scale dependence)")
    print(f"   {'M':>7} {'E[ll]':>9} {'se':>8} | {'E[ll|A=13]':>10} {'P(tw|13)':>9} "
          f"{'n_13':>8} | {'E[ll|A=31]':>10} {'P(tw|31)':>9} {'n_31':>8}")
    for M in MEAN_SCALES:
        s = sgn[1:M + 1].astype(np.float64)
        tw = twin[1:M + 1]
        e_all = s.mean()
        cells = [f"   {M:>7.0e} {e_all:>+9.5f} {1 / math.sqrt(M):>8.5f}"]
        for A in A_SURV:
            sel = surv[A][1:M + 1]
            nA = int(sel.sum())
            eA = s[sel].mean()
            ptw = tw[sel].mean()
            cells.append(f" {eA:>+10.5f} {ptw:>9.5f} {nA:>8}")
        print(" |".join(cells))
    print("   (null: E[ll|surv] = P(tw|surv) if non-twin survivors were sign-balanced;")
    print("    se ~ 1/sqrt(n) per cell)")

    # final verdict table
    print("\n" + "=" * 78)
    print("summary verdict per family (CLT null: S ~ +-sqrt(|W|))")
    print(f"   {'family':<28} {'|W|':>8} {'S':>8} {'S/sqrt':>8} {'signs':>7} "
          f"{'flip':>5} {'twin/N+':>8}  verdict")
    for r in rows:
        print(f"   {r['name']:<28} {r['n']:>8} {r['S']:>+8} {r['norm']:>+8.3f} "
              f"{str(r['pos']) + '+/' + str(r['neg']) + '-':>7} {r['flip']:>5.2f} "
              f"{r['twin_share']:>8.4f}  {r['verdict']}")
    n_stable = sum(1 for r in rows if r["verdict"] == "STABLE")
    worst = max(abs(r["norm"]) for r in rows)
    print(f"\n   families with sign-stable instances: {n_stable}/{len(rows)}   "
          f"max |S|/sqrt|W| over families = {worst:.3f}")
    print("   uniform nonvanishing requires |S|/sqrt|W| -> infinity and zero flip rate;")
    print("   see verdicts above (expected: none qualifies - the parity barrier).")

    print(f"\ndone in {time.time() - t0:.1f}s.")


if __name__ == "__main__":
    main()
