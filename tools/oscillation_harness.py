# oscillation_harness.py — Phase 1 phase mechanics of the two wing engines L = 6m-1, R = 6m+1.
#
# Sections (fixed-width tables; full log -> tools/oscillation_run1.log):
#   1. strike-phase verification: every prime clock q in [5, 97] strikes L on exactly one
#      residue class m = inv6 (mod q) and R on exactly the antipodal class -inv6 (mod q),
#      the two classes distinct, leaving q-2 admissible classes.  Numerical cross-check of
#      the Lean theorems strike_phase_left / strike_phase_right / strike_phases_antipodal /
#      admissible_card (EuclidsPath/Engine/Step00TwoEngineOscillation.lean).
#   2. per-clock interference factors: r_q = P(q!|L and q!|R) / [P(q!|L) P(q!|R)] measured
#      over m <= 10^6 for q in [5, 199] vs the exact CRT value q(q-2)/(q-1)^2; cumulative
#      product vs the Hardy-Littlewood limit 2*C2/1.5 = 4*C2/3 (per-component derivation of
#      ledger law L2).
#   3. CRT beats of clock pairs: for (5,7), (5,11), (7,11) the joint survival fraction over
#      one full period q1*q2 equals the product of the local fractions EXACTLY
#      (fractions.Fraction, no float error) — clock independence, EXACT-CANDIDATE.
#   4. foil test of ledger law L1: weighted MI(clip(Omega_L-1,0..5); clip(Omega_R-1,0..5))
#      under Selberg weights w = 1 (truth), 1 + lam_L lam_R (foil+), 1 - lam_L lam_R (foil-),
#      against a shuffled-weight permutation null; decomposed into the parity channel
#      (Omega mod 2) and the parity-blind graded shadow (clip((Omega-1)//2, 0..2));
#      everything repeated on survivors at A = 13.  Decision: |dMI| < 3 sigma_null =>
#      PARITY-BLIND, strongly above => PARITY-SENSITIVE.
#   5. sign-corner visitation per decade of m (10^3..10^6), plus the Lean prime-power corner
#      witnesses: 5^(2k+1) as L-values (lam_L = -1 always) and 7^k as R-values
#      (lam_R = (-1)^k), for all k with center m <= 10^7.
#
# Output: fixed-width console tables.  Feeds tools/LAWS_ordered_exponent.md (L7+).

import numpy as np
import math
import time
from fractions import Fraction

M_PHASE = 10**6            # m-range for sections 1, 2, 4, 5 (full range, no reduction)
Q_PHASE_MAX = 97           # clocks verified in section 1
Q_INTERF_MAX = 199         # clocks measured in section 2
CLOCK_PAIRS = [(5, 7), (5, 11), (7, 11)]
A_FOIL = 13                # survivor scale for the conditioned foil test
N_PERM = 50                # shuffled-weight null resamples per foil weighting/channel
M_POWER = 10**7            # m-limit for the prime-power corner families
DECADES = [(10**3, 10**4), (10**4, 10**5), (10**5, 10**6)]
C2 = 0.6601618158468696    # twin prime constant
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


def omega_trial(n):
    """Omega by trial division (for isolated large values in section 5)."""
    cnt = 0
    d = 2
    while d * d <= n:
        while n % d == 0:
            n //= d
            cnt += 1
        d += 1 if d == 2 else 2
    if n > 1:
        cnt += 1
    return cnt


# ---------- weighted MI ----------

def weighted_mi(code, w, na, nb):
    """MI (bits) of the joint distribution given by nonneg weights w on symbols code = a*nb+b."""
    joint = np.bincount(code, weights=w, minlength=na * nb).astype(float).reshape(na, nb)
    joint /= joint.sum()
    px = joint.sum(1, keepdims=True)
    py = joint.sum(0, keepdims=True)
    nz = joint > 0
    return float((joint[nz] * np.log2(joint[nz] / (px @ py)[nz])).sum())


def foil_channel(a, b, lamL, lamR, na, label):
    """Truth/foil+/foil- weighted MI of (a, b) against two permutation nulls.

    null W (task decision scale): shuffle the foil weight vector over the sample —
      measures how far the foil MI sits from the truth MI in units of half-sample noise.
    null I (mechanical-accounting scale): permute the R wing JOINTLY with its sign
      lam_R, recompute the foil weight and the MI — this is the foil MI that would
      arise if the two wings were INDEPENDENT; any excess above it is genuine
      cross-wing structure surviving the parity surgery.
    """
    n = a.size
    a64 = a.astype(np.int64) * na
    b64 = b.astype(np.int64)
    lam = (lamL * lamR).astype(np.float64)
    code = a64 + b64
    ones = np.ones(n)
    mi_t = weighted_mi(code, ones, na, na)
    null_t = np.empty(N_PERM)
    for i in range(N_PERM):
        null_t[i] = weighted_mi(a64 + b64[RNG.permutation(n)], ones, na, na)
    mu_t, sd_t = null_t.mean(), null_t.std() + 1e-15
    print(f"  channel {label} (n={n}):")
    print(f"    truth : MI = {mi_t:.6f} bits   indep-null {mu_t:.6f} +/- {sd_t:.6f}   "
          f"z_indep = {(mi_t - mu_t) / sd_t:+9.1f}")
    res = {}
    for name, sign in (("foil+", +1.0), ("foil-", -1.0)):
        w = 1.0 + sign * lam
        mi_f = weighted_mi(code, w, na, na)
        null_w = np.empty(N_PERM)
        ws = w.copy()
        for i in range(N_PERM):
            RNG.shuffle(ws)
            null_w[i] = weighted_mi(code, ws, na, na)
        mu_w, sd_w = null_w.mean(), null_w.std() + 1e-15
        null_i = np.empty(N_PERM)
        for i in range(N_PERM):
            perm = RNG.permutation(n)
            null_i[i] = weighted_mi(a64 + b64[perm],
                                    1.0 + sign * lamL * lamR[perm], na, na)
        mu_i, sd_i = null_i.mean(), null_i.std() + 1e-15
        d = mi_f - mi_t
        print(f"    {name} : MI = {mi_f:.6f}   dMI = {d:+.6f}  "
              f"({d / sd_w:+9.1f} sigma_W; shuffled-weight null {mu_w:.6f} +/- {sd_w:.6f})")
        print(f"            indep-null {mu_i:.6f} +/- {sd_i:.6f}   "
              f"excess over mechanical = {mi_f - mu_i:+.6f}  "
              f"({(mi_f - mu_i) / sd_i:+9.1f} sigma_I)")
        res[name] = dict(mi=mi_f, d=d, sd_w=sd_w, mu_i=mu_i, sd_i=sd_i)
    worst_w = max(abs(res[k]["d"]) / res[k]["sd_w"] for k in res)
    worst_i = max(abs(res[k]["mi"] - res[k]["mu_i"]) / res[k]["sd_i"] for k in res)
    verdict = "PARITY-SENSITIVE" if worst_w > 3 else "PARITY-BLIND"
    mech = ("beyond mechanical accounting" if worst_i > 3
            else "fully explained by mechanical parity-mass accounting")
    print(f"    channel verdict: {verdict} vs truth "
          f"(max |dMI|/sigma_W = {worst_w:.1f}); foil MI {mech} "
          f"(max |MI-indep|/sigma_I = {worst_i:.1f})")
    return mi_t, res, verdict


# ---------- section 1: strike phases ----------

def phase_verification(m):
    qs = [int(q) for q in np.flatnonzero(prime_sieve(Q_PHASE_MAX)) if q >= 5]
    print(f"\n-- 1. strike-phase verification, q in [5, {Q_PHASE_MAX}], m <= {M_PHASE:.0e} --")
    print("   (Lean: strike_phase_left/right, strike_phases_antipodal, admissible_card)")
    print(f"   {'q':>4} {'inv6':>5} {'resL':>5} {'resR':>5} {'#strkL':>8} {'#strkR':>8} "
          f"{'#adm':>5} {'q-2':>5}  status")
    all_ok = True
    for q in qs:
        inv6 = pow(6, -1, q)
        mq = m % q
        resL = np.unique(mq[(6 * m - 1) % q == 0])
        resR = np.unique(mq[(6 * m + 1) % q == 0])
        okL = resL.size == 1 and resL[0] == inv6
        okR = resR.size == 1 and resR[0] == (q - inv6) % q
        distinct = okL and okR and resL[0] != resR[0]
        n_adm = q - np.union1d(resL, resR).size
        ok = okL and okR and distinct and n_adm == q - 2
        all_ok &= ok
        print(f"   {q:>4} {inv6:>5} {int(resL[0]) if resL.size == 1 else -1:>5} "
              f"{int(resR[0]) if resR.size == 1 else -1:>5} "
              f"{int(((6 * m - 1) % q == 0).sum()):>8} {int(((6 * m + 1) % q == 0).sum()):>8} "
              f"{n_adm:>5} {q - 2:>5}  {'OK' if ok else 'FAIL'}")
    msg = ("OK - one class per wing, antipodal, distinct, q-2 admissible"
           if all_ok else "FAIL (see rows above)")
    print(f"   overall: {msg}")


# ---------- section 2: interference factors ----------

def interference_factors(m):
    qs = [int(q) for q in np.flatnonzero(prime_sieve(Q_INTERF_MAX)) if q >= 5]
    print(f"\n-- 2. per-clock interference factors, q in [5, {Q_INTERF_MAX}], m <= {M_PHASE:.0e} --")
    print(f"   r_q = P(q!|L and q!|R) / [P(q!|L) P(q!|R)],  exact CRT = q(q-2)/(q-1)^2")
    print(f"   {'q':>4} {'r_meas':>10} {'r_exact':>10} {'err':>10}   "
          f"{'cumprod_meas':>12} {'cumprod_exact':>13}")
    prod_meas, prod_exact = 1.0, 1.0
    for q in qs:
        inv6 = pow(6, -1, q)
        mq = m % q
        okL = mq != inv6
        okR = mq != (q - inv6) % q
        pL, pR = okL.mean(), okR.mean()
        pLR = (okL & okR).mean()
        r_meas = pLR / (pL * pR)
        r_exact = q * (q - 2) / (q - 1) ** 2
        prod_meas *= r_meas
        prod_exact *= r_exact
        print(f"   {q:>4} {r_meas:>10.6f} {r_exact:>10.6f} {r_meas - r_exact:>+10.2e}   "
              f"{prod_meas:>12.6f} {prod_exact:>13.6f}")
    limit = 2 * C2 / 1.5
    print(f"\n   cumulative product over q <= {Q_INTERF_MAX}: measured {prod_meas:.6f}, "
          f"exact partial {prod_exact:.6f}")
    print(f"   Hardy-Littlewood limit 2*C2/1.5 = 4*C2/3 = {limit:.6f}")
    print(f"   partial/limit = {prod_exact / limit:.6f}  "
          f"(tail factor prod_(q>{Q_INTERF_MAX})(1 - 1/(q-1)^2) ~ {limit / prod_exact:.6f};"
          f" convergence from above, ~1/(Q log Q) tail)")


# ---------- section 3: CRT beats ----------

def crt_beats():
    print(f"\n-- 3. CRT beats of clock pairs (exact fractions over one full period) --")
    all_ok = True
    for q1, q2 in CLOCK_PAIRS:
        period = q1 * q2
        mm = np.arange(period)
        ok = np.ones(period, dtype=bool)
        singles = {}
        for q in (q1, q2):
            inv6 = pow(6, -1, q)
            sv = (mm % q != inv6) & (mm % q != (q - inv6) % q)
            singles[q] = Fraction(int(sv.sum()), period)
            ok &= sv
        joint = Fraction(int(ok.sum()), period)
        prod = Fraction(q1 - 2, q1) * Fraction(q2 - 2, q2)
        exact = joint == prod and all(singles[q] == Fraction(q - 2, q) for q in (q1, q2))
        all_ok &= exact
        print(f"   pair ({q1:>2},{q2:>2}), period {period:>4}: "
              f"joint = {joint} ; ({q1}-2)/{q1} * ({q2}-2)/{q2} = {prod} ; "
              f"singles {singles[q1]}, {singles[q2]} ; "
              f"{'EXACT EQUAL' if exact else 'MISMATCH'}")
    print(f"   clock independence over CRT period: {'OK (exact, zero error)' if all_ok else 'FAIL'}")


# ---------- section 4: foil test of L1 ----------

def foil_section(OL, OR, surv_m):
    a6 = np.clip(OL - 1, 0, 5)
    b6 = np.clip(OR - 1, 0, 5)
    pa = (OL & 1).astype(np.int64)      # Omega mod 2 — the exact lambda channel
    pb = (OR & 1).astype(np.int64)
    ga = np.clip((OL - 1) // 2, 0, 2)   # parity-blind graded shadow
    gb = np.clip((OR - 1) // 2, 0, 2)
    print(f"\n-- 4. foil test of ledger L1: weighted MI(Omega_L; Omega_R), m <= {M_PHASE:.0e} --")
    print(f"   weights: truth w=1, foil+ w=1+lam_L lam_R, foil- w=1-lam_L lam_R "
          f"({N_PERM} shuffled-weight perms per null)")
    lamL = (1 - 2 * (OL & 1)).astype(np.float64)
    lamR = (1 - 2 * (OR & 1)).astype(np.float64)
    for tag, sel in (("all centers", np.ones(OL.size, dtype=bool)),
                     (f"survivors A={A_FOIL}", surv_m)):
        print(f"\n   == {tag} ==")
        lL, lR = lamL[sel], lamR[sel]
        foil_channel(a6[sel], b6[sel], lL, lR, 6, "full 6x6 clip(Omega-1,0..5)")
        foil_channel(pa[sel], pb[sel], lL, lR, 2, "parity 2x2 (Omega mod 2)   ")
        foil_channel(ga[sel], gb[sel], lL, lR, 3, "graded 3x3 clip((Om-1)//2) ")


# ---------- section 5: sign corners and prime-power witnesses ----------

def corner_section(OL, OR):
    lamL = 1 - 2 * (OL & 1)
    lamR = 1 - 2 * (OR & 1)
    corner = (lamL < 0).astype(np.int64) * 2 + (lamR < 0).astype(np.int64)
    names = ["(+,+)", "(+,-)", "(-,+)", "(-,-)"]
    print(f"\n-- 5. sign-corner visitation per decade of m --")
    print(f"   {'decade':>16} " + "".join(f"{nm:>10}" for nm in names) + f"{'all>0':>8}")
    for lo, hi in DECADES:
        cnt = np.bincount(corner[lo - 1:hi - 1], minlength=4)   # index m-1
        print(f"   [{lo:.0e}, {hi:.0e}) " + "".join(f"{int(c):>10}" for c in cnt)
              + f"{'OK' if (cnt > 0).all() else 'FAIL':>8}")

    print(f"\n   prime-power corner witnesses (Lean families), m <= {M_POWER:.0e}:")
    print(f"   5^(2k+1) as L-values  (predict lam_L = -1 for every k):")
    print(f"   {'e':>3} {'v=5^e':>10} {'m':>9} {'Om(v)':>6} {'lamL':>5} {'pred':>5} "
          f"{'lamR':>5} {'corner':>7}  status")
    e = 1
    while (5**e + 1) // 6 <= M_POWER:
        v = 5**e
        mval = (v + 1) // 6
        om = omega_trial(v)
        lamL = (-1) ** om
        lamR = (-1) ** omega_trial(v + 2)
        ok = (v + 1) % 6 == 0 and om == e and lamL == -1
        cr = f"({'+' if lamL > 0 else '-'},{'+' if lamR > 0 else '-'})"
        print(f"   {e:>3} {v:>10} {mval:>9} {om:>6} {lamL:>+5} {-1:>+5} {lamR:>+5} "
              f"{cr:>7}  {'OK' if ok else 'FAIL'}")
        e += 2
    print(f"   7^k as R-values  (predict lam_R = (-1)^k, alternating):")
    print(f"   {'k':>3} {'v=7^k':>10} {'m':>9} {'Om(v)':>6} {'lamR':>5} {'pred':>5} "
          f"{'lamL':>5} {'corner':>7}  status")
    k = 1
    while (7**k - 1) // 6 <= M_POWER:
        v = 7**k
        mval = (v - 1) // 6
        om = omega_trial(v)
        lamR = (-1) ** om
        pred = (-1) ** k
        lamL = (-1) ** omega_trial(v - 2)
        ok = (v - 1) % 6 == 0 and om == k and lamR == pred
        cr = f"({'+' if lamL > 0 else '-'},{'+' if lamR > 0 else '-'})"
        print(f"   {k:>3} {v:>10} {mval:>9} {om:>6} {lamR:>+5} {pred:>+5} {lamL:>+5} "
              f"{cr:>7}  {'OK' if ok else 'FAIL'}")
        k += 1


# ---------- main ----------

def main():
    print("=" * 78)
    print("TWO-ENGINE OSCILLATION - Phase 1 phase mechanics (ordered exponent geometry)")
    print("=" * 78)
    t0 = time.time()
    big = omega_array(6 * M_PHASE + 1)
    m = np.arange(1, M_PHASE + 1, dtype=np.int64)
    OL = big[6 * m - 1].astype(np.int32)
    OR = big[6 * m + 1].astype(np.int32)
    surv_m = survivor_mask(M_PHASE, A_FOIL)[m]
    print(f"[build] Omega array to {6 * M_PHASE + 1} + survivor mask A={A_FOIL} "
          f"in {time.time() - t0:.1f}s")

    phase_verification(m)
    interference_factors(m)
    crt_beats()
    foil_section(OL, OR, surv_m)
    corner_section(OL, OR)

    print(f"\ndone in {time.time() - t0:.1f}s.")


if __name__ == "__main__":
    main()
