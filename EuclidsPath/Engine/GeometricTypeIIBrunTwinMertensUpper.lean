/-
  GeometricTypeIIBrunTwinMertensUpper — MERTENS' SECOND THEOREM, UPPER FORM:

      Σ_{p ≤ x} 1/p  ≤  log 4 · log log x + log 4 · (1/log 2 − log log 2)     (x ≥ 2)

  and its sieve-ready corollary

      Σ_{p ∈ sievePrimes z} 2/p  ≤  3 · log log z + 6                        (z ≥ 3).

  ORIGIN.  Autonomous continuation (stage 4b-A of the Brun track).  The
  stage-4a rate has denominator log²z; running the sieve at large z (the true
  Brun regime) requires the TRUNCATED sieve, whose error control needs an
  UPPER bound on Σ 1/p over the sieve primes — this module supplies it.
  Design adversarially verified (4b pre-pass), fallback Route A chosen at
  implementation time: the classical Legendre/factorial route to Mertens'
  first theorem is skipped entirely; instead Chebyshev's bound θ(x) ≤ x·log 4
  (IN THE PIN: `Chebyshev.theta_le_log4_mul_x`) is fed directly into Abel
  summation (IN THE PIN: `sum_mul_eq_sub_integral_mul₁`).  Cost: the leading
  constant is log 4 ≈ 1.386 instead of the optimal 1 — irrelevant for the
  stage-4b shape, which only needs SOME explicit constant.

  THE ROUTE (four moves, all against pin API):
    1. `c k := if k.Prime then log k else 0` has partial sums exactly θ(t)
       (`Chebyshev.theta_eq_sum_Icc`), and against the weight
       `f t := (t·log t)⁻¹` the summands `f k · c k` are exactly 1/p.
    2. Abel summation:  Σ_{p ≤ ⌊x⌋} 1/p = θ(x)/(x·log x) − ∫₂ˣ f′(t)·θ(t) dt,
       with f′(t) = −(log t + 1)/(t·log t)².
    3. θ(t) ≤ t·log 4 pointwise makes the integrand at most
       log 4 · (log t + 1)/(t·log²t), whose EXACT antiderivative is
       log 4 · (log log t − 1/log t); the boundary term θ(x)/(x·log x) ≤
       log 4/log x cancels the −log 4/log x from the antiderivative EXACTLY.
    4. Numeric closing of the constant (`Real.log_two_gt_d9` etc.) gives the
       rounded sieve corollary with constants 3 and 6.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `sum_primesLE_inv_abel` — the exact Abel identity for Σ 1/p against θ;
    * `sum_primesLE_inv_le` — **MERTENS UPPER**: the display above, explicit
      constant `log 4 · (1/log 2 − log log 2) ≈ 2.509`;
    * `sievePrimes_sum_inv_le` — the same over the twin-sieve prime set;
    * `sievePrimes_sum_two_div_le` — the rounded form Σ 2/p ≤ 3·loglog z + 6,
      the exact input shape for the stage-4b truncated error control.

  NUMERIC GROUNDING (4b pre-pass): at z = 10⁶ the true Σ_{p≤z} 1/p = 3.068;
  the bound gives log4·loglog(10⁶) + 2.509 = 5.16 — valid, slack ≈ 1.7×, as
  designed (the constant is NOT claimed optimal; Mertens' 1874 constant is
  loglog + M, M ≈ 0.2615 — NOT claimed).

  DISCLOSURES.
    * This is INFRASTRUCTURE for stage 4b, NOT a §110 event: no annihilation,
      no summability gain, no dimension reduction on any registered target.
      The parity wall (CRE / OneWingTarget / LowFreqRootCoherence /
      SemiprimeShortRestriction / HigherConductorDispersion) is UNTOUCHED.
    * The constant log 4 comes from Chebyshev, not PNT; nothing here needs or
      claims prime counting asymptotics.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIBrunTwin

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open Finset MeasureTheory

/-! ### Layer 1: the prime-log sequence and its partial sums (= Chebyshev θ) -/

/-- The sequence fed to Abel summation: `log p` at primes, `0` elsewhere.
Its partial sums over `Icc 0 ⌊t⌋₊` are exactly Chebyshev's `θ t`. -/
private noncomputable def primeLogSeq (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

private lemma primeLogSeq_apply (n : ℕ) :
    primeLogSeq n = if n.Prime then Real.log n else 0 := rfl

private lemma primeLogSeq_zero : primeLogSeq 0 = 0 := by
  simp [primeLogSeq_apply, Nat.not_prime_zero]

private lemma primeLogSeq_one : primeLogSeq 1 = 0 := by
  simp [primeLogSeq_apply, Nat.not_prime_one]

/-- Partial sums of `primeLogSeq` are Chebyshev's θ. -/
private lemma sum_primeLogSeq_eq_theta (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeq k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  exact Finset.sum_congr rfl fun k _ => by rw [primeLogSeq_apply]

/-! ### Layer 2: the Abel weight `(t·log t)⁻¹` and its derivative -/

/-- The Abel weight: `f t = (t·log t)⁻¹`, so that `f p · log p = 1/p`. -/
private noncomputable def invMulLog (t : ℝ) : ℝ := (t * Real.log t)⁻¹

private lemma invMulLog_apply (t : ℝ) : invMulLog t = (t * Real.log t)⁻¹ := rfl

private lemma hasDerivAt_invMulLog {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt invMulLog (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t :=
    Real.hasDerivAt_mul_log ht0.ne'
  exact h1.inv (mul_ne_zero ht0.ne' hlogt.ne')

private lemma deriv_invMulLog {t : ℝ} (ht : 2 ≤ t) :
    deriv invMulLog t = -(Real.log t + 1) / (t * Real.log t) ^ 2 :=
  (hasDerivAt_invMulLog ht).deriv

/-- The explicit derivative shape is continuous on `[2, x]`. -/
private lemma continuousOn_derivShape {x : ℝ} :
    ContinuousOn (fun t : ℝ => -(Real.log t + 1) / (t * Real.log t) ^ 2)
      (Set.Icc 2 x) := by
  have hsub : Set.Icc (2 : ℝ) x ⊆ {(0 : ℝ)}ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have h2 := ht.1
    intro h
    rw [h] at h2
    norm_num at h2
  have hlogc : ContinuousOn Real.log (Set.Icc 2 x) := Real.continuousOn_log.mono hsub
  refine ContinuousOn.div ((hlogc.add continuousOn_const).neg)
    ((continuous_id.continuousOn.mul hlogc).pow 2) ?_
  intro t ht
  have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by have := ht.1; linarith)
  exact pow_ne_zero 2 (mul_ne_zero ht0.ne' hlogt.ne')

private lemma integrableOn_deriv_invMulLog {x : ℝ} (_hx : 2 ≤ x) :
    IntegrableOn (deriv invMulLog) (Set.Icc 2 x) := by
  have hint : IntegrableOn (fun t : ℝ => -(Real.log t + 1) / (t * Real.log t) ^ 2)
      (Set.Icc 2 x) := continuousOn_derivShape.integrableOn_Icc
  exact hint.congr_fun (fun t ht => (deriv_invMulLog ht.1).symm) measurableSet_Icc

/-! ### Layer 3: the Abel identity for Σ 1/p -/

/-- **The Abel identity.**  For `x ≥ 2`,
`Σ_{p ≤ ⌊x⌋} 1/p = θ(x)/(x·log x) − ∫₂ˣ (invMulLog)′(t)·θ(t) dt`
(with the integrand kept in partial-sum form, ready for the integral bound). -/
private lemma sum_primesLE_inv_abel {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ))⁻¹
      = invMulLog x * Chebyshev.theta x
        - ∫ t in Set.Ioc (2 : ℝ) x,
            deriv invMulLog t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeq k := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ invMulLog t :=
    fun t ht => (hasDerivAt_invMulLog ht.1).differentiableAt
  have habel := sum_mul_eq_sub_integral_mul₁ primeLogSeq primeLogSeq_zero
    primeLogSeq_one x hdiff (integrableOn_deriv_invMulLog hx)
  calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ))⁻¹
      = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, invMulLog k * primeLogSeq k := by
        rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hp : k.Prime
        · have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hp.one_lt
          have hlog : Real.log (k : ℝ) ≠ 0 := (Real.log_pos hk1).ne'
          rw [if_pos hp, primeLogSeq_apply, if_pos hp, invMulLog_apply, mul_inv,
            mul_assoc, inv_mul_cancel₀ hlog, mul_one]
        · rw [if_neg hp, primeLogSeq_apply, if_neg hp, mul_zero]
    _ = invMulLog x * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, primeLogSeq k)
        - ∫ t in Set.Ioc (2 : ℝ) x,
            deriv invMulLog t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeq k := habel
    _ = _ := by rw [sum_primeLogSeq_eq_theta]

/-! ### Layer 4: the exact antiderivative of the majorant -/

/-- `log 4 · (log log t − 1/log t)` is an exact antiderivative of the
majorant `log 4 · (log t + 1)/(t·log²t)`. -/
private lemma hasDerivAt_logLog {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun s : ℝ => Real.log 4 * (Real.log (Real.log s) - (Real.log s)⁻¹))
      (Real.log 4 * ((Real.log t + 1) / (t * Real.log t ^ 2))) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have h1 : HasDerivAt (fun s : ℝ => Real.log (Real.log s)) (t⁻¹ / Real.log t) t :=
    (Real.hasDerivAt_log ht0.ne').log hlogt.ne'
  have h2 : HasDerivAt (fun s : ℝ => (Real.log s)⁻¹) (-t⁻¹ / Real.log t ^ 2) t :=
    (Real.hasDerivAt_log ht0.ne').inv hlogt.ne'
  have h3 := (h1.sub h2).const_mul (Real.log 4)
  have h4 : Real.log 4 * (t⁻¹ / Real.log t - -t⁻¹ / Real.log t ^ 2)
      = Real.log 4 * ((Real.log t + 1) / (t * Real.log t ^ 2)) := by
    field_simp
    ring
  exact h4 ▸ h3

/-- The majorant is continuous on `[2, x]`. -/
private lemma continuousOn_majorant {x : ℝ} :
    ContinuousOn (fun t : ℝ => Real.log 4 * ((Real.log t + 1) / (t * Real.log t ^ 2)))
      (Set.Icc 2 x) := by
  have hsub : Set.Icc (2 : ℝ) x ⊆ {(0 : ℝ)}ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have h2 := ht.1
    intro h
    rw [h] at h2
    norm_num at h2
  have hlogc : ContinuousOn Real.log (Set.Icc 2 x) := Real.continuousOn_log.mono hsub
  refine continuousOn_const.mul (ContinuousOn.div (hlogc.add continuousOn_const)
    (continuous_id.continuousOn.mul (hlogc.pow 2)) ?_)
  intro t ht
  have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by have := ht.1; linarith)
  exact (mul_pos ht0 (pow_pos hlogt 2)).ne'

/-- Exact evaluation of the majorant integral by the fundamental theorem. -/
private lemma integral_majorant_eq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, Real.log 4 * ((Real.log t + 1) / (t * Real.log t ^ 2))
      = Real.log 4 * (Real.log (Real.log x) - (Real.log x)⁻¹)
        - Real.log 4 * (Real.log (Real.log 2) - (Real.log 2)⁻¹) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Real.log 4 * (Real.log (Real.log s) - (Real.log s)⁻¹))
    (fun t ht => ?_) ?_
  · rw [Set.uIcc_of_le hx] at ht
    exact hasDerivAt_logLog ht.1
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx]
    exact continuousOn_majorant

/-! ### Layer 5: MERTENS UPPER -/

/-- **Mertens' second theorem, upper form** (machine-checked, explicit
constant):  for all real `x ≥ 2`,

`Σ_{p ≤ ⌊x⌋} 1/p  ≤  log 4 · log log x + log 4 · (1/log 2 − log log 2)`.

The leading constant `log 4 ≈ 1.386` comes from Chebyshev's `θ(x) ≤ x·log 4`;
the boundary term of Abel summation cancels the `−1/log x` of the exact
antiderivative, so no `o(1)` bookkeeping is needed. -/
theorem sum_primesLE_inv_le {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ))⁻¹
      ≤ Real.log 4 * Real.log (Real.log x)
        + Real.log 4 * ((Real.log 2)⁻¹ - Real.log (Real.log 2)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  rw [sum_primesLE_inv_abel hx,
    show (∫ t in Set.Ioc (2 : ℝ) x,
        deriv invMulLog t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeq k)
      = ∫ t in (2 : ℝ)..x,
        deriv invMulLog t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeq k
    from (intervalIntegral.integral_of_le hx).symm]
  -- Boundary term: θ(x)/(x·log x) ≤ log 4 / log x.
  have hbdry : invMulLog x * Chebyshev.theta x ≤ Real.log 4 * (Real.log x)⁻¹ := by
    have hθ := Chebyshev.theta_le_log4_mul_x hx0.le
    have hfpos : (0 : ℝ) ≤ invMulLog x := by
      rw [invMulLog_apply]
      exact inv_nonneg.mpr (mul_pos hx0 hlogx).le
    have h1 : invMulLog x * Chebyshev.theta x ≤ invMulLog x * (Real.log 4 * x) :=
      mul_le_mul_of_nonneg_left hθ hfpos
    have h2 : invMulLog x * (Real.log 4 * x) = Real.log 4 * (Real.log x)⁻¹ := by
      rw [invMulLog_apply, mul_inv]
      field_simp
    linarith
  -- Integral term: −∫ f′·θ ≤ log 4·(loglog x − 1/log x) − log 4·(loglog 2 − 1/log 2).
  have hmono : -(∫ t in (2 : ℝ)..x,
        deriv invMulLog t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeq k)
      ≤ Real.log 4 * (Real.log (Real.log x) - (Real.log x)⁻¹)
        - Real.log 4 * (Real.log (Real.log 2) - (Real.log 2)⁻¹) := by
    rw [← intervalIntegral.integral_neg, ← integral_majorant_eq hx]
    refine intervalIntegral.integral_mono_on hx ?_ ?_ ?_
    · -- integrability of the negated Abel integrand
      have h := integrableOn_mul_sum_Icc (c := primeLogSeq) (m := 0)
        (by norm_num : (0 : ℝ) ≤ 2) (integrableOn_deriv_invMulLog hx)
      have h' : IntegrableOn
          (fun t : ℝ => deriv invMulLog t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeq k)
          (Set.uIcc 2 x) := by
        rw [Set.uIcc_of_le hx]
        exact h
      exact h'.intervalIntegrable.neg
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hx]
      exact continuousOn_majorant
    · intro u hu
      have hu2 : (2 : ℝ) ≤ u := hu.1
      have hu0 : (0 : ℝ) < u := by linarith
      have hlogu : (0 : ℝ) < Real.log u := Real.log_pos (by linarith)
      rw [deriv_invMulLog hu2, sum_primeLogSeq_eq_theta]
      rw [neg_div, neg_mul, neg_neg]
      have hθu := Chebyshev.theta_le_log4_mul_x hu0.le
      have hcoef : (0 : ℝ) ≤ (Real.log u + 1) / (u * Real.log u) ^ 2 := by
        have hnum : (0 : ℝ) ≤ Real.log u + 1 := by linarith
        positivity
      calc (Real.log u + 1) / (u * Real.log u) ^ 2 * Chebyshev.theta u
          ≤ (Real.log u + 1) / (u * Real.log u) ^ 2 * (Real.log 4 * u) :=
            mul_le_mul_of_nonneg_left hθu hcoef
        _ = Real.log 4 * ((Real.log u + 1) / (u * Real.log u ^ 2)) := by
            field_simp
  -- Assemble: the two `1/log x` terms cancel exactly.
  have hexp : Real.log 4 * (Real.log (Real.log x) - (Real.log x)⁻¹)
        - Real.log 4 * (Real.log (Real.log 2) - (Real.log 2)⁻¹)
      = Real.log 4 * Real.log (Real.log x) - Real.log 4 * (Real.log x)⁻¹
        + Real.log 4 * ((Real.log 2)⁻¹ - Real.log (Real.log 2)) := by ring
  linarith [hbdry, hmono, hexp.le, hexp.ge]

/-! ### Layer 6: the sieve-ready corollaries -/

/-- Mertens upper over the twin-sieve prime set (`sievePrimes z ⊆ primesLE z`). -/
theorem sievePrimes_sum_inv_le {z : ℕ} (hz : 2 ≤ z) :
    ∑ p ∈ sievePrimes z, ((p : ℝ))⁻¹
      ≤ Real.log 4 * Real.log (Real.log z)
        + Real.log 4 * ((Real.log 2)⁻¹ - Real.log (Real.log 2)) := by
  have hx : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hmain := sum_primesLE_inv_le hx
  rw [Nat.floor_natCast] at hmain
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hmain
  · intro p hp
    have hp' : p ∈ (Finset.Icc 5 z).filter Nat.Prime := hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp'
    rw [Nat.mem_primesLE]
    exact ⟨hp'.1.2, hp'.2⟩
  · intro i _ _
    positivity

/-- **The stage-4b input** (rounded constants): for `z ≥ 3`,

`Σ_{p ∈ sievePrimes z} 2/p  ≤  3 · log log z + 6`.

This is the exact shape consumed by the truncated-sieve error control
(the `x` in the tail bound `Σ_{j>t} x^j/j! ≤ 2^{−(t+1)}·e^{3x}`). -/
theorem sievePrimes_sum_two_div_le {z : ℕ} (hz : 3 ≤ z) :
    ∑ p ∈ sievePrimes z, 2 / ((p : ℝ)) ≤ 3 * Real.log (Real.log z) + 6 := by
  have h := sievePrimes_sum_inv_le (z := z) (by omega)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  -- log 4 = 2·log 2 ≤ 3/2
  have hlog4 : Real.log 4 ≤ 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hlog4pos : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- 1/log 2 ≤ 3/2
  have hinv : (Real.log 2)⁻¹ ≤ 3 / 2 := by
    have h23 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith
    calc (Real.log 2)⁻¹ ≤ ((2 : ℝ) / 3)⁻¹ := inv_anti₀ (by norm_num) h23
      _ = 3 / 2 := by norm_num
  -- −log log 2 = log (1/log 2) ≤ 1/log 2 − 1 ≤ 1/2
  have hneg : -Real.log (Real.log 2) ≤ 1 / 2 := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hlog2pos)
    rw [Real.log_inv] at hh
    linarith
  have hC0 : (0 : ℝ) ≤ (Real.log 2)⁻¹ - Real.log (Real.log 2) := by
    have hn : Real.log (Real.log 2) < 0 := Real.log_neg hlog2pos (by linarith)
    have hp : (0 : ℝ) < (Real.log 2)⁻¹ := inv_pos.mpr hlog2pos
    linarith
  have hCub : (Real.log 2)⁻¹ - Real.log (Real.log 2) ≤ 2 := by linarith
  -- log log z ≥ 0 for z ≥ 3 > e
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log z) := by
    have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have h1 : (1 : ℝ) ≤ Real.log z := by
      rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (z : ℝ))]
      have := Real.exp_one_lt_d9
      linarith
    exact Real.log_nonneg h1
  have hp1 : Real.log 4 * Real.log (Real.log z) ≤ 3 / 2 * Real.log (Real.log z) :=
    mul_le_mul_of_nonneg_right hlog4 hL0
  have hp2 : Real.log 4 * ((Real.log 2)⁻¹ - Real.log (Real.log 2)) ≤ 3 := by
    calc Real.log 4 * ((Real.log 2)⁻¹ - Real.log (Real.log 2))
        ≤ 3 / 2 * 2 := mul_le_mul hlog4 hCub hC0 (by norm_num)
      _ = 3 := by norm_num
  have hsum : ∑ p ∈ sievePrimes z, 2 / ((p : ℝ))
      = 2 * ∑ p ∈ sievePrimes z, ((p : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => div_eq_mul_inv 2 _
  rw [hsum]
  linarith [h, hp1, hp2]

end TypeII
end Geometric
end EuclidsPath
