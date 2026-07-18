/-
  Engine/GeometricTypeIIMertensDifference — STAGE L-M2 of the Tauberian
  campaign: THE PARAMETRIC MERTENS DIFFERENCE UPPER BOUND.

  For any pointwise Chebyshev cap `θ(u) ≤ c·u` on `[s, t]`,

      Σ_{s < p ≤ t} 1/p  ≤  c·log(log t / log s) + 2c/log s.

  This is the honesty hinge of the landing: the crown needs ONLY this
  one-sided difference (an upper bound on the rung slice sums), and the
  pin's unconditional `θ(x) ≤ log 4·x` closes it with `c = log 4` — no
  Mertens asymptotic, no lower Chebyshev.  The Abel layer of the house
  Mertens module (`GeometricTypeIIBrunTwinMertensUpper`) is `private`
  there and is RE-DERIVED here in difference-ready parametric form
  (recorded, not imported).

  DISCLOSURES.
    * One-sided bound only; the constant `c·log 4` grade is NOT the true
      Mertens constant (not claimed, not needed).
    * No face of the parity wall is touched, and no §110 event is
      claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open Finset MeasureTheory

/-! ### Layer 1: the prime-log sequence (public re-derivation) -/

/-- `log p` at primes, `0` elsewhere; partial sums = Chebyshev θ. -/
noncomputable def primeLogSeqD (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

theorem primeLogSeqD_zero : primeLogSeqD 0 = 0 := by
  simp [primeLogSeqD, Nat.not_prime_zero]

theorem primeLogSeqD_one : primeLogSeqD 1 = 0 := by
  simp [primeLogSeqD, Nat.not_prime_one]

theorem sum_primeLogSeqD_eq_theta (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeqD k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  exact Finset.sum_congr rfl fun k _ => rfl

/-! ### Layer 2: the Abel weight and its derivative -/

/-- The Abel weight `(t·log t)⁻¹`. -/
noncomputable def invMulLogD (t : ℝ) : ℝ := (t * Real.log t)⁻¹

theorem hasDerivAt_invMulLogD {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt invMulLogD (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t :=
    Real.hasDerivAt_mul_log ht0.ne'
  exact h1.inv (mul_ne_zero ht0.ne' hlogt.ne')

theorem deriv_invMulLogD {t : ℝ} (ht : 2 ≤ t) :
    deriv invMulLogD t = -(Real.log t + 1) / (t * Real.log t) ^ 2 :=
  (hasDerivAt_invMulLogD ht).deriv

theorem integrableOn_deriv_invMulLogD {x : ℝ} :
    IntegrableOn (deriv invMulLogD) (Set.Icc 2 x) := by
  have hsub : Set.Icc (2 : ℝ) x ⊆ {(0 : ℝ)}ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have h2 := ht.1
    intro h
    rw [h] at h2
    norm_num at h2
  have hlogc : ContinuousOn Real.log (Set.Icc 2 x) :=
    Real.continuousOn_log.mono hsub
  have hint : IntegrableOn
      (fun t : ℝ => -(Real.log t + 1) / (t * Real.log t) ^ 2)
      (Set.Icc 2 x) := by
    refine (ContinuousOn.div ((hlogc.add continuousOn_const).neg)
      ((continuous_id.continuousOn.mul hlogc).pow 2) ?_).integrableOn_Icc
    intro t ht
    have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
    have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by
      have := ht.1; linarith)
    exact pow_ne_zero 2 (mul_ne_zero ht0.ne' hlogt.ne')
  exact hint.congr_fun (fun t ht => (deriv_invMulLogD ht.1).symm)
    measurableSet_Icc

/-! ### Layer 3: the Abel identity for prime-reciprocal partial sums -/

theorem sum_primesLE_inv_abelD {x : ℝ} (_hx : 2 ≤ x) :
    ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹
      = invMulLogD x * Chebyshev.theta x
        - ∫ t in Set.Ioc (2 : ℝ) x,
            deriv invMulLogD t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeqD k := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ invMulLogD t :=
    fun t ht => (hasDerivAt_invMulLogD ht.1).differentiableAt
  have habel := sum_mul_eq_sub_integral_mul₁ primeLogSeqD primeLogSeqD_zero
    primeLogSeqD_one x hdiff integrableOn_deriv_invMulLogD
  calc ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹
      = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, invMulLogD k * primeLogSeqD k := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hp : k.Prime
        · have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hp.one_lt
          have hlog : Real.log (k : ℝ) ≠ 0 := (Real.log_pos hk1).ne'
          rw [if_pos hp, show primeLogSeqD k = Real.log k by
            simp [primeLogSeqD, hp], invMulLogD, mul_inv, mul_assoc,
            inv_mul_cancel₀ hlog, mul_one]
        · rw [if_neg hp, show primeLogSeqD k = 0 by
            simp [primeLogSeqD, hp], mul_zero]
    _ = invMulLogD x * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, primeLogSeqD k)
        - ∫ t in Set.Ioc (2 : ℝ) x,
            deriv invMulLogD t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeqD k :=
      habel
    _ = _ := by rw [sum_primeLogSeqD_eq_theta]

/-! ### Layer 4: the parametric antiderivative -/

theorem hasDerivAt_logLogD {c t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun s : ℝ => c * (Real.log (Real.log s) - (Real.log s)⁻¹))
      (c * ((Real.log t + 1) / (t * Real.log t ^ 2))) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have h1 : HasDerivAt (fun s : ℝ => Real.log (Real.log s))
      (t⁻¹ / Real.log t) t :=
    (Real.hasDerivAt_log ht0.ne').log hlogt.ne'
  have h2 : HasDerivAt (fun s : ℝ => (Real.log s)⁻¹)
      (-t⁻¹ / Real.log t ^ 2) t :=
    (Real.hasDerivAt_log ht0.ne').inv hlogt.ne'
  have h3 := (h1.sub h2).const_mul c
  have h4 : c * (t⁻¹ / Real.log t - -t⁻¹ / Real.log t ^ 2)
      = c * ((Real.log t + 1) / (t * Real.log t ^ 2)) := by
    field_simp
    ring
  exact h4 ▸ h3

theorem continuousOn_majorantD {c s x : ℝ} (hs : 2 ≤ s) :
    ContinuousOn (fun t : ℝ => c * ((Real.log t + 1) / (t * Real.log t ^ 2)))
      (Set.Icc s x) := by
  have hsub : Set.Icc s x ⊆ {(0 : ℝ)}ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have h2 := ht.1
    intro h
    rw [h] at h2
    linarith
  have hlogc : ContinuousOn Real.log (Set.Icc s x) :=
    Real.continuousOn_log.mono hsub
  refine continuousOn_const.mul (ContinuousOn.div
    (hlogc.add continuousOn_const)
    (continuous_id.continuousOn.mul (hlogc.pow 2)) ?_)
  intro t ht
  have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by
    have := ht.1; linarith)
  exact (mul_pos ht0 (pow_pos hlogt 2)).ne'

theorem integral_majorantD_eq {c s x : ℝ} (hs : 2 ≤ s) (hsx : s ≤ x) :
    ∫ t in s..x, c * ((Real.log t + 1) / (t * Real.log t ^ 2))
      = c * (Real.log (Real.log x) - (Real.log x)⁻¹)
        - c * (Real.log (Real.log s) - (Real.log s)⁻¹) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => c * (Real.log (Real.log u) - (Real.log u)⁻¹))
    (fun t ht => ?_) ?_
  · rw [Set.uIcc_of_le hsx] at ht
    exact hasDerivAt_logLogD (le_trans hs ht.1)
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hsx]
    exact continuousOn_majorantD hs

/-! ### Layer 5: THE PARAMETRIC MERTENS DIFFERENCE -/

/-- **THE PARAMETRIC MERTENS DIFFERENCE UPPER**: a pointwise Chebyshev
cap `θ(u) ≤ c·u` on `[s, t]` caps the prime-reciprocal sum over the
slice `(⌊s⌋, ⌊t⌋]` by `c·log(log t/log s) + 2c/log s`. -/
theorem sum_inv_primes_Ioc_le {s t c : ℝ} (hs : 2 ≤ s) (hst : s ≤ t)
    (hc : 0 ≤ c)
    (hθ : ∀ u : ℝ, s ≤ u → u ≤ t → Chebyshev.theta u ≤ c * u) :
    ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹
      ≤ c * Real.log (Real.log t / Real.log s) + 2 * c / Real.log s := by
  have ht2 : (2 : ℝ) ≤ t := le_trans hs hst
  have hs0 : (0 : ℝ) < s := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogs : (0 : ℝ) < Real.log s := Real.log_pos (by linarith)
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hfl : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hst
  -- the slice sum as a difference of prefix sums
  have hsplitSum : ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹
      = (∑ p ∈ (Finset.Icc 0 ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹)
        - ∑ p ∈ (Finset.Icc 0 ⌊s⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹ := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_union ?_]
    · congr 1
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc,
        Finset.mem_Icc]
      constructor
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨_, h2⟩, hp⟩)
        · exact ⟨⟨Nat.zero_le _, h2⟩, hp⟩
        · exact ⟨⟨Nat.zero_le _, le_trans h2 hfl⟩, hp⟩
      · rintro ⟨⟨_, h2⟩, hp⟩
        by_cases hps : p ≤ ⌊s⌋₊
        · exact Or.inr ⟨⟨Nat.zero_le _, hps⟩, hp⟩
        · exact Or.inl ⟨⟨by omega, h2⟩, hp⟩
    · rw [Finset.disjoint_left]
      intro p hp hp'
      have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp').1).2
      omega
  -- integrability of the Abel integrand pieces
  have hInt : ∀ y : ℝ, IntegrableOn
      (fun u : ℝ => deriv invMulLogD u
        * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k) (Set.Icc 2 y) :=
    fun y => integrableOn_mul_sum_Icc (c := primeLogSeqD) (m := 0)
      (by norm_num : (0 : ℝ) ≤ 2) integrableOn_deriv_invMulLogD
  -- the integral splits at s
  have hIocSplit : ∫ u in Set.Ioc (2 : ℝ) t,
      deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k
      = (∫ u in Set.Ioc (2 : ℝ) s,
          deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k)
        + ∫ u in Set.Ioc s t,
            deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc
      (((hInt s).mono_set Set.Ioc_subset_Icc_self))
      (((hInt t).mono_set (Set.Ioc_subset_Icc_self.trans
        (Set.Icc_subset_Icc hs le_rfl)))),
      Set.Ioc_union_Ioc_eq_Ioc hs hst]
  -- assemble the difference identity
  rw [hsplitSum, sum_primesLE_inv_abelD ht2, sum_primesLE_inv_abelD hs,
    hIocSplit]
  -- bound the three surviving pieces
  have hb1 : invMulLogD t * Chebyshev.theta t ≤ c / Real.log t := by
    have hθt := hθ t hst le_rfl
    have hfpos : (0 : ℝ) ≤ invMulLogD t := by
      rw [invMulLogD]
      exact inv_nonneg.mpr (mul_pos ht0 hlogt).le
    have h1 : invMulLogD t * Chebyshev.theta t
        ≤ invMulLogD t * (c * t) := mul_le_mul_of_nonneg_left hθt hfpos
    have h2 : invMulLogD t * (c * t) = c / Real.log t := by
      rw [invMulLogD, mul_inv]
      field_simp
    linarith
  have hb2 : (0 : ℝ) ≤ invMulLogD s * Chebyshev.theta s := by
    apply mul_nonneg
    · rw [invMulLogD]
      exact inv_nonneg.mpr (mul_pos hs0 hlogs).le
    · exact Chebyshev.theta_nonneg s
  have hb3 : -(∫ u in Set.Ioc s t,
      deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k)
      ≤ c * (Real.log (Real.log t) - (Real.log t)⁻¹)
        - c * (Real.log (Real.log s) - (Real.log s)⁻¹) := by
    rw [show (∫ u in Set.Ioc s t,
        deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k)
      = ∫ u in s..t,
        deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k
      from (intervalIntegral.integral_of_le hst).symm,
      ← intervalIntegral.integral_neg, ← integral_majorantD_eq hs hst]
    refine intervalIntegral.integral_mono_on hst ?_ ?_ ?_
    · have h' : IntegrableOn
          (fun u : ℝ => deriv invMulLogD u
            * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k) (Set.uIcc s t) := by
        rw [Set.uIcc_of_le hst]
        exact (hInt t).mono_set (Set.Icc_subset_Icc hs le_rfl)
      exact h'.intervalIntegrable.neg
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hst]
      exact continuousOn_majorantD hs
    · intro u hu
      have hu2 : (2 : ℝ) ≤ u := le_trans hs hu.1
      have hu0 : (0 : ℝ) < u := by linarith
      have hlogu : (0 : ℝ) < Real.log u := Real.log_pos (by linarith)
      rw [deriv_invMulLogD hu2, sum_primeLogSeqD_eq_theta]
      rw [neg_div, neg_mul, neg_neg]
      have hθu := hθ u hu.1 hu.2
      have hcoef : (0 : ℝ) ≤ (Real.log u + 1) / (u * Real.log u) ^ 2 := by
        have hnum : (0 : ℝ) ≤ Real.log u + 1 := by linarith
        positivity
      calc (Real.log u + 1) / (u * Real.log u) ^ 2 * Chebyshev.theta u
          ≤ (Real.log u + 1) / (u * Real.log u) ^ 2 * (c * u) :=
            mul_le_mul_of_nonneg_left hθu hcoef
        _ = c * ((Real.log u + 1) / (u * Real.log u ^ 2)) := by
            field_simp
  -- final arithmetic: loglog t − loglog s = log(log t/log s); slack 2c/log s
  have hloglog : Real.log (Real.log t) - Real.log (Real.log s)
      = Real.log (Real.log t / Real.log s) :=
    (Real.log_div hlogt.ne' hlogs.ne').symm
  have hlt : c / Real.log t ≤ c / Real.log s := by
    apply div_le_div_of_nonneg_left hc hlogs
    exact Real.log_le_log (by linarith) hst
  have hloglogc : c * Real.log (Real.log t) - c * Real.log (Real.log s)
      = c * Real.log (Real.log t / Real.log s) := by
    rw [← hloglog]
    ring
  have hcancel : (∫ u in Set.Ioc (2 : ℝ) s,
      deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k)
      = ∫ t in Set.Ioc (2 : ℝ) s,
          deriv invMulLogD t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeqD k := rfl
  have hIeq : (∫ u in Set.Ioc (2 : ℝ) s,
      deriv invMulLogD u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, primeLogSeqD k)
      = ∫ t in Set.Ioc (2 : ℝ) s,
          deriv invMulLogD t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogSeqD k := rfl
  rw [← hIeq]
  have hdiv : c / Real.log t = c * (Real.log t)⁻¹ := by ring
  have hdiv2 : (2 : ℝ) * c / Real.log s = 2 * (c * (Real.log s)⁻¹) := by ring
  have hzero : 0 ≤ c * (Real.log s)⁻¹ := by positivity
  rw [hdiv2]
  rw [hdiv] at hb1
  linarith [hb1, hb2, hb3, hloglogc, hzero]

/-- The `log 4` instantiation — fully unconditional from the pin. -/
theorem sum_inv_primes_Ioc_le_log4 {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹
      ≤ Real.log 4 * Real.log (Real.log t / Real.log s)
        + 2 * Real.log 4 / Real.log s := by
  refine sum_inv_primes_Ioc_le hs hst
    (Real.log_nonneg (by norm_num)) fun u hu _ => ?_
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have := Chebyshev.theta_le_log4_mul_x hu0
  linarith

end TypeII
end Geometric
end EuclidsPath
