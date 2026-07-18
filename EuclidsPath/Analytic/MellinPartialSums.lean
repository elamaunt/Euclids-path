/-
  Analytic/MellinPartialSums — STAGE P-B1 of the Tauberian campaign: the
  MELLIN REPRESENTATIONS of the arithmetic partial sums, ready for the
  Newman interface.

  Contents: the restricted Chebyshev function `psiRes a x` (the partial
  sums of the von Mangoldt function on a residue class) with its
  monotonicity/positivity/Chebyshev bounds, its Mellin representation
  `L(Λ·1_a, s) = s·∫_1^∞ psiRes·t^{−s−1}` (the pin's
  `LSeries_eq_mul_integral_of_nonneg`), the twisted-Liouville analogue,
  and the PUBLIC integrability mirror of SumCoeff's private `lemma₁`
  (partial sums `O(n)` ⟹ the Mellin integrand is integrable on `(1,∞)`).

  DISCLOSURES.
    * Infrastructure over the pin's L-series frame: no face of the
      parity wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex ArithmeticFunction Filter MeasureTheory Set Finset
open scoped LSeries.notation

/-! ### The restricted Chebyshev function -/

/-- The partial sums of the von Mangoldt function on the residue class
`a` mod `q`: the restricted Chebyshev function. -/
noncomputable def psiRes {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass a n

theorem psiRes_nonneg {q : ℕ} (a : ZMod q) (x : ℝ) : 0 ≤ psiRes a x :=
  Finset.sum_nonneg fun n _ => vonMangoldt.residueClass_nonneg a n

theorem psiRes_mono {q : ℕ} (a : ZMod q) {x y : ℝ} (hxy : x ≤ y) :
    psiRes a x ≤ psiRes a y :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy))
    (fun n _ _ => vonMangoldt.residueClass_nonneg a n)

theorem psiRes_le_psi {q : ℕ} (a : ZMod q) (x : ℝ) :
    psiRes a x ≤ Chebyshev.psi x := by
  unfold psiRes Chebyshev.psi
  rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
  exact Finset.sum_le_sum fun n _ => vonMangoldt.residueClass_le a n

theorem psiRes_le_linear {q : ℕ} (a : ZMod q) {x : ℝ} (hx : 0 ≤ x) :
    psiRes a x ≤ (Real.log 4 + 4) * x :=
  le_trans (psiRes_le_psi a x) (Chebyshev.psi_le_const_mul_self hx)

/-- The `O(n)` bound on the natural-number partial sums. -/
theorem isBigO_psiRes {q : ℕ} (a : ZMod q) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, vonMangoldt.residueClass a k)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hsum : ∑ k ∈ Finset.Icc 1 n, vonMangoldt.residueClass a k
      = psiRes a (n : ℝ) := by
    unfold psiRes
    rw [Nat.floor_natCast]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hsum,
    abs_of_nonneg (psiRes_nonneg a _), Real.rpow_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  exact psiRes_le_linear a (by positivity)

/-! ### The Mellin representations -/

/-- **The Mellin representation of the restricted L-series**:
`L(Λ·1_a, s) = s·∫_1^∞ psiRes(a,t)·t^{−s−1} dt` for `Re s > 1`. -/
theorem LSeries_residueClass_eq_mul_integral {q : ℕ} (a : ZMod q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ↗(vonMangoldt.residueClass a) s
      = s * ∫ t in Set.Ioi (1 : ℝ),
          ((psiRes a t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg (vonMangoldt.residueClass a)
    (r := 1) zero_le_one hs (isBigO_psiRes a)
    (vonMangoldt.residueClass_nonneg a)
  rw [show (↗(vonMangoldt.residueClass a) : ℕ → ℂ)
      = fun n => ((vonMangoldt.residueClass a n : ℝ) : ℂ) from rfl, h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  congr 1
  unfold psiRes
  push_cast
  rfl

/-- The Mellin representation of the χ-twisted Liouville L-series
(`|χ·λ| ≤ 1` gives the crude `O(n)` bound). -/
theorem LSeries_twist_liouville_eq_mul_integral {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n * (ArithmeticFunction.liouville n : ℂ)) s
      = s * ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
            χ k * (ArithmeticFunction.liouville k : ℂ))
            * (t : ℂ) ^ (-(s + 1)) := by
  refine LSeries_eq_mul_integral' _ (r := 1) zero_le_one hs ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, one_mul,
    abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  calc ∑ k ∈ Finset.Icc 1 n, ‖χ k * (ArithmeticFunction.liouville k : ℂ)‖
      ≤ ∑ _ ∈ Finset.Icc 1 n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [norm_mul]
        have hk0 : k ≠ 0 := by
          have := (Finset.mem_Icc.mp hk).1
          omega
        have h1 : ‖((ArithmeticFunction.liouville k : ℤ) : ℂ)‖ ≤ 1 := by
          rw [ArithmeticFunction.liouville_apply hk0]
          push_cast
          rw [norm_pow, norm_neg, norm_one, one_pow]
        calc ‖χ k‖ * ‖((ArithmeticFunction.liouville k : ℤ) : ℂ)‖
            ≤ 1 * 1 := mul_le_mul (χ.norm_le_one k) h1 (norm_nonneg _)
              zero_le_one
          _ = 1 := one_mul 1
    _ = (n : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp

/-! ### The public integrability mirror of SumCoeff's `lemma₁` -/

/-- Partial sums `O(n)` make the Mellin integrand integrable on `(1,∞)`
for every exponent with `Re w > 1`. -/
theorem integrableOn_partialSum_mul_cpow {f : ℕ → ℂ}
    (hO : (fun n => ∑ k ∈ Finset.Icc 1 n, f k)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ))
    {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn
      (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-w - 1))
      (Set.Ioi 1) := by
  refine IntegrableOn.mono_set ?_ Set.Ioi_subset_Ici_self
  have h₁ : LocallyIntegrableOn
      (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-w - 1))
      (Set.Ici 1) := by
    simp_rw [mul_comm]
    refine locallyIntegrableOn_mul_sum_Icc f zero_le_one ?_
    refine ContinuousOn.locallyIntegrableOn (fun t ht => ?_) measurableSet_Ici
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  have h₂ : (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k)
      =O[atTop] fun t : ℝ => t ^ (1 : ℝ) :=
    (hO.comp_tendsto tendsto_nat_floor_atTop).trans
      (Asymptotics.isEquivalent_nat_floor.isBigO.rpow zero_le_one (eventually_ge_atTop 0))
  refine h₁.integrableOn_of_isBigO_atTop (g := fun t => t ^ (-w.re)) ?_ ?_
  · refine Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow 1 (-w.re - 1) _
      h₂ ?_ (by linarith)
    have h := (norm_ofReal_cpow_eventually_eq_atTop (-w - 1)).isBigO.of_norm_left
    simpa [Complex.sub_re, Complex.neg_re, Complex.one_re] using h
  · rw [integrableAtFilter_rpow_atTop_iff]
    linarith

end Analytic
end EuclidsPath
