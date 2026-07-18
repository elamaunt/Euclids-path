/-
  Analytic/LiouvilleLSeries — STAGE P-D2 of the Tauberian campaign: the
  Dirichlet-series factorization of the twisted Liouville function,
  `L(χλ, s) = L₁(q, 2s)·L(χ, s)⁻¹` for quadratic-squared characters.

  Route (the cheapest, per the campaign design): the D1 convolution
  `(χλ) ⍟ χ = χ·1_sq` multiplies out to
  `L(χλ, s)·L(χ, s) = L(χ·1_sq, s)`, and the right side REINDEXES along
  `m ↦ m²` to `L(χ², 2s)` (an UNCONDITIONAL tsum reindex — the squares
  indicator kills everything off the range).  For the moduli of the
  campaign (`q ∈ {1, 6}`) every character satisfies `χ² = 1`, so the
  numerator is the pole-carrying trivial L-function at `2s` — while the
  denominator is nonvanishing on `Re s ≥ 1`: the analytic input for the
  λ-cancellation (D3/D4).

  DISCLOSURES.
    * L-series bookkeeping over the pin's frame: no face of the parity
      wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Analytic.LiouvilleConvolution

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex ArithmeticFunction Filter DirichletCharacter
open scoped LSeries.notation

/-! ### The reindex `m ↦ m²` -/

/-- **The square reindex** (unconditional): the L-series of `χ·1_sq` at
`s` is the L-series of `χ²` at `2s`. -/
theorem LSeries_char_mul_sqIndicator {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) :
    LSeries ((↗χ : ℕ → ℂ) * fun n => sqIndicator n) s
      = LSeries ↗(χ ^ 2) (2 * s) := by
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) :=
    Nat.pow_left_injective (by norm_num)
  have hsupp : Function.support
      (LSeries.term ((↗χ : ℕ → ℂ) * fun n => sqIndicator n) s)
      ⊆ Set.range (fun m : ℕ => m ^ 2) := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hn
    · rw [Function.mem_support, LSeries.term_of_ne_zero hn0] at hn
      have hsq : sqIndicator n ≠ 0 := by
        intro h0
        apply hn
        rw [Pi.mul_apply]
        show ↗χ n * sqIndicator n / (n : ℂ) ^ s = 0
        rw [h0, mul_zero, zero_div]
      rw [sqIndicator_apply] at hsq
      by_cases hcond : IsSquare n ∧ n ≠ 0
      · obtain ⟨⟨r, hr⟩, _⟩ := hcond
        exact ⟨r, by rw [hr]; ring⟩
      · rw [if_neg hcond] at hsq
        exact absurd rfl hsq
  have hterm : ∀ m : ℕ,
      LSeries.term ((↗χ : ℕ → ℂ) * fun n => sqIndicator n) s (m ^ 2)
        = LSeries.term ↗(χ ^ 2) (2 * s) m := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
      rw [LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm]
      have h1 : sqIndicator (m ^ 2) = 1 := by
        rw [sqIndicator_apply, if_pos ⟨⟨m, pow_two m⟩, hm2⟩]
      have h2 : χ (((m ^ 2 : ℕ) : ZMod q)) = (χ ^ 2) (((m : ℕ) : ZMod q)) := by
        rw [MulChar.pow_apply' χ two_ne_zero]
        push_cast
        rw [map_pow]
      have h3 : ((m ^ 2 : ℕ) : ℂ) ^ s = (m : ℂ) ^ (2 * s) := by
        have := Complex.natCast_cpow_natCast_mul m 2 s
        rw [show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num] at this
        rw [this]
        congr 1
        push_cast
        ring
      rw [Pi.mul_apply, h1, mul_one, h2, h3]
  calc LSeries ((↗χ : ℕ → ℂ) * fun n => sqIndicator n) s
      = ∑' m : ℕ, LSeries.term ((↗χ : ℕ → ℂ) * fun n => sqIndicator n) s
          (m ^ 2) := (hinj.tsum_eq hsupp).symm
    _ = ∑' m : ℕ, LSeries.term ↗(χ ^ 2) (2 * s) m := tsum_congr hterm
    _ = LSeries ↗(χ ^ 2) (2 * s) := rfl

/-! ### The factorization -/

theorem LSeriesSummable_twist_liouville {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ((↗χ : ℕ → ℂ) * ↗ArithmeticFunction.liouville) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) ?_ hs
  intro n hn
  rw [Pi.mul_apply, norm_mul]
  have h1 : ‖((ArithmeticFunction.liouville n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [ArithmeticFunction.liouville_apply hn]
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]
  calc ‖χ n‖ * ‖((ArithmeticFunction.liouville n : ℤ) : ℂ)‖
      ≤ 1 * 1 := mul_le_mul (χ.norm_le_one _) h1 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The product form: `L(χλ, s)·L(χ, s) = L(χ², 2s)` on `Re s > 1`. -/
theorem LSeries_twist_liouville_mul_LSeries {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((↗χ : ℕ → ℂ) * ↗ArithmeticFunction.liouville) s
        * LSeries (↗χ : ℕ → ℂ) s
      = LSeries ↗(χ ^ 2) (2 * s) := by
  rw [← LSeries_char_mul_sqIndicator χ s, ← convolution_twist_liouville χ]
  exact (LSeries_convolution' (LSeriesSummable_twist_liouville χ hs)
    (LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (f := (↗χ : ℕ → ℂ)) (fun n _ => χ.norm_le_one _) hs)).symm

/-! ### Quadratic-squared moduli -/

/-- If every unit of `ZMod q` squares to `1`, every character mod `q`
has `χ² = 1`. -/
theorem sq_eq_one_of_mul_self_eq_one {q : ℕ}
    (hq : ∀ a : ZMod q, IsUnit a → a * a = 1)
    (χ : DirichletCharacter ℂ q) : χ ^ 2 = 1 := by
  apply MulChar.ext
  intro a
  rw [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply_coe]
  have ha : (a : ZMod q) * a = 1 := hq a a.isUnit
  calc χ (a : ZMod q) ^ 2 = χ ((a : ZMod q) * a) := by rw [pow_two, map_mul]
    _ = χ 1 := by rw [ha]
    _ = 1 := map_one χ

theorem sq_eq_one_of_zmod_six (χ : DirichletCharacter ℂ 6) : χ ^ 2 = 1 :=
  sq_eq_one_of_mul_self_eq_one (by decide) χ

theorem sq_eq_one_of_zmod_one (χ : DirichletCharacter ℂ 1) : χ ^ 2 = 1 :=
  sq_eq_one_of_mul_self_eq_one (by decide) χ

/-- Value trichotomy for characters with `χ² = 1`. -/
theorem apply_eq_one_or_neg_one_or_zero {q : ℕ}
    {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ n = 1 ∨ χ n = -1 ∨ χ n = 0 := by
  by_cases hu : IsUnit ((n : ℕ) : ZMod q)
  · have h1 : (χ ^ 2) ((n : ℕ) : ZMod q)
        = (1 : DirichletCharacter ℂ q) ((n : ℕ) : ZMod q) := by rw [hχ]
    rw [MulChar.pow_apply' χ two_ne_zero] at h1
    have hone : (1 : DirichletCharacter ℂ q) ((n : ℕ) : ZMod q) = 1 := by
      rw [← hu.unit_spec]
      exact MulChar.one_apply_coe hu.unit
    rw [hone, pow_two] at h1
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (χ.map_nonunit hu))

/-- **The key holomorphic identity**: for `χ² = 1` and `Re s > 1`,
`L(χλ, s) = L₁(q, 2s)·L(χ, s)⁻¹`. -/
theorem LSeries_twist_liouville_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((↗χ : ℕ → ℂ) * ↗ArithmeticFunction.liouville) s
      = LFunctionTrivChar q (2 * s) * (LFunction χ s)⁻¹ := by
  have h2s : 1 < (2 * s).re := by
    rw [show (2 * s : ℂ).re = 2 * s.re by simp [Complex.mul_re]]
    linarith
  have hne : LSeries (↗χ : ℕ → ℂ) s ≠ 0 := LSeries_ne_zero_of_one_lt_re χ hs
  have hmul := LSeries_twist_liouville_mul_LSeries χ hs
  rw [hχ] at hmul
  have hnum : LSeries ↗(1 : DirichletCharacter ℂ q) (2 * s)
      = LFunctionTrivChar q (2 * s) :=
    (LFunction_eq_LSeries (1 : DirichletCharacter ℂ q) h2s).symm
  have hden : LSeries (↗χ : ℕ → ℂ) s = LFunction χ s :=
    (LFunction_eq_LSeries χ hs).symm
  rw [hnum, hden] at hmul
  rw [hden] at hne
  rw [← hmul, mul_inv_cancel_right₀ hne]

/-- The `q = 1` corollary in ζ-language: `L(λ, s) = ζ(2s)/ζ(s)`. -/
theorem LSeries_liouville_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗ArithmeticFunction.liouville : ℕ → ℂ) s
      = riemannZeta (2 * s) * (riemannZeta s)⁻¹ := by
  have h := LSeries_twist_liouville_eq (1 : DirichletCharacter ℂ 1)
    (sq_eq_one_of_zmod_one 1) hs
  have hone : ((↗(1 : DirichletCharacter ℂ 1) : ℕ → ℂ)
      * ↗ArithmeticFunction.liouville) = ↗ArithmeticFunction.liouville := by
    funext n
    rw [Pi.mul_apply]
    show (1 : DirichletCharacter ℂ 1) ((n : ℕ) : ZMod 1) * _ = _
    rw [Subsingleton.elim ((n : ℕ) : ZMod 1) 1, map_one, one_mul]
  rw [hone] at h
  rw [h]
  congr 1
  · rw [show LFunctionTrivChar 1 = LFunction (1 : DirichletCharacter ℂ 1)
      from rfl, LFunction_modOne_eq]
  · rw [LFunction_modOne_eq]

end Analytic
end EuclidsPath
