/-
  Analytic/LiouvilleConvolution — STAGE P-D1 of the Tauberian campaign:
  the SQUARES INDICATOR and the convolution identity `λ ⍟ ζ = 1_sq`.

  The pin has NO squares indicator and NO `IsSquare ↔ even
  factorization` lemma (verified absent) — this module builds them and
  proves the classical Liouville convolution identity at the
  arithmetic-function level (by multiplicativity + prime powers, where
  it is the alternating geometric sum), then descends it to the
  sequence level (`⍟`) in both untwisted and χ-twisted forms — the
  inputs for the λ Dirichlet-series factorization (D2).

  DISCLOSURES.
    * Elementary multiplicative number theory over the pin's
      arithmetic-function frame: no face of the parity wall is touched,
      and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open ArithmeticFunction Finset
open scoped LSeries.notation ArithmeticFunction.zeta

/-! ### The squares indicator -/

/-- The indicator of positive perfect squares, as an arithmetic function. -/
noncomputable def sqIndicator : ArithmeticFunction ℂ :=
  ⟨fun n => if IsSquare n ∧ n ≠ 0 then 1 else 0, by simp⟩

theorem sqIndicator_apply {n : ℕ} :
    sqIndicator n = if IsSquare n ∧ n ≠ 0 then 1 else 0 := rfl

/-- A positive natural is a square iff its factorization is everywhere even. -/
theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := by
      intro h
      rw [h] at hn
      simp at hn
    intro p
    rw [Nat.factorization_mul hr hr]
    exact ⟨r.factorization p, by simp⟩
  · intro h
    refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
    have hprod : (n.factorization.prod fun p k => p ^ (k / 2))
        * (n.factorization.prod fun p k => p ^ (k / 2))
        = n.factorization.prod fun p k => p ^ k := by
      rw [← Finsupp.prod_mul]
      apply Finsupp.prod_congr
      intro p _
      rw [← pow_add]
      congr 1
      obtain ⟨c, hc⟩ := h p
      omega
    rw [hprod, Nat.prod_factorization_pow_eq_self hn]

/-- Squares detection on coprime products: both factors must be squares. -/
theorem isSquare_of_coprime_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hco : Nat.Coprime m n) (h : IsSquare (m * n)) :
    IsSquare m ∧ IsSquare n := by
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  rw [isSquare_iff_even_factorization hmn] at h
  have hfac : ∀ p, Even (m.factorization p + n.factorization p) := by
    intro p
    have := h p
    rwa [Nat.factorization_mul hm hn] at this
  have hdisj : Disjoint m.primeFactors n.primeFactors :=
    Nat.Coprime.disjoint_primeFactors hco
  constructor
  · rw [isSquare_iff_even_factorization hm]
    intro p
    by_cases hp : p ∈ m.primeFactors
    · have hp' : p ∉ n.primeFactors := Finset.disjoint_left.mp hdisj hp
      have hzero : n.factorization p = 0 := by
        rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp'
      have := hfac p
      rwa [hzero, add_zero] at this
    · have hzero : m.factorization p = 0 := by
        rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rw [hzero]
      exact ⟨0, rfl⟩
  · rw [isSquare_iff_even_factorization hn]
    intro p
    by_cases hp : p ∈ n.primeFactors
    · have hp' : p ∉ m.primeFactors := Finset.disjoint_right.mp hdisj hp
      have hzero : m.factorization p = 0 := by
        rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp'
      have := hfac p
      rwa [hzero, zero_add] at this
    · have hzero : n.factorization p = 0 := by
        rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rw [hzero]
      exact ⟨0, rfl⟩

theorem isMultiplicative_sqIndicator : sqIndicator.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [sqIndicator_apply]
    rw [if_pos ⟨⟨1, (one_mul 1).symm⟩, one_ne_zero⟩]
  · intro m n hco
    rcases eq_or_ne m 0 with rfl | hm
    · rw [Nat.coprime_zero_left] at hco
      subst hco
      simp [sqIndicator_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.coprime_zero_right] at hco
      subst hco
      simp [sqIndicator_apply]
    rw [sqIndicator_apply, sqIndicator_apply, sqIndicator_apply]
    by_cases hsm : IsSquare m <;> by_cases hsn : IsSquare n
    · rw [if_pos ⟨hsm.mul hsn, mul_ne_zero hm hn⟩, if_pos ⟨hsm, hm⟩,
        if_pos ⟨hsn, hn⟩, mul_one]
    · rw [if_neg (fun h => hsn (isSquare_of_coprime_mul hm hn hco h.1).2),
        if_pos ⟨hsm, hm⟩, if_neg (fun h => hsn h.1), mul_zero]
    · rw [if_neg (fun h => hsm (isSquare_of_coprime_mul hm hn hco h.1).1),
        if_neg (fun h => hsm h.1), if_pos ⟨hsn, hn⟩, zero_mul]
    · rw [if_neg (fun h => hsm (isSquare_of_coprime_mul hm hn hco h.1).1),
        if_neg (fun h => hsm h.1), if_neg (fun h => hsn h.1), zero_mul]

theorem sqIndicator_prime_pow {p k : ℕ} (hp : p.Prime) :
    sqIndicator (p ^ k) = if Even k then 1 else 0 := by
  rw [sqIndicator_apply]
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have hiff : (IsSquare (p ^ k) ∧ p ^ k ≠ 0) ↔ Even k := by
    rw [and_iff_left hpk, isSquare_iff_even_factorization hpk]
    constructor
    · intro h
      have := h p
      rwa [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this
    · intro hk q
      rw [Nat.Prime.factorization_pow hp]
      rcases eq_or_ne q p with rfl | hq
      · rwa [Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne hq]
        exact ⟨0, rfl⟩
  simp only [hiff]

/-! ### The convolution identity `λ ⍟ ζ = 1_sq` -/

/-- **The arithmetic-function identity**: `λ · ζ = 1_sq` (Dirichlet
product) — at prime powers it is the alternating geometric sum. -/
theorem liouville_mul_zeta_eq_sqIndicator :
    ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) :
        ArithmeticFunction ℂ) * (ζ : ArithmeticFunction ℂ) = sqIndicator := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_liouville.intCast.mul isMultiplicative_zeta.natCast) _
    isMultiplicative_sqIndicator).mpr ?_
  intro p i hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sqIndicator_prime_pow hp]
  have hterm : ∀ j : ℕ,
      ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) :
        ArithmeticFunction ℂ) (p ^ j) = (-1 : ℂ) ^ j := by
    intro j
    rw [ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.liouville_apply (pow_ne_zero j hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp]
    push_cast
    ring
  simp_rw [hterm]
  rw [neg_one_geom_sum]
  rcases Nat.even_or_odd i with he | ho
  · rw [if_neg (by simp [Nat.even_add_one, he]), if_pos he]
  · have hno : ¬Even i := by simpa [Nat.not_even_iff_odd] using ho
    rw [if_pos (Nat.even_add_one.mpr hno), if_neg hno]

/-- The sequence-level descent: `↗λ ⍟ ↗ζ = 1_sq` as complex sequences. -/
theorem convolution_liouville_zeta :
    (↗ArithmeticFunction.liouville : ℕ → ℂ) ⍟ ↗(ζ : ArithmeticFunction ℕ)
      = fun n => sqIndicator n := by
  ext n
  have h := congr_arg (fun f : ArithmeticFunction ℂ => f n)
    liouville_mul_zeta_eq_sqIndicator
  simpa [ArithmeticFunction.mul_apply, LSeries.convolution_def,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply] using h

/-- `↗λ ⍟ 1 = 1_sq` — the form the L-series factorization consumes. -/
theorem convolution_liouville_one :
    (↗ArithmeticFunction.liouville : ℕ → ℂ) ⍟ (1 : ℕ → ℂ)
      = fun n => sqIndicator n :=
  (LSeries.convolution_one_eq_convolution_zeta _).trans convolution_liouville_zeta

/-- The χ-twisted convolution identity: `(χλ) ⍟ χ = χ·1_sq`. -/
theorem convolution_twist_liouville {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ((↗χ : ℕ → ℂ) * ↗ArithmeticFunction.liouville) ⍟ (↗χ : ℕ → ℂ)
      = (↗χ : ℕ → ℂ) * fun n => sqIndicator n := by
  rw [← convolution_liouville_one, ← χ.mul_convolution_distrib, mul_one]

end Analytic
end EuclidsPath
