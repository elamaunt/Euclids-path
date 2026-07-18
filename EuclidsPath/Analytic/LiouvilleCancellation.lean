/-
  Analytic/LiouvilleCancellation — STAGES P-D3/D4 of the Tauberian
  campaign: THE LIOUVILLE CANCELLATION, full line and per class mod 6.

  D3 (`tendsto_twistLiouville_div`): for a quadratic-squared character,
  the χ-twisted Liouville partial sums are `o(x)` — Newman applied to
  `g(z) = L₁(q, 2z+2)·L(χ, z+1)⁻¹/(z+1)`, which is holomorphic on the
  shifted zero-free set (NO pole subtraction at all: the numerator's
  pole sits at `z = −1/2`, outside the closed half-plane), then the
  ±1-BOUNDED extraction (P-C1).

  D4: the untwisted case `Σλ = o(x)` (q = 1), the bridge to the repo's
  summatory `RiemannLiouville.L`, and the PER-CLASS mod-6 cancellation
  through character orthogonality (both characters mod 6 are quadratic).

  DISCLOSURES.
    * λ-cancellation machinery; no face of the parity wall is touched,
      and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Analytic.LiouvilleLSeries
import EuclidsPath.Analytic.NewmanInterface
import EuclidsPath.Engine.RiemannLiouville
import EuclidsPath.Analytic.MellinPartialSums
import EuclidsPath.Analytic.ZeroFreeNbhd
import EuclidsPath.Analytic.TauberianExtraction

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex ArithmeticFunction Filter MeasureTheory Set DirichletCharacter
open scoped LSeries.notation

/-! ### Real coefficients of quadratic characters -/

/-- The real value of a (quadratic-squared) character. -/
noncomputable def chiReal {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (χ n).re

theorem coe_chiReal {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    (n : ℕ) : ((chiReal χ n : ℝ) : ℂ) = χ n := by
  unfold chiReal
  rcases apply_eq_one_or_neg_one_or_zero hχ n with h | h | h <;>
    rw [h] <;> norm_num

theorem abs_chiReal_le {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    (n : ℕ) : |chiReal χ n| ≤ 1 := by
  unfold chiReal
  rcases apply_eq_one_or_neg_one_or_zero hχ n with h | h | h <;>
    rw [h] <;> norm_num

theorem abs_liouville_le (n : ℕ) :
    |(ArithmeticFunction.liouville n : ℝ)| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ArithmeticFunction.liouville_apply hn]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]

/-! ### D3: the twisted cancellation -/

/-- **The χ-twisted Liouville cancellation**: for `χ² = 1`, the twisted
partial sums are `o(x)`. -/
theorem tendsto_twistLiouville_div {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) :
    Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
      chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / x)
      atTop (nhds 0) := by
  have hf1 : ∀ n : ℕ,
      |chiReal χ n * (ArithmeticFunction.liouville n : ℝ)| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |chiReal χ n| * |(ArithmeticFunction.liouville n : ℝ)|
        ≤ 1 * 1 := mul_le_mul (abs_chiReal_le hχ n) (abs_liouville_le n)
          (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- the partial-sum function and its bound
  have hLbound : ∀ t : ℝ, 1 ≤ t →
      |(∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
        chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t| ≤ 1 := by
    intro t ht
    have htpos : (0 : ℝ) < t := by linarith
    rw [abs_div, abs_of_pos htpos, div_le_one htpos]
    calc |∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          chiReal χ k * (ArithmeticFunction.liouville k : ℝ)|
        ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, |chiReal χ k
            * (ArithmeticFunction.liouville k : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => hf1 k
      _ = (⌊t⌋₊ : ℝ) := by rw [Finset.sum_const, Nat.card_Icc]; simp
      _ ≤ t := Nat.floor_le htpos.le
  have hmeasL : Measurable (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
      chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t) :=
    ((measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      chiReal χ k * (ArithmeticFunction.liouville k : ℝ))).comp
      Nat.measurable_floor).div measurable_id
  -- the holomorphic data
  have hUopen : IsOpen ((((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q)
      ∩ {(-1 : ℂ)}ᶜ) ∩ {(-(1 / 2) : ℂ)}ᶜ) :=
    (((isOpen_zeroFreeSet q).preimage (by fun_prop)).inter
      isOpen_compl_singleton).inter isOpen_compl_singleton
  have hUmem : {z : ℂ | 0 ≤ z.re}
      ⊆ (((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q) ∩ {(-1 : ℂ)}ᶜ)
        ∩ {(-(1 / 2) : ℂ)}ᶜ := by
    intro z hz
    have hz0 : 0 ≤ z.re := hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply closedHalfPlane_subset_zeroFreeSet q
      show 1 ≤ (z + 1).re
      simp only [Complex.add_re, Complex.one_re]
      linarith
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [h] at hz0
      norm_num at hz0
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [h] at hz0
      norm_num at hz0
  have hgdiff : DifferentiableOn ℂ
      (fun z => LFunctionTrivChar q (2 * z + 2) * LFunctionInv χ (z + 1)
        / (z + 1))
      ((((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q) ∩ {(-1 : ℂ)}ᶜ)
        ∩ {(-(1 / 2) : ℂ)}ᶜ) := by
    apply DifferentiableOn.div
    · apply DifferentiableOn.mul
      · intro z hz
        have hne1 : (2 * z + 2 : ℂ) ≠ 1 := by
          intro h
          apply hz.2
          simp only [Set.mem_singleton_iff]
          linear_combination h / 2
        have houter := differentiableAt_LFunction
          (1 : DirichletCharacter ℂ q) (2 * z + 2) (Or.inl hne1)
        have hinner : DifferentiableAt ℂ (fun z : ℂ => 2 * z + 2) z := by
          fun_prop
        exact (houter.comp z hinner).differentiableWithinAt
      · exact DifferentiableOn.comp
          (g := LFunctionInv χ) (f := fun z : ℂ => z + 1)
          (differentiableOn_LFunctionInv χ)
          ((differentiable_id.add_const 1).differentiableOn)
          (fun w hw => hw.1.1)
    · intro z _
      exact ((differentiable_id.add_const 1) z).differentiableWithinAt
    · intro z hz h0
      apply hz.1.2
      simp only [Set.mem_singleton_iff]
      linear_combination h0
  -- the Mellin representation (no pole term)
  have hrep : ∀ z : ℂ, 0 < z.re →
      (fun z => LFunctionTrivChar q (2 * z + 2) * LFunctionInv χ (z + 1)
        / (z + 1)) z
        = ∫ t in Set.Ioi (1 : ℝ),
            (((∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
              chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t : ℝ) : ℂ)
              * (t : ℂ) ^ (-z - 1) := by
    intro z hz
    have hs1 : 1 < (z + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hs0 : (z + 1) ≠ 0 := by
      intro h
      have := congr_arg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
      linarith
    -- cast the integrand to the complex twist sums
    have hcast : ∀ t : ℝ, 1 < t →
        (((∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t : ℝ) : ℂ)
          * (t : ℂ) ^ (-z - 1)
        = (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
            χ k * (ArithmeticFunction.liouville k : ℂ))
            * (t : ℂ) ^ (-(z + 1) - 1) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      have hsum : ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          chiReal χ k * (ArithmeticFunction.liouville k : ℝ) : ℝ) : ℂ)
          = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
              χ k * (ArithmeticFunction.liouville k : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show ((chiReal χ k : ℝ) : ℂ) = χ k from coe_chiReal hχ k]
      have hcpow : (t : ℂ) ^ (-(z + 1) - 1)
          = (t : ℂ) ^ (-z - 1) / (t : ℂ) := by
        rw [show (-(z + 1) - 1 : ℂ) = (-z - 1) + (-1) by ring,
          Complex.cpow_add _ _ ht0, Complex.cpow_neg_one]
        ring
      rw [hcpow, ← hsum]
      push_cast
      field_simp
    -- the L-series representation
    have hL := LSeries_twist_liouville_eq_mul_integral χ hs1
    have hkey := LSeries_twist_liouville_eq χ hχ hs1
    have hInt_eq : ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          χ k * (ArithmeticFunction.liouville k : ℂ))
          * (t : ℂ) ^ (-(z + 1) - 1)
        = LSeries ((↗χ : ℕ → ℂ) * ↗ArithmeticFunction.liouville) (z + 1)
          / (z + 1) := by
      have halign : ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
            χ k * (ArithmeticFunction.liouville k : ℂ))
            * (t : ℂ) ^ (-((z + 1) + 1))
          = ∫ t in Set.Ioi (1 : ℝ),
              (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
                χ k * (ArithmeticFunction.liouville k : ℂ))
                * (t : ℂ) ^ (-(z + 1) - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [show (-((z + 1) + 1) : ℂ) = -(z + 1) - 1 by ring]
      have hL' : LSeries (fun n => χ n
          * (ArithmeticFunction.liouville n : ℂ)) (z + 1)
          = (z + 1) * ∫ t in Set.Ioi (1 : ℝ),
              (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
                χ k * (ArithmeticFunction.liouville k : ℂ))
                * (t : ℂ) ^ (-(z + 1) - 1) := by
        rw [← halign]
        exact hL
      rw [show ((↗χ : ℕ → ℂ) * ↗ArithmeticFunction.liouville)
          = fun n : ℕ => χ n * (ArithmeticFunction.liouville n : ℂ) from rfl,
        hL']
      field_simp
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => hcast t ht), hInt_eq, hkey]
    have h2s : (2 * (z + 1) : ℂ) = 2 * z + 2 := by ring
    rw [h2s]
    show LFunctionTrivChar q (2 * z + 2) * LFunctionInv χ (z + 1) / (z + 1)
        = LFunctionTrivChar q (2 * z + 2) * (LFunction χ (z + 1))⁻¹ / (z + 1)
    rw [LFunctionInv_eq_inv hs1]
  -- Newman + extraction
  have hNewman := newmanMellin_proved
    (fun t : ℝ => (((∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
      chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t : ℝ) : ℂ))
    (fun z => LFunctionTrivChar q (2 * z + 2) * LFunctionInv χ (z + 1)
      / (z + 1))
    ((((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q) ∩ {(-1 : ℂ)}ᶜ)
      ∩ {(-(1 / 2) : ℂ)}ᶜ)
    1
    (Complex.measurable_ofReal.comp hmeasL)
    (fun t ht => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hLbound t ht)
    hUopen hUmem hgdiff hrep
  have hre := (Complex.continuous_re.tendsto _).comp hNewman
  have hreal : Tendsto (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
        chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t ^ 2) atTop
      (nhds (((fun z => LFunctionTrivChar q (2 * z + 2)
        * LFunctionInv χ (z + 1) / (z + 1)) 0).re)) := by
    refine hre.congr fun X => ?_
    simp only [Function.comp_apply]
    have hcast2 : ∫ t in Set.Ioc (1 : ℝ) X,
        (((∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t : ℝ) : ℂ)
          / (t : ℂ)
        = ((∫ t in Set.Ioc (1 : ℝ) X,
            (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
              chiReal χ k * (ArithmeticFunction.liouville k : ℝ)) / t ^ 2
            : ℝ) : ℂ) := by
      rw [← _root_.integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      push_cast
      ring
    rw [hcast2, Complex.ofReal_re]
  exact tendsto_partialSum_div_of_integral_tendsto hf1 hreal

/-! ### D4: the untwisted and per-class cancellations -/

/-- **The Liouville cancellation** (full line): `Σ_{k ≤ x} λ(k) = o(x)`. -/
theorem liouville_partialSum_tendsto :
    Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
      (ArithmeticFunction.liouville k : ℝ)) / x) atTop (nhds 0) := by
  have h := tendsto_twistLiouville_div (1 : DirichletCharacter ℂ 1)
    (sq_eq_one_of_zmod_one 1)
  refine h.congr fun x => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : chiReal (1 : DirichletCharacter ℂ 1) k = 1 := by
    unfold chiReal
    rw [show (1 : DirichletCharacter ℂ 1) ((k : ℕ) : ZMod 1)
        = 1 by rw [Subsingleton.elim ((k : ℕ) : ZMod 1) 1, map_one]]
    norm_num
  rw [h1, one_mul]

/-- The bridge to the repo's summatory function `RiemannLiouville.L`. -/
theorem riemannLiouville_L_div_tendsto :
    Tendsto (fun n : ℕ => (EuclidsPath.RiemannLiouville.L n : ℝ) / n)
      atTop (nhds 0) := by
  have h := liouville_partialSum_tendsto.comp tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  congr 1
  unfold EuclidsPath.RiemannLiouville.L
  rw [Nat.floor_natCast]
  push_cast
  rfl

/-- The class-restricted Liouville summatory function. -/
noncomputable def liouvilleRes {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
    if ((k : ℕ) : ZMod q) = a then (ArithmeticFunction.liouville k : ℝ) else 0

/-- **The per-class mod-6 Liouville cancellation**: for unit classes,
`liouvilleRes(a, x) = o(x)` — character orthogonality over the two
quadratic characters mod 6. -/
theorem liouvilleRes_six_tendsto {a : ZMod 6} (ha : IsUnit a) :
    Tendsto (fun x : ℝ => liouvilleRes a x / x) atTop (nhds 0) := by
  have hφ : ((6 : ℕ).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by norm_num : 0 < 6)).ne'
  -- pointwise orthogonality
  have hpt : ∀ k : ℕ,
      (if ((k : ℕ) : ZMod 6) = a then
        ((ArithmeticFunction.liouville k : ℝ) : ℂ) else 0)
      = ((6 : ℕ).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ 6,
          χ a⁻¹ * (χ k * (ArithmeticFunction.liouville k : ℂ)) := by
    intro k
    rw [show (∑ χ : DirichletCharacter ℂ 6,
        χ a⁻¹ * (χ k * (ArithmeticFunction.liouville k : ℂ)))
        = (∑ χ : DirichletCharacter ℂ 6, χ a⁻¹ * χ k)
          * (ArithmeticFunction.liouville k : ℂ) by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun χ _ => by ring]
    rw [sum_char_inv_mul_char_eq ℂ ha ((k : ℕ) : ZMod 6)]
    by_cases hak : a = ((k : ℕ) : ZMod 6)
    · rw [if_pos hak, if_pos hak.symm, ← mul_assoc, inv_mul_cancel₀ hφ,
        one_mul]
      push_cast
      rfl
    · rw [if_neg hak, if_neg (fun h => hak h.symm), zero_mul, mul_zero]
  -- the complex-summed form
  have hkey : ∀ x : ℝ, ((liouvilleRes a x : ℝ) : ℂ)
      = ((6 : ℕ).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ 6,
          χ a⁻¹ * ((∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
            chiReal χ k * (ArithmeticFunction.liouville k : ℝ) : ℝ) : ℂ) := by
    intro x
    have hsum1 : ((liouvilleRes a x : ℝ) : ℂ)
        = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
            (if ((k : ℕ) : ZMod 6) = a then
              ((ArithmeticFunction.liouville k : ℝ) : ℂ) else 0) := by
      unfold liouvilleRes
      push_cast [apply_ite (fun r : ℝ => (r : ℂ))]
      rfl
    rw [hsum1]
    have hsum2 : ∀ χ : DirichletCharacter ℂ 6,
        ((∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
          chiReal χ k * (ArithmeticFunction.liouville k : ℝ) : ℝ) : ℂ)
        = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
            χ k * (ArithmeticFunction.liouville k : ℂ) := by
      intro χ
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show ((chiReal χ k : ℝ) : ℂ) = χ k
        from coe_chiReal (sq_eq_one_of_zmod_six χ) k]
    calc ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        (if ((k : ℕ) : ZMod 6) = a then
          ((ArithmeticFunction.liouville k : ℝ) : ℂ) else 0)
        = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((6 : ℕ).totient : ℂ)⁻¹
            * ∑ χ : DirichletCharacter ℂ 6,
                χ a⁻¹ * (χ k * (ArithmeticFunction.liouville k : ℂ)) :=
          Finset.sum_congr rfl fun k _ => hpt k
      _ = ((6 : ℕ).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ 6,
            χ a⁻¹ * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
              χ k * (ArithmeticFunction.liouville k : ℂ) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]
      _ = ((6 : ℕ).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ 6,
            χ a⁻¹ * ((∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
              chiReal χ k * (ArithmeticFunction.liouville k : ℝ) : ℝ) : ℂ) := by
          congr 1
          exact Finset.sum_congr rfl fun χ _ => by rw [hsum2 χ]
  -- complex tendsto from the finite character sum of D3 limits
  have hC : Tendsto (fun x : ℝ =>
      ((liouvilleRes a x : ℝ) : ℂ) / ((x : ℝ) : ℂ)) atTop (nhds 0) := by
    have hterm : ∀ χ : DirichletCharacter ℂ 6,
        Tendsto (fun x : ℝ => χ a⁻¹ * ((∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
          chiReal χ k * (ArithmeticFunction.liouville k : ℝ) : ℝ) : ℂ)
          / ((x : ℝ) : ℂ)) atTop (nhds 0) := by
      intro χ
      have hr := tendsto_twistLiouville_div χ (sq_eq_one_of_zmod_six χ)
      have hc := (Complex.continuous_ofReal.tendsto 0).comp hr
      rw [Complex.ofReal_zero] at hc
      have hc' : Tendsto (fun x : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
          chiReal χ k * (ArithmeticFunction.liouville k : ℝ) : ℝ) : ℂ)
          / ((x : ℝ) : ℂ)) atTop (nhds 0) := by
        apply hc.congr
        intro x
        simp only [Function.comp_apply]
        push_cast
        rfl
      have hmul := hc'.const_mul (χ a⁻¹)
      rw [mul_zero] at hmul
      apply hmul.congr
      intro x
      ring
    have hsumT := tendsto_finsetSum
      (Finset.univ : Finset (DirichletCharacter ℂ 6))
      (fun χ _ => hterm χ)
    rw [Finset.sum_const_zero] at hsumT
    have hfin := hsumT.const_mul (((6 : ℕ).totient : ℂ)⁻¹)
    rw [mul_zero] at hfin
    apply hfin.congr
    intro x
    rw [hkey x, ← Finset.sum_div, mul_div_assoc]
  -- descend to the real statement
  have hre := (Complex.continuous_re.tendsto (0 : ℂ)).comp hC
  rw [Complex.zero_re] at hre
  apply hre.congr
  intro x
  simp only [Function.comp_apply]
  rw [show ((liouvilleRes a x : ℝ) : ℂ) / ((x : ℝ) : ℂ)
      = ((liouvilleRes a x / x : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

end Analytic
end EuclidsPath
