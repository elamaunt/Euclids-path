/-
  Engine/GeometricTypeIIWingSign — STAGE L-M3 of the Tauberian campaign:
  **THE WING SIGN THEOREM (count level, minus wing)** — the §13
  disclosure upgraded to a theorem.

  On every FULL rough minus window with θ ∈ [7/20, 9/20] (integer-safe:
  `X^7 ≤ z^20 ≤ X^9`), eventually

      Σ_{m ∈ I(X,z)} λ(6m−1)  ≤  −(1/40)·X/log X  <  0.

  Route: `Σλ = S − P` (M1); `P` from `apCount` and the AP-PNT interface
  at scale `X`; `S` through the rung ladder (M1), sliced at 40ths of
  `log X`, each slice capped by the parametric Mertens difference (M2)
  with the pin's `log 4` Chebyshev constant.  Budget (pre-passed in
  `tools/wing_sign_prepass.py`, refined for the Lean endgame): interface
  slack `ε = 1/1000`, log-2 division slop absorbed as a `1/80`-notch in
  the slice weights (`X ≥ 2^80` eventually), Mertens cap certified by
  `log x ≤ x − 1` — coefficient `≤ −0.0357`, target `−1/40`, o(1)-room
  `0.0107`.

  The interface hypothesis `hAP` is the house named-hypothesis pattern —
  AND it is DISCHARGED at the end (`minus_wing_sign`) by the campaign's
  `Analytic.apCount_mul_log_div_tendsto`: the crown is UNCONDITIONAL.

  DISCLOSURES (mandatory reading before quoting):
    * OneWingTarget IS NOT DISCHARGED, NOT PREMISE-SHRUNK, NOT
      REWEIGHTED by this module.  Any valid instantiation of
      OneWingTarget forces twin-count > 0 (L₋+L₊ < 0 ⟺ B₋+B₊ < A;
      count = A−(B₋+B₊)+C > 0 since C ≥ 0): the target is twin-strength
      BY PIGEONHOLE.  Three attempted bridges from per-wing results to
      the target were refuted by the campaign's verifiers; PNT does NOT
      discharge it.  Proved here: the per-wing sign at count level on
      the FULL rough minus wing.  The surviving open core of route B is
      exactly the PAIR-ROUGH two-wing coupling: ONE window on which BOTH
      wings are rough with SUMMED negative bias.
    * EVENTUAL, NOT EFFECTIVE: the `Filter.atTop` threshold is
      astronomically large (the Chebyshev–Mertens boundary terms decay
      like `1/log X`); the numeric grounding at `X = 10⁷` confirms the
      SIGN empirically (Σλ = −172058/−238841/−299193 at
      θ = .35/.40/.45), NOT the Lean threshold.  No explicit `X₀` is
      claimed.
    * The margin constant is Chebyshev-inflated (`log 4`-grade), NOT the
      true `log((1−θ)/θ)`; sharper constants are named, unclaimed work.
    * The plus wing is named, unclaimed work (deferred).
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Engine.GeometricTypeIIWingWindow
import EuclidsPath.Engine.GeometricTypeIIMertensDifference

set_option maxHeartbeats 3200000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction Filter
open EuclidsPath.Analytic (apCount)

/-! ### Layer 1: interface extraction -/

/-- Two-sided eventual bounds from the AP-PNT interface. -/
theorem interface_bounds {a : ℕ}
    (h : Tendsto (fun n : ℕ => (apCount a n : ℝ) * (2 * Real.log n) / n)
      atTop (nhds 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 - ε) * n ≤ (apCount a n : ℝ) * (2 * Real.log n)
        ∧ (apCount a n : ℝ) * (2 * Real.log n) ≤ (1 + ε) * n := by
  have hev := Metric.tendsto_nhds.mp h ε hε
  filter_upwards [hev, eventually_ge_atTop 2] with n hn hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  rw [Real.dist_eq, abs_lt] at hn
  constructor
  · have h1 : (1 - ε) < (apCount a n : ℝ) * (2 * Real.log n) / n := by
      linarith [hn.1]
    calc (1 - ε) * n
        ≤ ((apCount a n : ℝ) * (2 * Real.log n) / n) * n := by
          apply mul_le_mul_of_nonneg_right h1.le hnpos.le
      _ = (apCount a n : ℝ) * (2 * Real.log n) := by
          field_simp
  · have h1 : (apCount a n : ℝ) * (2 * Real.log n) / n < 1 + ε := by
      linarith [hn.2]
    calc (apCount a n : ℝ) * (2 * Real.log n)
        = ((apCount a n : ℝ) * (2 * Real.log n) / n) * n := by
          field_simp
      _ ≤ (1 + ε) * n := mul_le_mul_of_nonneg_right h1.le hnpos.le

/-- The per-scale upper form: `apCount ≤ (1+ε)·m/(2·log m)`. -/
theorem apCount_upper_of_bound {a m : ℕ} {ε : ℝ}
    (hb : (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + ε) * m)
    (hm : 2 ≤ m) :
    (apCount a m : ℝ) ≤ (1 + ε) * m / (2 * Real.log m) := by
  have hlog : (0 : ℝ) < Real.log m :=
    Real.log_pos (by exact_mod_cast hm)
  rw [le_div_iff₀ (by positivity)]
  exact hb

/-- The scale-X lower form: `(1−ε)·X/(2·log X) ≤ apCount`. -/
theorem apCount_lower_of_bound {a X : ℕ} {ε : ℝ}
    (hb : (1 - ε) * X ≤ (apCount a X : ℝ) * (2 * Real.log X))
    (hX : 2 ≤ X) :
    (1 - ε) * X / (2 * Real.log X) ≤ (apCount a X : ℝ) := by
  have hlog : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast hX)
  rw [div_le_iff₀ (by positivity)]
  exact hb

/-- Crude cap: `apCount a z ≤ z`. -/
theorem apCount_le (a z : ℕ) : apCount a z ≤ z := by
  unfold EuclidsPath.Analytic.apCount
  calc ((Finset.Icc 1 z).filter fun n => n.Prime ∧ n % 6 = a).card
      ≤ (Finset.Icc 1 z).card := Finset.card_filter_le _ _
    _ = z := by rw [Nat.card_Icc]; omega

/-! ### Layer 2: window-parameter facts from the θ-range -/

theorem z_facts {X z : ℕ} (hX : 2 ≤ X) (h7 : X ^ 7 ≤ z ^ 20)
    (h9 : z ^ 20 ≤ X ^ 9) :
    2 ≤ z ∧ X < z ^ 3 ∧ z * z ≤ X ∧ X ^ 14 ≤ z ^ 40 := by
  have hz2 : 2 ≤ z := by
    by_contra h
    push Not at h
    have hz1 : z ≤ 1 := by omega
    have h1 : z ^ 20 ≤ 1 := by
      calc z ^ 20 ≤ 1 ^ 20 := Nat.pow_le_pow_left hz1 20
        _ = 1 := one_pow 20
    have h2 : 2 ^ 7 ≤ X ^ 7 := Nat.pow_le_pow_left hX 7
    have hcontra : (128 : ℕ) ≤ 1 := by
      calc (128 : ℕ) = 2 ^ 7 := by norm_num
        _ ≤ X ^ 7 := h2
        _ ≤ z ^ 20 := h7
        _ ≤ 1 := h1
    omega
  refine ⟨hz2, ?_, ?_, ?_⟩
  · -- X < z³: else X ≥ z³ gives X^7 ≥ z^21 ≥ 2·z^20 > z^20 ≥ X^7
    by_contra h
    push Not at h
    have h1 : z ^ 3 ≤ X := h
    have h2 : (z ^ 3) ^ 7 ≤ X ^ 7 := Nat.pow_le_pow_left h1 7
    have h3 : z ^ 21 ≤ X ^ 7 := by
      calc z ^ 21 = (z ^ 3) ^ 7 := by ring
        _ ≤ X ^ 7 := h2
    have h5 : z ^ 20 * 2 ≤ z ^ 20 * z := Nat.mul_le_mul_left _ hz2
    have h6 : z ^ 20 * z = z ^ 21 := by ring
    have h7' : 1 ≤ z ^ 20 := Nat.one_le_pow _ _ (by omega)
    omega
  · -- z² ≤ X: from z^20 ≤ X^9 ≤ X^10: (z²)^10 ≤ X^10
    have h1 : z ^ 20 ≤ X ^ 10 :=
      h9.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : (z * z) ^ 10 ≤ X ^ 10 := by
      calc (z * z) ^ 10 = z ^ 20 := by ring
        _ ≤ X ^ 10 := h1
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2
  · -- X^14 ≤ z^40: square of X^7 ≤ z^20
    calc X ^ 14 = (X ^ 7) ^ 2 := by ring
      _ ≤ (z ^ 20) ^ 2 := Nat.pow_le_pow_left h7 2
      _ = z ^ 40 := by ring

/-! ### Layer 3: the slice machinery -/

/-- Slice `i` of the rung set: `X^(14+i) < p^40 ≤ X^(15+i)`. -/
def rungSlice (X z i : ℕ) : Finset ℕ :=
  (rungPrimes X z).filter fun p => X ^ (14 + i) < p ^ 40 ∧ p ^ 40 ≤ X ^ (15 + i)

/-- The slices cover the rungs exactly (θ-range hypotheses). -/
theorem rungPrimes_eq_biUnion_slices {X z : ℕ} (_hX : 2 ≤ X)
    (h14 : X ^ 14 ≤ z ^ 40) :
    rungPrimes X z = (Finset.range 6).biUnion (fun i => rungSlice X z i) := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_range, rungSlice,
    Finset.mem_filter]
  constructor
  · intro hp
    have hmem := hp
    obtain ⟨hpIcc, hpp, hzp, hppX⟩ := Finset.mem_filter.mp hp |>.imp id id
    -- p^40 ∈ (X^14, X^20]
    have hlow : X ^ 14 < p ^ 40 := by
      calc X ^ 14 ≤ z ^ 40 := h14
        _ < p ^ 40 := Nat.pow_lt_pow_left hzp (by norm_num)
    have hhigh : p ^ 40 ≤ X ^ 20 := by
      calc p ^ 40 = (p * p) ^ 20 := by ring
        _ ≤ X ^ 20 := Nat.pow_le_pow_left hppX 20
    -- find the slice index
    by_cases h0 : p ^ 40 ≤ X ^ 15
    · exact ⟨0, by norm_num, hmem, by simpa using hlow, by simpa using h0⟩
    by_cases h1 : p ^ 40 ≤ X ^ 16
    · exact ⟨1, by norm_num, hmem, by simp only [Nat.reduceAdd]; omega,
        by simpa using h1⟩
    by_cases h2 : p ^ 40 ≤ X ^ 17
    · exact ⟨2, by norm_num, hmem, by simp only [Nat.reduceAdd]; omega,
        by simpa using h2⟩
    by_cases h3 : p ^ 40 ≤ X ^ 18
    · exact ⟨3, by norm_num, hmem, by simp only [Nat.reduceAdd]; omega,
        by simpa using h3⟩
    by_cases h4 : p ^ 40 ≤ X ^ 19
    · exact ⟨4, by norm_num, hmem, by simp only [Nat.reduceAdd]; omega,
        by simpa using h4⟩
    · exact ⟨5, by norm_num, hmem, by simp only [Nat.reduceAdd]; omega,
        by simpa using hhigh⟩
  · rintro ⟨i, _, hp, _, _⟩
    exact hp

theorem slices_disjoint {X z : ℕ} (hX : 2 ≤ X) :
    ∀ i ∈ Finset.range 6, ∀ j ∈ Finset.range 6, i ≠ j →
      Disjoint (rungSlice X z i) (rungSlice X z j) := by
  intro i _ j _ hij
  rw [Finset.disjoint_left]
  intro p hpi hpj
  obtain ⟨_, hi1, hi2⟩ := Finset.mem_filter.mp hpi |>.imp id id
  obtain ⟨_, hj1, hj2⟩ := Finset.mem_filter.mp hpj |>.imp id id
  rcases Nat.lt_or_ge i j with h | h
  · have : X ^ (15 + i) ≤ X ^ (14 + j) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hji : j < i := by omega
    have : X ^ (15 + j) ≤ X ^ (14 + i) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- Slice membership transfers to the real Mertens window
`(⌊X^((14+i)/40)⌋, ⌊X^((15+i)/40)⌋]`. -/
theorem slice_subset_Ioc {X z i : ℕ} (hX : 2 ≤ X) :
    rungSlice X z i ⊆
      (Finset.Ioc ⌊((X : ℝ) ^ (((14 + i : ℕ) : ℝ) / 40))⌋₊
        ⌊((X : ℝ) ^ (((15 + i : ℕ) : ℝ) / 40))⌋₊).filter Nat.Prime := by
  intro p hp
  obtain ⟨hpr, hlow, hhigh⟩ := Finset.mem_filter.mp hp |>.imp
    (fun h => (Finset.mem_filter.mp h).2.1) id
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, ?_⟩, hpr⟩
  · -- ⌊s⌋ < p from s < p from s^40 = X^(14+i) < p^40
    rw [Nat.floor_lt (Real.rpow_nonneg hX0.le _)]
    have h40 : ((X : ℝ) ^ (((14 + i : ℕ) : ℝ) / 40)) ^ (40 : ℕ)
        = (X : ℝ) ^ (14 + i : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ (((14 + i : ℕ) : ℝ) / 40)) 40,
        ← Real.rpow_mul hX0.le,
        show (((40 : ℕ) : ℝ)) = (40 : ℝ) from by norm_num,
        div_mul_cancel₀ _ (by norm_num : (40 : ℝ) ≠ 0), Real.rpow_natCast]
    have hcast : ((X : ℝ) ^ (14 + i : ℕ)) < ((p : ℝ)) ^ (40 : ℕ) := by
      exact_mod_cast hlow
    have hthis := hcast
    rw [← h40] at hthis
    exact lt_of_pow_lt_pow_left₀ 40 hp0 hthis
  · -- p ≤ ⌊t⌋ from p ≤ t from p^40 ≤ X^(15+i) = t^40
    rw [Nat.le_floor_iff (Real.rpow_nonneg hX0.le _)]
    have h40 : ((X : ℝ) ^ (((15 + i : ℕ) : ℝ) / 40)) ^ (40 : ℕ)
        = (X : ℝ) ^ (15 + i : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ (((15 + i : ℕ) : ℝ) / 40)) 40,
        ← Real.rpow_mul hX0.le,
        show (((40 : ℕ) : ℝ)) = (40 : ℝ) from by norm_num,
        div_mul_cancel₀ _ (by norm_num : (40 : ℝ) ≠ 0), Real.rpow_natCast]
    have hcast : ((p : ℝ)) ^ (40 : ℕ) ≤ (X : ℝ) ^ (15 + i : ℕ) := by
      exact_mod_cast hhigh
    rw [← h40] at hcast
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hX0.le _)
      hcast

/-- The slice Mertens cap: `Σ_{p ∈ slice i} 1/p ≤ log4/(14+i)
+ 80·log4/((14+i)·log X)`. -/
theorem slice_inv_sum_le {X z i : ℕ} (hXbig : 2 ^ 80 ≤ X) (_hi : i < 6) :
    ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹
      ≤ Real.log 4 * (1 / (14 + i : ℝ))
        + 2 * Real.log 4 * (40 / ((14 + i : ℝ) * Real.log X)) := by
  have hX : 2 ≤ X := le_trans (by norm_num) hXbig
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlogX : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast hX)
  set s : ℝ := (X : ℝ) ^ (((14 + i : ℕ) : ℝ) / 40) with hsdef
  set t : ℝ := (X : ℝ) ^ (((15 + i : ℕ) : ℝ) / 40) with htdef
  have hlogs : Real.log s = ((14 + i : ℕ) : ℝ) / 40 * Real.log X := by
    rw [hsdef, Real.log_rpow hX0]
  have hlogt : Real.log t = ((15 + i : ℕ) : ℝ) / 40 * Real.log X := by
    rw [htdef, Real.log_rpow hX0]
  have h280 : ((2 : ℝ) ^ (80 : ℝ)) = ((2 ^ 80 : ℕ) : ℝ) := by
    rw [show (80 : ℝ) = ((80 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    norm_num
  have hs2 : (2 : ℝ) ≤ s := by
    rw [hsdef]
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((80 : ℝ) * (((14 + i : ℕ) : ℝ) / 40)) := by
          apply (Real.rpow_le_rpow_left_iff (by norm_num)).mpr
          have h14 : (14 : ℝ) ≤ ((14 + i : ℕ) : ℝ) := by push_cast; linarith
          nlinarith
      _ = ((2 : ℝ) ^ (80 : ℝ)) ^ (((14 + i : ℕ) : ℝ) / 40) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (X : ℝ) ^ (((14 + i : ℕ) : ℝ) / 40) := by
          apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [h280]
          exact_mod_cast hXbig
  have hst : s ≤ t := by
    rw [hsdef, htdef]
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
      have h2X : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have : ((14 + i : ℕ) : ℝ) ≤ ((15 + i : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hsub := slice_subset_Ioc (X := X) (z := z) (i := i) hX
  have hmono : ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹
      ≤ ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => by positivity)
  have hM2 := sum_inv_primes_Ioc_le_log4 hs2 hst
  have hratio : Real.log t / Real.log s
      = ((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ) := by
    rw [hlogs, hlogt]
    have h14 : ((14 + i : ℕ) : ℝ) ≠ 0 := by push_cast; linarith
    field_simp
  have hlog_ratio : Real.log (Real.log t / Real.log s) ≤ 1 / (14 + i : ℝ) := by
    rw [hratio]
    have h14pos : (0 : ℝ) < ((14 + i : ℕ) : ℝ) := by push_cast; linarith
    have hratpos : (0 : ℝ) < ((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ) := by
      positivity
    calc Real.log (((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ))
        ≤ ((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hratpos
      _ = 1 / ((14 + i : ℕ) : ℝ) := by
          field_simp
          push_cast
          ring
      _ = 1 / (14 + i : ℝ) := by push_cast; ring
  have hlogs_inv : 2 * Real.log 4 / Real.log s
      = 2 * Real.log 4 * (40 / (((14 + i : ℕ) : ℝ) * Real.log X)) := by
    rw [hlogs]
    have h14 : ((14 + i : ℕ) : ℝ) ≠ 0 := by push_cast; linarith
    field_simp
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹
      ≤ ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹ := hmono
    _ ≤ Real.log 4 * Real.log (Real.log t / Real.log s)
        + 2 * Real.log 4 / Real.log s := hM2
    _ ≤ Real.log 4 * (1 / (14 + i : ℝ))
        + 2 * Real.log 4 * (40 / ((14 + i : ℝ) * Real.log X)) := by
        have h1 := mul_le_mul_of_nonneg_left hlog_ratio hlog4
        rw [hlogs_inv]
        have hpush : (((14 + i : ℕ) : ℝ)) = (14 + i : ℝ) := by push_cast; ring
        rw [hpush]
        linarith

/-! ### Layer 4: the per-rung count bound -/

theorem rungClass_or (p : ℕ) : rungClass p = 1 ∨ rungClass p = 5 := by
  unfold rungClass
  split <;> simp

/-- The per-rung `apCount` cap on slice `i`, with the `1/80`-notch weight
`80/(49−2i)` absorbing the ℕ-division `log 2` slop. -/
theorem slice_apCount_le {X z i p : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hXbig : 2 ^ 80 ≤ X) (hi : i < 6)
    (hup : ∀ a : ℕ, a = 1 ∨ a = 5 → ∀ m : ℕ, z < m →
      (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + ε) * m)
    (hp : p ∈ rungSlice X z i) :
    (apCount (rungClass p) (X / p) : ℝ)
      ≤ (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
          * ((X : ℝ) / ((p : ℝ) * (2 * Real.log X))) := by
  have hX : 2 ≤ X := le_trans (by norm_num) hXbig
  obtain ⟨hpr, hlow, hhigh⟩ : (p.Prime ∧ z < p ∧ p * p ≤ X)
      ∧ X ^ (14 + i) < p ^ 40 ∧ p ^ 40 ≤ X ^ (15 + i) := by
    have h1 := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_filter.mp h1.1).2, h1.2.1, h1.2.2⟩
  obtain ⟨hpp, hzp, hppX⟩ := hpr
  have hp2 : 2 ≤ p := hpp.two_le
  have hp0R : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by exact_mod_cast hX)
  set m : ℕ := X / p with hmdef
  have hpm : p ≤ m := (Nat.le_div_iff_mul_le (by omega)).mpr hppX
  have hm2 : 2 ≤ m := le_trans hp2 hpm
  have hzm : z < m := lt_of_lt_of_le hzp hpm
  have hlogm : (0 : ℝ) < Real.log m := Real.log_pos (by exact_mod_cast hm2)
  have hi5 : (i : ℝ) ≤ 5 := by exact_mod_cast Nat.lt_succ_iff.mp hi
  have h49 : (0 : ℝ) < 49 - 2 * (i : ℝ) := by linarith
  -- (1) numerator: m ≤ X/p
  have hcastdiv : (m : ℝ) ≤ (X : ℝ) / (p : ℝ) := by
    rw [hmdef]
    exact Nat.cast_div_le
  -- (2) denominator: log m ≥ ((49−2i)/80)·log X
  have hmlt : (X : ℝ) / (p : ℝ) < (m : ℝ) + 1 := by
    rw [div_lt_iff₀ hp0R]
    have hnat : X < p * (m + 1) := by
      have h1 : p * m + X % p = X := by
        rw [hmdef]
        exact Nat.div_add_mod X p
      have h2 : X % p < p := Nat.mod_lt _ (by omega)
      calc X = p * m + X % p := h1.symm
        _ < p * m + p := by omega
        _ = p * (m + 1) := by ring
    calc (X : ℝ) < ((p * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((m : ℝ) + 1) * (p : ℝ) := by push_cast; ring
  have hX2p : 2 * (p : ℝ) ≤ (X : ℝ) := by
    have h1 : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
    have h2 : 2 * p ≤ X := le_trans h1 hppX
    exact_mod_cast h2
  have hm_half : (X : ℝ) / (2 * (p : ℝ)) ≤ (m : ℝ) := by
    have h1 : (1 : ℝ) ≤ (X : ℝ) / (2 * (p : ℝ)) :=
      (one_le_div₀ (by positivity)).mpr hX2p
    have h2 : (X : ℝ) / (p : ℝ) = 2 * ((X : ℝ) / (2 * (p : ℝ))) := by
      field_simp
    linarith
  have hhalf_pos : (0 : ℝ) < (X : ℝ) / (2 * (p : ℝ)) := by positivity
  have hlog_half : Real.log ((X : ℝ) / (2 * (p : ℝ))) ≤ Real.log m :=
    Real.log_le_log hhalf_pos hm_half
  have hlog_expand : Real.log ((X : ℝ) / (2 * (p : ℝ)))
      = Real.log X - Real.log 2 - Real.log p := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    ring
  have hlogp : 40 * Real.log p ≤ (15 + (i : ℝ)) * Real.log X := by
    have hc : ((p : ℝ)) ^ (40 : ℕ) ≤ ((X : ℝ)) ^ (15 + i : ℕ) := by
      exact_mod_cast hhigh
    have hl := Real.log_le_log (by positivity) hc
    rw [Real.log_pow, Real.log_pow] at hl
    push_cast at hl
    linarith
  have hlog2 : 80 * Real.log 2 ≤ Real.log X := by
    have hc : ((2 : ℝ)) ^ (80 : ℕ) ≤ ((X : ℝ)) := by exact_mod_cast hXbig
    have hl := Real.log_le_log (by positivity) hc
    rw [Real.log_pow] at hl
    push_cast at hl
    linarith
  have hlogm_ge : (49 - 2 * (i : ℝ)) / 80 * Real.log X ≤ Real.log m := by
    have h1 : Real.log X - Real.log 2 - Real.log p ≤ Real.log m := by
      rw [← hlog_expand]
      exact hlog_half
    linarith
  -- (3) the interface at scale m, then the two monotonicities
  have happly := hup (rungClass p) (rungClass_or p) m hzm
  set T : ℝ := (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
      * ((X : ℝ) / ((p : ℝ) * (2 * Real.log X))) with hTdef
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    have h80 : (0 : ℝ) ≤ 80 / (49 - 2 * (i : ℝ)) := by positivity
    positivity
  have hTeq : T * (2 * ((49 - 2 * (i : ℝ)) / 80 * Real.log X))
      = (1 + ε) * ((X : ℝ) / (p : ℝ)) := by
    rw [hTdef]
    field_simp
  have hT2 : (1 + ε) * (m : ℝ) ≤ T * (2 * Real.log m) := by
    calc (1 + ε) * (m : ℝ)
        ≤ (1 + ε) * ((X : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hcastdiv (by linarith)
      _ = T * (2 * ((49 - 2 * (i : ℝ)) / 80 * Real.log X)) := hTeq.symm
      _ ≤ T * (2 * Real.log m) := by
          apply mul_le_mul_of_nonneg_left _ hT0
          linarith
  exact le_of_mul_le_mul_right (happly.trans hT2) (by positivity)

/-! ### Layer 5: the margin constant -/

/-- The Chebyshev-inflated wing margin constant:
`Σ_{i<6} (80/(49−2i))·(log 4/(14+i)) ≈ 0.9247`. -/
noncomputable def wingK : ℝ :=
  ∑ i ∈ Finset.range 6, (80 / (49 - 2 * (i : ℝ))) * (Real.log 4 / (14 + (i : ℝ)))

theorem wingK_nonneg : 0 ≤ wingK := by
  unfold wingK
  apply Finset.sum_nonneg
  intro i hi
  have hi5 : (i : ℝ) ≤ 5 := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h49 : (0 : ℝ) < 49 - 2 * (i : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  apply mul_nonneg (div_nonneg (by norm_num) h49.le)
  exact div_nonneg hlog4 (by positivity)

/-- Certified numeric cap (`log 4 < 1.38629437`, exact rationals):
`wingK ≤ 0.925`. -/
theorem wingK_le : wingK ≤ 0.925 := by
  unfold wingK
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_lt_d9
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

/-! ### Layer 6: the assembled semiprime bound and THE CROWN -/

/-- The full rung-sum cap: `Σ_p apCount(c_p, X/p) ≤
(1+ε)·(X/(2 log X))·wingK·(1 + 80/log X)`. -/
theorem rung_sum_le {X z : ℕ} {ε : ℝ} (hε : 0 < ε) (hXbig : 2 ^ 80 ≤ X)
    (h14 : X ^ 14 ≤ z ^ 40)
    (hup : ∀ a : ℕ, a = 1 ∨ a = 5 → ∀ m : ℕ, z < m →
      (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + ε) * m) :
    ∑ p ∈ rungPrimes X z, (apCount (rungClass p) (X / p) : ℝ)
      ≤ (1 + ε) * ((X : ℝ) / (2 * Real.log X)) * wingK
          * (1 + 80 / Real.log X) := by
  have hX : 2 ≤ X := le_trans (by norm_num) hXbig
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hdisj : (↑(Finset.range 6) : Set ℕ).PairwiseDisjoint
      (fun i => rungSlice X z i) := by
    intro i hi j hj hij
    exact slices_disjoint hX i (Finset.mem_coe.mp hi) j
      (Finset.mem_coe.mp hj) hij
  rw [rungPrimes_eq_biUnion_slices hX h14, Finset.sum_biUnion hdisj]
  have hper : ∀ i ∈ Finset.range 6,
      ∑ p ∈ rungSlice X z i, (apCount (rungClass p) (X / p) : ℝ)
        ≤ ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * (1 + 80 / Real.log X))
            * ((80 / (49 - 2 * (i : ℝ))) * (Real.log 4 / (14 + (i : ℝ)))) := by
    intro i hi
    have hi6 : i < 6 := Finset.mem_range.mp hi
    have hi5 : (i : ℝ) ≤ 5 := by exact_mod_cast Nat.lt_succ_iff.mp hi6
    have h49 : (0 : ℝ) < 49 - 2 * (i : ℝ) := by linarith
    have hstep1 : ∑ p ∈ rungSlice X z i, (apCount (rungClass p) (X / p) : ℝ)
        ≤ ∑ p ∈ rungSlice X z i, (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
            * ((X : ℝ) / ((p : ℝ) * (2 * Real.log X))) :=
      Finset.sum_le_sum fun p hp => slice_apCount_le hε hXbig hi6 hup hp
    have hstep2 : ∑ p ∈ rungSlice X z i, (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
          * ((X : ℝ) / ((p : ℝ) * (2 * Real.log X)))
        = ((1 + ε) * (80 / (49 - 2 * (i : ℝ)))
            * ((X : ℝ) / (2 * Real.log X)))
          * ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    have hD0 : (0 : ℝ) ≤ (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
        * ((X : ℝ) / (2 * Real.log X)) := by
      apply mul_nonneg (mul_nonneg (by linarith)
        (div_nonneg (by norm_num) h49.le))
      positivity
    have hstep3 := slice_inv_sum_le (X := X) (z := z) (i := i) hXbig hi6
    calc ∑ p ∈ rungSlice X z i, (apCount (rungClass p) (X / p) : ℝ)
        ≤ ((1 + ε) * (80 / (49 - 2 * (i : ℝ)))
              * ((X : ℝ) / (2 * Real.log X)))
            * ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹ := by
          rw [← hstep2]
          exact hstep1
      _ ≤ ((1 + ε) * (80 / (49 - 2 * (i : ℝ)))
              * ((X : ℝ) / (2 * Real.log X)))
            * (Real.log 4 * (1 / (14 + i : ℝ))
                + 2 * Real.log 4 * (40 / ((14 + i : ℝ) * Real.log X))) :=
          mul_le_mul_of_nonneg_left hstep3 hD0
      _ = ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * (1 + 80 / Real.log X))
            * ((80 / (49 - 2 * (i : ℝ))) * (Real.log 4 / (14 + (i : ℝ)))) := by
          have h14ne : (14 + (i : ℝ)) ≠ 0 := by positivity
          field_simp [h49.ne', hlogX.ne']
          ring
  calc ∑ i ∈ Finset.range 6, ∑ p ∈ rungSlice X z i,
        (apCount (rungClass p) (X / p) : ℝ)
      ≤ ∑ i ∈ Finset.range 6,
          ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * (1 + 80 / Real.log X))
            * ((80 / (49 - 2 * (i : ℝ))) * (Real.log 4 / (14 + (i : ℝ)))) :=
        Finset.sum_le_sum hper
    _ = ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * (1 + 80 / Real.log X))
          * wingK := by
        rw [← Finset.mul_sum]
        rfl
    _ = (1 + ε) * ((X : ℝ) / (2 * Real.log X)) * wingK
          * (1 + 80 / Real.log X) := by ring

/-- **THE WING SIGN THEOREM (conditional form).**  Under the AP-PNT
interface, every full rough minus window with `X^7 ≤ z^20 ≤ X^9`
eventually satisfies `Σ_m λ(6m−1) ≤ −(1/40)·X/log X`.

DISCLOSURE: this is the PER-WING sign at count level — it does NOT
discharge, shrink, or reweight OneWingTarget (twin-strength by
pigeonhole; three bridges refuted).  The `atTop` threshold is
ineffective; the constant is Chebyshev-inflated.  Twin sorry untouched. -/
theorem minus_wing_sign_of_apPNT
    (hAP : ∀ a : ℕ, a = 1 ∨ a = 5 →
      Tendsto (fun n : ℕ => (apCount a n : ℝ) * (2 * Real.log n) / n)
        atTop (nhds 1)) :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ minusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ)
        ≤ -(1 / 40) * X / Real.log X := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (interface_bounds (hAP 1 (Or.inl rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp
    (interface_bounds (hAP 5 (Or.inr rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  have hlogT : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzsm : ∀ᶠ n : ℕ in atTop,
      Real.log n / (n : ℝ) ^ ((11 : ℝ) / 20) ≤ 1 / 200 := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ ((11 : ℝ) / 20))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
    have h2 := h1.comp tendsto_natCast_atTop_atTop
    have h3 := Metric.tendsto_nhds.mp h2 (1 / 200) (by norm_num)
    filter_upwards [h3] with n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at hn
    exact hn.2.le
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop (2 ^ 80),
    eventually_ge_atTop N₅, eventually_ge_atTop ((max N₁ N₅ + 2) ^ 3),
    hlogT.eventually_ge_atTop 8000, hzsm]
    with X h2X hbig hN5X hNc h8000 hzs
  intro z h7 h9
  obtain ⟨hz2, hXz3, hzzX, h14⟩ := z_facts h2X h7 h9
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by exact_mod_cast h2X)
  -- the uniform upper interface above z
  have hzN : max N₁ N₅ + 2 ≤ z := by
    have h1 : (max N₁ N₅ + 2) ^ 20 ≤ z ^ 20 := by
      calc (max N₁ N₅ + 2) ^ 20
          ≤ (max N₁ N₅ + 2) ^ 21 :=
            Nat.pow_le_pow_right (by omega) (by omega)
        _ = ((max N₁ N₅ + 2) ^ 3) ^ 7 := by ring
        _ ≤ X ^ 7 := Nat.pow_le_pow_left hNc 7
        _ ≤ z ^ 20 := h7
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hup : ∀ a : ℕ, a = 1 ∨ a = 5 → ∀ m : ℕ, z < m →
      (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + 1 / 1000) * m := by
    intro a ha m hzm
    rcases ha with rfl | rfl
    · exact (hN₁ m (by have := le_max_left N₁ N₅; omega)).2
    · exact (hN₅ m (by have := le_max_right N₁ N₅; omega)).2
  -- Σλ = S − P, cast to ℝ
  have hsum := minusWindow_liouville_eq (X := X) (z := z) (by omega) hXz3
  have hsumR : ((∑ m ∈ minusRoughWindow X z,
        ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ)
      = (wingS X z : ℝ) - (wingP X z : ℝ) := by
    rw [hsum]
    push_cast
    ring
  -- P lower bound
  have hzX : z ≤ X := by
    calc z = z * 1 := by ring
      _ ≤ z * z := Nat.mul_le_mul_left z (by omega)
      _ ≤ X := hzzX
  have hPcast : (wingP X z : ℝ) = (apCount 5 X : ℝ) - (apCount 5 z : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (wingP_add_apCount (X := X) (z := z) hzX)
    push_cast at h
    linarith
  have hP5X : (1 - 1 / 1000) * X / (2 * Real.log X) ≤ (apCount 5 X : ℝ) :=
    apCount_lower_of_bound (hN₅ X hN5X).1 h2X
  have hz_apc : (apCount 5 z : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast apCount_le 5 z
  -- the z-term is o(X/log X): z ≤ X^{9/20} and log X ≤ X^{11/20}/200
  have hzrpow : (z : ℝ) ≤ (X : ℝ) ^ ((9 : ℝ) / 20) := by
    have h40 : ((X : ℝ) ^ ((9 : ℝ) / 20)) ^ (20 : ℕ) = (X : ℝ) ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ ((9 : ℝ) / 20)) 20,
        ← Real.rpow_mul hX0.le,
        show (((20 : ℕ) : ℝ)) = (20 : ℝ) from by norm_num,
        div_mul_cancel₀ _ (by norm_num : (20 : ℝ) ≠ 0),
        show ((9 : ℝ)) = (((9 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast]
    have hc : ((z : ℝ)) ^ (20 : ℕ) ≤ ((X : ℝ)) ^ (9 : ℕ) := by
      exact_mod_cast h9
    rw [← h40] at hc
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hX0.le _) hc
  have hzterm : (z : ℝ) ≤ (1 / 100) * ((X : ℝ) / (2 * Real.log X)) := by
    have hrp : (0 : ℝ) < (X : ℝ) ^ ((11 : ℝ) / 20) := by positivity
    have h200 : 200 * Real.log X ≤ (X : ℝ) ^ ((11 : ℝ) / 20) := by
      rw [div_le_iff₀ hrp] at hzs
      linarith
    have hsplit : (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20)
        = (X : ℝ) := by
      rw [← Real.rpow_add hX0,
        show (9 : ℝ) / 20 + 11 / 20 = 1 from by norm_num, Real.rpow_one]
    have hmul : (z : ℝ) * (200 * Real.log X) ≤ (X : ℝ) := by
      calc (z : ℝ) * (200 * Real.log X)
          ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (200 * Real.log X) :=
            mul_le_mul_of_nonneg_right hzrpow (by positivity)
        _ ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20) :=
            mul_le_mul_of_nonneg_left h200 (by positivity)
        _ = (X : ℝ) := hsplit
    rw [show (1 / 100 : ℝ) * ((X : ℝ) / (2 * Real.log X))
      = (X : ℝ) / (200 * Real.log X) from by ring]
    rw [le_div_iff₀ (by positivity)]
    exact hmul
  -- S upper bound
  have hScast : (wingS X z : ℝ)
      ≤ ∑ p ∈ rungPrimes X z, (apCount (rungClass p) (X / p) : ℝ) := by
    have h := wingS_le_rung_sum (X := X) (z := z)
    calc (wingS X z : ℝ)
        ≤ ((∑ p ∈ rungPrimes X z, apCount (rungClass p) (X / p) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = ∑ p ∈ rungPrimes X z, (apCount (rungClass p) (X / p) : ℝ) := by
          push_cast
          rfl
  have hSup := rung_sum_le (X := X) (z := z)
    (by norm_num : (0 : ℝ) < 1 / 1000) hbig h14 hup
  -- numeric assembly
  have h80 : 80 / Real.log X ≤ 1 / 100 := by
    rw [div_le_iff₀ hlogX]
    linarith
  have h80pos : (0 : ℝ) ≤ 80 / Real.log X := by positivity
  have hprod : (1 + 1 / 1000) * (wingK * (1 + 80 / Real.log X))
      ≤ 0.936 := by
    have hb1 : wingK * (1 + 80 / Real.log X) ≤ 0.925 * (1 + 1 / 100) :=
      mul_le_mul wingK_le (by linarith) (by linarith) (by norm_num)
    nlinarith
  have hA0 : (0 : ℝ) ≤ (X : ℝ) / (2 * Real.log X) := by positivity
  have hSfinal : (wingS X z : ℝ)
      ≤ 0.936 * ((X : ℝ) / (2 * Real.log X)) := by
    calc (wingS X z : ℝ)
        ≤ (1 + 1 / 1000) * ((X : ℝ) / (2 * Real.log X)) * wingK
            * (1 + 80 / Real.log X) := hScast.trans hSup
      _ = ((X : ℝ) / (2 * Real.log X))
            * ((1 + 1 / 1000) * (wingK * (1 + 80 / Real.log X))) := by ring
      _ ≤ ((X : ℝ) / (2 * Real.log X)) * 0.936 :=
          mul_le_mul_of_nonneg_left hprod hA0
      _ = 0.936 * ((X : ℝ) / (2 * Real.log X)) := by ring
  have hPfinal : 0.989 * ((X : ℝ) / (2 * Real.log X)) ≤ (wingP X z : ℝ) := by
    have h999 : (1 - 1 / 1000) * X / (2 * Real.log X)
        = 0.999 * ((X : ℝ) / (2 * Real.log X)) := by ring
    rw [hPcast]
    rw [h999] at hP5X
    linarith
  -- conclusion
  rw [hsumR]
  have hfin : (wingS X z : ℝ) - (wingP X z : ℝ)
      ≤ -(1 / 20) * ((X : ℝ) / (2 * Real.log X)) := by linarith
  calc (wingS X z : ℝ) - (wingP X z : ℝ)
      ≤ -(1 / 20) * ((X : ℝ) / (2 * Real.log X)) := hfin
    _ = -(1 / 40) * X / Real.log X := by ring

/-- **THE CROWN (unconditional).**  The AP-PNT interface is DISCHARGED
by the campaign's `Analytic.apCount_mul_log_div_tendsto`: eventually,
every full rough minus window with `X^7 ≤ z^20 ≤ X^9` carries strictly
negative Liouville bias of size `≥ (1/40)·X/log X`.

DISCLOSURES: per-wing count-level sign ONLY — OneWingTarget is NOT
discharged, NOT premise-shrunk, NOT reweighted (any valid instantiation
forces twin-count > 0 by pigeonhole; three bridges refuted).  The
threshold is ineffective (`1/log X`-rate boundary terms); the empirical
grounding at `X = 10⁷` (Σλ = −172058/−238841/−299193 at θ = .35/.40/.45)
confirms the sign, not the threshold.  `log 4`-grade constant, not the
true `log((1−θ)/θ)`.  The plus wing is named, unclaimed work.  The twin
sorry is untouched. -/
theorem minus_wing_sign :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ minusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ)
        ≤ -(1 / 40) * X / Real.log X :=
  minus_wing_sign_of_apPNT fun _ ha =>
    EuclidsPath.Analytic.apCount_mul_log_div_tendsto ha

/-- Display form: the window bias is eventually strictly negative. -/
theorem minus_wing_sign_neg :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      (∑ m ∈ minusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) < 0 := by
  filter_upwards [minus_wing_sign, eventually_ge_atTop 2] with X hX h2X
  intro z h7 h9
  have h := hX z h7 h9
  have hlogX : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast h2X)
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    linarith
  have hneg : ((∑ m ∈ minusRoughWindow X z,
      ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ) < 0 := by
    have : -(1 / 40 : ℝ) * X / Real.log X < 0 := by
      apply div_neg_of_neg_of_pos _ hlogX
      nlinarith
    linarith
  exact_mod_cast hneg

end TypeII
end Geometric
end EuclidsPath
