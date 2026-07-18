/-
  GeometricTwinFourCellLog — THE LOG-AVERAGED FOUR-CELL LAYER: the named
  logarithmically averaged two-point Chowla hypothesis for the split form,
  the machine-proved implication natural ⇒ log (discrete Abel summation),
  and the log-averaged sign-pattern equidistribution corollary.

  (1) `Chowla2LogHypothesis` — the LOG-AVERAGED two-point Chowla for the
      split form: `(Σ_{m ≤ X} λ(6m−1)λ(6m+1)/m) / log X → 0`.
      DISCLOSURE: THIS hypothesis is a THEOREM in the literature — Tao 2016
      (Forum Math. Pi, "The logarithmically averaged Chowla and Elliott
      conjectures for two-point correlations") proves logarithmically
      averaged Chowla for `λ(an+b)λ(cn+d)` with `ad − bc ≠ 0`; our case is
      `a = c = 6`, `b = −1`, `d = 1`.  It is NOT formalized in mathlib or
      in this repository, so here it stays a NAMED hypothesis in the house
      pattern — NO axiom, NO sorry.  Nothing in this file proves it.

  (2) THE IMPLICATION natural ⇒ log (`chowla2_log_of_natural`), through a
      GENERIC machine-proved Abel-summation lemma `log_average_of_natural`:
      for any `c : ℕ → ℝ` with `Σ_{m ≤ X} c m = o(X)` one has
      `Σ_{m ≤ X} c m / m = o(log X)`.  Route: the exact discrete Abel
      identity (proved by induction)

          Σ_{m ≤ X} c m/m = C(X)/X + Σ_{1 ≤ k < X} C(k)/(k(k+1)),

      with `C(k) = Σ_{m ≤ k} c m`, then an ε-split: `|C(k)| ≤ (ε/4)k` for
      `k ≥ K₀`, a bounded finite head, and the harmonic tail bound
      `Σ_{1 ≤ k < X} 1/(k+1) ≤ log X` (from mathlib's
      `harmonic_le_one_add_log`).

  (3) THE LOG-AVERAGED FOUR-CELL COROLLARY
      (`log_pattern_density_of_chowla2_log`): under `Chowla2LogHypothesis`
      alone, all four log-averaged sign-pattern densities

          (Σ_{m ≤ X, λ(6m−1)=e, λ(6m+1)=d} 1/m) / log X  →  1/4.

      The log-averaged single wings `(Σ_{m ≤ X} λ(6m∓1)/m)/log X → 0` are
      UNCONDITIONAL — instances of the same generic Abel lemma applied to
      the repository's unconditional `wingMinus_div_tendsto` /
      `wingPlus_div_tendsto`; the harmonic normalization
      `(Σ_{m ≤ X} 1/m)/log X → 1` is proved from mathlib's two-sided
      harmonic bounds.  The combinatorial engine is a weighted four-cell
      identity (`four_cell_weighted`) generalizing `four_cell_identity`.

  DISCLOSURES (mandatory reading before quoting).
    * The log-averaged hypothesis (1) is exactly where the WORLD'S proven
      frontier sits (Tao 2016).  The gap between `Chowla2Hypothesis`
      (natural density, OPEN) and `Chowla2LogHypothesis` (log-averaged,
      proven in the literature but not formalized) is the sharpest known
      formulation of the parity wall for this program.  The implication
      proved here goes in the direction natural ⇒ log — the EASY direction;
      the converse is open and NOTHING here addresses it.
    * NOTHING MOVES THE PARITY WALL.  This file converts one named
      hypothesis into another and proves unconditional bookkeeping around
      them.  No claim is made on sieved (pair-rough) windows.
    * No new axioms, no sorry.  The twin sorry (`twin_prime_conjecture`)
      is untouched.  This file is NOT registered in `EuclidsPath.lean`.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTwinFourCell

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace FourCellLog

open Finset Filter ArithmeticFunction FourCell

/-! ### (2a) The exact discrete Abel summation identity -/

/-- **Discrete Abel summation** (exact, any window): with
`C(k) = Σ_{m ∈ Icc 1 k} c m`,

`Σ_{m ∈ Icc 1 X} c m / m = C(X)/X + Σ_{k ∈ Ico 1 X} C(k)/(k(k+1))`.

Proved by induction on `X`; the step is the partial-fraction identity
`1/k = 1/(k+1) + 1/(k(k+1))`. -/
theorem abel_partial_summation (c : ℕ → ℝ) (X : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, c m / (m : ℝ)
      = (∑ m ∈ Finset.Icc 1 X, c m) / (X : ℝ)
        + ∑ k ∈ Finset.Ico 1 X,
            (∑ m ∈ Finset.Icc 1 k, c m) / ((k : ℝ) * ((k : ℝ) + 1)) := by
  induction X with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
      simp
  | succ X ih =>
      rcases Nat.eq_zero_or_pos X with rfl | hX
      · simp
      · rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ X + 1),
          Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ X + 1),
          Finset.sum_Ico_succ_top (by omega : (1 : ℕ) ≤ X), ih]
        have hX0 : ((X : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hX1 : ((X : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp
        ring

/-! ### (2b) Harmonic-sum bounds through mathlib's `harmonic` -/

/-- The harmonic window sum `Σ_{m ≤ X} 1/m` (real-valued). -/
noncomputable def harmonicWindow (X : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 X, (1 : ℝ) / (m : ℝ)

/-- The harmonic window sum is mathlib's `harmonic X`. -/
theorem harmonicWindow_eq (X : ℕ) :
    harmonicWindow X = ((harmonic X : ℚ) : ℝ) := by
  unfold harmonicWindow
  rw [harmonic_eq_sum_Icc]
  push_cast
  exact Finset.sum_congr rfl fun m _ => one_div _

/-- **The harmonic tail bound**: `Σ_{k ∈ Ico 1 X} 1/(k+1) ≤ log X`
(the sum is `H_X − 1` and `H_X ≤ 1 + log X`). -/
theorem sum_one_div_succ_le_log {X : ℕ} (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Ico 1 X, (1 : ℝ) / ((k : ℝ) + 1) ≤ Real.log X := by
  have hshift : ∑ k ∈ Finset.Ico 1 X, (1 : ℝ) / ((k : ℝ) + 1)
      = ∑ i ∈ Finset.Icc 2 X, (1 : ℝ) / (i : ℝ) := by
    have h1 : ∑ k ∈ Finset.Ico 1 X, (1 : ℝ) / ((k : ℝ) + 1)
        = ∑ k ∈ Finset.Ico 1 X, (fun i : ℕ => (1 : ℝ) / (i : ℝ)) (k + 1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [h1, Finset.sum_Ico_add' (fun i : ℕ => (1 : ℝ) / (i : ℝ)) 1 X 1]
    congr 1
  have hins : ((harmonic X : ℚ) : ℝ)
      = 1 + ∑ i ∈ Finset.Icc 2 X, (1 : ℝ) / (i : ℝ) := by
    rw [← harmonicWindow_eq]
    unfold harmonicWindow
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨le_refl 1, hX⟩
    rw [← Finset.add_sum_erase _ _ hmem]
    congr 1
    · norm_num
    · congr 1
      ext i
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
  have hlog := harmonic_le_one_add_log X
  rw [hshift]
  linarith

/-! ### (2c) The generic natural ⇒ log Abel lemma -/

/-- **THE GENERIC NATURAL ⇒ LOG-AVERAGE LEMMA** (machine-proved Abel
summation with ε-split): if `Σ_{m ≤ X} c m = o(X)`, then
`Σ_{m ≤ X} c m / m = o(log X)`.

Instantiated three times below: the cross sum (giving
`Chowla2Hypothesis → Chowla2LogHypothesis`) and both single wings
(giving the UNCONDITIONAL log-averaged wing cancellations). -/
theorem log_average_of_natural (c : ℕ → ℝ)
    (hC : Tendsto (fun X : ℕ => (∑ m ∈ Finset.Icc 1 X, c m) / (X : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun X : ℕ =>
        (∑ m ∈ Finset.Icc 1 X, c m / (m : ℝ)) / Real.log X)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hC ⊢
  intro ε hε
  obtain ⟨K0, hK0⟩ := hC (ε / 4) (by positivity)
  set K1 : ℕ := max K0 1
  have hK1ge1 : 1 ≤ K1 := le_max_right K0 1
  have hK0K1 : K0 ≤ K1 := le_max_left K0 1
  set M : ℝ := ∑ k ∈ Finset.Ico 1 K1,
    |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1))
  have hlogtop : Tendsto (fun Y : ℕ => Real.log Y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun Y : ℕ => (ε / 4 + M) / Real.log Y)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogtop
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hlog0 (ε / 2) (by positivity)
  refine ⟨max (max K1 2) N2, fun X hX => ?_⟩
  have hXK1 : K1 ≤ X :=
    le_trans (le_trans (le_max_left K1 2) (le_max_left (max K1 2) N2)) hX
  have hX2 : 2 ≤ X :=
    le_trans (le_trans (le_max_right K1 2) (le_max_left (max K1 2) N2)) hX
  have hXN2 : N2 ≤ X := le_trans (le_max_right (max K1 2) N2) hX
  have hX1 : 1 ≤ X := by omega
  have hlogpos : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < X))
  have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogpos
  -- the endpoint term
  have hCX : |∑ m ∈ Finset.Icc 1 X, c m| / (X : ℝ) < ε / 4 := by
    have h1 := hK0 X (le_trans hK0K1 hXK1)
    simp only [Real.dist_eq, sub_zero] at h1
    rwa [abs_div, Nat.abs_cast] at h1
  -- the pointwise tail bound for k ≥ K1
  have htailpt : ∀ k ∈ Finset.Ico K1 X,
      |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1))
        ≤ ε / 4 * (1 / ((k : ℝ) + 1)) := by
    intro k hk
    have hm := Finset.mem_Ico.mp hk
    have hk1 : 1 ≤ k := le_trans hK1ge1 hm.1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkpos1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have h1 := hK0 k (le_trans hK0K1 hm.1)
    simp only [Real.dist_eq, sub_zero] at h1
    rw [abs_div, Nat.abs_cast] at h1
    calc |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1))
        = |∑ m ∈ Finset.Icc 1 k, c m| / (k : ℝ) / ((k : ℝ) + 1) := by
          rw [← div_div]
      _ ≤ ε / 4 / ((k : ℝ) + 1) := by gcongr
      _ = ε / 4 * (1 / ((k : ℝ) + 1)) := by rw [div_eq_mul_one_div]
  -- the summed tail bound
  have htail : ∑ k ∈ Finset.Ico K1 X,
      |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1))
        ≤ ε / 4 * Real.log X := by
    calc ∑ k ∈ Finset.Ico K1 X,
        |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1))
        ≤ ∑ k ∈ Finset.Ico K1 X, ε / 4 * (1 / ((k : ℝ) + 1)) :=
          Finset.sum_le_sum htailpt
      _ ≤ ∑ k ∈ Finset.Ico 1 X, ε / 4 * (1 / ((k : ℝ) + 1)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun i _ _ => by positivity
          intro i hi
          have hm := Finset.mem_Ico.mp hi
          exact Finset.mem_Ico.mpr ⟨by omega, hm.2⟩
      _ = ε / 4 * ∑ k ∈ Finset.Ico 1 X, (1 : ℝ) / ((k : ℝ) + 1) := by
          rw [← Finset.mul_sum]
      _ ≤ ε / 4 * Real.log X := by
          exact mul_le_mul_of_nonneg_left (sum_one_div_succ_le_log hX1)
            (by positivity)
  -- the head is the constant M, split off exactly
  have hsplit : M + ∑ k ∈ Finset.Ico K1 X,
        |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1))
      = ∑ k ∈ Finset.Ico 1 X,
          |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1)) :=
    Finset.sum_Ico_consecutive _ hK1ge1 hXK1
  -- the Abel identity gives the master bound
  have habel : |∑ m ∈ Finset.Icc 1 X, c m / (m : ℝ)|
      ≤ |∑ m ∈ Finset.Icc 1 X, c m| / (X : ℝ)
        + ∑ k ∈ Finset.Ico 1 X,
            |∑ m ∈ Finset.Icc 1 k, c m| / ((k : ℝ) * ((k : ℝ) + 1)) := by
    rw [abel_partial_summation]
    refine le_trans (abs_add_le _ _) (add_le_add (le_of_eq ?_) ?_)
    · rw [abs_div, Nat.abs_cast]
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      rw [abs_div,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1))]
  have hbound : |∑ m ∈ Finset.Icc 1 X, c m / (m : ℝ)|
      ≤ ε / 4 + M + ε / 4 * Real.log X := by
    linarith [habel, hCX, htail, hsplit]
  -- assemble: divide by log X and use the ε-budget
  simp only [Real.dist_eq, sub_zero]
  have habs : |(∑ m ∈ Finset.Icc 1 X, c m / (m : ℝ)) / Real.log X|
      = |∑ m ∈ Finset.Icc 1 X, c m / (m : ℝ)| / Real.log X := by
    rw [abs_div, abs_of_pos hlogpos]
  have hdiv : |∑ m ∈ Finset.Icc 1 X, c m / (m : ℝ)| / Real.log X
      ≤ (ε / 4 + M + ε / 4 * Real.log X) / Real.log X := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr hlogpos.le)
  have hexp : (ε / 4 + M + ε / 4 * Real.log X) / Real.log X
      = (ε / 4 + M) / Real.log X + ε / 4 := by
    rw [add_div, mul_div_assoc, div_self hlogne, mul_one]
  have hfrac : (ε / 4 + M) / Real.log X < ε / 2 := by
    have h2 := hN2 X hXN2
    simp only [Real.dist_eq, sub_zero] at h2
    exact lt_of_abs_lt h2
  rw [habs]
  linarith [hdiv, hexp, hfrac]

/-! ### (1) The log-averaged window sums and the named hypothesis -/

/-- The log-averaged minus wing `Σ_{m ≤ X} λ(6m−1)/m`. -/
noncomputable def wingMinusLogSum (X : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 X, ((liouville (6 * m - 1) : ℤ) : ℝ) / (m : ℝ)

/-- The log-averaged plus wing `Σ_{m ≤ X} λ(6m+1)/m`. -/
noncomputable def wingPlusLogSum (X : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 X, ((liouville (6 * m + 1) : ℤ) : ℝ) / (m : ℝ)

/-- The log-averaged cross sum `Σ_{m ≤ X} λ(6m−1)λ(6m+1)/m`. -/
noncomputable def crossLogSum (X : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 X,
    ((liouville (6 * m - 1) : ℤ) : ℝ) * ((liouville (6 * m + 1) : ℤ) : ℝ)
      / (m : ℝ)

/-- The log-weighted sign-pattern sum
`Σ_{m ≤ X, λ(6m−1)=e, λ(6m+1)=d} 1/m`. -/
noncomputable def logPatternSum (X : ℕ) (e d : ℤ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 X).filter
    (fun m => liouville (6 * m - 1) = e ∧ liouville (6 * m + 1) = d),
      (1 : ℝ) / (m : ℝ)

/-- **Chowla2LogHypothesis** (house named-hypothesis pattern — NOT an
axiom): the LOGARITHMICALLY AVERAGED two-point Chowla for the split form,

`(Σ_{m ≤ X} λ(6m−1)·λ(6m+1)/m) / log X → 0`.

DISCLOSURE: this hypothesis is a THEOREM in the literature — Tao 2016
(Forum Math. Pi 4, e8: logarithmically averaged Chowla for
`λ(an+b)λ(cn+d)` with `ad − bc ≠ 0`; here `a = c = 6`, `b = −1`,
`d = 1`, so `ad − bc = 12 ≠ 0`) — but it is NOT formalized in mathlib or
in this repository.  It therefore stays a NAMED hypothesis: NO axiom, NO
sorry, and no theorem in this repository asserts it. -/
def Chowla2LogHypothesis : Prop :=
  Tendsto (fun X : ℕ => crossLogSum X / Real.log X) atTop (nhds 0)

/-! ### (2) The implication natural ⇒ log -/

/-- **Natural ⇒ log for the cross sum**: the natural-density two-point
Chowla `Chowla2Hypothesis` implies the log-averaged
`Chowla2LogHypothesis`.  This is the EASY direction of the gap; the
converse — recovering natural density from Tao's log-averaged theorem —
is the open parity-wall formulation, and nothing here addresses it. -/
theorem chowla2_log_of_natural (hC : Chowla2Hypothesis) :
    Chowla2LogHypothesis := by
  have hkey : ∀ X : ℕ, ((crossSum X : ℤ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 X,
          ((liouville (6 * m - 1) : ℤ) : ℝ)
            * ((liouville (6 * m + 1) : ℤ) : ℝ) := by
    intro X
    unfold crossSum
    push_cast
    rfl
  have hC' : Tendsto (fun X : ℕ =>
      (∑ m ∈ Finset.Icc 1 X,
        ((liouville (6 * m - 1) : ℤ) : ℝ)
          * ((liouville (6 * m + 1) : ℤ) : ℝ)) / (X : ℝ))
      atTop (nhds 0) := by
    refine hC.congr fun X => ?_
    rw [hkey]
  exact log_average_of_natural
    (fun m => ((liouville (6 * m - 1) : ℤ) : ℝ)
      * ((liouville (6 * m + 1) : ℤ) : ℝ)) hC'

/-- **The log-averaged minus wing is UNCONDITIONAL**:
`(Σ_{m ≤ X} λ(6m−1)/m)/log X → 0` — the generic Abel lemma applied to the
repository's unconditional `wingMinus_div_tendsto`. -/
theorem wingMinusLog_div_tendsto :
    Tendsto (fun X : ℕ => wingMinusLogSum X / Real.log X) atTop (nhds 0) := by
  have hkey : ∀ X : ℕ, ((wingMinusSum X : ℤ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 X, ((liouville (6 * m - 1) : ℤ) : ℝ) := by
    intro X
    unfold wingMinusSum
    push_cast
    rfl
  have hC' : Tendsto (fun X : ℕ =>
      (∑ m ∈ Finset.Icc 1 X, ((liouville (6 * m - 1) : ℤ) : ℝ)) / (X : ℝ))
      atTop (nhds 0) := by
    refine wingMinus_div_tendsto.congr fun X => ?_
    rw [hkey]
  exact log_average_of_natural
    (fun m => ((liouville (6 * m - 1) : ℤ) : ℝ)) hC'

/-- **The log-averaged plus wing is UNCONDITIONAL**:
`(Σ_{m ≤ X} λ(6m+1)/m)/log X → 0`. -/
theorem wingPlusLog_div_tendsto :
    Tendsto (fun X : ℕ => wingPlusLogSum X / Real.log X) atTop (nhds 0) := by
  have hkey : ∀ X : ℕ, ((wingPlusSum X : ℤ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 X, ((liouville (6 * m + 1) : ℤ) : ℝ) := by
    intro X
    unfold wingPlusSum
    push_cast
    rfl
  have hC' : Tendsto (fun X : ℕ =>
      (∑ m ∈ Finset.Icc 1 X, ((liouville (6 * m + 1) : ℤ) : ℝ)) / (X : ℝ))
      atTop (nhds 0) := by
    refine wingPlus_div_tendsto.congr fun X => ?_
    rw [hkey]
  exact log_average_of_natural
    (fun m => ((liouville (6 * m + 1) : ℤ) : ℝ)) hC'

/-! ### (3) The weighted four-cell identity and the log-averaged corollary -/

/-- **The WEIGHTED four-cell identity** (unconditional, any finite window,
any real weight): if `a` and `b` take values in `{1, −1}` on `I`, then for
signs `e, d ∈ {1, −1}` and any weight `w : ℕ → ℝ`,

`4·Σ_{m ∈ I, a m = e, b m = d} w m
  = Σ_I w + e·Σ_I a·w + d·Σ_I b·w + e·d·Σ_I a·b·w`.

The unweighted `four_cell_identity` is the case `w ≡ 1`. -/
theorem four_cell_weighted (I : Finset ℕ) (a b : ℕ → ℤ) (w : ℕ → ℝ)
    (ha : ∀ m ∈ I, a m ^ 2 = 1) (hb : ∀ m ∈ I, b m ^ 2 = 1)
    {e d : ℤ} (he : e ^ 2 = 1) (hd : d ^ 2 = 1) :
    4 * ∑ m ∈ I.filter (fun m => a m = e ∧ b m = d), w m
      = ∑ m ∈ I, w m + (e : ℝ) * ∑ m ∈ I, (a m : ℝ) * w m
        + (d : ℝ) * ∑ m ∈ I, (b m : ℝ) * w m
        + (e : ℝ) * (d : ℝ) * ∑ m ∈ I, (a m : ℝ) * (b m : ℝ) * w m := by
  have hcell : ∀ m ∈ I,
      ((1 : ℝ) + (e : ℝ) * (a m : ℝ)) * ((1 : ℝ) + (d : ℝ) * (b m : ℝ))
        = if a m = e ∧ b m = d then (4 : ℝ) else 0 := by
    intro m hm
    have h := cell_factor (ha m hm) (hb m hm) he hd
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
    have h3 : ((if a m = e ∧ b m = d then (4 : ℤ) else 0 : ℤ) : ℝ)
        = if a m = e ∧ b m = d then (4 : ℝ) else 0 := by
      split_ifs <;> norm_num
    rw [← h3, ← h2]
    push_cast
    ring
  calc 4 * ∑ m ∈ I.filter (fun m => a m = e ∧ b m = d), w m
      = ∑ m ∈ I, (if a m = e ∧ b m = d then (4 : ℝ) else 0) * w m := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> ring
    _ = ∑ m ∈ I, ((1 : ℝ) + (e : ℝ) * (a m : ℝ))
          * ((1 : ℝ) + (d : ℝ) * (b m : ℝ)) * w m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [hcell m hm]
    _ = ∑ m ∈ I, (w m + ((e : ℝ) * ((a m : ℝ) * w m)
          + ((d : ℝ) * ((b m : ℝ) * w m)
            + ((e : ℝ) * (d : ℝ)) * ((a m : ℝ) * (b m : ℝ) * w m)))) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ = ∑ m ∈ I, w m + ((e : ℝ) * ∑ m ∈ I, (a m : ℝ) * w m
          + ((d : ℝ) * ∑ m ∈ I, (b m : ℝ) * w m
            + ((e : ℝ) * (d : ℝ))
              * ∑ m ∈ I, (a m : ℝ) * (b m : ℝ) * w m)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ = ∑ m ∈ I, w m + (e : ℝ) * ∑ m ∈ I, (a m : ℝ) * w m
          + (d : ℝ) * ∑ m ∈ I, (b m : ℝ) * w m
          + (e : ℝ) * (d : ℝ) * ∑ m ∈ I, (a m : ℝ) * (b m : ℝ) * w m := by
        ring

/-- **The log-weighted window four-cell identity** (unconditional): on
`Icc 1 X` with weight `1/m`,

`4·logPatternSum(e,d) = Σ 1/m + e·L−_log + d·L+_log + e·d·Lx_log`. -/
theorem window_four_cell_log (X : ℕ) {e d : ℤ}
    (he : e ^ 2 = 1) (hd : d ^ 2 = 1) :
    4 * logPatternSum X e d
      = harmonicWindow X + (e : ℝ) * wingMinusLogSum X
        + (d : ℝ) * wingPlusLogSum X
        + (e : ℝ) * (d : ℝ) * crossLogSum X := by
  have ha : ∀ m ∈ Finset.Icc 1 X, (liouville (6 * m - 1)) ^ 2 = 1 := by
    intro m hm
    have h1 := (Finset.mem_Icc.mp hm).1
    exact liouville_sq (by omega)
  have hb : ∀ m ∈ Finset.Icc 1 X, (liouville (6 * m + 1)) ^ 2 = 1 := by
    intro m _
    exact liouville_sq (by omega)
  have h := four_cell_weighted (Finset.Icc 1 X)
    (fun m => liouville (6 * m - 1)) (fun m => liouville (6 * m + 1))
    (fun m => (1 : ℝ) / (m : ℝ)) ha hb he hd
  simp only [mul_one_div] at h
  exact h

/-- **The harmonic normalization** (unconditional):
`(Σ_{m ≤ X} 1/m)/log X → 1` — squeezed between `1` and `1/log X + 1`
through mathlib's two-sided harmonic bounds. -/
theorem harmonicWindow_div_log_tendsto :
    Tendsto (fun X : ℕ => harmonicWindow X / Real.log X) atTop (nhds 1) := by
  have hlogtop : Tendsto (fun Y : ℕ => Real.log Y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun Y : ℕ => 1 / Real.log Y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlogtop
  have hupper : Tendsto (fun Y : ℕ => 1 / Real.log Y + 1) atTop (nhds 1) := by
    have := h0.add (tendsto_const_nhds (x := (1 : ℝ)))
    rwa [zero_add] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with X hX2
    have hlogpos : (0 : ℝ) < Real.log X :=
      Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < X))
    have hlow : Real.log (X : ℝ) ≤ harmonicWindow X := by
      rw [harmonicWindow_eq]
      refine le_trans ?_ (log_add_one_le_harmonic X)
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast (by omega : 0 < X)
      · push_cast
        linarith
    exact (one_le_div hlogpos).mpr hlow
  · filter_upwards [eventually_ge_atTop 2] with X hX2
    have hlogpos : (0 : ℝ) < Real.log X :=
      Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < X))
    have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogpos
    have hup : harmonicWindow X ≤ 1 + Real.log X := by
      rw [harmonicWindow_eq]
      exact harmonic_le_one_add_log X
    calc harmonicWindow X / Real.log X
        ≤ (1 + Real.log X) / Real.log X := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hup (inv_nonneg.mpr hlogpos.le)
      _ = 1 / Real.log X + 1 := by rw [add_div, div_self hlogne]

/-- **THE LOG-AVERAGED FOUR-CELL COROLLARY**: under `Chowla2LogHypothesis`
alone (Tao's proven-in-the-literature but unformalized theorem), each of
the four log-averaged sign-pattern densities tends to `1/4`:

`(Σ_{m ≤ X, λ(6m−1)=e, λ(6m+1)=d} 1/m) / log X → 1/4`.

The wing inputs are the UNCONDITIONAL `wingMinusLog_div_tendsto` /
`wingPlusLog_div_tendsto`; the harmonic normalization is unconditional;
only the log-averaged cross sum is hypothetical. -/
theorem log_pattern_density_of_chowla2_log (hC : Chowla2LogHypothesis)
    {e d : ℤ} (he : e ^ 2 = 1) (hd : d ^ 2 = 1) :
    Tendsto (fun X : ℕ => logPatternSum X e d / Real.log X)
      atTop (nhds (1 / 4)) := by
  have hH := harmonicWindow_div_log_tendsto
  have hm := wingMinusLog_div_tendsto.const_mul (e : ℝ)
  have hp := wingPlusLog_div_tendsto.const_mul (d : ℝ)
  have hx : Tendsto (fun X : ℕ =>
      (e : ℝ) * (d : ℝ) * (crossLogSum X / Real.log X)) atTop
      (nhds ((e : ℝ) * (d : ℝ) * 0)) := hC.const_mul ((e : ℝ) * (d : ℝ))
  have hbase := hH.add (hm.add (hp.add hx))
  rw [show (1 : ℝ) + ((e : ℝ) * 0 + ((d : ℝ) * 0 + (e : ℝ) * (d : ℝ) * 0))
      = 1 by ring] at hbase
  have hquarter := hbase.div_const (4 : ℝ)
  refine hquarter.congr fun X => ?_
  have hid := window_four_cell_log X he hd
  have h4 : logPatternSum X e d
      = (harmonicWindow X + (e : ℝ) * wingMinusLogSum X
          + (d : ℝ) * wingPlusLogSum X
          + (e : ℝ) * (d : ℝ) * crossLogSum X) / 4 := by
    linarith [hid]
  rw [h4]
  ring

/-- The pair-relevant `(−1,−1)` cell explicitly: under
`Chowla2LogHypothesis` the log-averaged density of `m` with
`λ(6m−1) = λ(6m+1) = −1` tends to `1/4`. -/
theorem minus_minus_log_density_of_chowla2_log (hC : Chowla2LogHypothesis) :
    Tendsto (fun X : ℕ => logPatternSum X (-1) (-1) / Real.log X)
      atTop (nhds (1 / 4)) :=
  log_pattern_density_of_chowla2_log hC (by norm_num) (by norm_num)

end FourCellLog
end Geometric
end EuclidsPath
