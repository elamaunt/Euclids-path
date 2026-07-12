/-
  GeometricReduction — the §79–83 reduction skeleton as a GREEN CONDITIONAL theorem.

  ORIGIN (user's geometric program, §XXII / §XXVI / §XXXIX of
  `geometric_twin_prime_program_full.md`): with a positive prime marginal on a sparse
  weighting and a small connected defect of the soft projector `Q_t = t^{Ω−1}`, a fixed
  small `t` forces a positive weighted twin count — hence a twin center in the window.
  Quantifying over windows beyond every horizon gives infinitely many twin centers.

  This is the honest machine form of §29/§83: a ONE-DIRECTIONAL sufficient condition
  (geometric inputs ⟹ twins), NOT an iff with the conjecture.  The analytic inputs
  (positive marginals §29, connected-defect bound = diagonal §44 + two-prime mixing §45
  + shape-Fourier §82, all bundled as `hcov`) are EXPLICIT finite hypotheses — no `o(1)`,
  no `Tendsto`, is consumed as if proven.  The badge is 🟢 on the CONDITIONAL: it uses
  neither `step00FirstCause` nor `twin_prime_conjecture`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twinCenter_of_window` — the finite reduction: the four explicit bounds on one
      window force a twin center in that window (via the soft-projector sandwich, §28);
    * `twinCenters_cofinal_of_reduction` — quantifying over windows beyond every horizon:
      infinitely many twin centers `∀ N, ∃ m > N, IsTwinCenter m`.

  DISCLOSURE.  The operative connected-defect bound `hcov` (its off-diagonal §45/§81 part)
  is the genuinely open input; see `GeometricRouteClassification`.  This file proves the
  REDUCTION, not the inputs, and does not move the wall.  twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Step00_Overview
import EuclidsPath.Engine.GeometricPrimeProjector

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace Reduction

open scoped BigOperators
open EuclidsPath.Geometric.Projector

/-! ## The finite reduction (§28–29, §83) -/

/-- **Window reduction (§83).** Given, on a finite window `I` of centers (all `≥ 1`), a
    nonnegative normalized weighting `w`, positive prime marginals `≥ c` on both wings, and
    a connected-defect bound `≤ c²/4` for the soft projector `Q_t`, with a small fixed
    `t` (`2t + t² < c²/2`), there is a twin center in `I`. -/
theorem twinCenter_of_window
    {I : Finset ℕ} {w : ℕ → ℝ} {c t : ℝ}
    (hc0 : 0 < c) (_hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htc : 2 * t + t ^ 2 < c ^ 2 / 2)
    (hw : ∀ m ∈ I, 0 ≤ w m)
    (hnorm : ∑ m ∈ I, w m = 1)
    (hm1 : ∀ m ∈ I, 1 ≤ m)
    (hmarg_m : c ≤ ∑ m ∈ I, w m * (if (6 * m - 1).Prime then (1 : ℝ) else 0))
    (hmarg_p : c ≤ ∑ m ∈ I, w m * (if (6 * m + 1).Prime then (1 : ℝ) else 0))
    (hcov :
      (∑ m ∈ I, w m * softProjector t (6 * m - 1))
          * (∑ m ∈ I, w m * softProjector t (6 * m + 1))
        - (∑ m ∈ I, w m * (softProjector t (6 * m - 1) * softProjector t (6 * m + 1)))
      ≤ c ^ 2 / 4) :
    ∃ m ∈ I, IsTwinCenter m := by
  classical
  -- Per-term indicator / soft-projector data.
  set Xm : ℕ → ℝ := fun m => if (6 * m - 1).Prime then (1 : ℝ) else 0 with hXm
  set Xp : ℕ → ℝ := fun m => if (6 * m + 1).Prime then (1 : ℝ) else 0 with hXp
  set Qm : ℕ → ℝ := fun m => softProjector t (6 * m - 1) with hQm
  set Qp : ℕ → ℝ := fun m => softProjector t (6 * m + 1) with hQp
  have hbm : ∀ m ∈ I, Xm m ≤ Qm m ∧ Qm m ≤ Xm m + t := by
    intro m hm
    have h2 : 2 ≤ 6 * m - 1 := by have := hm1 m hm; omega
    exact softProjector_bounds ht0 ht1 h2
  have hbp : ∀ m ∈ I, Xp m ≤ Qp m ∧ Qp m ≤ Xp m + t := by
    intro m hm
    have h2 : 2 ≤ 6 * m + 1 := by have := hm1 m hm; omega
    exact softProjector_bounds ht0 ht1 h2
  have hXm01 : ∀ m, 0 ≤ Xm m ∧ Xm m ≤ 1 := by
    intro m; rw [hXm]; dsimp only; split <;> constructor <;> norm_num
  have hXp01 : ∀ m, 0 ≤ Xp m ∧ Xp m ≤ 1 := by
    intro m; rw [hXp]; dsimp only; split <;> constructor <;> norm_num
  have hQm0 : ∀ m, 0 ≤ Qm m := by
    intro m; rw [hQm]; dsimp only; unfold softProjector; positivity
  have hQp0 : ∀ m, 0 ≤ Qp m := by
    intro m; rw [hQp]; dsimp only; unfold softProjector; positivity
  -- Marginals lift from X to Q.
  have hEQm : c ≤ ∑ m ∈ I, w m * Qm m :=
    le_trans hmarg_m
      (Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hbm m hm).1 (hw m hm))
  have hEQp : c ≤ ∑ m ∈ I, w m * Qp m :=
    le_trans hmarg_p
      (Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hbp m hm).1 (hw m hm))
  -- Marginals of X are ≤ 1 (normalization).
  have hEXm_le : ∑ m ∈ I, w m * Xm m ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum fun m hm =>
      mul_le_of_le_one_right (hw m hm) (hXm01 m).2
  have hEXp_le : ∑ m ∈ I, w m * Xp m ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum fun m hm =>
      mul_le_of_le_one_right (hw m hm) (hXp01 m).2
  -- Lower bound on E[Qm Qp] from hcov and the two Q-marginals.
  have hQmQp_lb : 3 * c ^ 2 / 4 ≤ ∑ m ∈ I, w m * (Qm m * Qp m) := by
    have hprod : c ^ 2 ≤ (∑ m ∈ I, w m * Qm m) * (∑ m ∈ I, w m * Qp m) := by
      have := mul_le_mul hEQm hEQp hc0.le (le_trans hc0.le hEQm)
      nlinarith [this]
    nlinarith [hcov, hprod]
  -- Upper bound on E[Qm Qp] by E[Xm Xp] + 2t + t².
  have hQmQp_ub :
      ∑ m ∈ I, w m * (Qm m * Qp m)
        ≤ (∑ m ∈ I, w m * (Xm m * Xp m))
            + t * (∑ m ∈ I, w m * Xp m) + t * (∑ m ∈ I, w m * Xm m) + t ^ 2 := by
    have hterm : ∀ m ∈ I,
        w m * (Qm m * Qp m)
          ≤ w m * (Xm m * Xp m) + t * (w m * Xp m) + t * (w m * Xm m) + t ^ 2 * w m := by
      intro m hm
      have h1 := (hbm m hm).2
      have h2 := (hbp m hm).2
      have hx0 := (hXm01 m).1
      have hy0 := (hXp01 m).1
      have hprod : Qm m * Qp m ≤ (Xm m + t) * (Xp m + t) :=
        mul_le_mul h1 h2 (hQp0 m) (by linarith [hx0])
      have hexp : (Xm m + t) * (Xp m + t)
          = Xm m * Xp m + t * Xp m + t * Xm m + t ^ 2 := by ring
      have : Qm m * Qp m ≤ Xm m * Xp m + t * Xp m + t * Xm m + t ^ 2 := by
        rw [hexp] at hprod; exact hprod
      nlinarith [this, hw m hm]
    calc ∑ m ∈ I, w m * (Qm m * Qp m)
        ≤ ∑ m ∈ I, (w m * (Xm m * Xp m) + t * (w m * Xp m) + t * (w m * Xm m) + t ^ 2 * w m) :=
          Finset.sum_le_sum hterm
      _ = (∑ m ∈ I, w m * (Xm m * Xp m))
            + t * (∑ m ∈ I, w m * Xp m) + t * (∑ m ∈ I, w m * Xm m) + t ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hnorm, mul_one]
  -- Positivity of the weighted twin count.
  have hpos : 0 < ∑ m ∈ I, w m * (Xm m * Xp m) := by
    nlinarith [hQmQp_lb, hQmQp_ub, hEXm_le, hEXp_le, htc, ht0, hc0]
  -- Extract a twin center.
  obtain ⟨m, hmI, hne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
  refine ⟨m, hmI, ?_⟩
  have hxm : Xm m ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  have hxp : Xp m ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  constructor
  · by_contra hp
    rw [hXm] at hxm; dsimp only at hxm; rw [if_neg hp] at hxm; exact hxm rfl
  · by_contra hp
    rw [hXp] at hxp; dsimp only at hxp; rw [if_neg hp] at hxp; exact hxp rfl

/-! ## Cofinal twin centers from the reduction (§83) -/

/-- The geometric reduction inputs holding on windows beyond every horizon. -/
def ReductionHolds : Prop :=
  ∀ N : ℕ, ∃ (I : Finset ℕ) (w : ℕ → ℝ) (c t : ℝ),
    0 < c ∧ c ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ 2 * t + t ^ 2 < c ^ 2 / 2 ∧
    (∀ m ∈ I, 0 ≤ w m) ∧ (∑ m ∈ I, w m = 1) ∧ (∀ m ∈ I, N < m) ∧
    c ≤ (∑ m ∈ I, w m * (if (6 * m - 1).Prime then (1 : ℝ) else 0)) ∧
    c ≤ (∑ m ∈ I, w m * (if (6 * m + 1).Prime then (1 : ℝ) else 0)) ∧
    ((∑ m ∈ I, w m * softProjector t (6 * m - 1))
          * (∑ m ∈ I, w m * softProjector t (6 * m + 1))
        - (∑ m ∈ I, w m * (softProjector t (6 * m - 1) * softProjector t (6 * m + 1)))
      ≤ c ^ 2 / 4)

/-- **Cofinal twins from the reduction (§83).** If the geometric inputs hold on windows
    beyond every horizon, there are infinitely many twin centers.  🟢 conditional. -/
theorem twinCenters_cofinal_of_reduction (H : ReductionHolds) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsTwinCenter m := by
  intro N
  obtain ⟨I, w, c, t, hc0, hc1, ht0, ht1, htc, hw, hnorm, hN, hmm, hmp, hcov⟩ := H N
  have hm1 : ∀ m ∈ I, 1 ≤ m := fun m hm => by have := hN m hm; omega
  obtain ⟨m, hmI, htwin⟩ :=
    twinCenter_of_window hc0 hc1 ht0 ht1 htc hw hnorm hm1 hmm hmp hcov
  exact ⟨m, hN m hmI, htwin⟩

end Reduction
end Geometric
end EuclidsPath
