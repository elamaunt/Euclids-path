import EuclidsPath.Engine.Step00GenealogicalOrnament

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 ornament curvature reservoir — the quantitative decomposition of the wall

The committed `Step00GenealogicalOrnament` reduced the twins to the single hypothesis
`OrnamentEngineBridge M0 : NoSafeHoleAbove M0 → PerpetualEngineExists` (the sieve parity barrier).
This file — consolidating the user's OrnamentBridge_* patch pipeline into one coherent module —
DECOMPOSES that wall into a finite curvature-reservoir accounting, so the single open node becomes a
concrete finite numerical inequality (a *curvature margin*), and normalises the reported curvature
`κ = -5` into a candidate margin `5`.  It closes NOTHING new: the margin inequality stays a NAMED
structure field, `twin_prime_conjecture` stays `sorry`, no new axiom is introduced.

## What is green here (bookkeeping / algebra, no number theory)

  * `CurvatureReservoir` — a finite accounting `total = safe + boundary + dissipation + cycle`;
  * `positiveCycleResidue_of_gap` — if `safe = 0` (from NoSafeHole) and `boundary + dissipation < total`,
    then `0 < cycle` (pure `ℕ` arithmetic via the conservation identity);
  * `gap_of_marginCapEstimates` — the finite cap/margin form
    `boundaryCap + dissipationCap + margin ≤ totalLower` (with the reservoir bounded by the caps and a
    positive margin) implies the gap;
  * `ornamentEngineBridge_of_curvatureBridge` — a reservoir bridge PRODUCES the committed
    `OrnamentEngineBridge M0`, so the whole route reaches `TwinLowers.Infinite`
    (`twinLowersInfinite_of_curvatureFamilyFromFive`), CONDITIONAL on the reservoir family;
  * `usableSurplus` / `minusFiveMargin` — the κ = -5 sign convention: `|-5| = 5`, a candidate margin;
  * `TailFromFive` — the finite base case: twins at `m = 1,2,3,5,7`, none at `4,6`
    (`6·4+1 = 25`), so cofinality only needs horizons `M0 ≥ 5`.

## The one hard input — named, not decreed

`OrnamentCurvatureBridge.margin : R.boundary + R.dissipation < R.total` (equivalently the finite
`caps_plus_margin_le_totalLower`) is the sieve parity barrier: for the REAL ornament reservoir it
would say the boundary/discrepancy and dissipation caps cannot absorb the whole certified curvature,
leaving a positive cycle residue.  It is a structure FIELD, supplied by the caller — never an axiom,
never `sorry`.  The audit theorem `minusFive_requires_cap_domination` makes explicit that the value
`5` alone does NOT settle it: the caps must still be dominated.  Building this field for the concrete
ornament is the open problem; this file does not.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace GenealogicalOrnament
namespace Reservoir

open EuclidsPath.Residuals

/-! ### The curvature reservoir (green accounting) -/

/-- A finite curvature reservoir for one horizon: the certified total curvature splits into four
    channels — leaked into safe holes, absorbed by the boundary/discrepancy, paid away by
    dissipation, and left in cycles.  (`EuclideanFractal` §8.) -/
structure CurvatureReservoir where
  total : ℕ
  safe : ℕ
  boundary : ℕ
  dissipation : ℕ
  cycle : ℕ
  conservation : total = safe + boundary + dissipation + cycle

/-- **Green:** with no safe leakage and a strict boundary+dissipation gap, a positive cycle residue
    remains.  Pure `ℕ` arithmetic through the conservation identity — no number theory. -/
theorem positiveCycleResidue_of_gap {R : CurvatureReservoir}
    (hsafe : R.safe = 0) (hgap : R.boundary + R.dissipation < R.total) : 0 < R.cycle := by
  have hc := R.conservation
  omega

/-- The finite cap/margin certificate: the reservoir's boundary and dissipation are bounded by caps,
    a certified `totalLower ≤ total`, and the positive margin dominates the caps.  This is the
    concrete finite shape of the hard input. -/
structure MarginCapEstimates (R : CurvatureReservoir) where
  boundaryCap : ℕ
  dissipationCap : ℕ
  totalLower : ℕ
  margin : ℕ
  boundary_le_cap : R.boundary ≤ boundaryCap
  dissipation_le_cap : R.dissipation ≤ dissipationCap
  totalLower_le_total : totalLower ≤ R.total
  caps_plus_margin_le_totalLower : boundaryCap + dissipationCap + margin ≤ totalLower
  margin_pos : 0 < margin

/-- **Green:** the finite cap/margin certificate implies the strict gap. -/
theorem gap_of_marginCapEstimates {R : CurvatureReservoir} (E : MarginCapEstimates R) :
    R.boundary + R.dissipation < R.total := by
  have h1 := E.boundary_le_cap
  have h2 := E.dissipation_le_cap
  have h3 := E.totalLower_le_total
  have h4 := E.caps_plus_margin_le_totalLower
  have h5 := E.margin_pos
  omega

/-! ### The reservoir bridge produces the committed `OrnamentEngineBridge` -/

/-- The quantitative bridge for one horizon.  Two fields carry the genuinely hard content, both left
    to the caller: `margin` (the sieve parity barrier) and `cycle_builds_engine` (the structural
    realisation of a positive cycle residue as an actual repeatable engine, §10/§17). -/
structure OrnamentCurvatureBridge (M0 : ℕ) where
  reservoir : CurvatureReservoir
  zero_safe_from_noHole : NoSafeHoleAbove M0 → reservoir.safe = 0
  margin : reservoir.boundary + reservoir.dissipation < reservoir.total
  cycle_builds_engine : 0 < reservoir.cycle → PerpetualEngineExists

/-- **Green:** a reservoir bridge produces the committed black-box `OrnamentEngineBridge M0` by
    composing its fields through `positiveCycleResidue_of_gap`.  No hard input is discharged — the
    `margin` and `cycle_builds_engine` fields ARE the hard input, threaded through. -/
theorem ornamentEngineBridge_of_curvatureBridge {M0 : ℕ}
    (B : OrnamentCurvatureBridge M0) : OrnamentEngineBridge M0 :=
  fun hNoHole =>
    B.cycle_builds_engine
      (positiveCycleResidue_of_gap (B.zero_safe_from_noHole hNoHole) B.margin)

/-- Build a reservoir bridge from the finite cap/margin certificate (plus the two structural maps). -/
def curvatureBridge_of_marginCapEstimates {M0 : ℕ}
    (R : CurvatureReservoir)
    (zero_safe : NoSafeHoleAbove M0 → R.safe = 0)
    (E : MarginCapEstimates R)
    (cycle_engine : 0 < R.cycle → PerpetualEngineExists) :
    OrnamentCurvatureBridge M0 :=
  { reservoir := R
    zero_safe_from_noHole := zero_safe
    margin := gap_of_marginCapEstimates E
    cycle_builds_engine := cycle_engine }

/-! ### The κ = -5 sign normalisation (green, and honestly not a discharge) -/

/-- The orientation convention that fixes whether negative or positive curvature is the usable
    surplus (`EuclideanFractal` §7). -/
inductive CurvatureOrientation
  | negativeIsSurplus
  | positiveIsSurplus

/-- Convert a signed curvature to a non-negative usable surplus under a chosen orientation. -/
def usableSurplus : CurvatureOrientation → Int → ℕ
  | CurvatureOrientation.negativeIsSurplus, k => (-k).toNat
  | CurvatureOrientation.positiveIsSurplus, k => k.toNat

/-- The candidate margin extracted from `κ = -5` under the negative-is-surplus orientation. -/
def minusFiveMargin : ℕ := 5

/-- **Green (trivial arithmetic):** `κ = -5` under negative-is-surplus gives the candidate margin 5. -/
theorem usableSurplus_negativeIsSurplus_minusFive :
    usableSurplus CurvatureOrientation.negativeIsSurplus (-5) = minusFiveMargin := by
  decide

theorem minusFiveMargin_pos : 0 < minusFiveMargin := by decide

/-- **The honesty audit:** `κ = -5` alone does NOT settle the wall.  The margin certificate still
    requires the caps to be dominated (`boundaryCap + dissipationCap + margin ≤ totalLower`) — a
    computed Euler-characteristic-style `-5` is a candidate value, not a proof of the sieve margin. -/
theorem minusFive_requires_cap_domination {R : CurvatureReservoir} (E : MarginCapEstimates R) :
    E.boundaryCap + E.dissipationCap + E.margin ≤ E.totalLower :=
  E.caps_plus_margin_le_totalLower

/-! ### Tail from five (green finite base case) -/

theorem twinCenterZ_one : TwinCenterZ 1 := by norm_num [TwinCenterZ]
theorem twinCenterZ_two : TwinCenterZ 2 := by norm_num [TwinCenterZ]
theorem twinCenterZ_three : TwinCenterZ 3 := by norm_num [TwinCenterZ]
theorem not_twinCenterZ_four : ¬ TwinCenterZ 4 := by norm_num [TwinCenterZ]
theorem twinCenterZ_five : TwinCenterZ 5 := by norm_num [TwinCenterZ]
theorem not_twinCenterZ_six : ¬ TwinCenterZ 6 := by norm_num [TwinCenterZ]
theorem twinCenterZ_seven : TwinCenterZ 7 := by norm_num [TwinCenterZ]

/-- Cofinality only above `5` already gives full cofinality: for any horizon `M0 < 5` the known twin
    center `m = 5` (pair `(29, 31)`) is a witness above `M0`.  This lets the hard curvature input
    start at `M0 ≥ 5`, dodging the finite anomaly at `m = 4` (`6·4 + 1 = 25`). -/
def TwinCenterZCofinalFromFive : Prop :=
  ∀ M0 : ℕ, 5 ≤ M0 → ∃ m : ℕ, M0 < m ∧ TwinCenterZ m

theorem twinCofinal_of_fromFive (h : TwinCenterZCofinalFromFive) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  by_cases hM0 : 5 ≤ M0
  · exact h M0 hM0
  · exact ⟨5, by omega, twinCenterZ_five⟩

/-! ### The route reaches `TwinLowers.Infinite`, conditional on the reservoir family -/

/-- A reservoir bridge at every horizon `M0 ≥ 5` (data). -/
def OrnamentCurvatureFamilyFromFive : Type :=
  ∀ M0 : ℕ, 5 ≤ M0 → OrnamentCurvatureBridge M0

/-- **Green conditional:** the reservoir family (from five) reaches full twin cofinality — via the
    committed bridge route plus the green tail reduction.  Does NOT close the twin sorry: the family
    carries the unproven `margin` fields (the parity barrier). -/
theorem unboundedTwinCenters_of_curvatureFamilyFromFive
    (F : OrnamentCurvatureFamilyFromFive) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  apply twinCofinal_of_fromFive
  intro M0 hM0
  exact twin_exists_above_of_bridge (ornamentEngineBridge_of_curvatureBridge (F M0 hM0))

/-- **Green conditional capstone:** the reservoir family yields `TwinLowers.Infinite`.  The single
    remaining open node is the `margin` field of the reservoir bridges (the sieve parity barrier);
    `twin_prime_conjecture` stays `sorry`. -/
theorem twinLowersInfinite_of_curvatureFamilyFromFive
    (F : OrnamentCurvatureFamilyFromFive) : TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := unboundedTwinCenters_of_curvatureFamilyFromFive F N
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end Reservoir
end GenealogicalOrnament
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
