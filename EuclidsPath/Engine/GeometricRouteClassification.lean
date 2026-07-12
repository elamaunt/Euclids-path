/-
  GeometricRouteClassification — where the analytic (geometric) route meets the repo's
  already-localized twin barrier.  The HONEST "routes meet" layer (NOT "one wall, not
  three": the repo itself rejects that framing — identifying skeletons does not remove any
  red input; see `Step00TwinScaleAdvances`).

  ORIGIN (user's geometric program, §XXVI §45 / §XXXIX §81 of
  `geometric_twin_prime_program_full.md`): after the diagonal is discharged
  (`GeometricDiagonalCovariance`), the geometric route's remaining obstruction is the
  OFF-DIAGONAL two-prime normal mixing.  Bundled into the reduction's covariance bound it
  yields, one-directionally, positive twin density and hence twins.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twins_of_geometricMixingTarget` — 🟢 CONDITIONAL: the geometric mixing target
      (positive marginals + connected-defect bound holding cofinally) implies infinitely
      many twin centers.  Honest: the hypothesis is STRICTLY STRONGER than "twins", so this
      is a genuine sufficient condition, NOT an information-free iff-with-the-conjecture.
    * `mixing_forces_fourCorner` — 🟢 CONDITIONAL, FORWARD ONLY: a strictly negative
      connected defect (the mixing target in four-corner form) forces the real four-corner
      drop `N₃₃ < N₀₀`, reusing the repo's `N33_lt_N00_of_four_corner`.  This places the
      geometric barrier at the EXACT named open input of the combinatorial route
      (`RealFourCorner` remainder control) — the two routes meet there.

  DISCLOSURE.  `offDiagDecay` (§45/§81/§82), the operative off-diagonal input, stays 🔴
  OPEN — it is NOT proved here and is NOT stated as an iff with `SerialTwinBoundary` /
  `TwinLowers.Infinite` (that would be an information-free iff-with-the-conjecture, cf.
  `serialTwinBoundary_iff_unboundedTwinCenters`).  The cofinal-information reading of the
  same barrier is `ParityBarrier.sound_cert_requires_cofinal_information`.  Nothing here
  moves the wall.  twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Step00_Overview
import EuclidsPath.Engine.FourCorner
import EuclidsPath.Engine.GeometricReduction

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace Route

/-- **The geometric mixing target.** The reduction inputs (positive prime marginals + the
    connected-defect bound, whose off-diagonal part is the open §45/§81 mixing) holding on
    windows beyond every horizon. -/
def GeometricMixingTarget : Prop := Reduction.ReductionHolds

/-- **Twins from the geometric mixing target (§29/§83).** 🟢 conditional.  A one-directional
    sufficient condition: the mixing target implies infinitely many twin centers.  It does
    NOT assume the conjecture — the hypothesis is strictly stronger than "twins exist". -/
theorem twins_of_geometricMixingTarget (H : GeometricMixingTarget) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsTwinCenter m :=
  Reduction.twinCenters_cofinal_of_reduction H

/-- **Mixing forces the four-corner drop (§45).** 🟢 conditional, FORWARD ONLY.  A strictly
    negative connected defect `N₀₀·N₃₃ < N₀₃·N₃₀` (the mixing target in four-corner form),
    with the side-corner bound, forces `N₃₃ < N₀₀`.  The geometric barrier lands on the
    EXACT named open input of the combinatorial route — reusing `N33_lt_N00_of_four_corner`
    (`RealFourCorner` is where the two routes meet).  No iff: the reverse
    (twins ⟹ this exact decay) is unproved and would overclaim. -/
theorem mixing_forces_fourCorner {N00 N03 N30 N33 : ℕ} (hpos : 0 < N00)
    (hmix : N00 * N33 < N03 * N30) (hside : N03 * N30 ≤ N00 * N00) :
    N33 < N00 :=
  EuclidsPath.N33_lt_N00_of_four_corner hpos hmix hside

end Route
end Geometric
end EuclidsPath
