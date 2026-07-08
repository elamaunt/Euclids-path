import EuclidsPath.Engine.Step00RelativeOrnamentCurvatureCorrections
import EuclidsPath.Engine.Step00OrnamentCurvatureReservoir

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Real instance of the relative-curvature scaffold

A THIN adapter: it instantiates the generic relative-curvature scaffold
(`Step00RelativeOrnamentCurvatureCorrections`) with the project's REAL predicates
— `ActiveSieveSafe` for the safe hole and `EuclidsPath.Residuals.TwinCenterZ` for the
twin center — and discharges everything EXCEPT the hard field.

It introduces no new `structure`, no new safe-hole definition, no new axiom.  It only
adapts real names to the generic scaffold.  The single remaining open input is the
certificate family

  `certs : ∀ M0, 5 ≤ M0 → RelativeCurvatureCertificate ActiveSieveSafe M0`,

whose `relIndex_computed : relIndex = -5` field is the parity-barrier node.

**The field `relIndex_computed` is not discharged by `gaussBonnet_cone3`.  The cone3
computation is intentionally not imported here** — its `-5` is the ABSOLUTE Euler
characteristic of a fixed proof-structure graph (already containing a survivor), not the
relative sieve index at an arbitrary boundary `M0`.  Together with the collapse field
`NoSafeHole → relIndex = 0`, the field `relIndex = -5` forces a safe hole; it does not do
so alone, and it is not proved here.  `twin_prime_conjecture` stays `sorry`.
-/

namespace EuclidsPath
namespace GenealogicalOrnament
namespace RelativeCurvature
namespace RealInstance

open EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament.Reservoir

/-- Real adapter: the ONLY place the generic `SafeAt` is instantiated with the project's
    active-sieve safe-hole predicate.  Discharged by the committed sieve lemma
    `safeHole_implies_twin`. -/
theorem realSafeToTwin (M0 : ℕ) :
    PointwiseSafeHoleImpliesTwin ActiveSieveSafe EuclidsPath.Residuals.TwinCenterZ M0 := by
  intro m hm h1 hsafe
  exact safeHole_implies_twin h1 hsafe

/-- Conditional cofinality from real relative-curvature certificates.  The hard input is
    exactly the certificate family `certs`; everything else (seed at 5, safe→twin) is a
    real committed lemma. -/
theorem twinCenterZCofinal_of_realRelativeCertificates
    (certs : ∀ M0 : ℕ, 5 ≤ M0 → RelativeCurvatureCertificate ActiveSieveSafe M0) :
    TwinCenterZCofinal EuclidsPath.Residuals.TwinCenterZ := by
  apply twinCofinal_of_relativeCurvatureFamilyFromFive
  exact
    { seed_five := twinCenterZ_five
      certificateAt := certs
      safe_to_twin_tail := fun M0 _ => realSafeToTwin M0 }

/-- Real conditional twin infinitude from the relative-curvature certificate family.  This
    does NOT prove the certificate family: `TwinLowers.Infinite` here is conditional on
    `certs`, whose `relIndex = -5` fields are the parity-barrier node. -/
theorem twinLowersInfinite_of_realRelativeCertificates
    (certs : ∀ M0 : ℕ, 5 ≤ M0 → RelativeCurvatureCertificate ActiveSieveSafe M0) :
    TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := twinCenterZCofinal_of_realRelativeCertificates certs N
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end RealInstance
end RelativeCurvature
end GenealogicalOrnament
end EuclidsPath
