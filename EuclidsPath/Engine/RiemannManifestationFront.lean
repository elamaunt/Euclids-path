/-
  RiemannManifestationFront — GREEN (axiom-free) module of the Riemann branch
  of the first cause: "the perpetual engine cannot permit any deviations of
  non-trivial zeros", carried out by the same rank machine that handles twins on ℤ.

  Architecture (mirror of the twin chain):
    * off-critical zero = UNPAID DEVIATION;
    * manifestation law (`RiemannManifestationLaw`, FUTURE FIELD OF THE DECREE —
      here only DEFINED, not adopted): every zero at every scale no lower than
      its height, wherever the ledger closes the books, manifests as an
      infinite admissible family of generated flows — exactly the object that
      twin-bound builds green (L1);
    * GREEN impossibility (L2): at a resolved scale no such family exists —
      the finite-key projection collision builds a perpetual engine, the engine is killed
      by lexRank (`no_someConcreteEuclideanEngine`);
    * essence lemma (L3, mirror of `twins_infinite_of_noEngine_and_boundary`):
      no engines + accepted boundary + manifestation law ⟹ no zeros;
      all three hypotheses are consumed GENUINELY (not ex falso);
    * L4: same ⟹ RiemannHypothesis (zero extraction from ¬RH — mathlib-exact).

  HONESTY (machine-checked, mandatory audits):
    * L5: RH ⟹ law (vacuously — no zeros); the exposed reverse side.
    * L7: WITH the accepted boundary law ⟺ RH — the Riemann decree field is
      NO WEAKER than the theorem (mirror of `causalClosureAxiom_asserts_twins_at_every_scale`:
      accepting the extended first cause = accepting RH). WITHOUT the boundary "law ⟹ RH"
      is NOT provable green — this is the asymmetry with the condemned bridge
      (`offCriticalBridge_iff_RH`: that one ⟺ RH is already green).
    * L6: exact green characterisation of the law — "a zero would freeze every
      resolving ledger above its height" (reverse direction — ex falso
      from ¬resolves, exposed).
    * L9: the Bridge∧Impossible bundle for the manifestation family ⟺ absence of
      zeros (instantiation of the condemning audit `front_pair_iff_no_zero`) —
      ONLY the Bridge side will be decreed; the Impossible side at
      resolved scales — GREEN THEOREM L2, not a decree.
  This module does NOT import the quarantine and contains no axiom/sorry: the verifier
  must show all declarations AXIOM-TAINTED-free.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannImpossibleEngineOff
import EuclidsPath.Engine.RiemannTrivialZeros
import EuclidsPath.Engine.RiemannSpectralAnchorAudit

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-- Off-critical zero in the exact mathlib sense (alias for readability inside
    the rank namespace). -/
abbrev RiemannOffCriticalZero : Type :=
  EuclidsPath.RiemannImpossibleEngineOff.OffCriticalZero

/-#############################################################################
  §1. Zero height and the manifestation object
#############################################################################-/

/-- Height of an off-critical zero: the natural scale at which it lives
    (⌊|Im s|⌋). Substantively only `le_refl` is used below — the law
    binds the manifestation to scales NO LOWER than the zero's height. -/
noncomputable def zeroHeight (Z : RiemannOffCriticalZero) : ℕ :=
  ⌊|Z.s.im|⌋₊

/-- Unpaid deviation supply at ledger scale (A, M0): an infinite admissible
    family of extended generated flows — THE SAME object that twin-bound
    supplies green
    (`twinBoundForcesInfiniteExtendedGeneratedFlows_closed`). -/
def DeviationFlowSupply (A M0 : ℕ) : Prop :=
  ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
    InfiniteExtendedGeneratedFlowFamily A M0 𝓕

/-- A single off-critical zero manifests arithmetically: at every ledger scale
    no lower than its height, wherever the projection closes the books (collisions
    are resolved), the zero appears as an unpayable infinite supply of flows.
    Causal form: "the deviation must appear where the books are closed" —
    NOT a statement about the absence of zeros. -/
def OffCriticalDeviationManifests (Z : RiemannOffCriticalZero) : Prop :=
  ∀ (A M0 : ℕ), zeroHeight Z ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **MANIFESTATION LAW** — the content of the future Riemann decree field
    (`riemannBoundary`). Here only defined; adopted ONLY in the quarantine
    module, as a field of the same single axiom. -/
def RiemannManifestationLaw : Prop :=
  ∀ Z : RiemannOffCriticalZero, OffCriticalDeviationManifests Z

/-#############################################################################
  §2. Green chain: witness of non-vacuity and impossibility
#############################################################################-/

/-- **L1 (non-vacuity witness):** the manifestation object is not an empty
    form: twin-bound builds exactly it GREEN at every scale. The decree field
    supplies the same type of object as the genuine rank machine. -/
theorem deviationFlowSupply_of_twinBound {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0) : DeviationFlowSupply A M0 :=
  twinBoundForcesInfiniteExtendedGeneratedFlows_closed hTwinBound

/-- **L2 (GREEN impossibility — Impossible side as THEOREM):** at a resolved
    scale there is no deviation supply: stable no-energy universe + infinite
    family ⟹ collision ⟹ engine witness ⟹ killed by lexRank.
    This is exactly why Impossible is NOT decreed (cf. L9). -/
theorem no_deviationFlowSupply_at_resolved_scale {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ¬ DeviationFlowSupply A M0 := by
  rintro ⟨𝓕, h𝓕⟩
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact no_someConcreteEuclideanEngine ⟨A, M0, hEngine⟩

/-#############################################################################
  §3. Essence lemma and sufficiency (mirrors of the twin chain)
#############################################################################-/

/-- **L3 — ESSENCE LEMMA (mirror of `twins_infinite_of_noEngine_and_boundary`):**
    no engines + accepted causal boundary + manifestation law ⟹
    no off-critical zeros. All three hypotheses are consumed GENUINELY:
    the boundary gives resolution at the scale of the zero's height, the law
    supplies the family 𝓕, a perpetual engine WITNESS is built from the collision,
    and it is killed by exactly hNoEngine (not ex falso). -/
theorem noOffCriticalZero_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hManifest : RiemannManifestationLaw) :
    ¬ Nonempty RiemannOffCriticalZero := by
  rintro ⟨Z⟩
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves :
      SemanticExtendedFlowLedgerCollisionResolves (projOf (zeroHeight Z)) :=
    strictSemanticExtended_resolves_old (hres (zeroHeight Z))
  have hStable : NoEnergyStableUniverse (projOf (zeroHeight Z)) :=
    (noEnergyStableUniverse_iff_resolves (projOf (zeroHeight Z))).mpr hResolves
  obtain ⟨𝓕, h𝓕⟩ :=
    hManifest Z A (zeroHeight Z) (le_refl _) (projOf (zeroHeight Z)) hResolves
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hNoEngine ⟨A, zeroHeight Z, hEngine⟩

/-- **L4 — sufficiency as THEOREM:** the same triple of hypotheses ⟹ RH.
    Zero extraction from ¬RH is mathlib-exact (`offCriticalZero_of_not_RH`);
    the classification of trivial zeros is already proved
    (`trivialBelowZeroClassification`) and sits inside the extraction. -/
theorem riemannHypothesis_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hManifest : RiemannManifestationLaw) :
    RiemannHypothesis := by
  by_contra hNotRH
  exact noOffCriticalZero_of_manifestation_and_boundary
    hNoEngine hBoundary hManifest
    (EuclidsPath.RiemannImpossibleEngineOff.offCriticalZero_of_not_RH hNotRH)

/-#############################################################################
  §4. Mandatory honesty audits
#############################################################################-/

/-- **L5 (exposed vacuous reverse side):** RH ⟹ law — vacuously
    (no off-critical zeros under RH, the quantifier is empty). The load-bearing
    side is L4, and it requires the boundary. -/
theorem manifestationLaw_of_RH (hRH : RiemannHypothesis) :
    RiemannManifestationLaw := fun Z =>
  (EuclidsPath.RiemannImpossibleEngineOff.not_RH_of_offCriticalZero Z hRH).elim

/-- **L6 (exact green characterisation of the law):** law ⟺ "an off-critical zero
    would freeze every resolving ledger at scales above its height".
    ⚠️ Reverse direction — ex falso from ¬resolves (exposed): the substantive
    side is the forward one (law + resolution ⟹ supply ⟹ L2 contradiction). -/
theorem manifestationLaw_iff_no_resolution_above_zero :
    RiemannManifestationLaw ↔
      ∀ (Z : RiemannOffCriticalZero) (A M0 : ℕ), zeroHeight Z ≤ M0 →
        ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
          ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw Z A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw Z A M0 hle proj hres)
  · intro hFreeze Z A M0 hle proj hres
    exact ((hFreeze Z A M0 hle proj) hres).elim

/-- **L7 (MAIN AUDIT, mirror of "accepting the axiom = accepting twins"):**
    WITH the accepted boundary, manifestation law ⟺ RH — the Riemann decree
    field has exactly RH strength, the decree is NO WEAKER than the theorem.
    Machine asymmetry with the condemned bridge: `offCriticalBridge_iff_RH` is
    proved green WITHOUT any hypotheses, while here ⟺ is achievable ONLY with
    the boundary (without it L4 does not assemble). -/
theorem manifestationLaw_iff_RH_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    RiemannManifestationLaw ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_manifestation_and_boundary
      no_someConcreteEuclideanEngine hBoundary,
   manifestationLaw_of_RH⟩

/-- **L8 (domain localisation — theorem, not input):** every off-critical zero
    lies strictly in the critical strip (via the proved classification of
    trivial zeros). -/
theorem offCriticalZero_in_strip (Z : RiemannOffCriticalZero) :
    0 < Z.s.re ∧ Z.s.re < 1 :=
  EuclidsPath.TrivialZeros.nontrivialZero_in_strip_unconditional
    (⟨Z.zero, Z.nontrivial, Z.not_one⟩ :
      EuclidsPath.RiemannBranch.NontrivialZeroM Z.s)

/-- **L9 (instantiation of the condemning bundling audit):** for the family of
    manifestations the Bridge∧Impossible bundle ⟺ "no zeros" — therefore
    ONLY the Bridge side is decreed (`RiemannManifestationLaw` = Bridge);
    the Impossible side at resolved scales is green theorem L2. -/
theorem manifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun Z : RiemannOffCriticalZero => OffCriticalDeviationManifests Z) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun Z : RiemannOffCriticalZero => OffCriticalDeviationManifests Z)) ↔
      ¬ Nonempty RiemannOffCriticalZero :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Machine-visible purity directly in the build log: NOT ONE of the key lemmas
-- is AXIOM-TAINTED by a non-standard axiom (expected: [propext, Classical.choice, Quot.sound]).
#print axioms no_deviationFlowSupply_at_resolved_scale
#print axioms noOffCriticalZero_of_manifestation_and_boundary
#print axioms riemannHypothesis_of_manifestation_and_boundary
#print axioms manifestationLaw_iff_RH_of_boundary

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
