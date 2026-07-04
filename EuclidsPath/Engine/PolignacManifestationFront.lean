/-
  PolignacManifestationFront — the GREEN (axiom-free) module of TWO
  Polignac branches of the perpetual-engine programme: "refuting cousins (gap 4)
  or sexy (gap 6) = presenting a perpetual engine", carried out by
  Riemann's manifestation architecture. The Cousin* and Sexy* families are verbatim
  mirrors of the Mersenne template (MersenneManifestationFront), twice over.

  The deviation in both families is NOT a data object (like an off-critical zero), but
  a Π-witness: `CousinAbsenceAbove P` / `SexyAbsenceAbove P` — the absence
  of cousin- and sexy-centres above the threshold P (a mirror of MersenneTwinAbsenceAbove).
  The manifestation law is GATED by this witness: the ungated form
  (∀ P, Manifests P) would blow up the accepted boundary — like the manifestation
  candidates YM/NS (disclosed below).

  Architecture (a mirror of MersenneManifestationFront, for each family):
    * negation plumbing: absence witness ⟺ ¬unboundedness;
    * AND THE KEY DISCLOSURE — THERE IS NOTHING TO FORGE, BECAUSE THERE IS NO CHAIN:
      cousins/sexy are a FULL-DENSITY pattern of ADJACENT grid centres (m, m+1),
      NOT a distinguished subsequence of centres, like the chains 4c+1 (Mersenne),
      2c (Sophie Germain) or 6c²−4c+1 (Fermat) — there is nothing to whittle, the chain
      section is absent from this module IN ESSENCE, not by oversight. A forged
      witness (the V3 pattern of YM/NS) does not exist in these branches for
      lack of the forging substrate itself;
    * the manifestation object is BORROWED from the Riemann front:
      `DeviationFlowSupply` — and its substance witness L1 is borrowed
      THERE TOO (`deviationFlowSupply_of_twinBound`: the twin-bound builds exactly this
      supply greenly) — here L1 is NOT re-proven, disclosed;
    * the manifestation laws `CousinManifestationLaw` / `SexyManifestationLaw`
      (anchor M0 := P, consumed via le_refl); the Impossible side is the
      green theorem `no_deviationFlowSupply_at_resolved_scale`
      (reused), NOT a decree;
    * ESSENCE M3 (twice): no engines + accepted boundary + law ⟹
      centres unbounded (all three hypotheses genuinely consumed);
    * READABLE FORMS M3⁺ `cousinRefutation_carries_engine` /
      `sexyRefutation_carries_engine`: absence witness + law +
      reconciled books ⟹ engine-WITNESS as an object.

  THE FOURTH-BOUNDARY TRILEMMA IS PASSED BY BOTH FAMILIES (V1: not refutable —
  any absence witness ≥ 37 for cousins (M8: pair 223/227 at m = 37)
  and ≥ 17 for sexy (M8: minus-pair 101/107 at m = 17), while PRESENTING
  a witness = solving the open Polignac problem for gap 4/6;
  V2: not provable / not vacuous — vacuity ⟺ open unboundedness,
  the law is not green-decidable (M7); V3: it does not blow up the boundary — there is
  nothing to forge, see above). BUT THE BOUNDARIES ARE NOT ADDED — INTENTIONALLY, AND FOR
  THE FIRST TIME WITH A POSITIVE SIGN: ⚠️ THE HEURISTIC SIGN IS POSITIVE (Hardy–Littlewood
  predicts the infinitude of both classes of pairs) — the bet would be on the expected-true,
  AS WITH RIEMANN, unlike Mersenne/Fermat. AND NEVERTHELESS THE BOUNDARIES ARE NOT
  DECREED: serial expansion of the decree would devalue the quarantine —
  the uniqueness of the accepted boundary is precisely its content. The verdict
  is fixed by the §17 quarantine comment (see prose/44).

  THE SEXY WITNESS — A SPECIAL DISCLOSURE: the gate `IsSexyCenter` is two-sided (Or:
  minus-pair OR plus-pair), which is why the absence witness `SexyAbsenceAbove P`
  is STRONGER than either side separately — it bounds BOTH minus- AND plus-pairs
  simultaneously.

  THE SPINE OF HONESTY (`EuclidsPath.SideInfinitude.NoPairingClaimed`): the singletons
  are green — each side of the 6m±1 grid is separately infinite by Dirichlet;
  the AGREEMENT of the sides into a pair (gap 2, 4 or 6) is an open conjecture and is
  nowhere asserted here.

  BAN ON VACUITY №3: no free Prop-fields, no free gates and no
  renamed conclusions — every hypothesis is named arithmetically.
  The module does NOT import the quarantine; there is no axiom/sorry.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.PolignacBranch

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. COUSINS: the deviation witness — the absence of cousin-centres above the threshold

  ⚠️ There is NO chain section (the analogue of Mersenne's §2) in either family — intentionally:
  cousins/sexy are a pattern of adjacent centres, not a subsequence-chain;
  there is nothing to whittle (disclosure in the header).
#############################################################################-/

/-- **Absence of cousin-centres above `P`** (Π-witness, mirror of
    `MersenneTwinAbsenceAbove`): every cousin-centre `m` (pair `(6m+1, 6m+5)`)
    sits no higher than `P`. -/
def CousinAbsenceAbove (P : ℕ) : Prop :=
  ∀ m : ℕ, EuclidsPath.PolignacBranch.IsCousinCenter m → m ≤ P

/-- Plumbing: from boundedness an absence witness is extracted. -/
theorem exists_cousinAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.PolignacBranch.CousinCentersUnbounded) :
    ∃ P : ℕ, CousinAbsenceAbove P := by
  unfold EuclidsPath.PolignacBranch.CousinCentersUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun m hm => by
    by_contra hgt
    exact hP m (by omega) hm⟩

/-- Plumbing: unboundedness ⟺ there are no absence witnesses. -/
theorem cousinCentersUnbounded_iff_no_absence :
    EuclidsPath.PolignacBranch.CousinCentersUnbounded ↔
      ∀ P : ℕ, ¬ CousinAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨m, hlt, hm⟩ := hU P
    have := hAbs m hm
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_cousinAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **M8 (localization of the witness domain, mirror of L8):** every absence
    bound ≥ 37 — the cousin-centre `m = 37` (pair `(223, 227)`) exists
    greenly. -/
theorem cousinAbsenceBound_ge_37 {P : ℕ}
    (hAbs : CousinAbsenceAbove P) : 37 ≤ P := by
  have h := hAbs 37 ⟨by norm_num, by norm_num⟩
  omega

/-#############################################################################
  §2. COUSINS: the manifestation law (gated by the witness; the field is NOT decreed)
#############################################################################-/

/-- Absence above `P` manifests arithmetically: at every
    ledger scale no lower than `P`, everywhere the projection reconciles the books, the absence
    shows itself as an unpayable infinite supply of flows. The anchor `P ≤ M0`
    is consumed below only via `le_refl` (Riemann's pattern). The causal
    form: "a refutation must show itself where the books are reconciled" — NOT
    a statement about cousins themselves. -/
def CousinAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **COUSINS MANIFESTATION LAW** — gated by the absence witness.
    The ungated form `∀ P, CousinAbsenceManifests P` at P := 0 together with
    the accepted boundary would give a supply at a resolved scale — a contradiction
    with the green L2 (the exact mechanism by which the manifestation candidates YM/NS fail).
    The gate on a green-unpresentable witness is what distinguishes this form.
    THE FIELD IS NOT DECREED — under a POSITIVE heuristic sign (see the header):
    serial expansion of the decree would devalue the quarantine. -/
def CousinManifestationLaw : Prop :=
  ∀ P : ℕ, CousinAbsenceAbove P → CousinAbsenceManifests P

/-#############################################################################
  §3. COUSINS: ESSENCE and the readable form — a refutation presents an engine
#############################################################################-/

/-- **M3⁺ — READABLE FORM "refutation = engine":** the absence witness
    + law + reconciled books at a scale no lower than P MANIFEST a perpetual
    engine — as an OBJECT, before the kill by lexRank. -/
theorem cousinRefutation_carries_engine
    (hLaw : CousinManifestationLaw)
    {P : ℕ} (hAbs : CousinAbsenceAbove P)
    {A M0 : ℕ} (hM : P ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw P hAbs A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **M3 — ESSENCE (mirror of Mersenne's M3 and Riemann's L3):** no
    engines + accepted boundary + manifestation law ⟹ cousin-centres unbounded.
    All three hypotheses are consumed FOR REAL: from finiteness the
    absence witness P is extracted; the boundary grants resolution exactly at scale
    M0 := P; the law supplies the family 𝓕 (not ex falso); from the collision an
    engine-WITNESS is built; hNoEngine is precisely what kills it. -/
theorem cousinCentersUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : CousinManifestationLaw) :
    EuclidsPath.PolignacBranch.CousinCentersUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_cousinAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    cousinRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- Green carry-through to the programme's goal: the same triple ⟹ cousin pairs
    are infinite (via the honest bridge of the branch). -/
theorem cousinLowersInfinite_of_noEngine_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : CousinManifestationLaw) :
    EuclidsPath.PolignacBranch.CousinLowers.Infinite :=
  EuclidsPath.PolignacBranch.cousinLowersInfinite_of_unbounded
    (cousinCentersUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-#############################################################################
  §4. COUSINS: honesty audits (M5–M9)
#############################################################################-/

/-- **M5 (the vacuous reverse side, mirror of L5):** unboundedness ⟹ the law
    vacuously — the absence gate is empty. The carrying side is M3, and it needs the boundary. -/
theorem cousinManifestationLaw_of_unbounded
    (H : EuclidsPath.PolignacBranch.CousinCentersUnbounded) :
    CousinManifestationLaw := fun P hAbs =>
  ((cousinCentersUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **M6 (the exact green characterization, mirror of L6):** the law ⟺ "absence
    above P would freeze every resolving ledger at scales ≥ P".
    The reverse direction is ex falso from ¬resolves (disclosed). The gate hypothesis
    is potentially empty — which is why the characterization does NOT collapse into a global
    freeze (asymmetry with the ungated forms YM/NS). -/
theorem cousinManifestationLaw_iff_no_resolution_above_absence :
    CousinManifestationLaw ↔
      ∀ P : ℕ, CousinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **M7 — THE MAIN PRICE AUDIT (mirror of L7):** under the boundary the law ⟺
    unboundedness of cousin-centres — the field would be exactly of the strength of the gap-4 case
    of the Polignac conjecture. WITHOUT the boundary "law ⟹ unboundedness" does not
    green-assemble (M3 requires the boundary). ⚠️ The heuristic sign here is FOR the right-hand side
    (Hardy–Littlewood) — and still the field is not decreed (see the header). -/
theorem cousinManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    CousinManifestationLaw ↔
      EuclidsPath.PolignacBranch.CousinCentersUnbounded :=
  ⟨cousinCentersUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   cousinManifestationLaw_of_unbounded⟩

/-- Witness type for the bundling audit (subtype — front_pair works with Type). -/
abbrev CousinAbsenceWitness : Type := {P : ℕ // CousinAbsenceAbove P}

theorem nonempty_cousinAbsenceWitness_iff :
    Nonempty CousinAbsenceWitness ↔
      ¬ EuclidsPath.PolignacBranch.CousinCentersUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (cousinCentersUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_cousinAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- The law in Bridge form over the witness type. -/
theorem cousinManifestationLaw_iff_bridge :
    CousinManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : CousinAbsenceWitness => CousinAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **M9 (bundling audit, instantiation of the condemning machine):** the conjunction
    Bridge∧Impossible ⟺ "there are no absence witnesses" — ONLY the Bridge side
    could be decreed; the Impossible side at resolved scales is the
    green L2, never a decree. -/
theorem cousin_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : CousinAbsenceWitness => CousinAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : CousinAbsenceWitness => CousinAbsenceManifests W.1)) ↔
      ¬ Nonempty CousinAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

/-#############################################################################
  §5. SEXY: the deviation witness — the absence of sexy-centres above the threshold
#############################################################################-/

/-- **Absence of sexy-centres above `P`** (Π-witness, mirror of
    `CousinAbsenceAbove`): every sexy-centre `m` (minus-pair `(6m−1, 6m+5)`
    OR plus-pair `(6m+1, 6m+7)`) sits no higher than `P`. ⚠️ The gate is two-sided
    (Or) — the witness is STRONGER than either side separately: it bounds both
    minus- and plus-pairs simultaneously (disclosed in the header). -/
def SexyAbsenceAbove (P : ℕ) : Prop :=
  ∀ m : ℕ, EuclidsPath.PolignacBranch.IsSexyCenter m → m ≤ P

/-- Plumbing: from boundedness an absence witness is extracted. -/
theorem exists_sexyAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.PolignacBranch.SexyCentersUnbounded) :
    ∃ P : ℕ, SexyAbsenceAbove P := by
  unfold EuclidsPath.PolignacBranch.SexyCentersUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun m hm => by
    by_contra hgt
    exact hP m (by omega) hm⟩

/-- Plumbing: unboundedness ⟺ there are no absence witnesses. -/
theorem sexyCentersUnbounded_iff_no_absence :
    EuclidsPath.PolignacBranch.SexyCentersUnbounded ↔
      ∀ P : ℕ, ¬ SexyAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨m, hlt, hm⟩ := hU P
    have := hAbs m hm
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_sexyAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **M8 (localization of the witness domain, mirror of L8):** every absence
    bound ≥ 17 — the sexy-centre `m = 17` exists greenly on the MINUS side:
    pair `(101, 107)`. -/
theorem sexyAbsenceBound_ge_17 {P : ℕ}
    (hAbs : SexyAbsenceAbove P) : 17 ≤ P := by
  have h := hAbs 17 (Or.inl ⟨by norm_num, by norm_num⟩)
  omega

/-#############################################################################
  §6. SEXY: the manifestation law (gated by the witness; the field is NOT decreed)
#############################################################################-/

/-- Absence above `P` manifests arithmetically: at every
    ledger scale no lower than `P`, everywhere the projection reconciles the books, the absence
    shows itself as an unpayable infinite supply of flows. The anchor `P ≤ M0`
    is consumed below only via `le_refl` (Riemann's pattern). The causal
    form: "a refutation must show itself where the books are reconciled" — NOT
    a statement about sexy-pairs themselves. -/
def SexyAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **SEXY MANIFESTATION LAW** — gated by the absence witness.
    The ungated form `∀ P, SexyAbsenceManifests P` at P := 0 together with
    the accepted boundary would give a supply at a resolved scale — a contradiction
    with the green L2 (the exact mechanism by which the manifestation candidates YM/NS fail).
    The gate on a green-unpresentable witness is what distinguishes this form.
    THE FIELD IS NOT DECREED — under a POSITIVE heuristic sign (see the header):
    serial expansion of the decree would devalue the quarantine. -/
def SexyManifestationLaw : Prop :=
  ∀ P : ℕ, SexyAbsenceAbove P → SexyAbsenceManifests P

/-#############################################################################
  §7. SEXY: ESSENCE and the readable form — a refutation presents an engine
#############################################################################-/

/-- **M3⁺ — READABLE FORM "refutation = engine":** the absence witness
    + law + reconciled books at a scale no lower than P MANIFEST a perpetual
    engine — as an OBJECT, before the kill by lexRank. -/
theorem sexyRefutation_carries_engine
    (hLaw : SexyManifestationLaw)
    {P : ℕ} (hAbs : SexyAbsenceAbove P)
    {A M0 : ℕ} (hM : P ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw P hAbs A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **M3 — ESSENCE (mirror of Mersenne's M3 and Riemann's L3):** no
    engines + accepted boundary + manifestation law ⟹ sexy-centres unbounded.
    All three hypotheses are consumed FOR REAL: from finiteness the
    absence witness P is extracted; the boundary grants resolution exactly at scale
    M0 := P; the law supplies the family 𝓕 (not ex falso); from the collision an
    engine-WITNESS is built; hNoEngine is precisely what kills it. -/
theorem sexyCentersUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SexyManifestationLaw) :
    EuclidsPath.PolignacBranch.SexyCentersUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_sexyAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    sexyRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- Green carry-through to the programme's goal: the same triple ⟹ sexy pairs
    are infinite (via the honest bridge of the branch). -/
theorem sexyLowersInfinite_of_noEngine_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SexyManifestationLaw) :
    EuclidsPath.PolignacBranch.SexyLowers.Infinite :=
  EuclidsPath.PolignacBranch.sexyLowersInfinite_of_unbounded
    (sexyCentersUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-#############################################################################
  §8. SEXY: honesty audits (M5–M9)
#############################################################################-/

/-- **M5 (the vacuous reverse side, mirror of L5):** unboundedness ⟹ the law
    vacuously — the absence gate is empty. The carrying side is M3, and it needs the boundary. -/
theorem sexyManifestationLaw_of_unbounded
    (H : EuclidsPath.PolignacBranch.SexyCentersUnbounded) :
    SexyManifestationLaw := fun P hAbs =>
  ((sexyCentersUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **M6 (the exact green characterization, mirror of L6):** the law ⟺ "absence
    above P would freeze every resolving ledger at scales ≥ P".
    The reverse direction is ex falso from ¬resolves (disclosed). The gate hypothesis
    is potentially empty — which is why the characterization does NOT collapse into a global
    freeze (asymmetry with the ungated forms YM/NS). -/
theorem sexyManifestationLaw_iff_no_resolution_above_absence :
    SexyManifestationLaw ↔
      ∀ P : ℕ, SexyAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **M7 — THE MAIN PRICE AUDIT (mirror of L7):** under the boundary the law ⟺
    unboundedness of sexy-centres — the field would be exactly of the strength of the gap-6 case
    of the Polignac conjecture. WITHOUT the boundary "law ⟹ unboundedness" does not
    green-assemble (M3 requires the boundary). ⚠️ The heuristic sign here is FOR the right-hand side
    (Hardy–Littlewood) — and still the field is not decreed (see the header). -/
theorem sexyManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    SexyManifestationLaw ↔
      EuclidsPath.PolignacBranch.SexyCentersUnbounded :=
  ⟨sexyCentersUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   sexyManifestationLaw_of_unbounded⟩

/-- Witness type for the bundling audit (subtype — front_pair works with Type). -/
abbrev SexyAbsenceWitness : Type := {P : ℕ // SexyAbsenceAbove P}

theorem nonempty_sexyAbsenceWitness_iff :
    Nonempty SexyAbsenceWitness ↔
      ¬ EuclidsPath.PolignacBranch.SexyCentersUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (sexyCentersUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_sexyAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- The law in Bridge form over the witness type. -/
theorem sexyManifestationLaw_iff_bridge :
    SexyManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : SexyAbsenceWitness => SexyAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **M9 (bundling audit, instantiation of the condemning machine):** the conjunction
    Bridge∧Impossible ⟺ "there are no absence witnesses" — ONLY the Bridge side
    could be decreed; the Impossible side at resolved scales is the
    green L2, never a decree. -/
theorem sexy_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : SexyAbsenceWitness => SexyAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : SexyAbsenceWitness => SexyAbsenceManifests W.1)) ↔
      ¬ Nonempty SexyAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Machine-visible purity in the build log
-- (expected [propext, Classical.choice, Quot.sound] — WITHOUT step00FirstCause):
#print axioms cousinCentersUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms sexyCentersUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms cousinRefutation_carries_engine
#print axioms sexyRefutation_carries_engine
#print axioms cousinManifestationLaw_iff_unbounded_of_boundary
#print axioms sexyManifestationLaw_iff_unbounded_of_boundary
#print axioms cousinAbsenceBound_ge_37
#print axioms sexyAbsenceBound_ge_17

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
