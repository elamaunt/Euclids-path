/-
  MersenneManifestationFront — GREEN (axiom-free) module of the Mersenne branch
  of the perpetual engine programme: "refuting Mersenne twins = exhibiting
  a perpetual engine", carried out via the Riemann manifestation architecture.

  The deviation here is NOT an object-datum (like an off-critical zero) but a Π-witness:
  `MersenneTwinAbsenceAbove P` — absence of Mersenne twins above threshold P
  (mirror of TwinBoundAbove). The manifestation law is GATED by this witness:
  the ungated form (∀ P, Manifests P) would blow up the accepted boundary — like
  the manifestation candidates YM/NS (exposed below).

  Architecture (mirror of RiemannManifestationFront):
    * negation plumbing: absence witness ⟺ ¬unboundedness;
    * base-4 arithmetic of the center chain (m→4m+1, repunits) — strictly monotone,
      injective; AND THE KEY DISCLOSURE: the chain IS NOT PEELED
      (`isEmpty_properCenterPeel_five_one`) — coefficient 4 is not prime and
      ≢ ±1 (mod 6), already the first step 5→1 is empty (sides 29/31 are prime, targets 5/7).
      Therefore NO FORGED WITNESS exists in this branch — unlike
      YM (cookedLadder) and NS (cookedProfileCascade), exactly as with Riemann;
    * manifestation law `MersenneManifestationLaw` (anchor M0 := P,
      consumed below only via le_refl); the Impossible side — the green theorem
      `no_deviationFlowSupply_at_resolved_scale` (reused), NOT a decree;
    * ESSENCE M3: no engines + accepted boundary + law ⟹
      Mersenne twins are unbounded (all three hypotheses genuinely consumed);
    * READABLE FORM M3⁺ `mersenneRefutation_carries_engine`: absence witness
      + law + balanced ledger ⟹ engine-WITNESS as an object.

  FOURTH-FIELD TRILEMMA PASSED (V1: not refutable — any absence witness
  is ≥ 29 (M8) and its exhibition ≥ the solution of the open tail problem;
  V2: not provable / not vacuous — vacuity ⟺ open unboundedness;
  V3: does not blow up the boundary — nothing to forge). BUT THE FIELD IS NOT ADDED — DELIBERATELY:
  ⚠️ HEURISTIC SIGN IS INVERTED. Under the boundary, law ⟺
  MersenneTwinCentersUnbounded (M7), but the heuristic points AGAINST
  unboundedness (Σ over Mersenne twin pairs converges; only p = 3, 5 are known;
  for p ≡ 3 (mod 4) always 5 ∣ 2^p−3). Riemann was a bet on the expectedly-true;
  Mersenne would be the first boundary whose expected truth is negative.
  Decision recorded: the law lives here by definition (like
  RiemannManifestationLaw before §10); quarantine consistency is NOT
  staked on it. See the §16 quarantine comment and prose/43.

  VACUITY PROHIBITION №3: no free Prop-fields, free gates, or
  renamed conclusions — every hypothesis is named arithmetically.
  The module does NOT import quarantine; no axiom/sorry.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.MersennePeelPressure
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. Deviation witness: absence of Mersenne twins above threshold
#############################################################################-/

/-- **Absence of Mersenne twins above `P`** (Π-witness, mirror of
    `TwinBoundAbove`): every Mersenne twin sits on the lower side
    `2^p − 3` at most `P`. ⚠️ Do NOT confuse with
    `Mersenne.PeelPaymentPressure.MersenneTwinAbsentAtOrAbove` — that form is
    indexed by chain index k and is parametric over PrimeLike. -/
def MersenneTwinAbsenceAbove (P : ℕ) : Prop :=
  ∀ p : ℕ, (2 ^ p - 3).Prime → (mersenne p).Prime → 2 ^ p - 3 ≤ P

/-- Plumbing: an absence witness is extracted from boundedness. -/
theorem exists_mersenneAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded) :
    ∃ P : ℕ, MersenneTwinAbsenceAbove P := by
  unfold EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun p h1 h2 => by
    by_contra hgt
    exact hP p (by omega) h1 h2⟩

/-- Plumbing: unboundedness ⟺ no absence witnesses. -/
theorem mersenneTwinCentersUnbounded_iff_no_absence :
    EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded ↔
      ∀ P : ℕ, ¬ MersenneTwinAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨p, hlt, h1, h2⟩ := hU P
    have := hAbs p h1 h2
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_mersenneAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **M8 (witness domain localization, mirror of L8):** every absence bound
    is ≥ 29 — the pair (29, 31) at p = 5 exists by green proof. -/
theorem mersenneAbsenceBound_ge_29 {P : ℕ}
    (hAbs : MersenneTwinAbsenceAbove P) : 29 ≤ P := by
  have h := hAbs 5 (by norm_num) (by norm_num [mersenne])
  norm_num at h
  exact h

/-#############################################################################
  §2. Base-4 center chain: strictly monotone — and NOT PEELED (no forging)
#############################################################################-/

/-- The center chain strictly increases at each step (m → 4m+1). -/
theorem mersenneCenterChain_lt_succ (k : ℕ) :
    EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter k <
      EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter (k + 1) := by
  have h := EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter_base4PeelStep k
  unfold EuclidsPath.Mersenne.PeelPaymentPressure.Base4PeelStep at h
  omega

theorem mersenneCenterChain_strictMono :
    StrictMono EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter :=
  strictMono_nat_of_lt_succ mersenneCenterChain_lt_succ

theorem mersenneCenterChain_injective :
    Function.Injective EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter :=
  mersenneCenterChain_strictMono.injective

/-- Chain ↔ branch coupling: the repunit center of a layer equals the MersenneBranch center at
    p = 2k+1. -/
theorem mersenneCenterChain_eq_branchCenter (k : ℕ) :
    EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter k =
      EuclidsPath.MersenneBranch.mersenneCenter (2 * k + 1) := by
  have h1 := EuclidsPath.Mersenne.peelCenter_eq_conflictCenter k
  have h2 := EuclidsPath.Mersenne.sixCenter_add_one_eq_mersenne k
  have h3 := EuclidsPath.MersenneBranch.mersenne_eq_sixCenter_add_one
    (p := 2 * k + 1) ⟨k, by ring⟩
  unfold mersenne at h2 h3
  omega

/-- **KEY DISCLOSURE (contrast with the 5-adic chain): the base-4 chain IS NOT PEELED.**
    The 5-adic chain `c → 5c+1` admits the identity `6(5x+1)−1 = 5(6x+1)` with
    the PRIME constant divisor 5 — so it builds supply at A ≤ 4.
    The chain `c → 4c+1` has no such identity (coefficient 4 is not prime and
    ≢ ±1 mod 6), and already the FIRST step 5 → 1 carries no proper peel AT ANY
    scale: sides 29 and 31 are prime, sides of the target are merely 5 and 7.
    Consequence: the Mersenne chain does NOT build unconditional flow supply —
    NO FORGED WITNESS (the V3 pattern of YM/NS) exists in this branch. -/
theorem isEmpty_properCenterPeel_five_one (A : ℕ) :
    IsEmpty (ProperCenterPeel A 5 1) := by
  constructor
  rintro ⟨inS, outS, q, _hq, _hA, hfac, _hsm, _hpos⟩
  cases inS <;> cases outS <;> simp only [sideValue] at hfac <;> omega

/-#############################################################################
  §3. Manifestation law (gated by the witness; field NOT decreed)
#############################################################################-/

/-- Absence above `P` manifests arithmetically: at every ledger scale not below `P`,
    wherever the projection balances the ledger, the absence manifests as
    an unpayable infinite flow supply. The anchor `P ≤ M0`
    is consumed below only via `le_refl` (the Riemann pattern). Causal
    form: "a refutation must manifest wherever the ledger is balanced" — NOT
    a statement about Mersenne twins themselves. -/
def MersenneAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **MERSENNE MANIFESTATION LAW** — gated by the absence witness.
    The ungated form `∀ P, MersenneAbsenceManifests P` at P := 0 together with
    the accepted boundary would yield supply at the resolved scale — a contradiction
    with the green L2 (the exact mechanism by which YM/NS manifestation candidates fail).
    The gate on the greenly-unpresentable witness is what distinguishes this form.
    FIELD NOT DECREED (heuristic sign — see the header). -/
def MersenneManifestationLaw : Prop :=
  ∀ P : ℕ, MersenneTwinAbsenceAbove P → MersenneAbsenceManifests P

/-#############################################################################
  §4. ESSENCE and readable form: a refutation exhibits an engine
#############################################################################-/

/-- **M3⁺ — READABLE FORM "refutation = engine":** absence witness
    + law + balanced ledger at scale not below P MANIFEST a perpetual
    engine — as an OBJECT, before being killed by lexRank. -/
theorem mersenneRefutation_carries_engine
    (hLaw : MersenneManifestationLaw)
    {P : ℕ} (hAbs : MersenneTwinAbsenceAbove P)
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

/-- **M3 — ESSENCE (mirror of twins_infinite_of_noEngine_and_boundary and
    the Riemannian L3):** no engines + accepted boundary + manifestation law
    ⟹ Mersenne twins are unbounded. All three hypotheses are consumed
    GENUINELY: an absence witness P is extracted from finiteness; the boundary
    gives resolution exactly at scale M0 := P; the law supplies a family 𝓕
    (not ex falso); from the collision an engine-WITNESS is built; it is
    precisely hNoEngine that kills it. -/
theorem mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : MersenneManifestationLaw) :
    EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_mersenneAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    mersenneRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- Green reduction to the programme goal: the same triple ⟹ twins are infinite
    (via the honest bridge Mersenne ⟹ twins). -/
theorem twinLowersInfinite_of_noEngine_boundary_and_mersenneManifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : MersenneManifestationLaw) :
    EuclidsPath.TwinLowers.Infinite :=
  EuclidsPath.MersenneBranch.twinLowersInfinite_of_mersenneTwins
    (mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-#############################################################################
  §5. Honesty audits (M5–M9)
#############################################################################-/

/-- **M5 (vacuous reverse direction, mirror of L5):** unboundedness ⟹ law
    vacuously — the absence gate is empty. The load-bearing direction is M3, and it needs the boundary. -/
theorem mersenneManifestationLaw_of_unbounded
    (H : EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded) :
    MersenneManifestationLaw := fun P hAbs =>
  ((mersenneTwinCentersUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **M6 (exact green characterization, mirror of L6):** law ⟺ "absence
    above P would freeze every resolving ledger at scales ≥ P".
    The reverse direction is ex falso from ¬resolves (unfolded). The gate hypothesis
    is potentially empty — so the characterization does NOT collapse into a global
    freeze (asymmetry with the ungated YM/NS forms). -/
theorem mersenneManifestationLaw_iff_no_resolution_above_absence :
    MersenneManifestationLaw ↔
      ∀ P : ℕ, MersenneTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **M7 — MAIN PRICE AUDIT (mirror of L7):** under the boundary, law ⟺
    unboundedness of Mersenne twins — the fourth field would be exactly
    of Mersenne-twin strength. WITHOUT the boundary, "law ⟹ unboundedness" does not
    assemble greenly (M3 requires the boundary). ⚠️ THIS IS EXACTLY WHERE one sees why the field
    is deferred: the heuristic points AGAINST the right-hand side of this ⟺. -/
theorem mersenneManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    MersenneManifestationLaw ↔
      EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded :=
  ⟨mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   mersenneManifestationLaw_of_unbounded⟩

/-- Witness type for the bundling audit (subtype — front_pair works with Type). -/
abbrev MersenneAbsenceWitness : Type := {P : ℕ // MersenneTwinAbsenceAbove P}

theorem nonempty_mersenneAbsenceWitness_iff :
    Nonempty MersenneAbsenceWitness ↔
      ¬ EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (mersenneTwinCentersUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_mersenneAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- Law in Bridge form over the witness type. -/
theorem mersenneManifestationLaw_iff_bridge :
    MersenneManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : MersenneAbsenceWitness => MersenneAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **M9 (bundling audit, instantiation of the condemning machine):** the bundle
    Bridge∧Impossible ⟺ "no absence witnesses" — only the Bridge side could
    ever be decreed; the Impossible side at resolved scales is
    the green L2, never a decree. -/
theorem mersenneManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : MersenneAbsenceWitness => MersenneAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : MersenneAbsenceWitness => MersenneAbsenceManifests W.1)) ↔
      ¬ Nonempty MersenneAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Machine-visible purity in the build log
-- (expected [propext, Classical.choice, Quot.sound] — WITHOUT step00FirstCause):
#print axioms mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms mersenneRefutation_carries_engine
#print axioms mersenneManifestationLaw_iff_unbounded_of_boundary
#print axioms isEmpty_properCenterPeel_five_one
#print axioms mersenneAbsenceBound_ge_29

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
