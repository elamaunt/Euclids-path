/-
  FermatManifestationFront — GREEN (axiom-free) module of the Fermat branch
  of the perpetual engine programme: "to refute Fermat twins = to exhibit a
  perpetual engine", carried out via the Riemann manifestation architecture —
  STRUCTURAL MIRROR of the Sophie-Germain front and Mersenne front (ch. 43),
  with Fermat data (minus-side of the center `c_k = (F_k + 1)/6`, quadratic chain).

  The deviation here is NOT a data object (like an off-critical zero) but a Π-witness:
  `FermatTwinAbsenceAbove P` — absence of Fermat twins above threshold P
  (mirror of `SGAbsenceAbove` and `MersenneTwinAbsenceAbove`). The manifestation law
  is GATED by this witness: the ungated form (∀ P, Manifests P) would explode the
  accepted boundary — as do the YM and NS manifestation candidates (disclosed below).

  Architecture (mirror of SophieGermainManifestationFront, M1–M9):
    * negation plumbing: absence witness ⟺ ¬unboundedness;
    * QUADRATIC chain of centers (minus-side: `c' + 4c = 6c² + 1`,
      branch disclosure `fermatCenter_chain`) strictly grows
      (`fermatCenter_strictMono_from_one`) — AND KEY DISCLOSURE: the chain does NOT
      PEEL (`isEmpty_properCenterPeel_three_one`) — the quadratic chain carries no
      identity with a constant prime divisor (unlike the linear
      5c + 1 of the 5-adic); already step 3 → 1 is empty (sides 17 and 19 are prime,
      goal sides are only 5 and 7). Therefore a FORGED witness in this branch DOES NOT
      EXIST — unlike YM (cookedLadder) and NS (cookedProfileCascade), exactly as with
      Riemann, Mersenne, and Sophie Germain;
    * manifestation law `FermatManifestationLaw` (anchor M0 := P, consumed
      via le_refl); Impossible-side — the green theorem
      `no_deviationFlowSupply_at_resolved_scale` (reused), NOT a decree;
    * ESSENCE M3: no engines + accepted boundary + law ⟹ Fermat twins are unbounded
      (all three hypotheses are genuinely consumed);
    * READABLE FORM M3⁺ `fermatRefutation_carries_engine`: absence witness
      + law + balanced ledger ⟹ engine-WITNESS as an object.

  FOURTH-FIELD TRILEMMA PASSED (V1: not refutable — any absence witness
  ≥ 65537 (M8) is green, and EXHIBITING a witness = solving the open
  question about the Fermat-twin tail; V2: not provable and not vacuous green — under
  the boundary the law ⟺ open unboundedness (M7), vacuity of gate ⟺ same
  open question; V3: does not explode the boundary — nothing to forge, isEmpty green).
  BUT THE FIELD IS NOT ADDED — DELIBERATELY: ⚠️ THE HEURISTIC SIGN IS INVERTED MORE
  SHARPLY THAN FOR MERSENNE. Only F₀–F₄ are known prime, while F₅–F₃₂ are PROVABLY
  composite, so the input `FermatTwinCentersUnbounded` is most likely FALSE — the
  expected truth of the boundary is negative here even more sharply than Mersenne
  (there the sum over twin pairs converges but does not directly forbid infinitude;
  here the known tail of composite Fermat numbers is enormous). Riemann was a bet on
  the expected-true; Fermat would be the boundary with the most negative expected
  truth in the programme. AND YET THE FIELD IS ABSENT — verdict of §16 and §17:
  the programme does not multiply manifestation fields beyond Riemann; the law lives
  here AS A DEFINITION (like RiemannManifestationLaw before §10), and the quarantine
  consistency is NOT staked on it. See the §16 quarantine comment and prose/43.

  BORROWING DISCLOSURE L1: the supply object `DeviationFlowSupply` and its
  non-triviality witness (Riemann L1) ARE TAKEN from the Riemann front and
  are not reproved here; the Impossible-side on resolved scales is
  green L2, never a decree.

  VACUITY BAN №3: no free Prop-fields, free gates, or renamed conclusions —
  every hypothesis is arithmetically named.
  The module does NOT import quarantine; no axiom and no sorry.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.FermatBranch

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. Deviation witness: absence of Fermat twins above threshold
#############################################################################-/

/-- **Absence of Fermat twins above `P`** (Π-witness, mirror of
    `SGAbsenceAbove` and `MersenneTwinAbsenceAbove`): every Fermat number `F_k`
    (for `k ≥ 1`) such that `F_k` and `F_k + 2` are both prime sits, by its
    lesser member `F_k`, no higher than `P`. -/
def FermatTwinAbsenceAbove (P : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → (Nat.fermatNumber k).Prime →
    (Nat.fermatNumber k + 2).Prime → Nat.fermatNumber k ≤ P

/-- Plumbing: an absence witness is extracted from boundedness. -/
theorem exists_fermatAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) :
    ∃ P : ℕ, FermatTwinAbsenceAbove P := by
  unfold EuclidsPath.FermatBranch.FermatTwinCentersUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun k h1 h2 h3 => by
    by_contra hgt
    exact hP k h1 (by omega) h2 h3⟩

/-- Plumbing: unboundedness ⟺ no absence witnesses. -/
theorem fermatTwinCentersUnbounded_iff_no_absence :
    EuclidsPath.FermatBranch.FermatTwinCentersUnbounded ↔
      ∀ P : ℕ, ¬ FermatTwinAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨k, hk1, hlt, h1, h2⟩ := hU P
    have := hAbs k hk1 h1 h2
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_fermatAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **M8 (witness-domain localisation, mirror of SG8):** every absence bound
    is ≥ 65537 — the pair `(F₄, F₄ + 2) = (65537, 65539)` at `k = 4`
    exists greenly (`fermat_twin_instances` of the branch — the strongest
    concrete twin localisation in the programme). -/
theorem fermatAbsenceBound_ge_65537 {P : ℕ}
    (hAbs : FermatTwinAbsenceAbove P) : 65537 ≤ P := by
  have hF4 : Nat.fermatNumber 4 = 65537 := by norm_num [Nat.fermatNumber]
  have h := hAbs 4 (by norm_num)
    (by rw [hF4]; norm_num) (by rw [hF4]; norm_num)
  rw [hF4] at h
  omega

/-#############################################################################
  §2. Quadratic chain of centers: strictly grows — and does NOT PEEL (no forging)
#############################################################################-/

/-- Bridging remark to the branch disclosure: on the minus-side the Fermat center
    chain is QUADRATIC (`fermatCenter_chain`: `c' + 4c = 6c² + 1`) and strictly
    climbs at every step for `k ≥ 1` (`fermatCenter_strictMono_from_one`) — like
    the doubling `m → 2m` of Sophie Germain and the base-4 `m → 4m+1` of Mersenne.
    Growth exists, but it is precisely that which makes the disclosure below
    non-trivial: the chain can grow, but it cannot PEEL. -/
theorem fermatCenter_lt_succ {k : ℕ} (hk : 1 ≤ k) :
    EuclidsPath.FermatBranch.fermatCenter k <
      EuclidsPath.FermatBranch.fermatCenter (k + 1) :=
  EuclidsPath.FermatBranch.fermatCenter_strictMono_from_one hk

/-- **KEY DISCLOSURE (contrast with the 5-adic, mirror of
    `isEmpty_properCenterPeel_two_one` and `isEmpty_properCenterPeel_five_one`):
    the quadratic Fermat center chain does NOT PEEL.**
    The 5-adic chain `c → 5c+1` has the identity `6(5x+1)−1 = 5(6x+1)` with
    PRIME constant divisor 5 — hence it builds flows for A ≤ 4.
    The quadratic Fermat chain `c' + 4c = 6c² + 1` has no such identity with a
    constant prime divisor (`fermatCenter_chain` discloses it without division):
    already step 3 → 1 carries no intrinsic peel AT ANY SCALE — sides 17 and 19 are
    prime, goal sides are only 5 and 7. Consequence: the Fermat chain does NOT build
    an unconditional supply of flows — a FORGED witness (the YM and NS V3 pattern)
    does not exist in this branch. -/
theorem isEmpty_properCenterPeel_three_one (A : ℕ) :
    IsEmpty (ProperCenterPeel A 3 1) := by
  constructor
  rintro ⟨inS, outS, q, _hq, _hA, hfac, _hsm, _hpos⟩
  cases inS <;> cases outS <;> simp only [sideValue] at hfac <;> omega

/-#############################################################################
  §3. Manifestation law (gated by witness; field is NOT decreed)
#############################################################################-/

/-- Absence above `P` manifests arithmetically: at every ledger scale
    no lower than `P`, wherever the projection balances the ledger, the absence
    manifests as an unpayable infinite supply of flows. The anchor `P ≤ M0`
    is consumed below only via `le_refl` (Riemann pattern). Causal
    form: "a refutation must manifest where the ledger is balanced" — NOT
    a statement about Fermat twins themselves. -/
def FermatAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **FERMAT MANIFESTATION LAW** — gated by the absence witness.
    The ungated form `∀ P, FermatAbsenceManifests P` at P := 0 together with
    the accepted boundary would yield a supply at a resolved scale — contradiction
    with green L2 (the exact failure mechanism of the YM and NS manifestation
    candidates). Gate by a greenly-unpresentable witness is what distinguishes this form.
    THE FIELD IS NOT DECREED — even though the heuristic sign is INVERTED MORE SHARPLY
    than Mersenne (F₅–F₃₂ are composite; verdict of §16 and §17, see header). -/
def FermatManifestationLaw : Prop :=
  ∀ P : ℕ, FermatTwinAbsenceAbove P → FermatAbsenceManifests P

/-#############################################################################
  §4. ESSENCE and readable form: refutation exhibits the engine
#############################################################################-/

/-- **M3⁺ — READABLE FORM "refutation = engine":** absence witness
    + law + balanced ledger at scale no lower than P MANIFEST a perpetual
    engine — as an OBJECT, prior to killing by lexRank. -/
theorem fermatRefutation_carries_engine
    (hLaw : FermatManifestationLaw)
    {P : ℕ} (hAbs : FermatTwinAbsenceAbove P)
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

/-- **M3 — ESSENCE (mirror of SG3 and Riemann L3):** no engines +
    accepted boundary + manifestation law ⟹ Fermat twins are unbounded.
    All three hypotheses are GENUINELY consumed: from finiteness an absence
    witness P is extracted; the boundary gives resolution exactly at scale
    M0 := P; the law supplies family 𝓕 (not ex falso); from the collision an
    engine-WITNESS is built; it is killed by exactly hNoEngine. -/
theorem fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : FermatManifestationLaw) :
    EuclidsPath.FermatBranch.FermatTwinCentersUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_fermatAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    fermatRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- Green path to the programme's goal: the same triple ⟹ twins are infinite
    (via the ONLY honest direction of the Fermat branch ⟹ twins,
    `twinLowersInfinite_of_fermatTwins`). -/
theorem twinLowersInfinite_of_noEngine_boundary_and_fermatManifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : FermatManifestationLaw) :
    EuclidsPath.TwinLowers.Infinite :=
  EuclidsPath.FermatBranch.twinLowersInfinite_of_fermatTwins
    (fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-#############################################################################
  §5. Honesty audits (M5–M9)
#############################################################################-/

/-- **M5 (vacuous converse, mirror of SG5):** unboundedness ⟹
    law vacuously — the absence gate is empty. The load-bearing side is M3, and
    it requires the boundary. -/
theorem fermatManifestationLaw_of_unbounded
    (H : EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) :
    FermatManifestationLaw := fun P hAbs =>
  ((fermatTwinCentersUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **M6 (exact green characterisation, mirror of SG6):** law ⟺ "absence
    above P would freeze every resolving ledger at scales ≥ P".
    Reverse direction — ex falso from ¬resolves (disclosed). Gate hypothesis
    is potentially empty — so the characterisation does NOT collapse into global
    freeze (asymmetry with the ungated YM and NS forms). -/
theorem fermatManifestationLaw_iff_no_resolution_above_absence :
    FermatManifestationLaw ↔
      ∀ P : ℕ, FermatTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **M7 — MAIN PRICE AUDIT (mirror of SG7 and Mersenne M7):** under the boundary,
    law ⟺ unboundedness of Fermat twins — the fourth field would have exactly
    Fermat-conjecture strength. WITHOUT the boundary "law ⟹ unboundedness" does not
    assemble greenly (M3 requires the boundary). ⚠️ IT IS PRECISELY HERE that one sees
    why the field is deferred: the heuristic is directed AGAINST the right-hand side of
    this ⟺ MORE SHARPLY than Mersenne — only F₀–F₄ are prime, while F₅–F₃₂ are
    provably composite. -/
theorem fermatManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    FermatManifestationLaw ↔
      EuclidsPath.FermatBranch.FermatTwinCentersUnbounded :=
  ⟨fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   fermatManifestationLaw_of_unbounded⟩

/-- Witness type for the bundling audit (subtype — front_pair works with Type). -/
abbrev FermatAbsenceWitness : Type := {P : ℕ // FermatTwinAbsenceAbove P}

theorem nonempty_fermatAbsenceWitness_iff :
    Nonempty FermatAbsenceWitness ↔
      ¬ EuclidsPath.FermatBranch.FermatTwinCentersUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (fermatTwinCentersUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_fermatAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- Law in Bridge-form over the witness type. -/
theorem fermatManifestationLaw_iff_bridge :
    FermatManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : FermatAbsenceWitness => FermatAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **M9 (bundling audit, instantiation of the convicting machine):** the bundle
    Bridge∧Impossible ⟺ "no absence witnesses" — ONLY the Bridge-side could be
    decreed; the Impossible-side on resolved scales is green L2, never a decree. -/
theorem fermatManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : FermatAbsenceWitness => FermatAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : FermatAbsenceWitness => FermatAbsenceManifests W.1)) ↔
      ¬ Nonempty FermatAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Machine-visible purity in the build log
-- (expected [propext, Classical.choice, Quot.sound] — WITHOUT step00FirstCause):
#print axioms fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms fermatRefutation_carries_engine
#print axioms fermatManifestationLaw_iff_unbounded_of_boundary
#print axioms fermatAbsenceBound_ge_65537
#print axioms isEmpty_properCenterPeel_three_one

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
