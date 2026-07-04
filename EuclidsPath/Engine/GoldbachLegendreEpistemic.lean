/-
  GoldbachLegendreEpistemic — EPISTEMIC COMPLEMENT of Goldbach and Legendre
  (Tier 1 programme: "to solve from within = to build a perpetual engine").
  Reference models: PNPFirstCause (substantive pair), CollatzFirstCause (post-mortem).
  Fronts: GoldbachManifestationFront (G3⁺, G8), LegendreDesertFront (LG3⁺, LG8,
  unconditional Bertrand no_desert_doubles).

  WHAT THIS IS. "Internal self-justification of a solution" for two witness-object
  fronts of the arithmetic zoo: scale anchor + ledger settled + manifestation of
  ONE'S OWN witness. Self-justification self-destructs (`no_internalised*Ground`),
  so "the cause cannot be known from within" — theorems `goldbachCause_unknowable` /
  `legendreCause_unknowable`; the trilemmas `*_no_internal_decision_without_engine`
  show: to refute = to exhibit an engine, to self-justify =
  to self-destruct, only the external boundary + external decide-check decides.
  Overall summary — `goldbachLegendre_locked_behind_engine_status`.

  WHAT PAYS FOR SUBSTANTIVENESS (honestly, by the skeptic's verdict). The contradiction
  in `no_internalised*Ground` is supplied NOT by the form P ∧ ¬P, but by the GREEN engine
  theorem `no_deviationFlowSupply_at_resolved_scale` (family → collision →
  engine-witness → killed by lexRank; NOT ex falso), and the supply form is non-empty:
  `deviationFlowSupply_of_twinBound` constructs it greenly. SCALE ANCHOR (CORR):
  the `ground` field ("ledger settled") is gated by the anchor `anchored` — the scale is
  NO LOWER than the witness (`V.1 ≤ M0` for Goldbach, `V.1 ^ 2 ≤ M0` for Legendre);
  without the anchor the manifestation cannot be applied to the projection.

  TWO HONEST DEGRADATIONS AGAINST REFERENCE MODELS (disclosed): (a) the field
  `beyondOwnHorizon` — manifestation of the witness THROUGH the law-definition and never
  instantiated greenly (type of witnesses is expectedly EMPTY); for PNP the analogue
  `concreteSupply_unbounded_smallScale` is greenly TRUE — this layer is weaker;
  (b) the Collatz variant ground := Law / beyondOwnHorizon := ¬Law would be a bare
  P ∧ ¬P (for Collatz the tautologousness was paid by the decree `collatzBoundary`,
  which the zoo does NOT have per §17-verdict) — it is NOT used here.

  HONESTY. This is model-internal epistemic unknowability (like
  `collatzCause_unknowable`/`pnpCause_unknowable`), and NOT a solution to binary
  Goldbach (1742) or Legendre (1808) and NOT Gödel (no incompleteness /
  fixed point — only the engine wall). The summary WITHOUT the decree-conjunct is
  a mirror of `pnp_locked_behind_engine_status`, not of the Collatz variant: the fields
  goldbach/legendre in Step00FirstCause are absent (§17: seriality would devalue the
  quarantine), the boundary enters only as HYPOTHESIS `TheStrictLastStep00Obligation`.
  Twin-epistemics lives in CausalClosureAxiom §8 under the names
  InternalisedStep00HorizonBoundary / InternalisedStep00OriginEvent (not Ground).
  The module does NOT import quarantine; no axiom/sorry/native_decide — ENTIRELY
  green, the repository taint does not change.
-/
import EuclidsPath.Engine.GoldbachManifestationFront
import EuclidsPath.Engine.LegendreDesertFront

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace Epistemic

/-#############################################################################
  §1. Goldbach: internal self-justification and its self-destruction (🟢)
#############################################################################-/

/-- **Internal self-justification of the Goldbach solution.** The carrier simultaneously
    (a) ANCHORS the scale no lower than the witness (`anchored`, CORR: ledger settled at
    a scale no lower than the violating number itself), (b) SETTLES the ledger (`ground` —
    ledger collisions are resolved) and (c) carries the manifestation of ITS OWN witness
    (`beyondOwnHorizon`). The form is not substantive by itself: the contradiction is
    supplied by the green `no_deviationFlowSupply_at_resolved_scale`, and the non-emptiness
    of the supply form is exhibited by `deviationFlowSupply_of_twinBound`. HONESTLY:
    `beyondOwnHorizon` — belief in the law-definition, it has no green instance
    (the type `GoldbachViolation` is expectedly empty) — the layer is weaker than the PNP reference model. -/
structure InternalisedGoldbachGround
    (V : EuclidsPath.GoldbachBranch.GoldbachViolation)
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop where
  anchored : V.1 ≤ M0
  ground : SemanticExtendedFlowLedgerCollisionResolves proj
  beyondOwnHorizon : GoldbachViolationManifests V

/-- "Internal knowledge of the Goldbach cause" = internal self-justification. -/
abbrev InternalKnowledgeOfGoldbachCause
    (V : EuclidsPath.GoldbachBranch.GoldbachViolation)
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  InternalisedGoldbachGround V proj

/-- Self-justification self-destructs: manifestation over the settled ledger (through
    the anchor) yields a supply — but at the resolved scale there IS NO supply (the green
    engine theorem `no_deviationFlowSupply_at_resolved_scale`, NOT the form
    P ∧ ¬P and NOT ex falso). GREEN. -/
theorem no_internalisedGoldbachGround
    {V : EuclidsPath.GoldbachBranch.GoldbachViolation}
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0} :
    InternalisedGoldbachGround V proj → False :=
  fun H => no_deviationFlowSupply_at_resolved_scale proj H.ground
    (H.beyondOwnHorizon A M0 H.anchored proj H.ground)

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM** (mirror of `pnpCause_unknowable` /
    `collatzCause_unknowable`): internal knowledge of the Goldbach cause is impossible.
    NOT a solution to the 1742 conjecture and NOT Gödel — a model-internal wall. -/
theorem goldbachCause_unknowable
    {V : EuclidsPath.GoldbachBranch.GoldbachViolation}
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0} :
    ¬ InternalKnowledgeOfGoldbachCause V proj :=
  no_internalisedGoldbachGround

/-- **"Carries an engine" — GENUINE CONSTRUCTION (not ex falso):** from
    self-justification an engine-witness is built AS AN OBJECT — the same chain as
    in G3⁺ `goldbachViolation_carries_engine`, but fuelled by the manifestation of
    ONE witness from the field `beyondOwnHorizon` (not the whole law). Together with
    `no_internalisedGoldbachGround` this is the price: self-justification costs
    a perpetual engine, which does not exist (`no_someConcreteEuclideanEngine`). -/
theorem internalisedGoldbachGround_builds_engine
    {V : EuclidsPath.GoldbachBranch.GoldbachViolation}
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0} :
    InternalisedGoldbachGround V proj → ConcreteEuclideanEngineWitness A M0 := by
  intro H
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr H.ground
  obtain ⟨𝓕, h𝓕⟩ := H.beyondOwnHorizon A M0 H.anchored proj H.ground
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **"SOLUTION LOCKED BEHIND THE ENGINE" — Goldbach trilemma (mirror of
    `pnp_no_internal_decision_without_engine`):**
    (1) REFUTE from within: witness + law + settled ledger at the anchor
        scale manifest an engine AS AN OBJECT (G3⁺; conditional on the
        law-definition — there is no unconditional analogue of
        `nonHalting_carries_perpetual_engine` for this front and there cannot be
        one without solving the open problem);
    (2) SELF-JUSTIFY from within — self-destructs (`no_internalisedGoldbachGround`);
    (3) Only the EXTERNAL boundary decides (hypothesis `TheStrictLastStep00Obligation`,
        no decree instantiation — §17) + law: then the Goldbach conjecture
        holds (G3-form, the wall `no_someConcreteEuclideanEngine` is already embedded).
    Gödelian independence is NOT claimed and this is NOT a solution to Goldbach. -/
theorem goldbach_no_internal_decision_without_engine :
    (GoldbachManifestationLaw →
      ∀ (V : EuclidsPath.GoldbachBranch.GoldbachViolation) (A M0 : ℕ),
        V.1 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) ∧
    (∀ (V : EuclidsPath.GoldbachBranch.GoldbachViolation) (A M0 : ℕ)
        (proj : SemanticExtendedFlowLedgerProjection A M0),
          ¬ InternalisedGoldbachGround V proj) ∧
    (TheStrictLastStep00Obligation → GoldbachManifestationLaw →
      EuclidsPath.GoldbachBranch.GoldbachConjecture) :=
  ⟨fun hLaw V _ _ hM proj hres =>
      goldbachViolation_carries_engine hLaw V hM proj hres,
   fun _ _ _ _ => no_internalisedGoldbachGround,
   fun hBoundary hLaw =>
      goldbachConjecture_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine hBoundary hLaw⟩

/-- **"VERIFICATION, NOT DERIVATION" — the strongest arm of the series (mirror of
    `pnp_verification_not_derivation`):** (1) internal knowledge of the cause is
    impossible (theorem); (2) verification — LITERALLY `decide`: all even numbers
    4..50 are decomposed by machine (`goldbach_upTo_52`, pointwise decidability
    `GoldbachRep`); (3) therefore every witness ≥ 52 (G8) — a solution is findable
    exactly as far as the verification has been checked (the literary
    4·10^18 are NOT formalised — only this is green). -/
theorem goldbach_verification_not_derivation :
    (∀ (V : EuclidsPath.GoldbachBranch.GoldbachViolation) (A M0 : ℕ)
        (proj : SemanticExtendedFlowLedgerProjection A M0),
          ¬ InternalKnowledgeOfGoldbachCause V proj) ∧
    (∀ E, E < 52 → 4 ≤ E → E % 2 = 0 →
        EuclidsPath.GoldbachBranch.GoldbachRep E) ∧
    (∀ V : EuclidsPath.GoldbachBranch.GoldbachViolation, 52 ≤ V.1) :=
  ⟨fun _ _ _ _ => goldbachCause_unknowable,
   EuclidsPath.GoldbachBranch.goldbach_upTo_52,
   goldbachViolation_ge_52⟩

/-#############################################################################
  §2. Legendre: the same self-destruction + unique Bertrand arm (🟢)
#############################################################################-/

/-- **Internal self-justification of the Legendre solution** — mirror of the Goldbach one,
    with a quadratic anchor: `V.1 ^ 2 ≤ M0` (scale no lower than the square of the
    violation point — the deviation height for a desert is quadratic). The same honest
    caveats: substantiveness is paid for by the green
    `no_deviationFlowSupply_at_resolved_scale`; `beyondOwnHorizon` — belief in the
    law-definition, no green instance (type `LegendreViolation` is expectedly empty). -/
structure InternalisedLegendreGround
    (V : EuclidsPath.PrimeDeserts.LegendreViolation)
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop where
  anchored : V.1 ^ 2 ≤ M0
  ground : SemanticExtendedFlowLedgerCollisionResolves proj
  beyondOwnHorizon : LegendreDesertManifests V

/-- "Internal knowledge of the Legendre cause" = internal self-justification. -/
abbrev InternalKnowledgeOfLegendreCause
    (V : EuclidsPath.PrimeDeserts.LegendreViolation)
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  InternalisedLegendreGround V proj

/-- Self-justification self-destructs — the same green wall
    `no_deviationFlowSupply_at_resolved_scale` (NOT P ∧ ¬P, NOT ex falso). -/
theorem no_internalisedLegendreGround
    {V : EuclidsPath.PrimeDeserts.LegendreViolation}
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0} :
    InternalisedLegendreGround V proj → False :=
  fun H => no_deviationFlowSupply_at_resolved_scale proj H.ground
    (H.beyondOwnHorizon A M0 H.anchored proj H.ground)

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM** for Legendre (mirror of
    `goldbachCause_unknowable`). NOT a solution to the 1808 problem and NOT Gödel. -/
theorem legendreCause_unknowable
    {V : EuclidsPath.PrimeDeserts.LegendreViolation}
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0} :
    ¬ InternalKnowledgeOfLegendreCause V proj :=
  no_internalisedLegendreGround

/-- **"Carries an engine" — genuine construction** (mirror of the Goldbach one):
    an engine-witness is built as an object from the manifestation of one Legendre
    witness over the settled ledger of the anchor scale. -/
theorem internalisedLegendreGround_builds_engine
    {V : EuclidsPath.PrimeDeserts.LegendreViolation}
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0} :
    InternalisedLegendreGround V proj → ConcreteEuclideanEngineWitness A M0 := by
  intro H
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr H.ground
  obtain ⟨𝓕, h𝓕⟩ := H.beyondOwnHorizon A M0 H.anchored proj H.ground
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **"SOLUTION LOCKED BEHIND THE ENGINE" — Legendre trilemma WITH A FOURTH ARM**
    (unique in the series): to the three mirror arms is added an UNCONDITIONAL green
    wall of arithmetic itself — Bertrand: a desert does NOT double
    (`no_desert_doubles`, mathlib, no open problem) — together with the honest
    conjunct `NoBertrandToLegendreImplicationClaimed`: the Legendre interval is
    SHORTER than Bertrand's (`legendre_interval_shorter_than_bertrand`), no
    implication Bertrand ⟹ Legendre is claimed — the fourth arm is strong, but
    does not close the quadratic gap. -/
theorem legendre_no_internal_decision_without_engine :
    (LegendreManifestationLaw →
      ∀ (V : EuclidsPath.PrimeDeserts.LegendreViolation) (A M0 : ℕ),
        V.1 ^ 2 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) ∧
    (∀ (V : EuclidsPath.PrimeDeserts.LegendreViolation) (A M0 : ℕ)
        (proj : SemanticExtendedFlowLedgerProjection A M0),
          ¬ InternalisedLegendreGround V proj) ∧
    (TheStrictLastStep00Obligation → LegendreManifestationLaw →
      EuclidsPath.PrimeDeserts.LegendreConjecture) ∧
    ((∀ n : ℕ, n ≠ 0 →
        ¬ EuclidsPath.PrimeDeserts.PrimeDesertBetween n (2 * n + 1)) ∧
      EuclidsPath.PrimeDeserts.NoBertrandToLegendreImplicationClaimed) :=
  ⟨fun hLaw V _ _ hM proj hres =>
      legendreViolation_carries_engine hLaw V hM proj hres,
   fun _ _ _ _ => no_internalisedLegendreGround,
   fun hBoundary hLaw =>
      legendreConjecture_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine hBoundary hLaw,
   fun _ hn => EuclidsPath.PrimeDeserts.no_desert_doubles hn,
   EuclidsPath.PrimeDeserts.noBertrandToLegendreImplicationClaimed_holds⟩

/-- **"VERIFICATION, NOT DERIVATION" for Legendre:** (1) internal knowledge of the cause is
    impossible (theorem); (2) verification — literally `decide`: no violations below 11
    (`legendre_holds_upTo_10`, pointwise decidability
    `LegendreViolationAt`); (3) therefore every witness ≥ 11 (LG8) —
    the literary bound (>10^18) is NOT formalised, only this is green. -/
theorem legendre_verification_not_derivation :
    (∀ (V : EuclidsPath.PrimeDeserts.LegendreViolation) (A M0 : ℕ)
        (proj : SemanticExtendedFlowLedgerProjection A M0),
          ¬ InternalKnowledgeOfLegendreCause V proj) ∧
    (∀ n, n < 11 → 1 ≤ n →
        ¬ EuclidsPath.PrimeDeserts.LegendreViolationAt n) ∧
    (∀ V : EuclidsPath.PrimeDeserts.LegendreViolation, 11 ≤ V.1) :=
  ⟨fun _ _ _ _ => legendreCause_unknowable,
   EuclidsPath.PrimeDeserts.legendre_holds_upTo_10,
   EuclidsPath.PrimeDeserts.legendreViolation_ge_11⟩

/-#############################################################################
  §3. Overall summary: both solutions are locked behind the engine status (🟢)
#############################################################################-/

/-- **OVERALL SUMMARY "LOCKED BEHIND THE ENGINE" (mirror of
    `pnp_locked_behind_engine_status`; WITHOUT the decree-conjunct — the fields
    goldbach/legendre are absent from Step00FirstCause per the §17-verdict, unlike
    the Collatz variant where the decree was taken and lifted):**
    (1) no engines — green wall (`no_someConcreteEuclideanEngine`);
    (2) internal knowledge of the Goldbach cause is impossible (theorem);
    (3) internal knowledge of the Legendre cause is impossible (theorem);
    (4) verified Goldbach horizon: every witness ≥ 52 (decide);
    (5) verified Legendre horizon: every witness ≥ 11 (decide);
    (6) Goldbach is decided only by the EXTERNAL boundary (hypothesis) + law;
    (7) Legendre — likewise.
    ENTIRELY green; does NOT solve either problem, NOT Gödel — both conjectures
    remain open inputs with the door locked from within. -/
theorem goldbachLegendre_locked_behind_engine_status :
    (¬ SomeConcreteEuclideanEngine) ∧
    (∀ (V : EuclidsPath.GoldbachBranch.GoldbachViolation) (A M0 : ℕ)
        (proj : SemanticExtendedFlowLedgerProjection A M0),
          ¬ InternalKnowledgeOfGoldbachCause V proj) ∧
    (∀ (V : EuclidsPath.PrimeDeserts.LegendreViolation) (A M0 : ℕ)
        (proj : SemanticExtendedFlowLedgerProjection A M0),
          ¬ InternalKnowledgeOfLegendreCause V proj) ∧
    (∀ V : EuclidsPath.GoldbachBranch.GoldbachViolation, 52 ≤ V.1) ∧
    (∀ V : EuclidsPath.PrimeDeserts.LegendreViolation, 11 ≤ V.1) ∧
    (TheStrictLastStep00Obligation → GoldbachManifestationLaw →
      EuclidsPath.GoldbachBranch.GoldbachConjecture) ∧
    (TheStrictLastStep00Obligation → LegendreManifestationLaw →
      EuclidsPath.PrimeDeserts.LegendreConjecture) :=
  ⟨no_someConcreteEuclideanEngine,
   fun _ _ _ _ => goldbachCause_unknowable,
   fun _ _ _ _ => legendreCause_unknowable,
   goldbachViolation_ge_52,
   EuclidsPath.PrimeDeserts.legendreViolation_ge_11,
   fun hBoundary hLaw =>
      goldbachConjecture_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine hBoundary hLaw,
   fun hBoundary hLaw =>
      legendreConjecture_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine hBoundary hLaw⟩

/-! ## Axiom audit: the module is ENTIRELY green (standard triple), taint does not change -/
#print axioms no_internalisedGoldbachGround
#print axioms goldbachCause_unknowable
#print axioms internalisedGoldbachGround_builds_engine
#print axioms goldbach_no_internal_decision_without_engine
#print axioms goldbach_verification_not_derivation
#print axioms no_internalisedLegendreGround
#print axioms legendreCause_unknowable
#print axioms internalisedLegendreGround_builds_engine
#print axioms legendre_no_internal_decision_without_engine
#print axioms legendre_verification_not_derivation
#print axioms goldbachLegendre_locked_behind_engine_status

end Epistemic
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
