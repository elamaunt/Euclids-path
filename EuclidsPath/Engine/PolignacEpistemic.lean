/-
  PolignacEpistemic — EPISTEMIC COMPLEMENT OF POLIGNAC (cousin primes p, p+4 and
  sexy primes p, p+6 — cases 4 and 6 of the Polignac conjecture). Tier 1 programme.
  Green machine for both families: Engine/PolignacManifestationFront.lean (M1–M9).
  Reference chain: CollatzFirstCause (post-mortem epistemic), PNPFirstCause
  (P/NP complement); the twin version lives in §8 of the quarantine and is NOT imported here.

  WHAT THIS IS. "Solving case 4/6 from the inside" is modelled by the three-field bundle
  `InternalisedCousinGround` / `InternalisedSexyGround`: the manifestation law
  (`ground`), an absence witness for centers no higher than the ledger scale (`absence`),
  and the settled ledger at that scale (`beyondOwnHorizon`). The triple is INCOMPATIBLE
  in green: it directly assembles a perpetual engine (`cousinRefutation_carries_engine` /
  `sexyRefutation_carries_engine` — a genuine construction via
  `infiniteFlows_in_stableNoEnergy_build_engine`, NOT ex falso) — and dies against
  the green wall `no_someConcreteEuclideanEngine` (lexRank strictly drops).

  HONESTY (all caveats disclosed, also in docstrings):
  * this is MODEL-INTERNAL epistemic — NOT a proof and NOT a refutation
    of Polignac cases 4/6 (they are open) and NOT Gödel (self-destruction against
    the lexRank wall, not a theorem about incompleteness/fixed points);
  * the bundle is three-field and no field is the negation of another — this is the STYLE
    of P/NP, but NOT arity: the reference `InternalisedPNPGround` is itself TWO-field
    (resolves + beyondOwnHorizon); the common lineage is non-tautologicity
    of the pair/triple, unlike the honestly-labelled tautological two-field
    `InternalisedCollatzGround` (ground + ¬ground = P ∧ ¬P);
  * the law `CousinManifestationLaw` / `SexyManifestationLaw` is GATED by the absence
    witness (∀ P, witness → manifestation) and NOT decreed (the fields
    cousinBoundary/sexyBoundary in Step00FirstCause do not exist — verdict §17, with
    POSITIVE sign of Hardy–Littlewood): payment of the contradiction is CONDITIONAL on
    the non-decreed law and settled ledger — weaker than the unconditional
    `nonHalting_carries_perpetual_engine` of Collatz and the green pigeonhole
    `no_fullPayment_of_unboundedSupply` of P/NP;
  * NONE of the three fields is greenly inhabited (in P/NP `beyondOwnHorizon`
    is greenly inhabited — `concreteSupply_unbounded_smallScale`): the bundle is
    the green INCOMPATIBILITY of three individually-unknown fields;
  * the boundary appears ONLY as the hypothesis `TheStrictLastStep00Obligation`
    (in conjuncts of the form "boundary → (law ↔ unboundedness)"): the module
    does not import the quarantine, is entirely green, the repository taint does not change.
-/

import EuclidsPath.Engine.PolignacManifestationFront

set_option autoImplicit false

namespace EuclidsPath.Polignac.Epistemic

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.PolignacBranch

/-! ## Model: internal solution = self-justification beyond its own horizon

For EACH of the two families (cousins — case 4, sexy primes — case 6) the bundle is
parametric over the ledger scale `(A, M0)` — the very one at which
`cousinRefutation_carries_engine` assembles the engine. -/

/-- **Internal self-justification of a solution to case 4 (cousin primes `p, p+4`).** Carries
    (a) the manifestation law `ground` — GATED by the witness and NOT decreed
    (§17); (b) an absence witness for cousin centers no higher than scale `absence`;
    (c) the settled ledger at that scale `beyondOwnHorizon`. No field is
    the negation of another (style of P/NP; but the reference `InternalisedPNPGround` is itself
    TWO-field — the common element is STYLE, not arity), and no field is greenly
    inhabited (unlike the greenly-inhabited `beyondOwnHorizon` in P/NP):
    the substance of the bundle is the green INCOMPATIBILITY of three individually-unknown
    fields, paid for by the genuine engine construction
    `cousinRefutation_carries_engine` against the wall `no_someConcreteEuclideanEngine`. -/
structure InternalisedCousinGround (A M0 : ℕ) : Prop where
  ground : CousinManifestationLaw
  absence : ∃ P : ℕ, P ≤ M0 ∧ CousinAbsenceAbove P
  beyondOwnHorizon : ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
    SemanticExtendedFlowLedgerCollisionResolves proj

/-- "Internal knowledge of the cause of case 4" = internal self-justification. -/
abbrev InternalKnowledgeOfCousinCause (A M0 : ℕ) : Prop :=
  InternalisedCousinGround A M0

/-- **Internal self-justification of a solution to case 6 (sexy primes `p, p+6`)** — mirror
    of cousins; the witness `SexyAbsenceAbove` is TWO-SIDED (gate over Or of minus/plus
    pairs — stronger than either side alone, disclosed in the front). Same honest
    caveats as `InternalisedCousinGround`. -/
structure InternalisedSexyGround (A M0 : ℕ) : Prop where
  ground : SexyManifestationLaw
  absence : ∃ P : ℕ, P ≤ M0 ∧ SexyAbsenceAbove P
  beyondOwnHorizon : ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
    SemanticExtendedFlowLedgerCollisionResolves proj

/-- "Internal knowledge of the cause of case 6" = internal self-justification. -/
abbrev InternalKnowledgeOfSexyCause (A M0 : ℕ) : Prop :=
  InternalisedSexyGround A M0

/-! ## Core: self-justification builds the engine and dies against the lexRank wall (🟢) -/

/-- **Self-justification of case 4 BUILDS the engine** — direct composition of
    `cousinRefutation_carries_engine` (genuine construction: the law supplies
    a family of flows, the stable universe turns it into an engine-WITNESS),
    NOT ex falso — unlike `internalisedPNPGround_builds_engine`, where
    the route is ex falso. The price of honesty: the construction is CONDITIONAL on the gated
    non-decreed law and settled ledger — both fields individually unknown. -/
theorem internalisedCousinGround_builds_engine {A M0 : ℕ}
    (H : InternalisedCousinGround A M0) : SomeConcreteEuclideanEngine := by
  obtain ⟨P, hPM, hAbs⟩ := H.absence
  obtain ⟨proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, cousinRefutation_carries_engine H.ground hAbs hPM proj hres⟩

/-- Self-justification of case 4 self-destructs: the built engine dies against
    the green wall `no_someConcreteEuclideanEngine` (lexRank strictly drops).
    GREEN, standard triple. -/
theorem no_internalisedCousinGround {A M0 : ℕ} :
    InternalisedCousinGround A M0 → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedCousinGround_builds_engine H)

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM for case 4** (mirror of
    `collatzCause_unknowable` / `pnpCause_unknowable`): internal knowledge
    of the cause of cousins is impossible at any ledger scale. NOT a statement about
    cousins themselves: case 4 is open, the law is not decreed. -/
theorem cousinCause_unknowable {A M0 : ℕ} :
    ¬ InternalKnowledgeOfCousinCause A M0 :=
  no_internalisedCousinGround

/-- **Self-justification of case 6 BUILDS the engine** — same caveats as for
    cousins (genuine construction, conditional on the gated law and ledger). -/
theorem internalisedSexyGround_builds_engine {A M0 : ℕ}
    (H : InternalisedSexyGround A M0) : SomeConcreteEuclideanEngine := by
  obtain ⟨P, hPM, hAbs⟩ := H.absence
  obtain ⟨proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, sexyRefutation_carries_engine H.ground hAbs hPM proj hres⟩

/-- Self-justification of case 6 self-destructs against the same lexRank wall. -/
theorem no_internalisedSexyGround {A M0 : ℕ} :
    InternalisedSexyGround A M0 → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedSexyGround_builds_engine H)

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM for case 6.** -/
theorem sexyCause_unknowable {A M0 : ℕ} :
    ¬ InternalKnowledgeOfSexyCause A M0 :=
  no_internalisedSexyGround

/-! ## Trilemma: solution is locked behind the engine (🟢) -/

/-- **3-way trilemma for case 4 (mirror of `pnp_no_internal_decision_without_engine`):**
    (1) SELF-JUSTIFY from within = build the engine (genuine construction);
    (2) what is built self-destructs against the lexRank wall;
    (3) the only remaining path — an EXTERNAL decree: under the boundary-HYPOTHESIS
        `TheStrictLastStep00Obligation` the law ⟺ unboundedness of cousin centers
        (M7: the field would cost exactly case 4) — and this field is DELIBERATELY not taken.
    NOT Gödelian independence and NOT a solution to case 4 — only: internal
    solution costs a perpetual engine, and the external door is not decreed. -/
theorem cousin_no_internal_decision_without_engine {A M0 : ℕ} :
    (InternalisedCousinGround A M0 → SomeConcreteEuclideanEngine) ∧
    (InternalisedCousinGround A M0 → False) ∧
    (TheStrictLastStep00Obligation →
        (CousinManifestationLaw ↔ CousinCentersUnbounded)) :=
  ⟨internalisedCousinGround_builds_engine,
   no_internalisedCousinGround,
   cousinManifestationLaw_iff_unbounded_of_boundary⟩

/-- **3-way trilemma for case 6** — sexy-prime mirror (M7: the field would cost exactly case 6). -/
theorem sexy_no_internal_decision_without_engine {A M0 : ℕ} :
    (InternalisedSexyGround A M0 → SomeConcreteEuclideanEngine) ∧
    (InternalisedSexyGround A M0 → False) ∧
    (TheStrictLastStep00Obligation →
        (SexyManifestationLaw ↔ SexyCentersUnbounded)) :=
  ⟨internalisedSexyGround_builds_engine,
   no_internalisedSexyGround,
   sexyManifestationLaw_iff_unbounded_of_boundary⟩

/-- **"POLIGNAC-4/6 SOLUTION IS LOCKED BEHIND THE ENGINE" — both families at once**
    (mirror of `pnp_no_internal_decision_without_engine`, two trilemmas in one
    theorem). Boundary — hypothesis only; law — gate only; module is green. -/
theorem polignac_no_internal_decision_without_engine {A M0 : ℕ} :
    ((InternalisedCousinGround A M0 → SomeConcreteEuclideanEngine) ∧
     (InternalisedCousinGround A M0 → False) ∧
     (TheStrictLastStep00Obligation →
         (CousinManifestationLaw ↔ CousinCentersUnbounded))) ∧
    ((InternalisedSexyGround A M0 → SomeConcreteEuclideanEngine) ∧
     (InternalisedSexyGround A M0 → False) ∧
     (TheStrictLastStep00Obligation →
         (SexyManifestationLaw ↔ SexyCentersUnbounded))) :=
  ⟨cousin_no_internal_decision_without_engine,
   sexy_no_internal_decision_without_engine⟩

/-! ## Status summaries: without the decree-conjunct — no boundary fields in Polignac (🟢) -/

/-- Final epistemic status of case 4 (mirror of
    `pnp_locked_behind_engine_status`, WITHOUT the decree-conjunct — verdict §17):
    internal knowledge is impossible (theorem) / every absence witness sits
    no lower than 37 — cousin center 37 = pair (223, 227) greenly exists (M8) /
    under the boundary-hypothesis the law ⟺ unboundedness (M7 — price of the non-decreed
    field) / unboundedness would reach the programme's goal: cousin pairs are
    infinite (honest branch bridge). GREEN throughout. -/
theorem cousin_locked_behind_engine_status {A M0 : ℕ} :
    (¬ InternalKnowledgeOfCousinCause A M0) ∧
    (∀ P : ℕ, CousinAbsenceAbove P → 37 ≤ P) ∧
    (TheStrictLastStep00Obligation →
        (CousinManifestationLaw ↔ CousinCentersUnbounded)) ∧
    (CousinCentersUnbounded → CousinLowers.Infinite) :=
  ⟨cousinCause_unknowable,
   fun _P hAbs => cousinAbsenceBound_ge_37 hAbs,
   cousinManifestationLaw_iff_unbounded_of_boundary,
   cousinLowersInfinite_of_unbounded⟩

/-- Final epistemic status of case 6 (M8 threshold = 17: minus-pair
    (101, 107) at m = 17; witness is two-sided). GREEN throughout. -/
theorem sexy_locked_behind_engine_status {A M0 : ℕ} :
    (¬ InternalKnowledgeOfSexyCause A M0) ∧
    (∀ P : ℕ, SexyAbsenceAbove P → 17 ≤ P) ∧
    (TheStrictLastStep00Obligation →
        (SexyManifestationLaw ↔ SexyCentersUnbounded)) ∧
    (SexyCentersUnbounded → SexyLowers.Infinite) :=
  ⟨sexyCause_unknowable,
   fun _P hAbs => sexyAbsenceBound_ge_17 hAbs,
   sexyManifestationLaw_iff_unbounded_of_boundary,
   sexyLowersInfinite_of_unbounded⟩

/-- **Final epistemic status of Polignac-4/6 — both families at once**
    (without the decree-conjunct: the fields cousinBoundary/sexyBoundary in
    Step00FirstCause do not exist — §17, with positive sign of the heuristic).
    Cases 4 and 6 remain 🔴 open; what is shown here is only the machine-visible price:
    from within — the engine, from without — a non-decreed law of exactly hypothesis
    strength. GREEN throughout, taint does not change. -/
theorem polignac_locked_behind_engine_status {A M0 : ℕ} :
    ((¬ InternalKnowledgeOfCousinCause A M0) ∧
     (∀ P : ℕ, CousinAbsenceAbove P → 37 ≤ P) ∧
     (TheStrictLastStep00Obligation →
         (CousinManifestationLaw ↔ CousinCentersUnbounded)) ∧
     (CousinCentersUnbounded → CousinLowers.Infinite)) ∧
    ((¬ InternalKnowledgeOfSexyCause A M0) ∧
     (∀ P : ℕ, SexyAbsenceAbove P → 17 ≤ P) ∧
     (TheStrictLastStep00Obligation →
         (SexyManifestationLaw ↔ SexyCentersUnbounded)) ∧
     (SexyCentersUnbounded → SexyLowers.Infinite)) :=
  ⟨cousin_locked_behind_engine_status,
   sexy_locked_behind_engine_status⟩

/-! ## Axiom audit: the entire module is green (standard triple),
    WITHOUT step00FirstCause — repository taint does NOT change -/
#print axioms internalisedCousinGround_builds_engine
#print axioms no_internalisedCousinGround
#print axioms cousinCause_unknowable
#print axioms internalisedSexyGround_builds_engine
#print axioms no_internalisedSexyGround
#print axioms sexyCause_unknowable
#print axioms cousin_no_internal_decision_without_engine
#print axioms sexy_no_internal_decision_without_engine
#print axioms polignac_no_internal_decision_without_engine
#print axioms cousin_locked_behind_engine_status
#print axioms sexy_locked_behind_engine_status
#print axioms polignac_locked_behind_engine_status

end EuclidsPath.Polignac.Epistemic
