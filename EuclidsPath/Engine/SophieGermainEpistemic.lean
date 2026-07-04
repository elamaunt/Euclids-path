/-
  SophieGermainEpistemic — EPISTEMIC COMPLEMENT of Sophie Germain
  (another axis of the template after twin/Collatz/PNP).
  Green front: Engine/SophieGermainManifestationFront.lean (SG1–SG9 + restrict §6).
  Reference models: PNPFirstCause.lean (the substantive pair), CollatzFirstCause.lean
  (post-mortem), twin-§8 CausalClosureAxiom (`cause_unknowable`) — the quarantine itself
  is NOT imported here.

  WHAT THIS IS. "Solving Sophie Germain from the inside" is modelled by the bundle `InternalisedSGGround`:
  (ground) the manifestation law `SGManifestationLaw`, (gate) an absence witness
  for SG-pairs not above the node's own event horizon M0, (books) the ledger balanced at this
  scale. The three fields together present a perpetual engine WITNESS
  (`sgRefutation_carries_engine` — a genuine construction via
  `infiniteFlows_in_stableNoEnergy_build_engine`, not ex falso) — and perish against
  the lexRank wall `no_someConcreteEuclideanEngine`. Hence `sgCause_unknowable`:
  the internal self-grounding of the SG solution is impossible. The mirror restrict-bundle
  3 (mod 4) feeds the anti-Mersenne conjunct of the locked ledger.

  HONESTY (mandatory caveats).
  (1) This is MODEL-INTERNAL epistemics: NOT a proof and NOT a refutation
      of the Sophie Germain conjecture, and NOT Gödel — no independence or
      fixed point, only the green incompatibility of three fields against the wall
      of well-foundedness (lexRank).
  (2) The degree of substance is BELOW the PNP reference model (the STYLE matches — no field
      is the negation of another — but not the strength): in PNP the field `beyondOwnHorizon`
      is greenly inhabited (`concreteSupply_unbounded_smallScale`), whereas here NOT ONE
      of the three fields is greenly inhabited — gate is the negation of the open conjecture
      (exhibiting a witness = solving the open problem about the SG tail), books —
      decree-forces (supplied only by the boundary hypothesis), ground — the law
      of open status. The exact degree — twin-`InternalisedStep00HorizonBoundary`:
      green INCOMPATIBILITY of three mutually-unknown fields. What pays for it:
      two genuine green facts — the construction of the engine-witness
      (inside `sgRefutation_carries_engine`) and the lexRank-killer
      `no_someConcreteEuclideanEngine`. The bundle is NOT a tautology, but also NOT new
      mathematics: `no_internalisedSGGround` — a contrapositive repackaging
      of the by_contra-core of essence SG3.
  (3) The 2-field Collatz form `ground + ¬ground` would degenerate here into a bare
      `P ∧ ¬P` (neither side can be identified with a green fact) — deliberately
      NOT taken.
  (4) "Refutation = perpetual engine" for SG is LAW-CONDITIONAL — weaker than the unconditional
      Collatz tail `nonHalting_carries_perpetual_engine`.
  (5) There is NO decree-conjunct in the locked ledgers: the boundary field for SG was deliberately not
      added (verdict §17, despite the positive sign of the Hardy–Littlewood heuristic)
      — a mirror of `pnp_locked_behind_engine_status`, not the Collatz variant. The boundary enters only as HYPOTHESIS
      `TheStrictLastStep00Obligation`.
  The module is ENTIRELY green: quarantine is not imported, axiom/sorry/native_decide
  absent, the repository taint does not change.
-/

import EuclidsPath.Engine.SophieGermainManifestationFront

set_option autoImplicit false

namespace EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.SophieGermain.Epistemic

/-! ## Model: internal solution = self-grounding beyond one's own event horizon -/

/-- **Internal self-grounding of the Sophie Germain solution at scale `(A, M0)`.**
    The carrier simultaneously (a) holds the manifestation law (`ground`), (b) owns
    an absence witness for SG-pairs not above its own event horizon (`gate`), and
    (c) balances the ledger at this scale (`books`). PNP style: no field is the
    negation of another; but, UNLIKE PNP, NOT ONE field is greenly inhabited —
    gate = negation of the open conjecture, books is supplied only by the decree-force of the
    boundary, ground — the law of open status. The substance of the bundle lies in the fact
    that the contradiction below is paid for by two genuine green facts
    (engine construction + lexRank-killer), not by the form `P ∧ ¬P`. -/
structure InternalisedSGGround (A M0 : ℕ) : Prop where
  ground : SGManifestationLaw
  gate : ∃ P : ℕ, P ≤ M0 ∧ SGAbsenceAbove P
  books : ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
    SemanticExtendedFlowLedgerCollisionResolves proj

/-- "Internal knowledge of the Sophie Germain cause" = internal self-grounding of the solution. -/
abbrev InternalKnowledgeOfSGCause (A M0 : ℕ) : Prop := InternalisedSGGround A M0

/-! ## Core: self-grounding builds the engine and perishes against lexRank (🟢) -/

/-- **Self-grounding builds a perpetual engine — by a GENUINE construction**
    (not ex falso): gate and books are unpacked, `sgRefutation_carries_engine`
    presents `ConcreteEuclideanEngineWitness A M0` as an object (via the real
    collision `infiniteFlows_in_stableNoEnergy_build_engine`). GREEN. -/
theorem internalisedSGGround_builds_engine {A M0 : ℕ}
    (H : InternalisedSGGround A M0) : SomeConcreteEuclideanEngine := by
  obtain ⟨P, hPM, hAbs⟩ := H.gate
  obtain ⟨proj, hres⟩ := H.books
  exact ⟨A, M0, sgRefutation_carries_engine H.ground hAbs hPM proj hres⟩

/-- Self-grounding self-destructs: the constructed engine perishes against the green
    lexRank wall `no_someConcreteEuclideanEngine`. HONESTY: this is a
    contrapositive repackaging of the by_contra-core of essence SG3 — epistemic
    packaging, not new mathematics. GREEN. -/
theorem no_internalisedSGGround {A M0 : ℕ} :
    InternalisedSGGround A M0 → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedSGGround_builds_engine H)

/-- **"CANNOT BE KNOWN FROM THE INSIDE" — THEOREM** (mirror of twin-`cause_unknowable`,
    `collatzCause_unknowable`, `pnpCause_unknowable`): internal
    self-grounding of the Sophie Germain solution is impossible at any scale.
    NOT a statement about SG-pairs themselves — only about the cost of an internal solution. -/
theorem sgCause_unknowable {A M0 : ℕ} : ¬ InternalKnowledgeOfSGCause A M0 :=
  no_internalisedSGGround

/-- COMPANION (machine honesty, pattern of twin-`knowledge_proves_anything`):
    from internal knowledge ANYTHING follows — knowledge explodes everything. The route —
    ex falso; the load-bearing part — the impossibility itself (`no_internalisedSGGround`). -/
theorem sgKnowledge_proves_anything {A M0 : ℕ} {C : Prop} :
    InternalisedSGGround A M0 → C :=
  fun H => (no_internalisedSGGround H).elim

/-- SUBSTANTIVE DICHOTOMY (no ex falso in the statement): either the cause is
    unknowable from the inside, or SG-pairs are unbounded. The left disjunct — theorem;
    the right — an open conjecture, NOT asserted here. -/
theorem unknowable_or_sg_unbounded {A M0 : ℕ} :
    (¬ InternalKnowledgeOfSGCause A M0) ∨
      EuclidsPath.SophieGermainBranch.SophieGermainUnbounded :=
  Or.inl sgCause_unknowable

/-- "No engines ⟹ cannot be known" — genuine contraposition (not explosion),
    mirror of twin-`unknowable_of_noEngine`. -/
theorem sg_unknowable_of_noEngine
    (hNoEngine : ¬ SomeConcreteEuclideanEngine) {A M0 : ℕ} :
    ¬ InternalKnowledgeOfSGCause A M0 :=
  fun hK => hNoEngine (internalisedSGGround_builds_engine hK)

/-! ## Ledgers: solution locked behind the engine (🟢, no decree-conjunct) -/

/-- **"SOLUTION LOCKED BEHIND THE ENGINE" — trilemma** (mirror of
    `pnp_no_internal_decision_without_engine`):
    (1) REFUTE from the inside (absence witness under the law on balanced
        ledger) = exhibit a perpetual engine — genuine construction,
        CONDITIONAL on the law (honest caveat against the unconditional Collatz);
    (2) SELF-GROUND the solution from the inside — self-destructs
        (`no_internalisedSGGround`);
    (3) only an EXTERNAL boundary would resolve it: under `TheStrictLastStep00Obligation`
        the law ⟺ open SG-unboundedness (SG7) — but §17
        deliberately did NOT issue this boundary, it remains a hypothesis.
    Gödelian independence is NOT asserted and the SG-conjecture is NOT solved —
    only: both internal solutions cost a perpetual engine. -/
theorem sg_no_internal_decision_without_engine {A M0 : ℕ} :
    (SGManifestationLaw → ∀ P : ℕ, SGAbsenceAbove P → P ≤ M0 →
        ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
          SemanticExtendedFlowLedgerCollisionResolves proj →
            SomeConcreteEuclideanEngine) ∧
    (InternalisedSGGround A M0 → False) ∧
    (TheStrictLastStep00Obligation →
        (SGManifestationLaw ↔
          EuclidsPath.SophieGermainBranch.SophieGermainUnbounded)) :=
  ⟨fun hLaw _P hAbs hPM proj hres =>
      ⟨A, M0, sgRefutation_carries_engine hLaw hAbs hPM proj hres⟩,
   no_internalisedSGGround,
   sgManifestationLaw_iff_unbounded_of_boundary⟩

/-- Final epistemic status of Sophie Germain (mirror of
    `pnp_locked_behind_engine_status` — WITHOUT decree-conjunct: no boundary field for SG
    per verdict §17): every absence witness lives not below 89
    (theorem) / internal knowledge is impossible (theorem) / accepting the law under
    boundary-HYPOTHESIS would yield SG-unboundedness (conditionally) / refutation
    from the inside under the law = engine (conditional construction). GREEN throughout. -/
theorem sg_locked_behind_engine_status {A M0 : ℕ} :
    (∀ P : ℕ, SGAbsenceAbove P → 89 ≤ P) ∧
    (¬ InternalKnowledgeOfSGCause A M0) ∧
    (TheStrictLastStep00Obligation → SGManifestationLaw →
        EuclidsPath.SophieGermainBranch.SophieGermainUnbounded) ∧
    (SGManifestationLaw → ∀ P : ℕ, SGAbsenceAbove P → P ≤ M0 →
        ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
          SemanticExtendedFlowLedgerCollisionResolves proj →
            SomeConcreteEuclideanEngine) :=
  ⟨fun _P hAbs => sgAbsenceBound_ge_89 hAbs,
   sgCause_unknowable,
   fun hB hLaw => (sgManifestationLaw_iff_unbounded_of_boundary hB).mp hLaw,
   fun hLaw _P hAbs hPM proj hres =>
     ⟨A, M0, sgRefutation_carries_engine hLaw hAbs hPM proj hres⟩⟩

/-! ## Restrict-mirror 3 (mod 4): same epistemics, anti-Mersenne conjunct -/

/-- **Internal self-grounding of the restrict-solution 3 (mod 4)** — the same structure,
    but over the subfamily of SG-primes `p ≡ 3 (mod 4)` (the very one that the
    branch's pearl turns into killers of Mersenne primality). The gate is weaker than the full-family gate
    (see §6 front expansion) — implications between bundles are NOT asserted here. -/
structure InternalisedSGThreeMod4Ground (A M0 : ℕ) : Prop where
  ground : SGThreeMod4ManifestationLaw
  gate : ∃ P : ℕ, P ≤ M0 ∧ SGThreeMod4AbsenceAbove P
  books : ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
    SemanticExtendedFlowLedgerCollisionResolves proj

/-- "Internal knowledge of the restrict-cause 3 (mod 4)". -/
abbrev InternalKnowledgeOfSGThreeMod4Cause (A M0 : ℕ) : Prop :=
  InternalisedSGThreeMod4Ground A M0

/-- Restrict-self-grounding builds the engine — by a genuine construction
    (`sgThreeMod4Refutation_carries_engine`). GREEN. -/
theorem internalisedSGThreeMod4Ground_builds_engine {A M0 : ℕ}
    (H : InternalisedSGThreeMod4Ground A M0) : SomeConcreteEuclideanEngine := by
  obtain ⟨P, hPM, hAbs⟩ := H.gate
  obtain ⟨proj, hres⟩ := H.books
  exact ⟨A, M0, sgThreeMod4Refutation_carries_engine H.ground hAbs hPM proj hres⟩

/-- Restrict-self-grounding self-destructs against the same lexRank wall. -/
theorem no_internalisedSGThreeMod4Ground {A M0 : ℕ} :
    InternalisedSGThreeMod4Ground A M0 → False :=
  fun H =>
    no_someConcreteEuclideanEngine (internalisedSGThreeMod4Ground_builds_engine H)

/-- "Cannot be known from the inside" for the restrict-family 3 (mod 4). -/
theorem sgThreeMod4Cause_unknowable {A M0 : ℕ} :
    ¬ InternalKnowledgeOfSGThreeMod4Cause A M0 :=
  no_internalisedSGThreeMod4Ground

/-- Trilemma of the restrict-front: (1) refute from the inside under the restrict-law =
    engine (conditional construction); (2) self-ground = self-destruction;
    (3) only an external boundary-hypothesis would resolve it (essence of the restrict-front with
    green `no_someConcreteEuclideanEngine` in place of hNoEngine). -/
theorem sgThreeMod4_no_internal_decision_without_engine {A M0 : ℕ} :
    (SGThreeMod4ManifestationLaw →
        ∀ P : ℕ, SGThreeMod4AbsenceAbove P → P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              SomeConcreteEuclideanEngine) ∧
    (InternalisedSGThreeMod4Ground A M0 → False) ∧
    (TheStrictLastStep00Obligation → SGThreeMod4ManifestationLaw →
        EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded) :=
  ⟨fun hLaw _P hAbs hPM proj hres =>
      ⟨A, M0, sgThreeMod4Refutation_carries_engine hLaw hAbs hPM proj hres⟩,
   no_internalisedSGThreeMod4Ground,
   fun hB hLaw => sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hB hLaw⟩

/-- Final restrict-status WITH THE ANTI-MERSENNE CONJUNCT: every restrict-witness
    lives not below 11 (theorem) / internal knowledge is impossible (theorem) /
    the restrict-law under the boundary-hypothesis would yield unboundedness of the class
    3 (mod 4) (conditionally) / and at the same time — unboundedness of primes `p` with COMPOSITE
    `M_p` (conditionally; the Euler–Lagrange pearl feeds the composite side of that
    quantity whose prime side the Mersenne front refused to assert).
    HONESTY: the unconditional infinitude of composite `M_p` (for prime `p`)
    is UNKNOWN in the literature — open, just like the infinitude of Mersenne primes;
    the SG-route 3 (mod 4) is the standard CONDITIONAL path to it, here further
    conditioned on the boundary-hypothesis. GREEN throughout. -/
theorem sgThreeMod4_locked_behind_engine_status {A M0 : ℕ} :
    (∀ P : ℕ, SGThreeMod4AbsenceAbove P → 11 ≤ P) ∧
    (¬ InternalKnowledgeOfSGThreeMod4Cause A M0) ∧
    (TheStrictLastStep00Obligation → SGThreeMod4ManifestationLaw →
        EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded) ∧
    (TheStrictLastStep00Obligation → SGThreeMod4ManifestationLaw →
        ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ¬ (mersenne p).Prime) :=
  ⟨fun _P hAbs => sgThreeMod4AbsenceBound_ge_11 hAbs,
   sgThreeMod4Cause_unknowable,
   fun hB hLaw => sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hB hLaw,
   fun hB hLaw => mersenneComposites_unbounded_of_noEngine_boundary_and_sgManifestation
      no_someConcreteEuclideanEngine hB hLaw⟩

/-! ## Axiom audit: module is ENTIRELY green (standard triple at most),
    quarantine not imported, repository taint does NOT change -/
#print axioms InternalisedSGGround
#print axioms InternalKnowledgeOfSGCause
#print axioms internalisedSGGround_builds_engine
#print axioms no_internalisedSGGround
#print axioms sgCause_unknowable
#print axioms sgKnowledge_proves_anything
#print axioms unknowable_or_sg_unbounded
#print axioms sg_unknowable_of_noEngine
#print axioms sg_no_internal_decision_without_engine
#print axioms sg_locked_behind_engine_status
#print axioms InternalisedSGThreeMod4Ground
#print axioms InternalKnowledgeOfSGThreeMod4Cause
#print axioms internalisedSGThreeMod4Ground_builds_engine
#print axioms no_internalisedSGThreeMod4Ground
#print axioms sgThreeMod4Cause_unknowable
#print axioms sgThreeMod4_no_internal_decision_without_engine
#print axioms sgThreeMod4_locked_behind_engine_status

end EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.SophieGermain.Epistemic
