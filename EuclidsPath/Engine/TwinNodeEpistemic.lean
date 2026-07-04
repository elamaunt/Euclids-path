/-
  TwinNodeEpistemic — EPISTEMIC COMPLEMENT OF THE MAIN NODE (twins),
  mirror of CollatzFirstCause / PNPFirstCause. Green machine: Engine/ConcreteStep00Graph.lean.

  WHAT THIS IS. The final twin node — TheLastStep00Obligation: "there exists a scale A and
  ledger projections onto all bases M0 that resolve every same-key genealogy collision".
  "Solving the node from within on its own horizon" = exhibiting an A-slice of the node with
  the system horizon A ≤ 4 visibly green. This self-destructs NOT by substituting P ∧ ¬P,
  but by a genuine pigeonhole: the 5-adic chain yields an infinite injective admissible supply
  (`fiveAdicChainFlow`, injectivity via `fiveAdicChain_strictMono`), and
  `Finite.exists_ne_map_eq_of_infinite` extracts a same-key pair from any finite key
  (`no_projection_resolves_at_smallScale`) — exactly the same currency as
  `no_fullPayment_of_unboundedSupply` in P/NP and the perpetual-engine wall in Collatz.

  HONESTY. This is model-internal epistemic unknowability, NOT a proof
  and NOT a refutation of the twin-prime conjecture, and NOT Gödel (pigeonhole self-destruction,
  not an incompleteness theorem). Substantiveness IS SPLIT BY SCALE: at A ≤ 4 the bundle
  `ground` + `beyondOwnHorizon` is substantive (contradiction — a theorem paid for by the
  pigeonhole); at A ≥ 5 the structure `InternalisedTwinGround` is already empty on the horizon
  field (A ≤ 4), i.e. there the bundle IS FORMAL — and so it should be: no green contradiction
  exists at A ≥ 5, nor can it, otherwise the node would have been solved. The unknowability of
  the twin node is machine-visible precisely as this split. Unlike Collatz, "refutation ⟹ engine"
  for twins is NOT unconditional: the engine is built only in a stable universe
  (`NoEnergyStableUniverse`) — ledger stability is exactly what is open at A ≥ 5
  and is supplied by decree in the quarantine layer.

  The file IS ENTIRELY GREEN: it does not import Engine/CausalClosureAxiom (quarantine),
  does not touch the axiom step00FirstCause or the taint list of 52 declarations.
-/

import EuclidsPath.Engine.ConcreteStep00Graph

set_option autoImplicit false

namespace EuclidsPath.ConcreteStep00Graph.Epistemic

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-! ## (a) Refutation of twins carries an unconditional infinite supply (🟢) -/

/-- **"REFUTATION EXHIBITS SUPPLY" (green, unconditional).** If the set of
    lower twins is finite, there exists a twin-bound `M0`, and at EVERY scale `A`
    an infinite admissible supply of genealogies is constructed from it — analogous to
    `UnboundedCertificateSupply` in P/NP. Genuine construction via
    cofactor-normalizer (`twinBoundForcesInfiniteExtendedGeneratedFlows_closed`),
    not a placeholder. HONESTY: the supply alone does NOT yet build the engine —
    see the next theorem and its price. -/
theorem twinBound_carries_unbounded_supply
    (hfin : ¬ TwinLowers.Infinite) :
    ∃ M0 : ℕ, ∀ A : ℕ,
      ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
        InfiniteExtendedGeneratedFlowFamily A M0 𝓕 := by
  obtain ⟨M0, hBound⟩ := exists_twinBoundAbove_of_not_twinLowersInfinite hfin
  exact ⟨M0, fun A =>
    twinBoundForcesInfiniteExtendedGeneratedFlows_closed hBound⟩

/-! ## (b) Refutation in a stable universe builds the engine (🟢, conditional) -/

/-- **"REFUTATION IN A STABLE UNIVERSE BUILDS THE ENGINE" (green).**
    Finiteness of twins + stable no-energy ledger at every slice ⟹
    a concrete Euclidean engine (`SomeConcreteEuclideanEngine`), which is forbidden
    (`no_someConcreteEuclideanEngine`, lexRank strictly decreases).
    HONESTY (three caveats):
    (1) this is NOT the unconditional "refutation = engine" as in Collatz
        (`nonHalting_carries_perpetual_engine`): the hypothesis `NoEnergyStableUniverse`
        is required, and ledger stability is exactly what is open at A ≥ 5 and
        is supplied by decree in the quarantine layer;
    (2) this chain is run verbatim inside `twins_infinite_of_noEngine_and_boundary`
        (CausalClosureAxiom.lean, §8) — here it is an EXPORT OF THE GREEN NAME from the
        quarantine file into a clean module, not new content;
    (3) the half "supply + stability ⟹ engine" is a thin wrapper over the existing
        `infiniteFlows_in_stableNoEnergy_build_engine`. -/
theorem twinRefutation_in_stableUniverse_builds_engine
    (hfin : ¬ TwinLowers.Infinite)
    (hstable : ∀ A M0 : ℕ,
      ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        NoEnergyStableUniverse proj) :
    SomeConcreteEuclideanEngine := by
  obtain ⟨M0, hBound⟩ := exists_twinBoundAbove_of_not_twinLowersInfinite hfin
  obtain ⟨𝓕, h𝓕⟩ :=
    twinBoundForcesInfiniteExtendedGeneratedFlows_closed
      (A := 0) (M0 := M0) hBound
  obtain ⟨proj, hstab⟩ := hstable 0 M0
  obtain ⟨_, _, _, W⟩ := infiniteFlows_in_stableNoEnergy_build_engine hstab h𝓕
  exact ⟨0, M0, W⟩

/-! ## (c) Node confinement in the exact strict form of the decree (🟢) -/

/-- **NODE CONFINEMENT, STRICT FORM.** `TheStrictLastStep00Obligation` — exactly the form
    asserted by `causalBoundary` of the decree (in the quarantine layer; the decree itself
    is NOT used here) — is machine-forced into `A ≥ 5`: the A ≤ 4 slice is refuted by the
    5-adic chain. Trivial composition of the iff-bridge
    `strictLastStep00Obligation_iff_lastStep00Obligation` and the already-proved confinement
    `lastStep00Obligation_forces_scale_ge_five`; sharpens the stretch
    `quarantine_inconsistent_if_node_refuted`. -/
theorem strictLastStep00Obligation_forces_scale_ge_five
    (H : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧
      ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
        ∀ M0 : ℕ, StrictSemanticExtendedFlowLedgerCollisionResolves (projOf M0) := by
  obtain ⟨A, hA5, projOf, hRes⟩ :=
    lastStep00Obligation_forces_scale_ge_five
      (strictLastStep00Obligation_iff_lastStep00Obligation.mp H)
  exact ⟨A, hA5, projOf,
    fun M0 => (strictResolves_iff_resolves (projOf M0)).mpr (hRes M0)⟩

/-! ## (d) Model: internal resolution of the node = self-grounding beyond the horizon -/

/-- **Internal self-grounding of the twin node on its own horizon.** Carries
    (a) `ground` — the A-slice of the final node: projections onto all bases `M0` resolve
    every collision (a slice of `TheLastStep00Obligation` at a fixed scale), and
    (b) `beyondOwnHorizon` — the scale itself lies within the system's visibly-green horizon
    (A ≤ 4, where the 5-adic chain operates).
    SUBSTANTIVENESS: `ground` and `beyondOwnHorizon` are not `P` and `¬P`; the contradiction
    is supplied by the pigeonhole `no_projection_resolves_at_smallScale`
    (`Finite.exists_ne_map_eq_of_infinite` on the injective family `fiveAdicChainFlow`).
    HONESTY: at A ≥ 5 the structure is already empty on the `beyondOwnHorizon` field —
    the bundle there is formal, and rightly so: no green contradiction exists at A ≥ 5
    (otherwise the node would have been solved); unknowability is visible as the split by scale. -/
structure InternalisedTwinGround (A : ℕ) : Prop where
  ground : ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0)
  beyondOwnHorizon : A ≤ 4

/-- "Internal knowledge of the twin cause" = internal self-grounding of the node. -/
abbrev InternalKnowledgeOfTwinCause (A : ℕ) : Prop := InternalisedTwinGround A

/-- Self-grounding self-destructs — paid for by the pigeonhole
    `no_projection_resolves_at_smallScale` (via
    `smallScale_branch_of_lastStep00Obligation_refuted`), NOT by tautology. GREEN. -/
theorem no_internalisedTwinGround {A : ℕ} :
    InternalisedTwinGround A → False :=
  fun H =>
    smallScale_branch_of_lastStep00Obligation_refuted H.beyondOwnHorizon H.ground

/-- **"UNKNOWABLE FROM WITHIN" — THEOREM** (mirror of `collatzCause_unknowable`,
    `pnpCause_unknowable`): internal resolution of the twin node on its own horizon
    is impossible. GREEN, with no hypotheses whatsoever. -/
theorem twinNode_unknowable {A : ℕ} : ¬ InternalKnowledgeOfTwinCause A :=
  no_internalisedTwinGround

/-! ## Summary: solution is locked behind the engine (🟢) -/

/-- **"SOLUTION LOCKED BEHIND THE ENGINE" — 3-WAY TRILEMMA (green; mirror of
    `collatz_no_internal_decision_without_engine`, `pnp_no_internal_decision_without_engine`):**
    (1) REFUTE twins against a stable ledger = build the engine
        (twin-bound ⟹ infinite supply ⟹ same-key collision ⟹ `LegalCycle`,
        forbidden by lexRank); the price is honestly visible: `NoEnergyStableUniverse` is needed;
    (2) SELF-GROUND the node on its own horizon — self-destructs
        (`no_internalisedTwinGround`, pigeonhole);
    (3) the only path — EXTERNAL BOUNDARY: the strict node, honestly accepted from outside,
        implies infinitely many twins (`twinLowersInfinite_of_strictLastStep00Obligation`,
        green conditional arrow; the strict node is NOT asserted here).
    Neither Gödelian independence nor a solution to the twin-prime conjecture is asserted —
    only: both internal resolutions cost a perpetual engine. -/
theorem twin_no_internal_decision_without_engine (A : ℕ) :
    (∀ M0 : ℕ, TwinBoundAbove M0 →
      ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
        NoEnergyStableUniverse proj → ConcreteEuclideanEngineWitness A M0) ∧
    (InternalisedTwinGround A → False) ∧
    (TheStrictLastStep00Obligation → TwinLowers.Infinite) := by
  refine ⟨?_, no_internalisedTwinGround,
    twinLowersInfinite_of_strictLastStep00Obligation⟩
  intro M0 hBound proj hstab
  obtain ⟨𝓕, h𝓕⟩ :=
    twinBoundForcesInfiniteExtendedGeneratedFlows_closed hBound
  obtain ⟨_, _, _, W⟩ := infiniteFlows_in_stableNoEnergy_build_engine hstab h𝓕
  exact W

/-- Final epistemic status of the twin node (green; mirror of
    `pnp_locked_behind_engine_status` — WITHOUT the decree conjunct: the yellow version with
    `step00FirstCause` would add newly tainted declarations and is excluded here):
    (1) the supply at A ≤ 4 exists unconditionally (5-adic chain, injectivity);
    (2) the node is unknowable from within (theorem);
    (3) the node is forced into A ≥ 5 (`lastStep00Obligation_forces_scale_ge_five`);
    (4) refutation of twins in a stable universe builds the engine;
    (5) the engine is forbidden (`no_someConcreteEuclideanEngine`, lexRank).
    Together (4)+(5) give conditional infinitude of twins in a stable universe —
    green content already recorded as `twins_infinite_of_noEngine_and_boundary`
    in the quarantine file; here it lives without quarantine. -/
theorem twin_locked_behind_engine_status {A : ℕ} (hA : A ≤ 4) :
    InfiniteExtendedGeneratedFlowFamily A 1 (Set.range (fiveAdicChainFlow hA)) ∧
    (¬ InternalKnowledgeOfTwinCause A) ∧
    (TheLastStep00Obligation →
      ∃ B : ℕ, 5 ≤ B ∧
        ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection B M0,
          ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0)) ∧
    (¬ TwinLowers.Infinite →
      (∀ B M0 : ℕ,
        ∃ proj : SemanticExtendedFlowLedgerProjection B M0,
          NoEnergyStableUniverse proj) →
      SomeConcreteEuclideanEngine) ∧
    (¬ SomeConcreteEuclideanEngine) :=
  ⟨⟨Set.infinite_range_of_injective (fiveAdicChainFlow_injective hA),
    fun F _ => extendedFlow_admissible F⟩,
   twinNode_unknowable,
   lastStep00Obligation_forces_scale_ge_five,
   twinRefutation_in_stableUniverse_builds_engine,
   no_someConcreteEuclideanEngine⟩

/-! ## Axiom audit: the entire module is green (standard triple), repo taint does NOT change -/
#print axioms twinBound_carries_unbounded_supply
#print axioms twinRefutation_in_stableUniverse_builds_engine
#print axioms strictLastStep00Obligation_forces_scale_ge_five
#print axioms no_internalisedTwinGround
#print axioms twinNode_unknowable
#print axioms twin_no_internal_decision_without_engine
#print axioms twin_locked_behind_engine_status

end EuclidsPath.ConcreteStep00Graph.Epistemic
