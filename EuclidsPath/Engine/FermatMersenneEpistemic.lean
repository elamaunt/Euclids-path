/-
  FermatMersenneEpistemic — EPISTEMIC COMPLEMENT of the Fermat and Mersenne branches
  (mirror of CollatzFirstCause/PNPFirstCause, but for TWO fronts at once).
  Green machines: Engine/FermatManifestationFront.lean and
  Engine/MersenneManifestationFront.lean.

  WHAT THIS IS. Both branches have their manifestation boundaries INTENTIONALLY NOT TAKEN —
  verdict §16/§17: the heuristic sign is inverted. For Fermat it is the hardest case in the
  programme (only F₀–F₄ are known to be prime, while F₅–F₃₂ are PROVABLY composite —
  the input `FermatTwinCentersUnbounded` is most likely false); for Mersenne the sum over
  twin pairs converges, only p = 3, 5 are known, and 5 ∣ 2^p − 3 when p ≡ 3 (mod 4).
  The manifestation laws live as DEFINITIONS (`FermatManifestationLaw`,
  `MersenneManifestationLaw`), not decrees; M7-audits of the fronts show that
  a decree would cost exactly an open hypothesis. This module adds an epistemic
  explanation to the refusal of the decree: there are NO INTERNAL paths either. To
  self-justify the law on top of one's own refutation witness = to assemble a perpetual engine
  (`fermatRefutation_carries_engine` / `mersenneRefutation_carries_engine`
  build `ConcreteEuclideanEngineWitness` as an object) — and to perish against
  `lexRank` (`no_someConcreteEuclideanEngine`); the only engine-free
  path is the EXTERNAL boundary `TheStrictLastStep00Obligation`, which these branches
  are intentionally not given. Both doors — the decree door and the internal door — are closed,
  and both are closed GREEN.

  HONESTY (mandatory caveats).
  (1) This is MODEL-INTERNAL epistemic unknowability (like
      `collatzCause_unknowable` and `pnpCause_unknowable`), NOT a resolution of the question
      of infinitude of Fermat- and Mersenne-twins and NOT Gödel: no incompleteness theorem —
      only pigeonhole self-destruction against the wall of well-foundedness.
  (2) The bundle does NOT degenerate into bare `P ∧ ¬P`: `beyondOwnHorizon` is NOT the negation
      of `ground`, but an independent package "absence witness + balanced ledger",
      and False is paid for by a genuine engine construction (the law converts
      absence into a supply of flows, the pigeonhole on the finite key collides two
      flows, from the collision a engine-WITNESS is assembled, `lexRank` kills it).
      The degenerate form `beyondOwnHorizon := ¬FermatManifestationLaw` MUST NOT be taken
      — it would be a tautology without payment (the Collatz form, honestly
      labelled as such in CollatzFirstCause).
  (3) STRENGTH CAVEAT: the bundle is WEAKER than the P/NP benchmark — there `beyondOwnHorizon`
      (`UnboundedCertificateSupply`) is greenly INSTANTIABLE at A ≤ 4
      (`concreteSupply_unbounded_smallScale`); here NOT A SINGLE field is greenly
      realizable: absence witness = solution of the open tail problem,
      balanced ledger = content of the intentionally not-taken decree. But
      STRONGER than the Collatz tautological pair ground/¬ground. Hybrid:
      the contradiction construction is genuine; inhabitability of the sides is open.

  The module is ENTIRELY GREEN: the quarantine (CausalClosureAxiom) is NOT imported,
  no axiom/sorry/native_decide, the repository taint does not change.
-/

import EuclidsPath.Engine.FermatManifestationFront
import EuclidsPath.Engine.MersenneManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace Epistemic

/-! ## Model: internal self-justification of the Fermat branch -/

/-- **Internal self-justification of the Fermat branch.** Carries the manifestation law
    (`ground` = `FermatManifestationLaw` — exact content of the intentionally NOT
    taken boundary, §16/§17) AND the package "refutation witness inside a world with
    a balanced ledger" (`beyondOwnHorizon`): absence threshold `P`, scale
    `M0 ≥ P`, and a resolving projection. The form is substantive — `beyondOwnHorizon`
    is NOT `¬ground` (the degenerate form `beyondOwnHorizon := ¬Law` must not be taken
    — bare `P ∧ ¬P`); the contradiction below is paid for by the genuine engine
    construction `fermatRefutation_carries_engine`. HONEST CAVEAT: not a single
    field is greenly instantiable (witness = solution of the open tail problem of
    Fermat twins, resolves = content of the not-taken decree) — weaker than the
    P/NP benchmark (`concreteSupply_unbounded_smallScale` at A ≤ 4), stronger than
    the Collatz tautological form. -/
structure InternalisedFermatGround : Prop where
  ground : FermatManifestationLaw
  beyondOwnHorizon :
    ∃ (P A M0 : ℕ), FermatTwinAbsenceAbove P ∧ P ≤ M0 ∧
      ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj

/-- "Internal knowledge of the Fermat-branch cause" = internal self-justification. -/
abbrev InternalKnowledgeOfFermatCause : Prop := InternalisedFermatGround

/-- **Fermat self-justification BUILDS an engine — as an object, NOT ex falso:**
    the law (`ground`) converts the absence witness into an unpayable supply of
    flows at the permitted scale, the pigeonhole on the finite key collides two
    flows, from the collision `ConcreteEuclideanEngineWitness` is assembled (all
    the mechanics are inside `fermatRefutation_carries_engine`). The engine is
    exhibited BEFORE any killing — this is the load-bearing construction of the bundle. -/
theorem internalisedFermatGround_builds_engine :
    InternalisedFermatGround → SomeConcreteEuclideanEngine := by
  intro H
  obtain ⟨P, A, M0, hAbs, hM, proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, fermatRefutation_carries_engine H.ground hAbs hM proj hres⟩

/-- Self-justification destroys itself against the perpetual-engine wall: the built
    witness is killed by `lexRank` (`no_someConcreteEuclideanEngine`). GREEN. -/
theorem no_internalisedFermatGround : InternalisedFermatGround → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedFermatGround_builds_engine H)

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM of the Fermat branch** (mirror of
    `collatzCause_unknowable` / `pnpCause_unknowable`): internal self-justification
    of the Fermat manifestation law is impossible. This is NOT a statement
    about the Fermat twins themselves — only about the internal path to the boundary
    the branch is intentionally not given (§16/§17). -/
theorem fermatCause_unknowable : ¬ InternalKnowledgeOfFermatCause :=
  no_internalisedFermatGround

/-- SUBSTANTIVE DICHOTOMY (no ex falso in the statement): either the cause is
    unknowable from within, or under the law the ledger NEVER balances above the
    absence witness (right-hand side — M6-freeze
    `fermatManifestationLaw_iff_no_resolution_above_absence`).
    The left disjunct is a theorem. -/
theorem unknowable_or_fermat_books_never_resolve :
    (¬ InternalKnowledgeOfFermatCause) ∨
      (FermatManifestationLaw →
        ∀ P : ℕ, FermatTwinAbsenceAbove P →
          ∀ (A M0 : ℕ), P ≤ M0 →
            ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
              ¬ SemanticExtendedFlowLedgerCollisionResolves proj) :=
  Or.inl fermatCause_unknowable

/-! ## Model: internal self-justification of the Mersenne branch (mirror) -/

/-- **Internal self-justification of the Mersenne branch** — exact mirror of
    `InternalisedFermatGround` with `MersenneManifestationLaw` (the boundary is also
    intentionally NOT taken — §16: Σ over twin pairs converges, 5 ∣ 2^p − 3 when
    p ≡ 3 (mod 4)). All caveats of the Fermat version transfer verbatim: fields
    are not greenly instantiable, `beyondOwnHorizon ≠ ¬ground`, payment —
    engine construction `mersenneRefutation_carries_engine`. -/
structure InternalisedMersenneGround : Prop where
  ground : MersenneManifestationLaw
  beyondOwnHorizon :
    ∃ (P A M0 : ℕ), MersenneTwinAbsenceAbove P ∧ P ≤ M0 ∧
      ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj

/-- "Internal knowledge of the Mersenne-branch cause" = internal self-justification. -/
abbrev InternalKnowledgeOfMersenneCause : Prop := InternalisedMersenneGround

/-- **Mersenne self-justification BUILDS an engine — as an object, NOT ex falso**
    (mirror of `internalisedFermatGround_builds_engine`, mechanics inside
    `mersenneRefutation_carries_engine`). -/
theorem internalisedMersenneGround_builds_engine :
    InternalisedMersenneGround → SomeConcreteEuclideanEngine := by
  intro H
  obtain ⟨P, A, M0, hAbs, hM, proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, mersenneRefutation_carries_engine H.ground hAbs hM proj hres⟩

/-- Self-justification destroys itself against the same wall (`lexRank`). GREEN. -/
theorem no_internalisedMersenneGround : InternalisedMersenneGround → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedMersenneGround_builds_engine H)

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM of the Mersenne branch** (mirror of
    `fermatCause_unknowable`): internal self-justification of the Mersenne manifestation
    law is impossible. NOT a resolution of the question about Mersenne twins. -/
theorem mersenneCause_unknowable : ¬ InternalKnowledgeOfMersenneCause :=
  no_internalisedMersenneGround

/-- SUBSTANTIVE DICHOTOMY for Mersenne (mirror of the Fermat version; right-hand side —
    M6-freeze `mersenneManifestationLaw_iff_no_resolution_above_absence`).
    The left disjunct is a theorem. -/
theorem unknowable_or_mersenne_books_never_resolve :
    (¬ InternalKnowledgeOfMersenneCause) ∨
      (MersenneManifestationLaw →
        ∀ P : ℕ, MersenneTwinAbsenceAbove P →
          ∀ (A M0 : ℕ), P ≤ M0 →
            ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
              ¬ SemanticExtendedFlowLedgerCollisionResolves proj) :=
  Or.inl mersenneCause_unknowable

/-! ## Summary: both branches are locked behind the engine (🟢) -/

/-- **"SOLUTION LOCKED BEHIND THE ENGINE" — both branches at once** (mirror of
    `pnp_no_internal_decision_without_engine` /
    `collatz_no_internal_decision_without_engine`):
    (1) TO REFUTE under the law with a balanced ledger = to exhibit an engine as
        an object (`fermatRefutation_carries_engine` /
        `mersenneRefutation_carries_engine` — genuine consumption of hypotheses);
    (2) TO SELF-JUSTIFY from within — destroys itself
        (`no_internalisedFermatGround` / `no_internalisedMersenneGround`);
    (3) the only engine-free path is the EXTERNAL boundary
        `TheStrictLastStep00Obligation`: under it the law yields unboundedness
        (ESSENCE M3 of both fronts with the green wall
        `no_someConcreteEuclideanEngine`) — but precisely this boundary is
        intentionally NOT given to the branches (§16/§17, heuristic sign).
    Gödelian independence is NOT asserted and the hypotheses themselves are NOT resolved —
    only: both internal paths cost a perpetual engine, and the decree door is
    intentionally left unopened. -/
theorem fermatMersenne_no_internal_decision_without_engine :
    ((FermatManifestationLaw → ∀ P : ℕ, FermatTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) ∧
     (MersenneManifestationLaw → ∀ P : ℕ, MersenneTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0)) ∧
    ((InternalisedFermatGround → False) ∧
     (InternalisedMersenneGround → False)) ∧
    ((TheStrictLastStep00Obligation → FermatManifestationLaw →
        EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) ∧
     (TheStrictLastStep00Obligation → MersenneManifestationLaw →
        EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded)) :=
  ⟨⟨fun hLaw _P hAbs _A _M0 hM proj hres =>
        fermatRefutation_carries_engine hLaw hAbs hM proj hres,
    fun hLaw _P hAbs _A _M0 hM proj hres =>
        mersenneRefutation_carries_engine hLaw hAbs hM proj hres⟩,
   ⟨no_internalisedFermatGround, no_internalisedMersenneGround⟩,
   ⟨fun hB hLaw => fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
        no_someConcreteEuclideanEngine hB hLaw,
    fun hB hLaw => mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
        no_someConcreteEuclideanEngine hB hLaw⟩⟩

/-- Final epistemic status of both branches (mirror of
    `pnp_locked_behind_engine_status` — WITHOUT the decree conjunct: the fields
    fermatBoundary/mersenneBoundary are absent from the first cause, and this is the intentional
    decision of §16/§17 by heuristic sign):
    (1) localization of witness domains — every absence boundary ≥ 65537
        (Fermat, pair F₄ = 65537) and ≥ 29 (Mersenne, pair p = 5);
    (2) internal knowledge is impossible — both theorems;
    (3) M7-price audit: under the external boundary law ⟺ open unboundedness —
        a decree would cost exactly an open hypothesis (hence not taken);
    (4) wall: no perpetual engines at any scale
        (`no_someConcreteEuclideanEngine`, lexRank).
    ENTIRELY GREEN; the epistemics explains why, with the boundaries not taken, there are
    also no internal paths: both doors lead to the same wall. -/
theorem fermatMersenne_locked_behind_engine_status :
    ((∀ P : ℕ, FermatTwinAbsenceAbove P → 65537 ≤ P) ∧
     (∀ P : ℕ, MersenneTwinAbsenceAbove P → 29 ≤ P)) ∧
    ((¬ InternalKnowledgeOfFermatCause) ∧
     (¬ InternalKnowledgeOfMersenneCause)) ∧
    (TheStrictLastStep00Obligation →
      ((FermatManifestationLaw ↔
          EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) ∧
       (MersenneManifestationLaw ↔
          EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded))) ∧
    ¬ SomeConcreteEuclideanEngine :=
  ⟨⟨fun _ hAbs => fermatAbsenceBound_ge_65537 hAbs,
    fun _ hAbs => mersenneAbsenceBound_ge_29 hAbs⟩,
   ⟨fermatCause_unknowable, mersenneCause_unknowable⟩,
   fun hB => ⟨fermatManifestationLaw_iff_unbounded_of_boundary hB,
              mersenneManifestationLaw_iff_unbounded_of_boundary hB⟩,
   no_someConcreteEuclideanEngine⟩

/-! ## Axiom audit: the entire module is green (standard triple), taint does not change -/
#print axioms InternalisedFermatGround
#print axioms InternalKnowledgeOfFermatCause
#print axioms internalisedFermatGround_builds_engine
#print axioms no_internalisedFermatGround
#print axioms fermatCause_unknowable
#print axioms unknowable_or_fermat_books_never_resolve
#print axioms InternalisedMersenneGround
#print axioms InternalKnowledgeOfMersenneCause
#print axioms internalisedMersenneGround_builds_engine
#print axioms no_internalisedMersenneGround
#print axioms mersenneCause_unknowable
#print axioms unknowable_or_mersenne_books_never_resolve
#print axioms fermatMersenne_no_internal_decision_without_engine
#print axioms fermatMersenne_locked_behind_engine_status

end Epistemic
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
