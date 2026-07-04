/-
  RiemannLawEpistemic — the EPISTEMIC COMPLEMENT of the Riemann manifestation law
  (mirror of CollatzFirstCause/PNPFirstCause under the Tier-1 programme).
  Green machine: Engine/RiemannManifestationFront.lean (chain L1–L9).

  WHAT THIS IS. "Solving Riemann from inside" = internally self-grounding the
  manifestation law (`RiemannManifestationLaw`, the content of the decree field
  `riemannBoundary` — NOT accepted here): carrying at once the law itself and a
  witness that it was derived from beyond one's own horizon. The self-grounding
  self-destructs (`riemannCause_unknowable`), and the only internal trace of a
  deviation is a perpetual engine: a deviation supply at a resolved scale BUILDS
  an engine-witness (`deviation_carries_engine_at_resolved_scale`), which is
  killed by lexRank. Only an external decree decides: the law under the boundary
  gives RH — here the boundary appears as a HYPOTHESIS
  (`h : TheStrictLastStep00Obligation`), NOT an axiom; the module does not import
  the quarantine.

  HONESTY (mandatory caveats):
    * This is model-internal epistemics, NOT a solution of the Riemann hypothesis
      and NOT Gödel (no independence/fixed point — only a pigeonhole wall).
    * The bundle `InternalisedRiemannGround` is FORMAL — as with Collatz after
      the decree fell: `beyondOwnHorizon = ¬ground` (the form P ∧ ¬P). What pays
      for it: the genuine green fact "a supply in a stable universe builds an
      engine" (`infiniteFlows_in_stableNoEnergy_build_engine`, consumed in
      `no_deviationFlowSupply_at_resolved_scale`) — it is consumed NOT ex falso
      in the separate theorem
      `deviation_carries_engine_at_resolved_scale`.
    * No field of the bundle is green-populatable: the zero-witness = ¬RH,
      the resolving ledger — an open twin node (at A ≤ 4 resolution is
      refuted by `no_projection_resolves_at_smallScale`); by L6
      (`manifestationLaw_iff_no_resolution_above_zero`) `beyondOwnHorizon`
      under a given `ground` is equivalent to the negation of its consequence.
      This is BELOW the P/NP benchmark (there `beyondOwnHorizon` is green-
      instantiated at A ≤ 4) and exactly the Collatz level.
    * Unlike the object-unconditional `nonHalting_carries_perpetual_engine` of
      Collatz, the Riemann engine is GATED by the resolving scale: a deviation
      presents an engine only where the books are reconciled — and reconciliation
      is exactly the open twin node/boundary.
  The module is ENTIRELY GREEN: no axiom/sorry, no import of the quarantine
  (CausalClosureAxiom); the repository taint (47 after removing the fourth
  boundary, 1936826) does NOT change.
-/

import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.RiemannLiouville

set_option autoImplicit false

namespace EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic

/-! ## Model: internal solution = self-grounding beyond one's own horizon -/

/-- **Internal self-grounding of the Riemann manifestation law**: carries the
    law itself (`ground`) AND a witness that it was derived from beyond one's own
    horizon (`beyondOwnHorizon`). SAME FORM AS COLLATZ (`InternalisedCollatzGround`):
    `beyondOwnHorizon = ¬ground` — a tautological P ∧ ¬P pair, and this is said
    outright. The substance is paid for separately: the genuine green fact "a
    deviation supply in a stable universe builds an engine"
    (`infiniteFlows_in_stableNoEnergy_build_engine` inside
    `no_deviationFlowSupply_at_resolved_scale`) is consumed NOT ex falso in
    `deviation_carries_engine_at_resolved_scale` below. No field is green-
    populatable: the zero = ¬RH, the resolving ledger — an open twin node. -/
structure InternalisedRiemannGround : Prop where
  ground : RiemannManifestationLaw
  beyondOwnHorizon : ¬ RiemannManifestationLaw

/-- "Internal knowledge of the Riemann cause" = internal self-grounding of the
    manifestation law (mirror of `InternalKnowledgeOfCollatzCause`). -/
abbrev InternalKnowledgeOfRiemannCause : Prop := InternalisedRiemannGround

/-! ## Core: the self-grounding self-destructs (🟢) -/

/-- The self-grounding self-destructs — exactly Collatz's `fun H =>
    H.beyondOwnHorizon H.ground`. HONESTY: the load-bearing part here is the
    form; the content lives in `deviation_carries_engine_at_resolved_scale`.
    GREEN, no axioms. -/
theorem no_internalisedRiemannGround : InternalisedRiemannGround → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **"CANNOT BE KNOWN FROM INSIDE" — THEOREM** (mirror of `collatzCause_unknowable`,
    `pnpCause_unknowable`): internal self-grounding of the manifestation law is
    impossible. Neither Gödelian independence nor anything about RH itself is
    asserted — only the impossibility of internal self-grounding. GREEN. -/
theorem riemannCause_unknowable : ¬ InternalKnowledgeOfRiemannCause :=
  no_internalisedRiemannGround

/-! ## Payment: refutation-carries-engine for Riemann (🟢, not ex falso) -/

/-- **"A DEVIATION CARRIES AN ENGINE" (genuine construction, mirror of
    `nonHalting_carries_perpetual_engine`):** a deviation supply at a resolved
    scale BUILDS a concrete Euclidean engine — a stable no-energy universe +
    an infinite family ⟹ a pigeonhole collision of the finite key ⟹ an
    engine-witness. The hypotheses are consumed FOR REAL (not ex falso): this is
    the very chain inside L2 (`no_deviationFlowSupply_at_resolved_scale`), with
    an explicit engine in the conclusion.
    CAVEAT: unlike Collatz, the fact is gated by the resolving scale (`hres`) —
    and reconciliation is exactly the open twin node (at A ≤ 4 it is refuted by
    `no_projection_resolves_at_smallScale`). -/
theorem deviation_carries_engine_at_resolved_scale {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj)
    (hSupply : DeviationFlowSupply A M0) :
    SomeConcreteEuclideanEngine := by
  obtain ⟨𝓕, h𝓕⟩ := hSupply
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact ⟨A, M0, hEngine⟩

/-- Ex-falso companion (mirror of `internalisedPNPGround_builds_engine`): from
    the (already false) self-grounding the engine itself is also derived. HONESTY:
    an ex-falso route; the load-bearing part is `no_internalisedRiemannGround`,
    while the NON-ex-falso Riemann engine is `deviation_carries_engine_at_resolved_scale`. -/
theorem internalisedRiemannGround_builds_engine :
    InternalisedRiemannGround → SomeConcreteEuclideanEngine :=
  fun H => (no_internalisedRiemannGround H).elim

/-! ## Summaries: the solution is locked behind the engine (🟢) -/

/-- **"THE SOLUTION IS LOCKED BEHIND THE ENGINE" — 3-PRONGED FORK (green; mirror of
    `collatz_no_internal_decision_without_engine`):**
    (1) A DEVIATION WITH THE BOOKS RECONCILED = AN ENGINE — a genuine construction
        (`deviation_carries_engine_at_resolved_scale`), the engine then killed by
        lexRank (`no_someConcreteEuclideanEngine`);
    (2) SELF-GROUNDING the law from inside — self-destructs
        (`no_internalisedRiemannGround`);
    (3) AN EXTERNAL DECREE decides: the law under the boundary gives RH
        (`riemannHypothesis_of_manifestation_and_boundary` +
        `no_someConcreteEuclideanEngine`) — the boundary appears as a HYPOTHESIS
        `h : TheStrictLastStep00Obligation`, NOT an axiom: the conjunct stays a
        green implication, the taint does not grow.
    Neither RH nor its independence is asserted — only: both internal paths cost
    an engine, and the decree door is assessed (by L7 the law under the boundary
    is exactly RH-strength: `manifestationLaw_iff_RH_of_boundary`). -/
theorem riemann_no_internal_decision_without_engine :
    (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0 → SomeConcreteEuclideanEngine) ∧
    (InternalisedRiemannGround → False) ∧
    (∀ _h : TheStrictLastStep00Obligation,
        RiemannManifestationLaw → RiemannHypothesis) :=
  ⟨fun _A _M0 proj hres hSupply =>
      deviation_carries_engine_at_resolved_scale proj hres hSupply,
   no_internalisedRiemannGround,
   fun h hLaw =>
      riemannHypothesis_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine h hLaw⟩

/-- The final epistemic status of the Riemann horizon (mirror of
    `pnp_locked_behind_engine_status` / `collatz_open_status`; entirely in
    implication form — green, the decree only as a hypothesis):
    internal knowledge is impossible (theorem) / a deviation with the books
    reconciled builds an engine (theorem, genuine construction) / there is no
    deviation supply at a resolved scale (theorem L2 — the same wall) / the law
    under the boundary gives RH (conditionally, `TheStrictLastStep00Obligation`
    as a hypothesis). RH stays open; this status does NOT move it. -/
theorem riemann_locked_behind_engine_status :
    (¬ InternalKnowledgeOfRiemannCause) ∧
    (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0 → SomeConcreteEuclideanEngine) ∧
    (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
        ¬ DeviationFlowSupply A M0) ∧
    (TheStrictLastStep00Obligation →
        RiemannManifestationLaw → RiemannHypothesis) :=
  ⟨riemannCause_unknowable,
   fun _A _M0 proj hres hSupply =>
      deviation_carries_engine_at_resolved_scale proj hres hSupply,
   fun _A _M0 proj hres => no_deviationFlowSupply_at_resolved_scale proj hres,
   fun hBoundary hLaw =>
      riemannHypothesis_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine hBoundary hLaw⟩

/-! ## Twin side: the twin boundary freezes every resolving ledger (🟢) -/

/-- **The twin boundary freezes resolution**: if above scale `M0` there are no
    twins (`TwinBoundAbove M0`), then NO ledger projection at this scale
    reconciles the books — the twin-bound green-supplies an infinite family of
    flows (L1, `deviationFlowSupply_of_twinBound`), and a resolved scale does not
    tolerate such a supply (L2, `no_deviationFlowSupply_at_resolved_scale`:
    collision ⟹ engine ⟹ lexRank). Names the twin side of the L6 characterisation
    (`manifestationLaw_iff_no_resolution_above_zero`) with an explicit lemma.
    HONESTY: logically this is a repackaging of the composition L1 ∘ L2 — NOT
    `twins_infinite_of_noEngine_and_boundary` (that lemma lives in the quarantine
    module and derives the infinitude of twins from ¬engines + the boundary — a
    different statement). Nothing is asserted here about the twins themselves:
    `TwinBoundAbove` is a hypothesis. GREEN, no axioms. -/
theorem twinBound_freezes_resolution {M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0) :
    ∀ (A : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
      ¬ SemanticExtendedFlowLedgerCollisionResolves proj :=
  fun _A proj hres =>
    no_deviationFlowSupply_at_resolved_scale proj hres
      (deviationFlowSupply_of_twinBound hTwinBound)

/-! ## Liouville branch: both RH branches converge to one decree (🟢-conditional) -/

/-- **Liouville sewn into the decree (green-conditional chain):** the classical
    Liouville bridge (as a hypothesis) + ¬engines + the boundary (as a hypothesis)
    + the manifestation law ⟹ `LiouvilleBound` (`|L(x)| ≤ C·x^{1/2+ε}`). The
    composition: the triple of essence-hypotheses gives RH (L4,
    `riemannHypothesis_of_manifestation_and_boundary`), the bridge carries RH into
    the arithmetic bound (`bridge.mpr`). WHAT PAYS FOR IT (honestly, by layers):
    (1) `LiouvilleRHBridge` — a RED input: the classical equivalence
        `LiouvilleBound ⟺ RH` of analytic number theory, absent from mathlib —
        here strictly as a HYPOTHESIS;
    (2) the boundary — as a HYPOTHESIS (`TheStrictLastStep00Obligation`), not an axiom;
    (3) the manifestation law under the boundary is exactly RH-strength (L7,
        `manifestationLaw_iff_RH_of_boundary`) — the theorem does NOT extract a bound,
        but shows the CONVERGENCE of both RH branches (the zero one and the Liouville
        one) to one and the same decree. NOT a solution of RH and not a new bound. -/
theorem liouvilleBound_of_manifestation_and_boundary
    (hBridge : EuclidsPath.RiemannLiouville.LiouvilleRHBridge)
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hManifest : RiemannManifestationLaw) :
    EuclidsPath.RiemannLiouville.LiouvilleBound :=
  hBridge.mpr
    (riemannHypothesis_of_manifestation_and_boundary
      hNoEngine hBoundary hManifest)

/-! ## Minimising the second boundary: the law only at the zero's own height (🟢) -/

/-- **MINIMAL manifestation law (law-at-own-height):** every off-critical zero
    is required to manifest ONLY at the scale of its own height
    `M0 = zeroHeight Z` — and not at all scales `M0 ≥ zeroHeight Z`, as in the
    full `RiemannManifestationLaw`. Syntactically strictly weaker than the full
    law (that one hangs a ∀-tail over the scales); the essence-lemma L3
    substantively uses EXACTLY this one scale (`le_refl` in
    `noOffCriticalZero_of_manifestation_and_boundary`) — hence the minimal form
    suffices (`minimalLaw_suffices` below). Documents the minimal logical content
    of the decree field `riemannBoundary`; not accepted here — only defined. -/
def MinimalRiemannManifestationLaw : Prop :=
  ∀ (Z : RiemannOffCriticalZero) (A : ℕ)
    (proj : SemanticExtendedFlowLedgerProjection A (zeroHeight Z)),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A (zeroHeight Z)

/-- The full law entails the minimal one: instantiation `M0 := zeroHeight Z`,
    `le_refl`. The trivial direction — a syntactic weakening. -/
theorem minimalLaw_of_manifestationLaw
    (hLaw : RiemannManifestationLaw) : MinimalRiemannManifestationLaw :=
  fun Z A proj hres => hLaw Z A (zeroHeight Z) (le_refl _) proj hres

/-- The essence-lemma under the MINIMAL law (L3 replayed): ¬engines + the
    boundary (as a hypothesis) + the minimal law ⟹ there are no off-critical
    zeros. Verbatim the same conclusion as L3 — confirmation that the full law
    was nowhere used beyond the zero's own height. All hypotheses are consumed
    for real (the engine-witness is killed precisely by `hNoEngine`). -/
theorem noOffCriticalZero_of_minimalLaw_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hMinimal : MinimalRiemannManifestationLaw) :
    ¬ Nonempty RiemannOffCriticalZero := by
  rintro ⟨Z⟩
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves :
      SemanticExtendedFlowLedgerCollisionResolves (projOf (zeroHeight Z)) :=
    strictSemanticExtended_resolves_old (hres (zeroHeight Z))
  have hStable : NoEnergyStableUniverse (projOf (zeroHeight Z)) :=
    (noEnergyStableUniverse_iff_resolves (projOf (zeroHeight Z))).mpr hResolves
  obtain ⟨𝓕, h𝓕⟩ := hMinimal Z A (projOf (zeroHeight Z)) hResolves
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hNoEngine ⟨A, zeroHeight Z, hEngine⟩

/-- **The minimal form suffices:** ¬engines + the boundary (as a hypothesis) +
    the minimal law ⟹ RH. Mirror of L4 over `MinimalRiemannManifestationLaw`;
    extraction of a zero from ¬RH is mathlib-precise (`offCriticalZero_of_not_RH`).
    THE BOUNDARY AS A HYPOTHESIS, not an axiom — the conjunct is green, the taint
    does not grow. -/
theorem minimalLaw_suffices
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hMinimal : MinimalRiemannManifestationLaw) :
    RiemannHypothesis := by
  by_contra hNotRH
  exact noOffCriticalZero_of_minimalLaw_and_boundary
    hNoEngine hBoundary hMinimal
    (EuclidsPath.RiemannImpossibleEngineOff.offCriticalZero_of_not_RH hNotRH)

/-- **MANDATORY PRICE AUDIT (mirror of L7):** under the boundary the minimal law
    ⟺ RH — the same RH-strength as the full law. -/
theorem minimalManifestationLaw_iff_RH_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    MinimalRiemannManifestationLaw ↔ RiemannHypothesis :=
  ⟨minimalLaw_suffices no_someConcreteEuclideanEngine hBoundary,
   fun hRH => minimalLaw_of_manifestationLaw (manifestationLaw_of_RH hRH)⟩

/-- **HONEST CAVEAT, MACHINE-CHECKED:** under the boundary the minimal law ⟺ the
    full one — the "weakening" is SYNTACTIC, not in strength (by L7 and the audit
    above both forms are exactly RH-strength). This is a REFINEMENT of the decree's
    price — precisely which logical content of the field `riemannBoundary` carries
    the whole load — and NOT a reduction of that price. WITHOUT the boundary only
    the trivial half is proved (`minimalLaw_of_manifestationLaw`). -/
theorem minimalLaw_iff_manifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    MinimalRiemannManifestationLaw ↔ RiemannManifestationLaw :=
  (minimalManifestationLaw_iff_RH_of_boundary hBoundary).trans
    (manifestationLaw_iff_RH_of_boundary hBoundary).symm

/-! ## Axiom audit: the whole module is green (standard triple at most),
the repository taint does NOT change -/
#print axioms InternalisedRiemannGround
#print axioms InternalKnowledgeOfRiemannCause
#print axioms no_internalisedRiemannGround
#print axioms riemannCause_unknowable
#print axioms deviation_carries_engine_at_resolved_scale
#print axioms internalisedRiemannGround_builds_engine
#print axioms riemann_no_internal_decision_without_engine
#print axioms riemann_locked_behind_engine_status
#print axioms twinBound_freezes_resolution
#print axioms liouvilleBound_of_manifestation_and_boundary
#print axioms MinimalRiemannManifestationLaw
#print axioms minimalLaw_of_manifestationLaw
#print axioms noOffCriticalZero_of_minimalLaw_and_boundary
#print axioms minimalLaw_suffices
#print axioms minimalManifestationLaw_iff_RH_of_boundary
#print axioms minimalLaw_iff_manifestationLaw_of_boundary

end EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic
