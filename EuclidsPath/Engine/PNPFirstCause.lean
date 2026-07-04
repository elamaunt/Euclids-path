/-
  PNPFirstCause — EPISTEMIC COMPLEMENT of P/NP (mirror of CollatzFirstCause).
  Discussion: prose/56_CollatzFirstCause.md (section "P/NP behind the same horizon").
  Green rank-payment machine: Engine/PNPRankPaymentFront.lean.

  WHAT THIS IS. The verifying machine — "a computer in pure form on finite fuel" with
  strict rules: it is a `RankedForwardGraph` (rules = `Step`, fuel = `lexRank`,
  fuel law = `RankFastTraversal`), starting from an ARBITRARY (random) position
  (5-adic chain for A ≤ 4). "Solving P/NP from within" = paying injectively with a finite
  key for EVERY certificate of an UNBOUNDED supply (`FullRankCertificatePayment`
  of an unbounded `UnboundedCertificateSupply`). This is the same perpetual-engine
  contradiction as in Collatz: "non-falling tail = engine" ↦ "full payment of
  unbounded supply = engine". Both perish against the same wall of well-foundedness
  (pigeonhole = no injection of infinite into finite = no ℕ-descent, `no_perpetual_engine_on_nat`).

  HONESTY. This is model-internal epistemic unknowability (like
  `collatzCause_unknowable`), and NOT a proof of classical P≠NP (the frame layer
  is plastic — `allPFrame`/`constantsFrame`, from it nothing follows about real P/NP)
  and NOT Gödel (this is pigeonhole self-destruction, not an incompleteness/fixed-point theorem).
  KEY DIFFERENCE FROM COLLATZ: P/NP has NO decree — the trilemma (`pnpLawUniversal_refuted`,
  `pnpLawExistential_green`) proved machine-wise that no honest third boundary `step00FirstCause`
  exists. Therefore this entire file is GREEN, WITHOUT importing quarantine, without `step00FirstCause`:
  the repository taint does NOT change. Unconditional core — for A ≤ 4 (boundary
  `PNPRankPaymentFront`); the extension at the end of the file adds the exact payment law
  (`fullPayment_iff_boundedSupply`) and locks on VISIBLE hypotheses — twin-bound across
  all scales and the decreed scale A ≥ 5 (boundary as hypothesis, style L14–L16).
-/

import EuclidsPath.Engine.PNPRankPaymentFront
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.PNPRankPayment.FirstCause

open EuclidsPath.PNPRankPayment
open EuclidsPath.LocalPNP
open EuclidsPath.LocalPNP.Concrete
open EuclidsPath.UniversalEngine

/-! ## Model: internal decision = self-grounding beyond one's own horizon -/

/-- **Internal self-grounding of the P/NP decision on finite fuel.** The machine
    simultaneously (a) PAYS injectively with a finite key for the entire certificate supply
    (`resolves`) and (b) that supply is UNBOUNDED (`beyondOwnHorizon`).
    HONESTY (refined after the exact law `fullPayment_iff_boundedSupply` below):
    the fields are PROVABLY exact complements; semantically the structure is equivalent to the pair
    "payment ∧ ¬payment" (machine-wise: `internalisedPNPGround_semantically_selfNegating`).
    The substance lives NOT in the form of the structure but in what the contradiction is PAID with:
    `beyondOwnHorizon` — an independently proven green fact (5-adic chain
    `fiveAdicChainFlow_injective`); the contradiction is supplied by the pigeonhole
    `no_fullPayment_of_unboundedSupply`. This is precisely the attempt to "reach with one's gaze"
    beyond one's own finite-fuel horizon. -/
structure InternalisedPNPGround {G : RankedForwardGraph} (F : GenealogyFamily G) : Prop where
  resolves : FullRankCertificatePayment F
  beyondOwnHorizon : UnboundedCertificateSupply F

/-- "Internal knowledge of the P/NP cause" = internal self-grounding of the decision. -/
abbrev InternalKnowledgeOfPNPCause {G : RankedForwardGraph} (F : GenealogyFamily G) : Prop :=
  InternalisedPNPGround F

/-- Concrete honest instance for A ≤ 4 (5-adic chain, with no hypotheses at all). -/
abbrev InternalPNPDecision (A : ℕ) : Prop := InternalisedPNPGround (concreteFamily A 1)

/-! ## Core: self-grounding self-destructs = perpetual-engine wall (🟢) -/

/-- Self-grounding self-destructs — exactly `fun H => H.beyondOwnHorizon H.ground`
    of Collatz, only the negation is supplied by the pigeonhole. GREEN. -/
theorem no_internalisedPNPGround {G : RankedForwardGraph} {F : GenealogyFamily G} :
    InternalisedPNPGround F → False :=
  fun H => no_fullPayment_of_unboundedSupply H.beyondOwnHorizon H.resolves

/-- **"UNKNOWABLE FROM WITHIN" — THEOREM** (mirror of `collatzCause_unknowable`,
    twin-`cause_unknowable`): an internal finite-fuel decision on P/NP is impossible.
    GREEN, with no axioms at all. -/
theorem pnpCause_unknowable {G : RankedForwardGraph} {F : GenealogyFamily G} :
    ¬ InternalKnowledgeOfPNPCause F :=
  no_internalisedPNPGround

/-- **THE SAME PERPETUAL-ENGINE CONTRADICTION (green):** the impossibility of an internal P/NP
    decision AND the impossibility of a perpetual engine on ℕ — ONE wall of well-foundedness
    (mirror of `UniversalEngine.discrete_forbids_continuous_realizes`: finite fuel on
    ℕ bottlenecks descent). Paying an unbounded supply with a finite key = cramming
    an infinite index into a finite one = the same ℕ-prohibition. -/
theorem internalPNPDecision_carries_perpetual_engine {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    (InternalisedPNPGround F → False) ∧ ¬ PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  ⟨no_internalisedPNPGround, no_perpetual_engine_on_nat⟩

/-- Ex-falso companion ("carries the engine"): from self-grounding (already false) one derives
    the perpetual engine on ℕ itself — self-grounding explodes everything. HONESTY: the route is
    ex falso; the load-bearing part is the impossibility itself (`no_internalisedPNPGround`). -/
theorem internalisedPNPGround_builds_engine {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    InternalisedPNPGround F → PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  fun H => (no_internalisedPNPGround H).elim

/-- SUBSTANTIVE DICHOTOMY (without ex falso in the statement): either the cause is unknowable
    from within, or the unbounded supply is fully payable. The left disjunct is a theorem. -/
theorem unknowable_or_pnp_fullyPayable {A : ℕ} :
    (¬ InternalKnowledgeOfPNPCause (concreteFamily A 1)) ∨
      FullRankCertificatePayment (concreteFamily A 1) :=
  Or.inl pnpCause_unknowable

/-! ## Summaries: decision locked behind the engine; verification not derivation (🟢) -/

/-- **"DECISION LOCKED BEHIND THE ENGINE" (green; mirror of
    `collatz_no_internal_decision_without_engine`):**
    (1) PAYING the unbounded supply FROM WITHIN = perpetual-engine wall (pigeonhole,
        `concrete_noFullPayment_smallScale`) — internal decision is impossible;
    (2) SELF-GROUNDING the decision from within — self-destructs (`no_internalisedPNPGround`);
    (3) the only engine-free path — EXTERNAL VERIFICATION: local P-success entails
        full payment (`concrete_localPSuccess_iff_fullPayment`), i.e. the decision is reached
        by verification, not by internal derivation.
    Neither Gödelian independence nor P≠NP is asserted — only: both internal decisions
    cost a perpetual engine. -/
theorem pnp_no_internal_decision_without_engine {A : ℕ} (hA : A ≤ 4) :
    (FullRankCertificatePayment (concreteFamily A 1) → False) ∧
    (InternalisedPNPGround (concreteFamily A 1) → False) ∧
    (∀ M0 : ℕ, LocalPSuccess (concreteProblem A M0) →
        FullRankCertificatePayment (concreteFamily A M0)) :=
  ⟨concrete_noFullPayment_smallScale hA,
   no_internalisedPNPGround,
   fun M0 hP => (concrete_localPSuccess_iff_fullPayment A M0).mp hP⟩

/-- **"VERIFICATION, NOT DERIVATION" (mirror of `collatz_verification_not_derivation`):**
    (1) the internal P/NP decision is unknowable (`pnpCause_unknowable`);
    (2) paying the unbounded supply from within is impossible — engine wall;
    (3) hence the decision is accessible only by VERIFICATION (local success ⟹ full payment),
        reachable exactly as far as the finite-fuel horizon extends. -/
theorem pnp_verification_not_derivation {A : ℕ} (hA : A ≤ 4) :
    (¬ InternalPNPDecision A) ∧
    (FullRankCertificatePayment (concreteFamily A 1) → False) ∧
    (∀ M0 : ℕ, LocalPSuccess (concreteProblem A M0) →
        FullRankCertificatePayment (concreteFamily A M0)) :=
  ⟨pnpCause_unknowable,
   concrete_noFullPayment_smallScale hA,
   fun M0 hP => (concrete_localPSuccess_iff_fullPayment A M0).mp hP⟩

/-- Final epistemic status of the P/NP horizon (mirror of
    `collatz_locked_behind_engine_status`, but WITHOUT the decree-conjunct — P/NP has no boundary):
    engine traverses rank fast / supply is unbounded / unknowable from within
    (theorem) / full payment = engine wall (theorem). GREEN throughout. -/
theorem pnp_locked_behind_engine_status {A : ℕ} (hA : A ≤ 4) :
    RankFastTraversal (concreteGraph A 1) ∧
    UnboundedCertificateSupply (concreteFamily A 1) ∧
    (¬ InternalPNPDecision A) ∧
    (FullRankCertificatePayment (concreteFamily A 1) → False) :=
  ⟨concrete_rankFastTraversal A 1,
   concreteSupply_unbounded_smallScale hA,
   pnpCause_unknowable,
   concrete_noFullPayment_smallScale hA⟩

/-! ## Axiom audit: the entire module is green (standard triple), repository taint does NOT change -/
#print axioms no_internalisedPNPGround
#print axioms pnpCause_unknowable
#print axioms internalPNPDecision_carries_perpetual_engine
#print axioms internalisedPNPGround_builds_engine
#print axioms unknowable_or_pnp_fullyPayable
#print axioms pnp_no_internal_decision_without_engine
#print axioms pnp_verification_not_derivation
#print axioms pnp_locked_behind_engine_status

/-! ## Extension: exact payment law and locks on visible hypotheses (🟢)

Quarantine is still NOT imported: `TwinBoundAbove` and
`TheStrictLastStep00Obligation` appear below only as VISIBLE hypotheses
(style L14–L16 of the front `PNPRankPaymentFront`) — repository taint does not change. -/

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-- **Payment bounds supply** — contrapositive of the pigeonhole core
    `no_fullPayment_of_unboundedSupply`: full injective finite-key payment of a certificate
    family is incompatible with its unboundedness. GREEN,
    for any ranked graph and any family. -/
theorem fullPayment_implies_boundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    FullRankCertificatePayment F → ¬ UnboundedCertificateSupply F :=
  fun hPay hInf => no_fullPayment_of_unboundedSupply hInf hPay

/-- **EXACT PAYMENT LAW (pigeonhole becomes iff):** the entire family can be paid with
    an injective finite key ⟺ the certificate supply is BOUNDED.
    Forward direction — contrapositive of the L5 core (`fullPayment_implies_boundedSupply`);
    backward — construction: when `F.Index` is finite the index itself serves as the key
    (`Key := F.Index`, `keyOf := id`, injectivity for free). HONESTY:
    (1) the backward direction uses `Fintype.ofFinite` (noncomputable) — inside
    ∃-Prop this is legitimate; classical choice belongs to the standard axiom triple;
    (2) this is a model-internal law of the rank machine — NOTHING is asserted about classical P/NP
    (the frame layer is plastic: `allPFrame`/`constantsFrame`). -/
theorem fullPayment_iff_boundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    FullRankCertificatePayment F ↔ ¬ UnboundedCertificateSupply F := by
  classical
  constructor
  · exact fullPayment_implies_boundedSupply
  · intro hBound
    haveI : Finite F.Index := not_infinite_iff_finite.mp hBound
    exact ⟨⟨F.Index, Fintype.ofFinite F.Index, id⟩, Function.injective_id⟩

/-- **Self-grounding is semantically "payment ∧ ¬payment" (machine honesty):**
    after the exact law `fullPayment_iff_boundedSupply` the fields
    `resolves`/`beyondOwnHorizon` are provably exact complements, and the entire structure
    `InternalisedPNPGround` is equivalent to a contradictory pair. The substance
    lives NOT in the form but in what pays the contradiction: green iff + 5-adic chain
    (`fiveAdicChainFlow_injective`). Backward direction — ex falso (honest). -/
theorem internalisedPNPGround_semantically_selfNegating {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    InternalisedPNPGround F ↔
      (FullRankCertificatePayment F ∧ ¬ FullRankCertificatePayment F) :=
  ⟨fun H => ⟨H.resolves, no_fullPayment_of_unboundedSupply H.beyondOwnHorizon⟩,
   fun h => (h.2 h.1).elim⟩

/-- **EPISTEMIC LOCK AT ALL SCALES (twin-conditional):** given
    `TwinBoundAbove M0` (no twin centres above M0) at ANY scale (A, M0):
    engine traverses rank fast / supply is unbounded / unknowable from within
    / full payment — engine wall. HONESTY (mandatory): conjuncts
    1 and 3 are UNCONDITIONAL (`concrete_rankFastTraversal` and `pnpCause_unknowable` — with
    no hypotheses at all); the twin hypothesis feeds ONLY conjuncts 2 and 4 — this is a bundling
    of existing facts, disclosed directly. The value of the pair: it is machine-visible that
    the only input that unlocks PAYMENT at large scales —
    the infinitude of twins (the decree side) — while unknowability from within
    (conjunct 3) is unlocked by nothing at all. -/
theorem pnp_locked_behind_engine_status_of_twinBound {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0) :
    RankFastTraversal (concreteGraph A M0) ∧
    UnboundedCertificateSupply (concreteFamily A M0) ∧
    (¬ InternalKnowledgeOfPNPCause (concreteFamily A M0)) ∧
    (FullRankCertificatePayment (concreteFamily A M0) → False) :=
  ⟨concrete_rankFastTraversal A M0,
   concreteSupply_unbounded_of_twinBound hTwinBound,
   pnpCause_unknowable,
   fun hPay => fullPayment_implies_boundedSupply hPay
     (concreteSupply_unbounded_of_twinBound hTwinBound)⟩

/-- **DECREE PAYS BUT DOES NOT SELF-GROUND (yellow by visible hypothesis):** even
    at the decree-paid scale A ≥ 5, where `TheStrictLastStep00Obligation`
    forces full payment for every M0
    (`boundary_forces_fullPayment_at_decreed_scale`), internal self-grounding
    remains impossible. HONESTY: the second conjunct is UNCONDITIONAL
    (`no_internalisedPNPGround` — with no hypotheses); the substance is in the PAIR: payment without
    an unbounded horizon is NOT self-grounding; unknowability holds
    BOTH banks of the scale split. Quarantine is NOT imported — the boundary enters as a
    hypothesis. -/
theorem decree_pays_but_no_selfGrounding
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      FullRankCertificatePayment (concreteFamily A M0) ∧
      ¬ InternalisedPNPGround (concreteFamily A M0) := by
  obtain ⟨A, hA, hPay⟩ := boundary_forces_fullPayment_at_decreed_scale hBoundary
  exact ⟨A, hA, fun M0 => ⟨hPay M0, no_internalisedPNPGround⟩⟩

/-- **EPISTEMIC LOCK AT THE DECREED SCALE (yellow by visible hypothesis;
    mirror of `pnp_locked_behind_engine_status` on the OTHER bank of the split):** at
    the decreed scale A ≥ 5 the engine still traverses rank fast, payment is
    FORCED by the boundary, supply is therefore BOUNDED (exact law
    `fullPayment_iff_boundedSupply` in the form `fullPayment_implies_boundedSupply`),
    and yet it is impossible to decide FROM WITHIN. HONESTY: conjuncts 1 and 4 are unconditional
    (`concrete_rankFastTraversal`, `pnpCause_unknowable`); the boundary hypothesis feeds
    conjuncts 2–3. NOT Gödel and NOT P≠NP: model-internal epistemics; boundary —
    visible hypothesis (style L14–L16); quarantine not imported; taint unchanged. -/
theorem pnp_locked_behind_engine_status_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      RankFastTraversal (concreteGraph A M0) ∧
      FullRankCertificatePayment (concreteFamily A M0) ∧
      (¬ UnboundedCertificateSupply (concreteFamily A M0)) ∧
      (¬ InternalKnowledgeOfPNPCause (concreteFamily A M0)) := by
  obtain ⟨A, hA, hPay⟩ := boundary_forces_fullPayment_at_decreed_scale hBoundary
  exact ⟨A, hA, fun M0 =>
    ⟨concrete_rankFastTraversal A M0,
     hPay M0,
     fullPayment_implies_boundedSupply (hPay M0),
     pnpCause_unknowable⟩⟩

/-! ## Extension axiom audit: at most the standard triple, taint does NOT change -/
#print axioms fullPayment_implies_boundedSupply
#print axioms fullPayment_iff_boundedSupply
#print axioms internalisedPNPGround_semantically_selfNegating
#print axioms pnp_locked_behind_engine_status_of_twinBound
#print axioms decree_pays_but_no_selfGrounding
#print axioms pnp_locked_behind_engine_status_at_decreed_scale

end EuclidsPath.PNPRankPayment.FirstCause
