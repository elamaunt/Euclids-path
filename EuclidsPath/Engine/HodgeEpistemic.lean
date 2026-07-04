/-
  HodgeEpistemic — EPISTEMIC COMPLEMENT of the sixth front (Hodge), following
  the Tier 1 programme. Green machine: Engine/HodgeFront.lean.
  Mirror row: PNPFirstCause (pair "resolves + horizon"), CollatzFirstCause
  (pair "ground + its negation" — our case).

  WHAT THIS IS. Model-internal epistemics of the Hodge branch: "to resolve from
  within" = to self-justify the per-model descent law `DescentLaw S` by crossing
  its own horizon (`InternalisedHodgeGround`). Self-justification self-destructs
  (`no_internalisedHodgeGround`), and the contradiction is paid NOT only by
  form: under the law an unpaid class unfolds into a GENUINE infinite chain
  (`unpaidDescentChain_of_descentLaw`, not ex falso) — that is, into a perpetual
  engine on ℕ (`hodgeChain_builds_perpetual_engine`), burned by the wall of
  well-foundedness (`no_perpetual_engine_on_nat`, the same prohibition as in
  Collatz and P/NP).

  CRITICAL (sceptic's verdict, accounted for): the UNIVERSAL form of the law has
  ALREADY been machine-refuted (`hodgeLawUniversal_refuted`, V1 of the trilemma:
  forged witness cookedUnpaid, the descent step from height 1 hits the
  quantisation anchor) — so ground is taken HERE ONLY per-model (`DescentLaw S`),
  whose truth for the intended instantiation remains open. The universal path is
  closed by the forged refutation — as in YM and Collatz
  (`hodgeUniversal_forged_refutation`).

  HONESTY (loud). (1) This is model-internal epistemic unknowability, NOT a
  solution of the Hodge conjecture (mathlib does not even have the language for
  the target instantiation — see HodgeFront header) and NOT Godel (no
  incompleteness / fixed point — only self-destruction of the pair and ℕ-descent).
  (2) The pair `InternalisedHodgeGround` is formally "ground + its negation" (like
  `InternalisedCollatzGround`) — the form alone self-destructs in one line. What
  pays for substantiveness: (a) both sides are green-identified with content —
  the law ⟺ the model's Hodge conjecture (`descentLaw_iff_hodgeProperty`,
  collapse L9), its negation ⟺ existence of an unpaid class
  (`not_hodgeProperty_iff_unpaidClass`); (b) the contradiction has a SECOND,
  engine route: from the pair a genuine descent chain and a genuine
  `PerpetualEngine` are constructed (`internalisedHodgeGround_builds_engine` —
  unlike the ex-falso companion in P/NP, the construction here is authentic),
  and the EPMI wall burns it. (3) The distinction from Collatz is disclosed:
  there the negation of ground is unknown; here the sides of the per-model pair
  are green mutually-negative via collapse — this is acknowledged, the pair
  carries no dichotomous novelty; the module's value is architectural (Hodge
  joins the row unknowable / locked_behind_engine), not new mathematics.

  The module is ENTIRELY GREEN: quarantine is NOT imported, no axiom/sorry,
  the repository taint does not change.
-/

import EuclidsPath.Engine.HodgeFront
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath
namespace Hodge
namespace Epistemic

open EuclidsPath.UniversalEngine

/-! ## Model: internal resolution = self-justification of the per-model law -/

/-- **Internal self-justification of the Hodge ground (per-model!):** the machine
    carries the model's own descent law AND a witness that it was derived from
    within — crossing its own horizon. The pair's form is "ground + its negation"
    (like `InternalisedCollatzGround`; the first field in P/NP was called
    `resolves`). The UNIVERSAL ground must not be taken here: it has already been
    machine-refuted (`hodgeLawUniversal_refuted`) — unknowability would then be a
    consequence of V1, not of epistemics. The pair's substantiveness is paid by
    collapse L9: `ground` ⟺ the model's Hodge conjecture, `beyondOwnHorizon` ⟺
    presentability of an unpaid class — and by the genuine engine route of the
    contradiction (see `internalisedHodgeGround_builds_engine`). -/
structure InternalisedHodgeGround (S : HodgeLedger) : Prop where
  ground : DescentLaw S
  beyondOwnHorizon : ¬ DescentLaw S

/-- "Internal knowledge of the Hodge cause" = internal self-justification of the law. -/
abbrev InternalKnowledgeOfHodgeCause (S : HodgeLedger) : Prop :=
  InternalisedHodgeGround S

/-! ## Core: self-justification self-destructs (🟢) -/

/-- Self-justification self-destructs — exactly
    `fun H => H.beyondOwnHorizon H.ground` of Collatz. The formal route;
    the engine payment of the same truth — `no_internalisedHodgeGround'`. -/
theorem no_internalisedHodgeGround {S : HodgeLedger} :
    InternalisedHodgeGround S → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM** (mirror of `collatzCause_unknowable`,
    `pnpCause_unknowable`): internal self-justification of the per-model Hodge
    law is impossible. GREEN, without any axioms. Neither independence nor the
    status of the Hodge conjecture itself is asserted — only the impossibility of
    internal self-justification. -/
theorem hodgeCause_unknowable {S : HodgeLedger} :
    ¬ InternalKnowledgeOfHodgeCause S :=
  no_internalisedHodgeGround

/-! ## Bridge to the UniversalEngine vocabulary: Hodge chain = perpetual engine on ℕ -/

/-- **Unpaid descent chain = perpetual engine on ℕ** (bridge to the universal
    vocabulary, mirror of `internalPNPDecision_carries_perpetual_engine` in
    spirit): direct projection `height ∘ seq`, the witness is presented by
    construction — NOT ex falso. -/
theorem hodgeChain_builds_perpetual_engine {S : HodgeLedger}
    (C : UnpaidDescentChain S) : PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  ⟨fun n => S.height (C.seq n), C.descent⟩

/-- **"Unpaid class under the law carries the engine" — GENUINE** (mirror of
    `nonHalting_carries_perpetual_engine` of Collatz): from the per-model law and
    an unpaid class a genuine infinite chain is CONSTRUCTED
    (`unpaidDescentChain_of_descentLaw`, the choice is honestly visible) and
    projected into a `PerpetualEngine` on ℕ. Honest nuance (disclosed): in
    Collatz the engine arises from a bare counterexample; in Hodge — from a
    deviation UNDER the law (without the law there is no descent step:
    `cookedUnpaid_no_descent_step`). -/
theorem unpaidClass_under_law_carries_perpetual_engine {S : HodgeLedger}
    (hLaw : DescentLaw S) (p : UnpaidClass S) :
    PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  hodgeChain_builds_perpetual_engine (unpaidDescentChain_of_descentLaw hLaw p)

/-- **Engine companion — NOT ex falso** (unlike
    `internalisedPNPGround_builds_engine`): from the self-justification pair the
    engine is constructed GENUINELY — `beyondOwnHorizon` via collapse L9 presents
    an unpaid class, `ground` unfolds it into a chain, the chain is projected into
    a `PerpetualEngine`. This is precisely the payment for the pair's
    substantiveness. -/
theorem internalisedHodgeGround_builds_engine {S : HodgeLedger} :
    InternalisedHodgeGround S → PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  fun H =>
    ((not_hodgeProperty_iff_unpaidClass S).mp
        (fun hP => H.beyondOwnHorizon (descentLaw_of_hodgeProperty hP))).elim
      (fun p => unpaidClass_under_law_carries_perpetual_engine H.ground p)

/-- Second route of self-destruction — of the same truth, but via the engine and
    the EPMI wall (`no_perpetual_engine_on_nat`), not via the pair's form. -/
theorem no_internalisedHodgeGround' {S : HodgeLedger} :
    InternalisedHodgeGround S → False :=
  fun H => no_perpetual_engine_on_nat (internalisedHodgeGround_builds_engine H)

/-- **Hodge wall = engine wall** (mirror of the wall pair
    `internalPNPDecision_carries_perpetual_engine`): emptiness of chains in every
    model and the prohibition of a perpetual engine on ℕ — ONE wall of
    well-foundedness (EPMI, A = 1). -/
theorem hodge_wall_is_engine_wall (S : HodgeLedger) :
    IsEmpty (UnpaidDescentChain S) ∧ ¬ PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  ⟨isEmpty_unpaidDescentChain S, no_perpetual_engine_on_nat⟩

/-! ## Summaries: resolution is locked behind the engine (🟢) -/

/-- **"RESOLUTION IS LOCKED BEHIND THE ENGINE" — 3-WAY FORK (green; mirror of
    `collatz_no_internal_decision_without_engine`,
    `pnp_no_internal_decision_without_engine`):**
    (1) UNPAID CLASS UNDER THE LAW = infinite chain = perpetual engine on ℕ
        (genuine construction `unpaidDescentChain_of_descentLaw` + projection,
        NOT ex falso) — but a perpetual engine on ℕ is forbidden;
    (2) TO SELF-JUSTIFY the law from within — self-destructs
        (`no_internalisedHodgeGround`);
    (3) per-model law ⟺ the model's Hodge conjecture GREEN
        (`descentLaw_iff_hodgeProperty`, collapse of the condemned bridge):
        to decree the law = to decree the goal verbatim — so the engine-free path
        is only an EXTERNAL data anchor (genuine rational (p,p)-classes, which are
        absent from mathlib).
    Neither Godelian independence nor the Hodge conjecture is asserted. -/
theorem hodge_no_internal_decision_without_engine (S : HodgeLedger) :
    (DescentLaw S → Nonempty (UnpaidClass S) →
        PerpetualEngine (· < · : ℕ → ℕ → Prop)) ∧
    (InternalisedHodgeGround S → False) ∧
    (DescentLaw S ↔ HodgeProperty S) :=
  ⟨fun hLaw hp =>
      hp.elim (fun p => unpaidClass_under_law_carries_perpetual_engine hLaw p),
   no_internalisedHodgeGround,
   descentLaw_iff_hodgeProperty S⟩

/-- Final epistemic status of the sixth front (mirror of
    `pnp_locked_behind_engine_status` / `collatz_open_status`; no decree
    conjunct — the sixth boundary does not exist, collapse L9): the universal law
    is FORGEDLY REFUTED (theorem) / the engine is dead in every model (theorem,
    EPMI A = 1) / internal knowledge is impossible (theorem) / per-model law ⟺
    the model's conjecture (theorem — so the entry remains external). ENTIRELY
    GREEN. -/
theorem hodge_locked_behind_engine_status (S : HodgeLedger) :
    (¬ HodgeDescentLawUniversal) ∧
    IsEmpty (UnpaidDescentChain S) ∧
    (¬ InternalKnowledgeOfHodgeCause S) ∧
    (DescentLaw S ↔ HodgeProperty S) :=
  ⟨hodgeLawUniversal_refuted,
   isEmpty_unpaidDescentChain S,
   hodgeCause_unknowable,
   descentLaw_iff_hodgeProperty S⟩

/-! ## Universal form is forged — re-export of V1 -/

/-- **"LIKE YM AND COLLATZ: THE UNIVERSAL IS FORGED"** — named re-export of
    `hodgeLawUniversal_refuted` (V1 of the sixth-front trilemma): the universal
    form of the descent law is machine-refuted by the forged witness
    (`cookedUnpaid`: the descent step from height 1 would hit the paid-ness of
    height zero — the quantisation anchor `height_zero_iff` is genuinely consumed).
    Exactly as `ropeLaw_universal_refuted` in Collatz and the refutation of the
    universal form in YM: the decree path via the universal is machine-closed;
    only the per-model entry survives — and it, by collapse L9, equals the goal
    verbatim. -/
theorem hodgeUniversal_forged_refutation : ¬ HodgeDescentLawUniversal :=
  hodgeLawUniversal_refuted

end Epistemic
end Hodge
end EuclidsPath

-- Machine-visible cleanliness in the build log
-- (expected: a subset of [propext, Classical.choice, Quot.sound]):
#print axioms EuclidsPath.Hodge.Epistemic.InternalisedHodgeGround
#print axioms EuclidsPath.Hodge.Epistemic.InternalKnowledgeOfHodgeCause
#print axioms EuclidsPath.Hodge.Epistemic.no_internalisedHodgeGround
#print axioms EuclidsPath.Hodge.Epistemic.hodgeCause_unknowable
#print axioms EuclidsPath.Hodge.Epistemic.hodgeChain_builds_perpetual_engine
#print axioms EuclidsPath.Hodge.Epistemic.unpaidClass_under_law_carries_perpetual_engine
#print axioms EuclidsPath.Hodge.Epistemic.internalisedHodgeGround_builds_engine
#print axioms EuclidsPath.Hodge.Epistemic.no_internalisedHodgeGround'
#print axioms EuclidsPath.Hodge.Epistemic.hodge_wall_is_engine_wall
#print axioms EuclidsPath.Hodge.Epistemic.hodge_no_internal_decision_without_engine
#print axioms EuclidsPath.Hodge.Epistemic.hodge_locked_behind_engine_status
#print axioms EuclidsPath.Hodge.Epistemic.hodgeUniversal_forged_refutation
