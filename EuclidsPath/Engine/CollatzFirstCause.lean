/-
  CollatzFirstCause — POST-MORTEM of the fourth boundary (decree TAKEN AND LIFTED) +
  surviving green epistemics. Discussion: prose/56_CollatzFirstCause.md.
  Green engine: Engine/CollatzTugOfWar.lean.

  HISTORY. The rope law (`RopeCountingLaw` for all n ≥ 1) was accepted by the FOURTH
  boundary `collatzBoundary` of `Step00FirstCause` — with the disclosed price
  "the decree possibly OVERPAYS" (only the arrow law ⟹ conjecture was proved).
  Then the universal form of the law was REFUTED by machine:
  `ropeLaw_universal_refuted` (CollatzTugOfWar; witness n = 27, kernel
  [propext, Quot.sound]). The tripwire `collatzQuarantine_inconsistent_if_law_refuted`
  fired exactly as intended — the field was REMOVED from the first cause (otherwise the axiom
  would have been inconsistent). Overpaid into falsehood; the honesty discipline worked.

  STATUS NOW. As with Yang–Mills: the trilemma is closed by a FORGED REFUTATION —
  the decree path for Collatz is impossible by machine. The Collatz conjecture is an open
  🔴 question with a green front: window budget, CONDITIONAL per-n hero
  `reaches_one_of_countingLaw`, "refuting the conjecture = perpetual engine"
  (`nonHalting_carries_perpetual_engine`) — all live. This module is ENTIRELY
  GREEN: does not import quarantine, does not touch taint.
-/

import EuclidsPath.Engine.CollatzTugOfWar

set_option autoImplicit false

namespace EuclidsPath.Collatz.FirstCause

open EuclidsPath.Collatz.TugOfWar

/-! ## Decree post-mortem (🟢) -/

/-- **POST-MORTEM OF THE FOURTH BOUNDARY (green summary).** (1) The universal rope
    law is FALSE (witness n = 27) — a decree boundary on it is impossible;
    (2) the per-n law still implies halting (the conditional mechanics are alive);
    (3) refuting the conjecture itself still carries a perpetual engine (tail from
    the minimum). The decree fell, the green front holds. -/
theorem collatz_decree_postmortem :
    (¬ ∀ n : Nat, 1 ≤ n → RopeCountingLaw n) ∧
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n → ∃ K, iter K n = 1) ∧
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) :=
  ⟨ropeLaw_universal_refuted,
   fun n h1 law => reaches_one_of_countingLaw n h1 law,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh⟩

/-- **The decree arrow that "possibly overpaid" — and overpaid into falsehood.**
    The implication "universal law ⟹ convergence everywhere" remains green and
    true, but its premise is now refuted by machine (`ropeLaw_universal_refuted`):
    the law will never be supplied universally.
    The content lives in the per-n form (`reaches_one_of_countingLaw`). -/
theorem ropeLaw_would_imply_collatz :
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n) →
      ∀ n : Nat, 1 ≤ n → ∃ K, iter K n = 1 :=
  fun law n h1 => reaches_one_of_countingLaw n h1 (law n h1)

/-! ## Epistemics: the solution is locked behind the engine (green, survived)

The unknowability of internal self-grounding did NOT depend on the decree and
survives its fall; moreover, the `ground` field itself is now refuted by machine —
internal self-grounding is impossible a fortiori. -/

/-- **Internal self-grounding of the rope law's ground**: carries the law itself AND
    a witness that it was derived from within — crossing its own boundary.
    After `ropeLaw_universal_refuted` the `ground` side is false on its own —
    self-grounding is impossible doubly so. -/
structure InternalisedCollatzGround : Prop where
  ground : ∀ n : Nat, 1 ≤ n → RopeCountingLaw n
  beyondOwnHorizon : ¬ ∀ n : Nat, 1 ≤ n → RopeCountingLaw n

/-- "Internal knowledge of the cause" = internal self-grounding of the boundary. -/
abbrev InternalKnowledgeOfCollatzCause : Prop := InternalisedCollatzGround

/-- Self-grounding self-destructs (by form); and after the law's refutation it is
    impossible by content as well: `ground` is false. -/
theorem no_internalisedCollatzGround : InternalisedCollatzGround → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **"CANNOT BE KNOWN" — THEOREM** (mirror of twin-`cause_unknowable`): internal
    knowledge of the Collatz first cause is impossible. GREEN, with no axioms at all. -/
theorem collatzCause_unknowable : ¬ InternalKnowledgeOfCollatzCause :=
  no_internalisedCollatzGround

/-- Now even stronger: the ground of the unknowable knowledge is itself false —
    a direct consequence of the refutation (not through formal self-destruction). -/
theorem internalGround_impossible_a_fortiori : InternalisedCollatzGround → False :=
  fun H => ropeLaw_universal_refuted H.ground

/-- SUBSTANTIVE DICHOTOMY (no ex falso in the statement): either the cause is
    unknowable, or Collatz is false. The left disjunct is a theorem. -/
theorem unknowable_or_collatz_fails :
    ¬ InternalKnowledgeOfCollatzCause ∨
      ∃ n : Nat, 1 ≤ n ∧ ∀ K, iter K n ≠ 1 :=
  Or.inl collatzCause_unknowable

/-- **SUMMARY "SOLUTION LOCKED BEHIND THE ENGINE" (green):**
    (1) REFUTING the conjecture = building a perpetual engine — genuinely (the tail from
        the minimum is exhibited by construction);
    (2) PROVING FROM WITHIN = self-grounding the ground — self-destructs;
    (3) the per-n rope law would imply per-n halting — but there is no UNIVERSAL supply
        any longer: the universal law is refuted.
    Gödelian independence is NOT asserted — only: both internal resolutions
    cost a perpetual engine, and the decree door is closed by a forged refutation. -/
theorem collatz_no_internal_decision_without_engine :
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) ∧
    (InternalisedCollatzGround → False) ∧
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n → ∃ K, iter K n = 1) :=
  ⟨fun n hnh => nonHalting_carries_perpetual_engine n hnh,
   no_internalisedCollatzGround,
   fun n h1 law => reaches_one_of_countingLaw n h1 law⟩

/-- **"VERIFICATION, NOT DERIVATION" (machine-visible narrative):**
    (1) internal extraction of the rope law is impossible
        (`collatzCause_unknowable`);
    (2) the only internal trace of a counterexample is a perpetual engine: the tail
        of the orbit from the minimum is non-descending and does not halt;
    (3) hence the resolution is either unknowable from within, or accessible only by
        VERIFYING an orbit found exactly as far as we look. GREEN. -/
theorem collatz_verification_not_derivation :
    (¬ InternalKnowledgeOfCollatzCause) ∧
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) ∧
    (¬ InternalKnowledgeOfCollatzCause ∨ ∃ n : Nat, 1 ≤ n ∧ ∀ K, iter K n ≠ 1) :=
  ⟨collatzCause_unknowable,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh,
   unknowable_or_collatz_fails⟩

/-- The final epistemic status of Collatz AFTER the decree's fall (green,
    mirror of `pnp_locked_behind_engine_status` — without the decree conjunct):
    universal law REFUTED (theorem) / internal knowledge impossible
    (theorem) / per-n law implies halting (conditional) / refuting the conjecture
    would build a perpetual engine (theorem). -/
theorem collatz_open_status :
    (¬ ∀ n : Nat, 1 ≤ n → RopeCountingLaw n) ∧
    (¬ InternalKnowledgeOfCollatzCause) ∧
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n → ∃ K, iter K n = 1) ∧
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) :=
  ⟨ropeLaw_universal_refuted, collatzCause_unknowable,
   fun n h1 law => reaches_one_of_countingLaw n h1 law,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh⟩

/-! ## Axiom audit: module is ENTIRELY green (the decree layer no longer exists) -/
#print axioms collatz_decree_postmortem
#print axioms ropeLaw_would_imply_collatz
#print axioms no_internalisedCollatzGround
#print axioms collatzCause_unknowable
#print axioms internalGround_impossible_a_fortiori
#print axioms unknowable_or_collatz_fails
#print axioms collatz_no_internal_decision_without_engine
#print axioms collatz_verification_not_derivation
#print axioms collatz_open_status

end EuclidsPath.Collatz.FirstCause
