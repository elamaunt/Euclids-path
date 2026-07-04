/-
  PNPDataAnchor — FRONT DATA ANCHOR for the machine model of P/NP: named data-anchors
  over REAL mathlib structures TM2 (Turing.TM2ComputableInPolyTime,
  Mathlib/Computability/TuringMachine/Computable.lean:179), docked to
  the abstract frame of the repository (ClassicalComplexityFrame / FaithfulPFrame).

  Lesson from PNPRankPaymentFront: "the genuinely missing piece is a data-anchored real
  machine model". This module introduces two NAMED red def-inputs (named inputs):
    * TM2CompositionLaw — the composition law of polytime computability; in the pin this is
      VERBATIM proof_wanted TM2ComputableInPolyTime.comp (Computable.lean:284) —
      it creates NO declarations in the environment — nothing to refer to: the input is honestly red;
    * TM2FrameBridge — what the builder must supply to obtain
      a genuine faithful ClassicalComplexityFrame from a TM2 model (InP on
      ℕ-languages ⟺ TM2-decidability over the CANONICAL encoding encodeNat).

  Green witnesses of non-vacuity: tm2_id_computable (re-export of
  idComputableInPolyTime, Computable.lean:221 — the model is INHABITED),
  tm2_model_inhabited, tm2CompositionLaw_shape_inhabited_id.

  ⚠️ MACHINE HONESTY (goal-renaming audits — all theorems):
    * tm2DecidesWithSomeEncoding_free — the ∃-quantifier over the encoding SMUGGLES IN
      THE ANSWER (enc x := encodeBool (run x), the machine is an identity transport):
      "decidability with some encoding" is True for EVERY language;
      therefore the frame anchor must live over a FIXED canonical
      encoding (lesson SpectralAnchorAudit: Prop-non-vacuity is the wrong
      criterion; here it is exposed at the level of encodings);
    * faithful_frame_alone_is_free — Nonempty (FaithfulPFrame C) by itself is
      FREE (freeFrame); the full weight of TM2FrameBridge lies in the iff-clause;
    * frame_p_overclosure / tm2FrameBridge_overclosure — the free Prop-field
      polynomial_time in PolyManyOneReduction TAINTS the closure: one
      non-constant TM2-decidable ℕ-language in InP would flood InP with ALL
      ℕ-languages. The genuine builder must first replace the reductions
      with machine ones — this is fixed machine-wise, not in prose.

  NOT a solution to P/NP, NOT a Gödel move: anchors_do_not_decide_pnp — the anchors by
  themselves decide nothing (coverage marker in the style of notAProofOfBeal).
  The module does NOT import the quarantine (CausalClosureAxiom); no axiom/sorry/
  native_decide; taint 47 does not change.
-/
import Mathlib
import EuclidsPath.Engine.ClassicalPNPBridge
import EuclidsPath.Engine.CanonicalSelfReduction

set_option autoImplicit false

namespace EuclidsPath
namespace PNPDataAnchor

open EuclidsPath.ClassicalPNPBridge
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction.CanonicalSelfReduction

/-#############################################################################
  §1. Green witnesses: the TM2 mathlib model is inhabited
#############################################################################-/

/-- **🟢 Green witness of non-vacuity: the model is inhabited.** Re-export of
    `Turing.idComputableInPolyTime`
    (Mathlib/Computability/TuringMachine/Computable.lean:221): the identity
    function is computable in polynomial time by a REAL TM2 machine
    (`Turing.FinTM2`), not a Prop stub. Everything the anchors below assert
    is asserted about a non-empty type of machines. -/
noncomputable def tm2_id_computable {α αΓ : Type} [Fintype αΓ]
    (ea : α → List αΓ) :
    Turing.TM2ComputableInPolyTime ea ea id :=
  Turing.idComputableInPolyTime ea

/-- **🟢 Inhabitedness at a concrete point:** the type of polytime machines for `id : Bool → Bool`
    over the encoding `Computability.encodeBool` is non-empty. -/
theorem tm2_model_inhabited :
    Nonempty (Turing.TM2ComputableInPolyTime
      Computability.encodeBool Computability.encodeBool (id : Bool → Bool)) :=
  ⟨tm2_id_computable Computability.encodeBool⟩

/-#############################################################################
  §2. Red named input #1: the composition law (proof_wanted in the pin)
#############################################################################-/

/-- **🔴 RED NAMED INPUT #1 (data-anchor): TM2-polytime composition law.**

    The composition of polytime-computable functions is polytime-computable — stated
    over the real structures `Turing.TM2ComputableInPolyTime` of the pin. In mathlib
    v4.31 this is ABSENT: Mathlib/Computability/TuringMachine/Computable.lean:284
    contains verbatim

    ```
    proof_wanted TM2ComputableInPolyTime.comp
        {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
        {eγ : γ → List γΓ} {f : α → β} {g : β → γ} (h1 : TM2ComputableInPolyTime eα eβ f)
        (h2 : TM2ComputableInPolyTime eβ eγ g) :
      Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))
    ```

    `proof_wanted` does NOT create a declaration in the environment — there is nothing to refer to.
    Mathematics MUST supply: a construction of the composite machine (tapes of both
    machines + transfer of the output stack of the first to the input stack of the second) and
    a polynomial bound on its running time. This is NOT a goal renaming of P/NP:
    the composition law is a lemma about the MODEL; both sides of P vs NP are compatible with it. -/
def TM2CompositionLaw : Prop :=
  ∀ (α β γ αΓ βΓ γΓ : Type)
    (eα : α → List αΓ) (eβ : β → List βΓ) (eγ : γ → List γΓ)
    (f : α → β) (g : β → γ),
    Turing.TM2ComputableInPolyTime eα eβ f →
    Turing.TM2ComputableInPolyTime eβ eγ g →
    Nonempty (Turing.TM2ComputableInPolyTime eα eγ (g ∘ f))

/-- **🟢 The conclusion form of the anchor is inhabited** (non-vacuity of the statement, not its
    proof): for `f = g = id` the conclusion of the composition law is
    a theorem already now. The type `Nonempty (… (id ∘ id))` is non-empty thanks to
    `tm2_id_computable`. -/
theorem tm2CompositionLaw_shape_inhabited_id
    {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    Nonempty (Turing.TM2ComputableInPolyTime ea ea (id ∘ id : α → α)) := by
  have h : (id ∘ id : α → α) = id := Function.comp_id id
  rw [h]
  exact ⟨tm2_id_computable ea⟩

/-#############################################################################
  §3. Encoding audit: the ∃-encoding smuggles in the answer (machine-wise)
#############################################################################-/

/-- **🟡 Answer-transport machine (audit tool for §3).** For ANY function
    `run : α → Bool` and a cheating encoding `enc x := encodeBool (run x)`
    the identity machine `Turing.idComputer` "computes" `run`: the answer is already
    written in the input. The construction honestly reuses
    `idComputableInPolyTime.outputsFun` — input and output coincide verbatim. -/
noncomputable def tm2AnswerTransport {α : Type} (run : α → Bool) :
    Turing.TM2ComputableInPolyTime
      (fun x : α => Computability.encodeBool (run x))
      Computability.encodeBool run where
  toTM2ComputableAux :=
    (Turing.idComputableInPolyTime Computability.encodeBool).toTM2ComputableAux
  time := (Turing.idComputableInPolyTime Computability.encodeBool).time
  outputsFun a :=
    (Turing.idComputableInPolyTime Computability.encodeBool).outputsFun (run a)

/-- "A language is TM2-decidable with SOME encoding" — a tempting but
    INCORRECT anchor form (see `tm2DecidesWithSomeEncoding_free`). -/
def TM2DecidesWithSomeEncoding (L : ClassicalProblem) : Prop :=
  ∃ (enc : L.Instance → List Bool) (run : L.Instance → Bool),
    (∀ x : L.Instance, run x = true ↔ L.Accepts x) ∧
    Nonempty (Turing.TM2ComputableInPolyTime enc Computability.encodeBool run)

/-- **🟢 AUDIT (goal renaming exposed machine-wise): the ∃-encoding is FREE.**
    For EVERY language `TM2DecidesWithSomeEncoding` is a theorem: classical
    decider + cheating encoding + answer-transport machine (§3). Therefore,
    formulating the frame anchor via an ∃-encoding equals renaming True.
    That is exactly why `TM2DecidesNatLanguage` below is pinned to the FIXED
    canonical `Computability.encodeNat`. Lesson SpectralAnchorAudit
    (Prop-non-vacuity is the wrong criterion) — here exposed at the level of encodings. -/
theorem tm2DecidesWithSomeEncoding_free (L : ClassicalProblem) :
    TM2DecidesWithSomeEncoding L := by
  classical
  exact ⟨fun x => Computability.encodeBool (decide (L.Accepts x)),
    fun x => decide (L.Accepts x),
    fun x => ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩,
    ⟨tm2AnswerTransport _⟩⟩

/-#############################################################################
  §4. Red named input #2: bridge from the TM2 model to the faithful frame
#############################################################################-/

/-- An ℕ-language as a classical frame problem (instances are natural numbers). -/
def natProblem (Accepts : ℕ → Prop) : ClassicalProblem where
  Instance := ℕ
  Accepts := Accepts

/-- TM2-decidability of an ℕ-language in polynomial time over the CANONICAL
    binary encoding `Computability.encodeNat` (no ∃ over the encoding —
    see audit §3). The machine's answer is read via `Computability.encodeBool`. -/
def TM2DecidesNatLanguage (Accepts : ℕ → Prop) : Prop :=
  ∃ run : ℕ → Bool,
    (∀ n : ℕ, run n = true ↔ Accepts n) ∧
    Nonempty (Turing.TM2ComputableInPolyTime
      Computability.encodeNat Computability.encodeBool run)

/-- **🔴 RED NAMED INPUT #2 (data-anchor): bridge TM2 model → faithful frame.**

    Disclosure: the builder must supply a frame `C` such that
      1. `Nonempty (FaithfulPFrame C)` — concrete deciders for `InP`
         and both constant languages in P (rules out degenerate frames);
      2. `C.InP` on ℕ-languages is EXACTLY TM2-polytime-decidability over
         the canonical encoding (both sides of the iff; otherwise `¬ InP` says nothing
         about real machines).

    What is ABSENT from mathlib v4.31 (and what mathematics must supply):
      * closure under composition — proof_wanted
        `TM2ComputableInPolyTime.comp` (Computable.lean:284, §2);
      * no machine of the form `run : ℕ → Bool` over `encodeNat` — not even
        a constant one (the sole inhabitant of the model is `idComputableInPolyTime`,
        Computable.lean:221, type-to-itself);
      * recoders between encodings (recoding machines).

    ⚠️ Honesty audits: `faithful_frame_alone_is_free` — item 1 by itself is
    free; `tm2FrameBridge_overclosure` — under the CURRENT structure of
    `ClassicalComplexityFrame` (closure under FREE PolyManyOneReductions)
    item 2 is almost certainly non-trivially unfulfillable: one non-constant
    decidable language floods InP with all ℕ-languages. That is, the anchor records
    both the obligation and the machine-exposed trap: machine reductions first,
    then the bridge. -/
def TM2FrameBridge : Prop :=
  ∃ C : ClassicalComplexityFrame,
    Nonempty (FaithfulPFrame C) ∧
    ∀ Accepts : ℕ → Prop,
      C.InP (natProblem Accepts) ↔ TM2DecidesNatLanguage Accepts

/-- **🟢 With the anchor in place the front closes:** `TM2FrameBridge` gives a faithful frame
    in which `InP` on ℕ-languages carries GENUINE machine semantics, and all
    bridge machinery of the repository (`Step00ToClassicalBridge` +
    incompressibility ⟹ `ClassesSeparate`) operates over it.
    ⚠️ HONESTY: the last conjunct is `bridgeSlogan`, which holds for ANY
    frame; the added value of the anchor is exclusively the iff-clause
    (machine semantics of InP), not "separation has come closer". -/
theorem tm2FrameBridge_closes_machine_front (h : TM2FrameBridge) :
    ∃ C : ClassicalComplexityFrame,
      Nonempty (FaithfulPFrame C) ∧
      (∀ Accepts : ℕ → Prop,
        C.InP (natProblem Accepts) ↔ TM2DecidesNatLanguage Accepts) ∧
      ∀ N : Step00LocalNode, Step00ToClassicalBridge C N →
        N.LocalSearchIncompressible → C.ClassesSeparate := by
  obtain ⟨C, hFaithful, hIff⟩ := h
  exact ⟨C, hFaithful, hIff,
    fun _N B hInc => B.classicalSeparation_of_localIncompressible hInc⟩

/-#############################################################################
  §5. Goal-renaming audits for named input #2
#############################################################################-/

/-- The "everything in P" frame: a local twin of `allPFrame` from PNPRankPaymentFront
    (that module is not imported here — the audit is self-contained). -/
def freeFrame : ClassicalComplexityFrame where
  InP := fun _ => True
  InNP := fun _ => True
  P_closed_under_poly_preimage := fun _ _ => trivial

/-- Classical decider for any language (twin of `classicalPDecider`):
    `PDecider` carries no complexity content. -/
noncomputable def freeDecider (L : ClassicalProblem) : PDecider L := by
  classical
  exact
    { run := fun x => decide (L.Accepts x)
      sound := fun x hx => of_decide_eq_true hx
      complete := fun x hx => decide_eq_true hx }

/-- `freeFrame` passes the faithfulness gate of the repository. -/
theorem freeFrame_faithful : Nonempty (FaithfulPFrame freeFrame) :=
  ⟨{ concreteP := ⟨fun L _ => ⟨freeDecider L⟩⟩
     true_inP := trivial
     false_inP := trivial }⟩

/-- **🟢 AUDIT (the first half of named input #2 is free):** the existence of
    a faithful frame is NOT the content of the anchor: `freeFrame` gives it for free.
    The full weight of `TM2FrameBridge` lies in the iff-clause with `TM2DecidesNatLanguage`. -/
theorem faithful_frame_alone_is_free :
    ∃ C : ClassicalComplexityFrame, Nonempty (FaithfulPFrame C) :=
  ⟨freeFrame, freeFrame_faithful⟩

/-- **🟢 AUDIT (closure is tainted by the free poly-field):** in ANY frame of
    the repository one non-constant ℕ-language in InP floods InP with all
    ℕ-languages: the classical reduction `n ↦ if A n then n₁ else n₀` is legal,
    because the field `polynomial_time` in `PolyManyOneReduction` is a free Prop
    (`polynomial_time := True`). No machine behind `map` is required —
    that is the hole. -/
theorem frame_p_overclosure
    (C : ClassicalComplexityFrame)
    (A : ℕ → Prop) {A' : ℕ → Prop} {n₁ n₀ : ℕ}
    (h₁ : A' n₁) (h₀ : ¬ A' n₀)
    (hInP : C.InP (natProblem A')) :
    C.InP (natProblem A) := by
  classical
  refine C.P_closed_under_poly_preimage
    { map := fun n : ℕ => if A n then n₁ else n₀
      preserves := ?_
      polynomial_time := True
      polynomial_time_proof := trivial } hInP
  intro n
  by_cases hn : A n
  · rw [if_pos hn]
    exact iff_of_true hn h₁
  · rw [if_neg hn]
    exact iff_of_false hn h₀

/-- **🟢 AUDIT (the trap of named input #2 exposed machine-wise):** the anchor `TM2FrameBridge`
    + AT LEAST ONE non-constant TM2-decidable ℕ-language ⟹ ALL ℕ-languages are TM2-decidable
    (which is mathematically absurd, although unprovably false in the pin — there is no
    diagonalisation over `FinTM2` in mathlib). The conclusion is fixed as a theorem: non-trivial
    satisfaction of the anchor under the current `ClassicalComplexityFrame` requires first
    REPLACING the free reductions with machine ones. The anchor is not painted as satisfiable —
    the trap is exposed in the open. -/
theorem tm2FrameBridge_overclosure
    (hBridge : TM2FrameBridge)
    (hWitness : ∃ (A' : ℕ → Prop) (n₁ n₀ : ℕ),
      TM2DecidesNatLanguage A' ∧ A' n₁ ∧ ¬ A' n₀) :
    ∀ A : ℕ → Prop, TM2DecidesNatLanguage A := by
  obtain ⟨C, _hFaithful, hIff⟩ := hBridge
  obtain ⟨A', n₁, n₀, hDec, h₁, h₀⟩ := hWitness
  intro A
  exact (hIff A).1 (frame_p_overclosure C A h₁ h₀ ((hIff A').2 hDec))

/-#############################################################################
  §6. Coverage marker: the anchors do NOT decide P/NP
#############################################################################-/

/-- **🟢 COVERAGE HONESTY (in the style of `notAProofOfBeal`):** this module does NOT
    prove and does NOT refute P = NP and does NOT bring the verdict closer. It only contains:
    two NAMED red def-inputs (`TM2CompositionLaw` — proof_wanted in
    mathlib; `TM2FrameBridge` — model→frame bridge), green witnesses
    of TM2-model inhabitedness, and machine honesty audits (∃-encoding
    smuggles in the answer; the faithful part is free; closure is tainted by
    the free poly-field). The anchors are docking points for FUTURE mathematics,
    not a substitute for it. -/
abbrev AnchorsDoNotDecidePNP : Prop := True

theorem anchors_do_not_decide_pnp : AnchorsDoNotDecidePNP := trivial

-- Machine-visible purity directly in the build log: all new exports
-- are axiom-free (no more than the standard triple
-- [propext, Classical.choice, Quot.sound]); taint 47 does not change.
#print axioms tm2_id_computable
#print axioms tm2_model_inhabited
#print axioms TM2CompositionLaw
#print axioms tm2CompositionLaw_shape_inhabited_id
#print axioms tm2AnswerTransport
#print axioms TM2DecidesWithSomeEncoding
#print axioms tm2DecidesWithSomeEncoding_free
#print axioms natProblem
#print axioms TM2DecidesNatLanguage
#print axioms TM2FrameBridge
#print axioms tm2FrameBridge_closes_machine_front
#print axioms freeFrame
#print axioms freeDecider
#print axioms freeFrame_faithful
#print axioms faithful_frame_alone_is_free
#print axioms frame_p_overclosure
#print axioms tm2FrameBridge_overclosure
#print axioms anchors_do_not_decide_pnp

end PNPDataAnchor
end EuclidsPath
