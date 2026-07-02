/-
  CausalClosureAxiom — КАРАНТИННЫЙ модуль: ЕДИНСТВЕННЫЙ `axiom` всего репозитория.
  Проза: prose/24_BoundaryDecomp.md (раздел «Causal-closure как внешняя аксиома»).

  ⚠️⚠️⚠️ ВНИМАНИЕ. Этот модуль СОЗНАТЕЛЬНО объявляет аксиому
    `step00CausalClosure : TheStrictLastStep00Obligation`
  — это ОТКРЫТЫЙ ФИНАЛЬНЫЙ УЗЕЛ, принятый декретом, а НЕ доказанный факт.
  Всё, что от неё зависит (включая `twinLowersInfinite_from_step00CausalClosure :
  TwinLowers.Infinite`), — УСЛОВНО НА АКСИОМЕ и НЕ является доказательством
  гипотезы близнецов. `Step00.twin_prime_conjecture` остаётся `sorry` и НЕ
  замыкается через этот модуль.

  Карантин машинно отслеживается: узловой верификатор репортит каждую
  декларацию, заражённую нестандартной аксиомой (`AXIOM-TAINTED`). Ожидаемое
  состояние: заражены РОВНО декларации этого модуля — и никакие другие.

  Смысл кирпича (честный): зафиксировать последний Step00-принцип как ЯВНУЮ
  внешнюю аксиому, а не как скрытую теорему; и показать (уже доказано в
  ConcreteStep00Graph), что его внутреннее самозаверение строит запрещённый
  двигатель. Машинная честность: аксиома ⟺ старый узел
  (`strictLastStep00Obligation_iff_lastStep00Obligation`), и она УЖЕ утверждает
  близнецов на каждом масштабе (`causalClosureAxiom_asserts_twins_at_every_scale`)
  — принять её = принять близнецов, декрет не слабее вывода.
-/
import EuclidsPath.Engine.ConcreteStep00Graph

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. The external causal-closure principle
#############################################################################-/

/--
The Step00 causal-closure axiom, stated in the strict return-certificate form.

Unfolded, it says that there is a fixed scale `A` and, for every alleged last
twin bound `M0`, a finite semantic flow-ledger projection `ΠOf M0` such that
same-key collisions of extended generated-flow genealogies are not free
information-loss.  They must be resolved by the strict local resolver, i.e. by
an explicit return certificate or the already audited payment alternative.

This is the exact final principle previously called
`TheStrictLastStep00Obligation`.
-/
abbrev Step00CausalClosureAxiom : Prop :=
  TheStrictLastStep00Obligation

/--
The single external axiom of this patch — AND OF THE WHOLE REPOSITORY.

Reading: Step00 causal closure is accepted as an outside universe-generating
principle.  It is not derived by the internal no-engine machinery.

⚠️ Everything depending on this axiom is CONDITIONAL and machine-flagged by
the node verifier as AXIOM-TAINTED.
-/
axiom step00CausalClosure : Step00CausalClosureAxiom

/-#############################################################################
  §2. What the axiom generates (⚠️ conditional on the axiom, NOT proofs)
#############################################################################-/

/--
As an external axiom, Step00 causal closure proves infinitude of lower twin
centres.  ⚠️ AXIOM-TAINTED: this is NOT a proof of the twin-prime conjecture;
it is the reduction closed by decree.
-/
theorem twinLowersInfinite_from_step00CausalClosure :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation step00CausalClosure

/--
Equivalent named theorem: adding the causal-closure axiom closes the Step00
universe.  ⚠️ AXIOM-TAINTED.
-/
theorem step00CausalClosure_generates_twins :
    TwinLowers.Infinite :=
  twinLowersInfinite_from_step00CausalClosure

/-#############################################################################
  §3. Why the axiom is external, not internally self-certified
#############################################################################-/

/--
An internal self-derivation attempt of the causal-closure axiom.

This is the already audited boundary-crossing shape: the principle is available
as a proposition and is then converted back into an internal stable Step00
decision attempt.  The previous patches prove that such internalisation builds
the forbidden engine.
-/
abbrev InternalSelfDerivationOfStep00CausalClosure : Prop :=
  BoundaryCrossingSelfProof Step00CausalClosureAxiom

/--
Any internal self-derivation of Step00 causal closure builds the forbidden
concrete Euclidean engine.  (Axiom-free.)
-/
theorem internalSelfDerivation_step00CausalClosure_builds_engine
    (B : InternalSelfDerivationOfStep00CausalClosure) :
    SomeConcreteEuclideanEngine :=
  boundaryCrossingSelfProof_builds_engine B

/--
Therefore Step00 causal closure cannot be internally self-derived in the
stable no-engine Step00 architecture.  (Axiom-free.)
-/
theorem no_internalSelfDerivation_step00CausalClosure :
    ¬ InternalSelfDerivationOfStep00CausalClosure :=
  no_boundaryCrossingSelfProof

/--
If one nevertheless supplies an internal self-derivation, contradiction follows.
(Axiom-free.)
-/
theorem internalSelfDerivation_step00CausalClosure_contradiction
    (B : InternalSelfDerivationOfStep00CausalClosure) : False :=
  no_internalSelfDerivation_step00CausalClosure B

/-#############################################################################
  §4. External-only package
#############################################################################-/

/--
The causal-closure axiom as an external-only principle: it is accepted as an
outside axiom, and it cannot be self-certified internally without the forbidden
engine.
-/
abbrev Step00CausalClosureExternalOnly : Prop :=
  Step00CausalClosureAxiom ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure

/--
The external-only status of the causal-closure axiom.  ⚠️ AXIOM-TAINTED
(первый конъюнкт — сама аксиома).
-/
theorem step00CausalClosure_externalOnly :
    Step00CausalClosureExternalOnly := by
  exact ⟨step00CausalClosure, no_internalSelfDerivation_step00CausalClosure⟩

/--
The axiom both generates the twin conclusion and refuses internal
self-certification without a forbidden engine.  ⚠️ AXIOM-TAINTED.
-/
abbrev Step00CausalClosureGeneratesButDoesNotSelfCertify : Prop :=
  TwinLowers.Infinite ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure

/-- Realisation of the final audit slogan.  ⚠️ AXIOM-TAINTED. -/
theorem step00CausalClosure_generatesButDoesNotSelfCertify :
    Step00CausalClosureGeneratesButDoesNotSelfCertify := by
  exact ⟨twinLowersInfinite_from_step00CausalClosure,
         no_internalSelfDerivation_step00CausalClosure⟩

/-#############################################################################
  §5. Self-proving engine contradiction, specialised to the axiom
#############################################################################-/

/--
A self-proving Step00 causal-closure engine is just an internal self-derivation
of the external causal-closure axiom.  The name records the intended audit
reading: if the axiom tries to prove itself from within the no-engine universe,
it becomes a forbidden engine construction.
-/
abbrev SelfProvingStep00CausalClosureEngine : Prop :=
  InternalSelfDerivationOfStep00CausalClosure

/-- A self-proving causal-closure engine builds a concrete Euclidean engine.
(Axiom-free.) -/
theorem selfProvingStep00CausalClosureEngine_builds_engine
    (H : SelfProvingStep00CausalClosureEngine) :
    SomeConcreteEuclideanEngine :=
  internalSelfDerivation_step00CausalClosure_builds_engine H

/-- No self-proving causal-closure engine exists.  (Axiom-free.) -/
theorem no_selfProvingStep00CausalClosureEngine :
    ¬ SelfProvingStep00CausalClosureEngine :=
  no_internalSelfDerivation_step00CausalClosure

/--
Formal version of the slogan:

  “a perpetual engine proving itself is contradiction.”

Here the perpetual engine is the internal self-proof of the external causal
closure principle; by the earlier audit it builds a forbidden concrete engine,
and forbidden engines are impossible by `lexRank` acyclicity.  (Axiom-free.)
-/
theorem selfProvingStep00CausalClosureEngine_is_contradiction
    (H : SelfProvingStep00CausalClosureEngine) : False :=
  no_selfProvingStep00CausalClosureEngine H

/-#############################################################################
  §6. Scope marker: axiomatisation, not global independence
#############################################################################-/

/--
Marker proposition recording the intended scope.

This is deliberately just `True`: the real content is in the theorems above.
It prevents the axiom patch from being read as a Gödel-style independence proof
for the ordinary twin-prime conjecture.  No external proof system, model theory,
or relative consistency theorem is asserted here.
-/
abbrev ThisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem : Prop :=
  True

theorem thisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem :
    ThisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem := by
  trivial

/-#############################################################################
  §7. Машинная честность аксиомы
#############################################################################-/

/-- **ЧЕСТНОСТЬ (машинно): аксиома УЖЕ утверждает близнецов на каждом масштабе.**
    Из аксиомы на каждом `M0` извлекается twin выше `M0` (через
    `twin_above_of_strictResolves`): декрет не слабее вывода — принять аксиому
    = принять близнецов по-масштабно. Аксиома ⟺ старый узел
    (`strictLastStep00Obligation_iff_lastStep00Obligation`). ⚠️ AXIOM-TAINTED. -/
theorem causalClosureAxiom_asserts_twins_at_every_scale :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m := by
  intro M0
  obtain ⟨A, projOf, h⟩ := step00CausalClosure
  exact twin_above_of_strictResolves (projOf M0) (h M0)



/-#############################################################################
  ФИНАЛЬНЫЙ СТАТУС: АКСИОМНЫЙ vs БЕЗАКСИОМНЫЙ РЕЖИМ (кирпич:
  final_axiom_vs_theorem_status). Размещён в КАРАНТИНЕ, т.к. §2 использует
  аксиому (соответствующие декларации AXIOM-TAINTED у верификатора);
  аксиомо-свободные части (§1, §3, §4) остаются чистыми.
#############################################################################-/

/-#############################################################################
  §1. The two final regimes
#############################################################################-/

/--
Axiomatic Step00 closure: causal closure is accepted as an external axiom.

In the preceding axiom patch this is witnessed by
`step00CausalClosure : Step00CausalClosureAxiom`.
-/
abbrev Step00AxiomaticClosure : Prop :=
  Step00CausalClosureAxiom

/--
Non-axiomatic Step00 closure means that the last causal-closure principle has
actually been proved inside the non-axiomatic development.

Therefore, as a proposition, the remaining non-axiomatic obligation is exactly
`Step00CausalClosureAxiom`.  The name is intentionally different to make the
status explicit: this is not an additional theorem; it is the last theorem to be
proved if one refuses to add the causal-closure axiom.
-/
abbrev Step00NonAxiomaticRemainingObligation : Prop :=
  Step00CausalClosureAxiom

/--
The final non-axiomatic obligation is definitionally the causal-closure axiom.
-/
theorem nonAxiomaticRemainingObligation_iff_causalClosure :
    Step00NonAxiomaticRemainingObligation ↔ Step00CausalClosureAxiom :=
  Iff.rfl

/-#############################################################################
  §2. If the axiom is accepted, the Step00 universe is closed
#############################################################################-/

/--
External causal closure closes the Step00 proof and yields infinitely many lower
twin centres.
-/
theorem twinLowersInfinite_of_axiomaticClosure
    (H : Step00AxiomaticClosure) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation H

/--
The already accepted axiom from the previous patch gives the conclusion.
-/
theorem twinLowersInfinite_by_accepted_axiom :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_axiomaticClosure step00CausalClosure

/--
Named final theorem for the axiomatised Step00 theory.
-/
abbrev Step00AxiomatisedTheoryClosed : Prop :=
  TwinLowers.Infinite

/--
The axiomatised theory is closed.
-/
theorem step00AxiomatisedTheoryClosed :
    Step00AxiomatisedTheoryClosed :=
  twinLowersInfinite_by_accepted_axiom

/-#############################################################################
  §3. Without the axiom, exactly one theorem remains
#############################################################################-/

/--
A deliberately narrow predicate for “the Step00 pipeline closes without adding a
new axiom”.

By construction of the audit, such a close consists precisely of a proof of the
causal-closure principle.  This prevents the final status from being blurred by
additional wrappers.
-/
abbrev Step00PipelineClosesWithoutNewAxiom : Prop :=
  Step00NonAxiomaticRemainingObligation

/--
The pipeline closes without a new axiom if and only if the causal-closure
principle has been proved.
-/
theorem pipelineClosesWithoutNewAxiom_iff_causalClosure :
    Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom :=
  Iff.rfl

/--
If the causal-closure principle is unavailable, the audited Step00 pipeline does
not close without a new axiom.
-/
theorem no_pipelineClose_without_causalClosure
    (h : ¬ Step00CausalClosureAxiom) :
    ¬ Step00PipelineClosesWithoutNewAxiom := by
  intro H
  exact h H

/--
Conversely, any non-axiomatic close supplies exactly the missing causal-closure
principle.
-/
theorem causalClosure_of_pipelineCloseWithoutNewAxiom
    (H : Step00PipelineClosesWithoutNewAxiom) :
    Step00CausalClosureAxiom :=
  H

/--
A non-axiomatic close gives the twin conclusion by the already verified Step00
machinery.
-/
theorem twinLowersInfinite_of_pipelineCloseWithoutNewAxiom
    (H : Step00PipelineClosesWithoutNewAxiom) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation
    (causalClosure_of_pipelineCloseWithoutNewAxiom H)

/-#############################################################################
  §4. The axiom remains external
#############################################################################-/

/--
The accepted axiom does not become internally self-certified.  This is the
status theorem from the axiom patch, repackaged with the final terminology.
-/
theorem acceptedCausalClosure_is_not_internal_self_derivation :
    ¬ InternalSelfDerivationOfStep00CausalClosure :=
  no_internalSelfDerivation_step00CausalClosure

/--
Any attempt to turn the external causal-closure principle into an internal
self-derivation builds the forbidden Euclidean engine.
-/
theorem internalSelfDerivation_of_finalObligation_builds_engine
    (B : InternalSelfDerivationOfStep00CausalClosure) :
    SomeConcreteEuclideanEngine :=
  internalSelfDerivation_step00CausalClosure_builds_engine B

/--
Therefore an internal self-derivation of the final obligation is impossible in
the stable no-engine architecture.
-/
theorem no_internalSelfDerivation_of_finalObligation :
    ¬ InternalSelfDerivationOfStep00CausalClosure :=
  acceptedCausalClosure_is_not_internal_self_derivation

/-#############################################################################
  §5. Final dependency table as propositions
#############################################################################-/

/--
Final dependency table, encoded as a structure so that downstream audit files can
inspect the two regimes without rereading the prose.
-/
structure FinalStep00Status where
  /-- With the external axiom, twins follow. -/
  axiomatic_close : Step00AxiomaticClosure → TwinLowers.Infinite
  /-- Without adding the axiom, the exact remaining obligation is causal closure. -/
  nonaxiomatic_remaining :
    Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom
  /-- Internal self-certification of the causal-closure principle is impossible. -/
  no_internal_self_derivation :
    ¬ InternalSelfDerivationOfStep00CausalClosure

/--
The final audited status of the Step00 development.
-/
def finalStep00Status : FinalStep00Status where
  axiomatic_close := twinLowersInfinite_of_axiomaticClosure
  nonaxiomatic_remaining := pipelineClosesWithoutNewAxiom_iff_causalClosure
  no_internal_self_derivation := no_internalSelfDerivation_of_finalObligation

/--
Compressed slogan as a theorem:

  after adding the axiom, the theory is closed;
  before adding the axiom, the only remaining theorem is the axiom itself;
  the axiom cannot be internally self-certified without forbidden engine.
-/
theorem finalStatus_slogan :
    TwinLowers.Infinite ∧
    (Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom) ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure := by
  exact ⟨twinLowersInfinite_by_accepted_axiom,
         pipelineClosesWithoutNewAxiom_iff_causalClosure,
         no_internalSelfDerivation_of_finalObligation⟩

/-#############################################################################
  §6. Scope marker
#############################################################################-/

/--
Scope marker.  This file does not assert a global independence theorem for the
ordinary twin-prime conjecture.  It asserts the final dependency status of the
audited Step00 architecture:

  * axiom accepted  ⇒ closed;
  * axiom not accepted ⇒ exactly causal closure remains;
  * self-proving the axiom internally ⇒ forbidden engine.
-/
abbrev ThisFileIsFinalStatusNotNewMathematics : Prop :=
  True

/-! Машинная честность status-формы -/

/-- Безаксиомный остаток ⟺ старый узел: заявление кирпича «никакая обёртка не
    опускает открытое содержание ниже этого предложения» машинно подтверждено
    всей семьёй эквивалентностей (energy/nested/seam/gauge/no-energy/
    compression/atomic/stable/strict ⟺ TheLastStep00Obligation). -/
theorem nonAxiomaticRemainingObligation_iff_lastStep00Obligation :
    Step00NonAxiomaticRemainingObligation ↔ TheLastStep00Obligation :=
  strictLastStep00Obligation_iff_lastStep00Obligation

/-- Сужение распространяется на безаксиомный остаток: его масштаб живёт
    только в `A ≥ 5` (ветвь `A ≤ 4` машинно опровергнута). -/
theorem nonAxiomaticRemainingObligation_forces_scale_ge_five
    (H : Step00NonAxiomaticRemainingObligation) :
    ∃ A : ℕ, 5 ≤ A ∧
      ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
        ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0) :=
  lastStep00Obligation_forces_scale_ge_five
    (strictLastStep00Obligation_iff_lastStep00Obligation.mp H)



/-#############################################################################
  ФИНАЛЬНЫЙ МЕТА-КИРПИЧ: ПОБЕГ ИЛИ ВОЗВРАТ (кирпич: final_meta_escape_or_return).
  Размещён здесь из-за ссылок на имена модуля (Step00CausalClosureAxiom,
  twinLowersInfinite_of_axiomaticClosure), но АКСИОМУ НЕ ИСПОЛЬЗУЕТ — все
  декларации ниже axiom-clean (верификатор подтверждает: AXIOM-TAINTED не
  прибавилось). Дихотомия: внешнее доказательство либо транслируется назад в
  Step00 (⟹ двигатель ⟹ пусто), либо подлинно сбегает из архитектуры.
  Фиксы: ¬Step00MediatedStatement (data-структура) → `→ False`.
  Машинная честность: возврат ⟺ пустота, «побег» ⟺ существование —
  дихотомия тавтологична (Nonempty/IsEmpty), несущая часть — axiomGivesTwins.
#############################################################################-/

/-#############################################################################
  §1. One-sided Step00 mediation
#############################################################################-/

/--
A one-sided proof interface: every external proof certificate of `φ` can be
translated into an audited Step00 internal decision attempt.

This is weaker than `Step00MediatedStatement`, because it only talks about
proofs, not refutations.
-/
structure Step00ProofInterface
    (T : ExternalProofTheory) (φ : T.Sentence) where
  proofToInternal : T.proves φ → InternalStableDecisionAttempt

/--
A one-sided refutation interface: every external refutation certificate of `φ`
can be translated into an audited Step00 internal decision attempt.
-/
structure Step00RefutationInterface
    (T : ExternalProofTheory) (φ : T.Sentence) where
  refutationToInternal : T.refutes φ → InternalStableDecisionAttempt

/--
An external proof route returns to Step00 if such a one-sided proof translator
exists.
-/
abbrev ProofReturnsToStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  Nonempty (Step00ProofInterface T φ)

/--
An external refutation route returns to Step00 if such a one-sided refutation
translator exists.
-/
abbrev RefutationReturnsToStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  Nonempty (Step00RefutationInterface T φ)

/--
A proof route genuinely escapes Step00 when it does not return to the Step00
internal decision interface.
-/
abbrev ProofEscapesStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ¬ ProofReturnsToStep00Architecture T φ

/--
A refutation route genuinely escapes Step00 when it does not return to the
Step00 internal decision interface.
-/
abbrev RefutationEscapesStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ¬ RefutationReturnsToStep00Architecture T φ

/-#############################################################################
  §2. Returning to Step00 builds the forbidden engine
#############################################################################-/

/--
A returned proof certificate constructs the same forbidden concrete Euclidean
engine as every other internal Step00 decision attempt.
-/
theorem proofReturningToStep00_builds_engine
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00ProofInterface T φ) (p : T.proves φ) :
    SomeConcreteEuclideanEngine := by
  exact internalStableDecisionAttempt_builds_engine (M.proofToInternal p)

/--
A returned refutation certificate also constructs the forbidden concrete
Euclidean engine.
-/
theorem refutationReturningToStep00_builds_engine
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00RefutationInterface T φ) (r : T.refutes φ) :
    SomeConcreteEuclideanEngine := by
  exact internalStableDecisionAttempt_builds_engine (M.refutationToInternal r)

/--
Therefore a proof route that returns to Step00 has no external proof
certificates.
-/
theorem no_externalProof_under_proofReturn
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hReturn : ProofReturnsToStep00Architecture T φ) :
    IsEmpty (T.proves φ) := by
  refine ⟨?_⟩
  intro p
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine M p)

/--
Therefore a refutation route that returns to Step00 has no external refutation
certificates.
-/
theorem no_externalRefutation_under_refutationReturn
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hReturn : RefutationReturnsToStep00Architecture T φ) :
    IsEmpty (T.refutes φ) := by
  refine ⟨?_⟩
  intro r
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine M r)

/-#############################################################################
  §3. Actual external decisions force genuine escape
#############################################################################-/

/--
If an external proof certificate actually exists, then no proof translator back
into the Step00 no-engine architecture can exist.  Hence the proof genuinely
escapes the Step00 architecture.
-/
theorem existing_externalProof_forces_proofEscape
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ) :
    ProofEscapesStep00Architecture T φ := by
  intro hReturn
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine M p)

/--
If an external refutation certificate actually exists, then no refutation
translator back into the Step00 no-engine architecture can exist.  Hence the
refutation genuinely escapes the Step00 architecture.
-/
theorem existing_externalRefutation_forces_refutationEscape
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ) :
    RefutationEscapesStep00Architecture T φ := by
  intro hReturn
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine M r)

/--
Equivalently: an actual proof plus a claim that the proof does not escape Step00
is a contradiction.
-/
theorem externalProof_without_escape_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ)
    (hNoEscape : ¬ ProofEscapesStep00Architecture T φ) :
    False := by
  exact hNoEscape (existing_externalProof_forces_proofEscape p)

/--
Equivalently: an actual refutation plus a claim that the refutation does not
escape Step00 is a contradiction.
-/
theorem externalRefutation_without_escape_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ)
    (hNoEscape : ¬ RefutationEscapesStep00Architecture T φ) :
    False := by
  exact hNoEscape (existing_externalRefutation_forces_refutationEscape r)

/-#############################################################################
  §4. Relation with the earlier two-sided mediated-statement interface
#############################################################################-/

/--
A two-sided mediated statement supplies both one-sided interfaces.
-/
def Step00MediatedStatement.toProofInterface
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    Step00ProofInterface T φ where
  proofToInternal := M.proofToInternal

/--
A two-sided mediated statement also supplies the one-sided refutation interface.
-/
def Step00MediatedStatement.toRefutationInterface
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    Step00RefutationInterface T φ where
  refutationToInternal := M.refutationToInternal

/--
An actual external proof forbids the statement from being Step00-mediated.
-/
theorem actualProof_forbids_step00MediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ)
    (M : Step00MediatedStatement T φ) : False :=
  no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine M.toProofInterface p)

/--
An actual external refutation also forbids Step00 mediation.
-/
theorem actualRefutation_forbids_step00MediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ)
    (M : Step00MediatedStatement T φ) : False :=
  no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine M.toRefutationInterface r)

/-#############################################################################
  §5. The optional strong meta-completeness principle
#############################################################################-/

/--
A strong meta-completeness principle for a chosen external twin-prime sentence:
all of its external proofs and refutations return to Step00.

This is deliberately not proved here.  It is the exact strong meta-assumption
one would need in order to say that no external route can escape this
architecture.
-/
structure Step00CompletenessForTwinPrimeProofs
    (T : ExternalProofTheory) (φ : T.Sentence) where
  proofInterface : Step00ProofInterface T φ
  refutationInterface : Step00RefutationInterface T φ

/--
The strong completeness principle is equivalent to a two-sided mediated
statement, as far as the existing audit interface is concerned.
-/
def Step00CompletenessForTwinPrimeProofs.toMediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    Step00MediatedStatement T φ where
  proofToInternal := C.proofInterface.proofToInternal
  refutationToInternal := C.refutationInterface.refutationToInternal

/--
Conversely, a two-sided mediated statement is exactly such a completeness
certificate for that external sentence.
-/
def Step00CompletenessForTwinPrimeProofs.ofMediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    Step00CompletenessForTwinPrimeProofs T φ where
  proofInterface := M.toProofInterface
  refutationInterface := M.toRefutationInterface

/--
If all external twin-prime proofs/refutations are Step00-mediated, then neither
kind of certificate exists in the no-engine architecture.
-/
theorem step00Completeness_noProof_noRefutation
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    IsEmpty (T.proves φ) ∧ IsEmpty (T.refutes φ) := by
  constructor
  · exact no_externalProof_under_proofReturn ⟨C.proofInterface⟩
  · exact no_externalRefutation_under_refutationReturn ⟨C.refutationInterface⟩

/--
If the strong completeness principle holds, an actual external proof is
impossible.
-/
theorem step00Completeness_forbids_externalProof
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    ¬ Nonempty (T.proves φ) := by
  intro hp
  rcases hp with ⟨p⟩
  exact no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine C.proofInterface p)

/--
If the strong completeness principle holds, an actual external refutation is
also impossible.
-/
theorem step00Completeness_forbids_externalRefutation
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    ¬ Nonempty (T.refutes φ) := by
  intro hr
  rcases hr with ⟨r⟩
  exact no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine C.refutationInterface r)

/-#############################################################################
  §6. The final meta brick
#############################################################################-/

/--
The final meta-audit package for an external sentence `φ` intended to represent
`TwinLowers.Infinite` in an external proof theory.

It records exactly three facts:

* the internal Step00 theorem closes once the causal-closure axiom is accepted;
* any actual external proof must genuinely escape Step00;
* any actual external refutation must genuinely escape Step00;
* if one additionally assumes strong Step00 completeness for all external
  twin-prime decisions, then there are no such external decisions at all.
-/
structure LastMetaStep00Brick
    (T : ExternalProofTheory) (φ : T.Sentence) where
  axiomGivesTwins : Step00CausalClosureAxiom → TwinLowers.Infinite
  proofExistsForcesEscape :
    Nonempty (T.proves φ) → ProofEscapesStep00Architecture T φ
  refutationExistsForcesEscape :
    Nonempty (T.refutes φ) → RefutationEscapesStep00Architecture T φ
  completenessForbidsDecision :
    Step00CompletenessForTwinPrimeProofs T φ →
      IsEmpty (T.proves φ) ∧ IsEmpty (T.refutes φ)

/--
The audited final meta brick.
-/
def lastMetaStep00Brick
    (T : ExternalProofTheory) (φ : T.Sentence) :
    LastMetaStep00Brick T φ where
  axiomGivesTwins := by
    intro H
    exact twinLowersInfinite_of_axiomaticClosure H
  proofExistsForcesEscape := by
    intro hp
    rcases hp with ⟨p⟩
    exact existing_externalProof_forces_proofEscape p
  refutationExistsForcesEscape := by
    intro hr
    rcases hr with ⟨r⟩
    exact existing_externalRefutation_forces_refutationEscape r
  completenessForbidsDecision := by
    intro C
    exact step00Completeness_noProof_noRefutation C

/--
Compressed slogan as a theorem:

  inside Step00, causal closure gives twins;
  outside Step00, any actual proof/refutation must genuinely escape;
  if every route is forced back into Step00, no route exists.
-/
theorem finalMetaBrick_slogan
    {T : ExternalProofTheory} {φ : T.Sentence} :
    (Step00CausalClosureAxiom → TwinLowers.Infinite) ∧
    (Nonempty (T.proves φ) → ProofEscapesStep00Architecture T φ) ∧
    (Nonempty (T.refutes φ) → RefutationEscapesStep00Architecture T φ) ∧
    (Step00CompletenessForTwinPrimeProofs T φ →
      IsEmpty (T.proves φ) ∧ IsEmpty (T.refutes φ)) := by
  constructor
  · intro H
    exact twinLowersInfinite_of_axiomaticClosure H
  constructor
  · intro hp
    rcases hp with ⟨p⟩
    exact existing_externalProof_forces_proofEscape p
  constructor
  · intro hr
    rcases hr with ⟨r⟩
    exact existing_externalRefutation_forces_refutationEscape r
  · intro C
    exact step00Completeness_noProof_noRefutation C

/-#############################################################################
  §7. Scope guard
#############################################################################-/

/--
Scope marker: the file proves a relative escape-or-return theorem, not absolute
independence of the twin-prime conjecture from any standard foundation.
-/
abbrev ThisIsTheLastMetaBrickNotAnAbsoluteIndependenceTheorem : Prop := True

theorem thisIsTheLastMetaBrickNotAnAbsoluteIndependenceTheorem :
    ThisIsTheLastMetaBrickNotAnAbsoluteIndependenceTheorem := by
  trivial

/-! Машинная честность meta-формы -/

/-- Возврат в Step00 ⟺ пустота внешних доказательств (одностороннее
    «мост = пустота»). -/
theorem proofReturns_iff_noProofs
    {T : ExternalProofTheory} {φ : T.Sentence} :
    ProofReturnsToStep00Architecture T φ ↔ IsEmpty (T.proves φ) := by
  constructor
  · exact no_externalProof_under_proofReturn
  · intro hEmpty
    exact ⟨⟨fun p => (hEmpty.false p).elim⟩⟩

/-- Возврат опровержений ⟺ пустота внешних опровержений. -/
theorem refutationReturns_iff_noRefutations
    {T : ExternalProofTheory} {φ : T.Sentence} :
    RefutationReturnsToStep00Architecture T φ ↔ IsEmpty (T.refutes φ) := by
  constructor
  · exact no_externalRefutation_under_refutationReturn
  · intro hEmpty
    exact ⟨⟨fun r => (hEmpty.false r).elim⟩⟩

/-- ЧЕСТНОСТЬ: «побег» ⟺ существование доказательства. Дихотомия
    escape-or-return — переименование Nonempty/IsEmpty: «настоящее
    доказательство обязано сбежать» тавтологично («непустой тип не пуст»).
    Несущая часть кирпича — только axiomGivesTwins (условная, уже известная). -/
theorem proofEscapes_iff_proofExists
    {T : ExternalProofTheory} {φ : T.Sentence} :
    ProofEscapesStep00Architecture T φ ↔ Nonempty (T.proves φ) := by
  rw [ProofEscapesStep00Architecture, proofReturns_iff_noProofs,
    not_isEmpty_iff]

/-- «Побег» опровержения ⟺ существование опровержения. -/
theorem refutationEscapes_iff_refutationExists
    {T : ExternalProofTheory} {φ : T.Sentence} :
    RefutationEscapesStep00Architecture T φ ↔ Nonempty (T.refutes φ) := by
  rw [RefutationEscapesStep00Architecture, refutationReturns_iff_noRefutations,
    not_isEmpty_iff]

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
