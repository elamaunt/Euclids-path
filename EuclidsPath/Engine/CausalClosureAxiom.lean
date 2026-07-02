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

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
