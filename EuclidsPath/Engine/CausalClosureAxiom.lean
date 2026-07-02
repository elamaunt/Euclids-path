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

  РАСШИРЕНИЕ ДЕКРЕТА (§10, по решению автора): структура первопричины несёт
  ДВЕ причинные границы — twin-узел (`causalBoundary`) и римановский закон
  манифестации (`riemannBoundary` : каждый off-critical нуль манифестирует
  неоплатимой поставкой потоков на разрешённых масштабах; зелёная машина —
  Engine/RiemannManifestationFront). Аксиома по-прежнему ОДНА. Машинная
  честность расширения: при границе закон манифестации ⟺ RH
  (`riemannManifestation_asserts_RH`) — принять расширенную первопричину =
  принять RH; `riemannHypothesis_from_firstCause` — НЕ доказательство RH,
  а редукция, закрытая декретом. Растяжки §10: опровержение RH или закона —
  False ровно здесь.

  P/NP-ЯЗЫК ДЕКРЕТА (§11): ТРЕТЬЕЙ границы НЕТ — намеренно. Сепарация в
  авторском прочтении («ранго-быстрый проезд не может оплатить все
  сертификаты») — ЗЕЛЁНАЯ теорема при A ≤ 4 (Engine/PNPRankPaymentFront,
  pnp_rank_separation_smallScale); трилемма кандидатов третьего поля доказана
  машинно (универсальная форма опровержима — декрет был бы противоречив;
  decider-gated опровержима; экзистенциальная уже зелёно доказана — декрет
  был бы вакуумен). Существующая граница УЖЕ говорит на языке P/NP: на
  декретном масштабе A ≥ 5 она даёт LocalPSuccess/полную оплату/ограниченную
  поставку (§11) — чистый раскол по масштабам с зелёной сепарацией на A ≤ 4.

  ЯНГ–МИЛЛС-ЯЗЫК ДЕКРЕТА (§12): ЧЕТВЁРТОЙ границы НЕТ — намеренно. Трилемма
  (Engine/YangMillsFront §7): универсальный кандидат опровержим
  (cooked-лестница + EPMI), экзистенциальный вакуумен, манифестационный
  НЕСОВМЕСТИМ с принятой границей (лестница, в отличие от off-critical нуля,
  зелёно предъявима — ymManifestationLaw_refutes_boundary); per-model
  «закон квантования ⟺ масс-гэп» зелёно и БЕЗ границы
  (quantizationLaw_iff_massGap) — декретировать закон = декретировать цель.
  Сам вывод «квантованность ⟹ гэп» — зелёная условная цепь
  (massGap_of_quantizationLaw); §12 фиксирует лишь то, что декрет утверждает
  САМ: на его масштабе A ≥ 5 поставки отклонений нет — его мир гэпнут в
  языке поставок. Клэй НЕ решается и НЕ объявляется.
-/
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.PNPRankPaymentFront
import EuclidsPath.Engine.YangMillsFront

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
**СТРУКТУРА ПЕРВОПРИЧИНЫ** — намеренно принимаемое внешнее начало Step00-мира.

Четыре поля — точная структура события `0 → 1` и его причинные границы:
* `origin` — маркер сингулярности `0` (до-кадровое состояние; несёт `True`:
  до первого кадра внутреннего языка нет, утверждать нечего);
* `firstFrame` — маркер первого причинного кадра `1` (с него доступен язык
  состояний/шагов/леджеров; тоже `True` — маркер, не утверждение);
* `causalBoundary` — причинная граница БЛИЗНЕЦОВ: strict-обязательство Step00;
* `riemannBoundary` — причинная граница РИМАНА (расширение декрета, §10):
  закон манифестации — каждое off-critical отклонение нуля обязано проявиться
  неоплатимой поставкой потоков там, где леджер сводит книги
  (`RiemannManifestationLaw`, зелёная машина — RiemannManifestationFront).

Интернализация первопричины невозможна (доказано ранее: внутренняя
первопричина = запрещённый двигатель, `no_internalisedHorizonBoundary`) —
потому она принимается ИЗВНЕ, аксиомой, намеренно.
-/
structure Step00FirstCause : Prop where
  origin : True
  firstFrame : True
  causalBoundary : Step00CausalClosureAxiom
  riemannBoundary : RiemannManifestationLaw

/--
**ЕДИНСТВЕННАЯ АКСИОМА РЕПОЗИТОРИЯ — ПЕРВОПРИЧИНА (намеренно, структурой).**

Reading: внешнее начало `0 → 1` принято как корень архитектуры; из него
теоремой следует causal closure, а из той — весь условный слой.

⚠️ Everything depending on this axiom is CONDITIONAL and machine-flagged by
the node verifier as AXIOM-TAINTED (axiom name: `step00FirstCause`).
-/
axiom step00FirstCause : Step00FirstCause

/--
Прежняя causal-closure «аксиома» — теперь ТЕОРЕМА из первопричины: имя и все
использования ниже по течению не меняются, но корень архитектуры — намеренно
структурированная первопричина. ⚠️ AXIOM-TAINTED (через step00FirstCause).
-/
theorem step00CausalClosure : Step00CausalClosureAxiom :=
  step00FirstCause.causalBoundary

/-- **ЧЕСТНОСТЬ (машинно): структура первопричины ⟺ конъюнкция её границ.**
    Маркеры origin/firstFrame — `True`, вся сила — в двух границах: twin-узле
    и римановском законе манифестации. Намеренное включение первопричины
    меняет ПРОИСХОЖДЕНИЕ (корень архитектуры и имя аксиомы в таинте), но не
    математическую силу декрета — она ровно сумма принятых границ. -/
theorem step00FirstCause_iff_causalClosure :
    Step00FirstCause ↔ (Step00CausalClosureAxiom ∧ RiemannManifestationLaw) :=
  ⟨fun F => ⟨F.causalBoundary, F.riemannBoundary⟩,
   fun h => ⟨trivial, trivial, h.1, h.2⟩⟩

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



/-#############################################################################
  WELL-FOUNDED ПРИЧИННЫЙ ФРАКТАЛ (кирпич: well_founded_causal_fractal).
  Точный смысл слогана «вселенная фрактальна»: причинно-информационное
  самоподобие на мета-границе (в каждом мета-узле повторяется дихотомия
  побег/возврат) + внутренняя well-foundedness (∞-ветвь со строгим
  ℕ-спуском ранга невозможна). НЕ геометрический фрактал и не космология
  (scope guard кирпича). Аксиому НЕ использует — все декларации axiom-clean.
  Фиксы: RankedMetaFractalBranch несёт данные → `→ False`.
  Машинная честность: 6-ветвевой исход коллапсирует в 3-дизъюнкцию
  (узел ∨ есть доказательство ∨ есть опровержение); поля самоподобия —
  Nonempty/IsEmpty-тавтологии meta-уровня.
#############################################################################-/

open EuclidsPath.BoundaryDefectPayment

/-#############################################################################
  §1. Meta-fractal nodes
#############################################################################-/

/--
A node of the meta-fractal is an external proof theory together with one of its
sentences.  The intended sentence is often the external representation of
`TwinLowers.Infinite`, but the audit is stated for any external sentence.
-/
structure MetaFractalNode where
  T : ExternalProofTheory
  φ : T.Sentence

namespace MetaFractalNode

/--
The proof side of a node returns to Step00 if proofs of its sentence admit a
Step00 proof interface.
-/
abbrev proofReturns (N : MetaFractalNode) : Prop :=
  ProofReturnsToStep00Architecture N.T N.φ

/--
The refutation side of a node returns to Step00 if refutations of its sentence
admit a Step00 refutation interface.
-/
abbrev refutationReturns (N : MetaFractalNode) : Prop :=
  RefutationReturnsToStep00Architecture N.T N.φ

/--
The proof side genuinely escapes Step00 when it has no proof-return interface.
-/
abbrev proofEscapes (N : MetaFractalNode) : Prop :=
  ProofEscapesStep00Architecture N.T N.φ

/--
The refutation side genuinely escapes Step00 when it has no refutation-return
interface.
-/
abbrev refutationEscapes (N : MetaFractalNode) : Prop :=
  RefutationEscapesStep00Architecture N.T N.φ

end MetaFractalNode

/-#############################################################################
  §2. Local fractal alternatives
#############################################################################-/

/--
The local alternatives available at a meta-fractal node.

`externalBoundary` is the legitimate outside causal-closure input.
`proofEscape` and `refutationEscape` are genuine exits from Step00 mediation.
`seam`, `payment`, and `engine` are the already audited failure/forbidden
branches.
-/
inductive MetaFractalOutcome (N : MetaFractalNode) : Prop where
  | externalBoundary :
      ExternalUniverseCause Step00CausalClosureAxiom → MetaFractalOutcome N
  | proofEscape :
      N.proofEscapes → MetaFractalOutcome N
  | refutationEscape :
      N.refutationEscapes → MetaFractalOutcome N
  | seam :
      RealisedDenialOfCausalCause → MetaFractalOutcome N
  | payment :
      ImpossiblePayment → MetaFractalOutcome N
  | engine :
      SomeConcreteEuclideanEngine → MetaFractalOutcome N

/--
An actual external proof certificate cannot return to Step00.  It is therefore
a genuine proof escape at that meta-fractal node.
-/
theorem actualProof_forces_metaFractalProofEscape
    (N : MetaFractalNode) (p : N.T.proves N.φ) :
    N.proofEscapes :=
  existing_externalProof_forces_proofEscape p

/--
An actual external refutation certificate cannot return to Step00.  It is
therefore a genuine refutation escape at that meta-fractal node.
-/
theorem actualRefutation_forces_metaFractalRefutationEscape
    (N : MetaFractalNode) (r : N.T.refutes N.φ) :
    N.refutationEscapes :=
  existing_externalRefutation_forces_refutationEscape r

/--
An actual external proof produces one of the local meta-fractal outcomes:
genuine proof escape.
-/
theorem actualProof_metaFractalOutcome
    (N : MetaFractalNode) (p : N.T.proves N.φ) :
    MetaFractalOutcome N :=
  MetaFractalOutcome.proofEscape
    (actualProof_forces_metaFractalProofEscape N p)

/--
An actual external refutation produces one of the local meta-fractal outcomes:
genuine refutation escape.
-/
theorem actualRefutation_metaFractalOutcome
    (N : MetaFractalNode) (r : N.T.refutes N.φ) :
    MetaFractalOutcome N :=
  MetaFractalOutcome.refutationEscape
    (actualRefutation_forces_metaFractalRefutationEscape N r)

/--
If a proof route returns to Step00, then it has no actual external proof
certificate in the audited no-engine architecture.
-/
theorem proofReturn_has_no_actualProof
    (N : MetaFractalNode) (hReturn : N.proofReturns) :
    IsEmpty (N.T.proves N.φ) :=
  no_externalProof_under_proofReturn hReturn

/--
If a refutation route returns to Step00, then it has no actual external
refutation certificate in the audited no-engine architecture.
-/
theorem refutationReturn_has_no_actualRefutation
    (N : MetaFractalNode) (hReturn : N.refutationReturns) :
    IsEmpty (N.T.refutes N.φ) :=
  no_externalRefutation_under_refutationReturn hReturn

/--
A proof cannot both exist and fail to escape the Step00 architecture.
-/
theorem actualProof_cannot_be_nonEscaping
    (N : MetaFractalNode) (p : N.T.proves N.φ)
    (hNoEscape : ¬ N.proofEscapes) : False :=
  hNoEscape (actualProof_forces_metaFractalProofEscape N p)

/--
A refutation cannot both exist and fail to escape the Step00 architecture.
-/
theorem actualRefutation_cannot_be_nonEscaping
    (N : MetaFractalNode) (r : N.T.refutes N.φ)
    (hNoEscape : ¬ N.refutationEscapes) : False :=
  hNoEscape (actualRefutation_forces_metaFractalRefutationEscape N r)

/-#############################################################################
  §3. Self-similarity law
#############################################################################-/

/--
The local self-similarity law of the causal fractal.

At every meta-node, actual proof/refutation certificates force genuine escape.
If one additionally asserts that the route returns to Step00, then the
corresponding certificates are empty.  This is the formal version of:

  an apparent exit either really exits, or it is translated back into Step00 and
  dies by the forbidden-engine audit.
-/
structure MetaFractalSelfSimilarity where
  proof_certificate_forces_escape :
    ∀ N : MetaFractalNode,
      Nonempty (N.T.proves N.φ) → N.proofEscapes
  refutation_certificate_forces_escape :
    ∀ N : MetaFractalNode,
      Nonempty (N.T.refutes N.φ) → N.refutationEscapes
  proof_return_forbids_certificate :
    ∀ N : MetaFractalNode,
      N.proofReturns → IsEmpty (N.T.proves N.φ)
  refutation_return_forbids_certificate :
    ∀ N : MetaFractalNode,
      N.refutationReturns → IsEmpty (N.T.refutes N.φ)

/--
The audited Step00 meta-boundary satisfies the local self-similarity law.
-/
def metaFractalSelfSimilarity : MetaFractalSelfSimilarity where
  proof_certificate_forces_escape := by
    intro N hp
    rcases hp with ⟨p⟩
    exact actualProof_forces_metaFractalProofEscape N p
  refutation_certificate_forces_escape := by
    intro N hr
    rcases hr with ⟨r⟩
    exact actualRefutation_forces_metaFractalRefutationEscape N r
  proof_return_forbids_certificate := by
    intro N hReturn
    exact proofReturn_has_no_actualProof N hReturn
  refutation_return_forbids_certificate := by
    intro N hReturn
    exact refutationReturn_has_no_actualRefutation N hReturn

/-#############################################################################
  §4. Infinite internal fractal branches
#############################################################################-/

/--
A ranked meta-fractal branch is an infinite sequence of apparent meta-levels
whose internalisation strictly lowers a natural rank at every step.

This abstracts the Step00 situation: return/nesting/compression/internalisation
is allowed to move to another level only if it pays a strict rank decrease.
-/
structure RankedMetaFractalBranch where
  node : ℕ → MetaFractalNode
  rank : ℕ → ℕ
  drops : ∀ i : ℕ, rank (i + 1) < rank i

/--
There is no infinite internal meta-fractal branch when every level strictly
lowers a natural rank.
-/
theorem no_rankedMetaFractalBranch
    (B : RankedMetaFractalBranch) : False :=
  no_infinite_nat_strict_descent B.rank B.drops

/--
Alias for the slogan: the Step00 causal fractal is well-founded internally.
-/
abbrev WellFoundedInternalCausalFractal : Prop :=
  RankedMetaFractalBranch → False

/--
The internal causal fractal is well-founded.
-/
theorem wellFoundedInternalCausalFractal :
    WellFoundedInternalCausalFractal :=
  no_rankedMetaFractalBranch

/-#############################################################################
  §5. Finite fractal prefixes
#############################################################################-/

/--
A finite prefix of a causal fractal is just a finite causal tower.  The name
connects the previous induction patch with the current fractal reading.
-/
abbrev FiniteCausalFractalPrefix (P : Prop) (n : ℕ) : Prop :=
  FiniteCausalTowerAttempt P n

/--
Every finite fractal prefix classifies into the same four finite tower outcomes:
external boundary, seam, payment, or engine.
-/
theorem finiteCausalFractalPrefix_classifies
    {P : Prop} {n : ℕ}
    (F : FiniteCausalFractalPrefix P n) : CausalTowerOutcome P :=
  finiteCausalTowerAttempt_classifies F

/--
If external boundary, seam, payment, and engine are all forbidden, no finite
fractal prefix can be completely internal.
-/
theorem no_closed_finiteCausalFractalPrefix
    {P : Prop} {n : ℕ}
    (hNoExternal : ¬ ExternalUniverseCause P)
    (hNoSeam : ¬ RealisedDenialOfCausalCause)
    (hNoPayment : ¬ ImpossiblePayment)
    (hNoEngine : ¬ SomeConcreteEuclideanEngine) :
    ¬ FiniteCausalFractalPrefix P n :=
  no_finiteCausalTowerAttempt_without_boundary_or_failure
    hNoExternal hNoSeam hNoPayment hNoEngine

/-#############################################################################
  §6. The well-founded causal-fractal audit package
#############################################################################-/

/--
The full audited meaning of "causal fractal" for Step00.

It packages three facts:

* local self-similarity of the escape-or-return dichotomy;
* finite internal prefixes still need boundary/seam/payment/engine;
* infinite internal self-similar regress is impossible under rank descent.
-/
structure WellFoundedCausalFractalAudit where
  local_self_similarity : MetaFractalSelfSimilarity
  finite_prefix_classifies :
    ∀ {P : Prop} {n : ℕ},
      FiniteCausalFractalPrefix P n → CausalTowerOutcome P
  no_closed_finite_prefix :
    ∀ {P : Prop} {n : ℕ},
      (¬ ExternalUniverseCause P) →
      (¬ RealisedDenialOfCausalCause) →
      (¬ ImpossiblePayment) →
      (¬ SomeConcreteEuclideanEngine) →
        ¬ FiniteCausalFractalPrefix P n
  no_infinite_internal_branch : WellFoundedInternalCausalFractal

/--
The audited Step00 universe is a well-founded causal fractal.
-/
def wellFoundedCausalFractalAudit : WellFoundedCausalFractalAudit where
  local_self_similarity := metaFractalSelfSimilarity
  finite_prefix_classifies := by
    intro P n F
    exact finiteCausalFractalPrefix_classifies F
  no_closed_finite_prefix := by
    intro P n hNoExternal hNoSeam hNoPayment hNoEngine
    exact no_closed_finiteCausalFractalPrefix
      hNoExternal hNoSeam hNoPayment hNoEngine
  no_infinite_internal_branch := wellFoundedInternalCausalFractal

/--
Compressed theorem form:

  the Step00 universe is self-similar at meta-boundaries, but well-founded
  internally.  Hence it behaves like a causal/informational fractal, not like an
  infinite internal regress.
-/
theorem wellFoundedCausalFractal_slogan :
    (∀ N : MetaFractalNode,
      Nonempty (N.T.proves N.φ) → N.proofEscapes) ∧
    (∀ N : MetaFractalNode,
      Nonempty (N.T.refutes N.φ) → N.refutationEscapes) ∧
    (∀ {P : Prop} {n : ℕ},
      FiniteCausalFractalPrefix P n → CausalTowerOutcome P) ∧
    WellFoundedInternalCausalFractal := by
  constructor
  · intro N hp
    exact metaFractalSelfSimilarity.proof_certificate_forces_escape N hp
  constructor
  · intro N hr
    exact metaFractalSelfSimilarity.refutation_certificate_forces_escape N hr
  constructor
  · intro P n F
    exact finiteCausalFractalPrefix_classifies F
  · exact wellFoundedInternalCausalFractal

/-#############################################################################
  §7. Scope guard
#############################################################################-/

/--
Scope marker: this is a causal/informational fractal audit, not a claim about
geometric fractals, physical cosmology, or absolute metamathematical
independence.
-/
abbrev ThisIsACausalInformationalFractalNotAGeometricFractal : Prop := True

/--
The scope marker is intentionally trivial.
-/
theorem thisIsACausalInformationalFractalNotAGeometricFractal :
    ThisIsACausalInformationalFractalNotAGeometricFractal := by
  trivial

/-! Машинная честность fractal-формы -/

/-- ИСХОД КОЛЛАПСИРУЕТ в честную 3-дизъюнкцию: seam/payment/engine сожжены,
    «побеги» ⟺ существование сертификатов, граница ⟺ сама аксиома-узел.
    Шестиветвевой фрактальный исход = (узел ∨ есть доказательство ∨ есть
    опровержение) — вся структура сведена к подлинным содержаниям. -/
theorem metaFractalOutcome_iff (N : MetaFractalNode) :
    MetaFractalOutcome N ↔
      (Step00CausalClosureAxiom ∨
        Nonempty (N.T.proves N.φ) ∨ Nonempty (N.T.refutes N.φ)) := by
  constructor
  · intro O
    cases O with
    | externalBoundary h => exact Or.inl h
    | proofEscape h =>
        exact Or.inr (Or.inl (proofEscapes_iff_proofExists.mp h))
    | refutationEscape h =>
        exact Or.inr (Or.inr (refutationEscapes_iff_refutationExists.mp h))
    | seam h => exact (no_realisedNegationOfCausalClosure h).elim
    | payment h => exact (BoundaryDefectPayment.impossiblePayment_false h).elim
    | engine h => exact (no_someConcreteEuclideanEngine h).elim
  · rintro (h | hp | hr)
    · exact MetaFractalOutcome.externalBoundary h
    · exact MetaFractalOutcome.proofEscape (proofEscapes_iff_proofExists.mpr hp)
    · exact MetaFractalOutcome.refutationEscape
        (refutationEscapes_iff_refutationExists.mpr hr)



/-#############################################################################
  STRICT-ПАКЕТ АКСИОМЫ (кирпич: strict_causal_closure_axiom_package).
  Максимально явная data-форма аксиомы: (A, projOf, resolves) — и запись
  того, что именно из неё следует. Кирпич честно отделяет её от «какой-то
  внешней причины» (§5): нужна ТОЧНАЯ Step00-каузальность, не произвольная.
  Новой аксиомы НЕТ; §3 переиспользует step00CausalClosure (эти декларации
  AXIOM-TAINTED). Фиксы: Π→proj; ofStep00CausalClosure — Prop→Type
  элиминация через .choose (noncomputable). Машинная честность: пакет ⟺
  старый узел; пакет — twin-детектор; У ЛЮБОГО ПАКЕТА A ≥ 5 (сужение бьёт
  прямо по полю данных).
#############################################################################-/

/-#############################################################################
  §1. The strict causal-closure package
#############################################################################-/

/--
Data form of the strict Step00 causal-closure axiom.

`A` is the global Step00 scale.  For every alleged finite bound `M0` on twin
centres, `projOf M0` is the finite semantic ledger projection on extended generated
flows at that bound.  The resolver says that every admissible same-key collision
of two distinct generated genealogies must produce the strict local certificate
from `StrictSemanticExtendedFlowLedgerCollisionResolves`.
-/
structure StrictStep00CausalClosurePackage where
  A : ℕ
  projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0
  resolves : ∀ M0 : ℕ,
    StrictSemanticExtendedFlowLedgerCollisionResolves (projOf M0)

/--
The proposition form of the strict package.

This is intentionally just existence of the data above.  It carries no hidden
claim that arbitrary external axioms prove anything.
-/
abbrev StrictStep00CausalClosurePackageExists : Prop :=
  ∃ C : StrictStep00CausalClosurePackage, True

/-- Convert package data into the previously isolated final Step00 obligation. -/
def StrictStep00CausalClosurePackage.toStep00CausalClosure
    (C : StrictStep00CausalClosurePackage) :
    Step00CausalClosureAxiom := by
  exact ⟨C.A, C.projOf, C.resolves⟩

/-- Convert the final Step00 obligation into explicit package data. -/
noncomputable def StrictStep00CausalClosurePackage.ofStep00CausalClosure
    (H : Step00CausalClosureAxiom) :
    StrictStep00CausalClosurePackage :=
  ⟨H.choose, H.choose_spec.choose, H.choose_spec.choose_spec⟩

/--
The explicit package formulation is equivalent to the already named final
causal-closure axiom.
-/
theorem strictStep00CausalClosurePackageExists_iff_axiom :
    StrictStep00CausalClosurePackageExists ↔ Step00CausalClosureAxiom := by
  constructor
  · rintro ⟨C, _⟩
    exact C.toStep00CausalClosure
  · intro H
    exact ⟨StrictStep00CausalClosurePackage.ofStep00CausalClosure H, trivial⟩

/-#############################################################################
  §2. Local consequence: no finite twin bound survives the axiom
#############################################################################-/

/--
For a fixed strict causal-closure package, no proposed finite twin bound `M0`
can survive.  The resolver at `M0` contradicts the generated-flow family forced
by such a bound.
-/
theorem no_twinBoundAbove_of_strictPackage
    (C : StrictStep00CausalClosurePackage)
    (M0 : ℕ) :
    ¬ TwinBoundAbove M0 := by
  intro hBound
  exact twinBound_impossible_with_strictSemanticExtendedResolution
    (A := C.A) (M0 := M0) (C.projOf M0) hBound (C.resolves M0)

/--
A strict causal-closure package gives infinitude of lower twin centres.
-/
theorem twinLowersInfinite_of_strictPackage
    (C : StrictStep00CausalClosurePackage) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation C.toStep00CausalClosure

/--
The proposition form of the package gives infinitude of lower twin centres.
-/
theorem twinLowersInfinite_of_strictPackageExists
    (H : StrictStep00CausalClosurePackageExists) :
    TwinLowers.Infinite := by
  rcases H with ⟨C, _⟩
  exact twinLowersInfinite_of_strictPackage C

/--
The named causal-closure axiom gives infinitude of lower twin centres.
This is the same theorem as the earlier endpoint, restated through the strict
package interface.
-/
theorem twinLowersInfinite_of_strictCausalClosureAxiom
    (H : Step00CausalClosureAxiom) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictPackage
    (StrictStep00CausalClosurePackage.ofStep00CausalClosure H)

/-#############################################################################
  §3. The accepted external axiom closes the Step00 universe
#############################################################################-/

/-- The already accepted external axiom supplies the strict package. -/
theorem accepted_strictStep00CausalClosurePackageExists :
    StrictStep00CausalClosurePackageExists :=
  (strictStep00CausalClosurePackageExists_iff_axiom).2 step00CausalClosure

/-- Therefore the accepted external axiom yields infinitely many lower twins. -/
theorem twinLowersInfinite_from_acceptedStrictPackage :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictPackageExists
    accepted_strictStep00CausalClosurePackageExists

/-#############################################################################
  §4. What exactly follows from the axiom
#############################################################################-/

/--
The audited list of final Step00 consequences of the causal-closure axiom.

This is the precise meaning of "from the axiom everything follows" in this
project:

  * the lower twin centres are infinite;
  * every finite twin bound is impossible once the package data are fixed;
  * the non-axiomatic remaining obligation is exactly this same axiom;
  * the axiom is external-only: an internal self-derivation would be a forbidden
    engine and is therefore impossible in the stable no-engine architecture.
-/
abbrev FinalConsequencesOfStep00CausalClosure
    (C : StrictStep00CausalClosurePackage) : Prop :=
  TwinLowers.Infinite ∧
  (∀ M0 : ℕ, ¬ TwinBoundAbove M0) ∧
  (Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom) ∧
  ¬ InternalSelfDerivationOfStep00CausalClosure

/--
All audited Step00 consequences follow from one strict causal-closure package.
-/
theorem finalConsequences_of_strictPackage
    (C : StrictStep00CausalClosurePackage) :
    FinalConsequencesOfStep00CausalClosure C := by
  exact ⟨
    twinLowersInfinite_of_strictPackage C,
    no_twinBoundAbove_of_strictPackage C,
    pipelineClosesWithoutNewAxiom_iff_causalClosure,
    no_internalSelfDerivation_step00CausalClosure
  ⟩

/--
All audited Step00 consequences follow from the named causal-closure axiom.
-/
theorem finalConsequences_of_step00CausalClosureAxiom
    (H : Step00CausalClosureAxiom) :
    FinalConsequencesOfStep00CausalClosure
      (StrictStep00CausalClosurePackage.ofStep00CausalClosure H) :=
  finalConsequences_of_strictPackage
    (StrictStep00CausalClosurePackage.ofStep00CausalClosure H)

/--
All audited Step00 consequences follow from the accepted external axiom.
-/
theorem finalConsequences_from_acceptedExternalAxiom :
    FinalConsequencesOfStep00CausalClosure
      (StrictStep00CausalClosurePackage.ofStep00CausalClosure
        step00CausalClosure) :=
  finalConsequences_of_step00CausalClosureAxiom step00CausalClosure

/-#############################################################################
  §5. Negative boundary: why this does not mean "any axiom proves everything"
#############################################################################-/

/--
A marker for arbitrary external causes.  It is deliberately independent from
`Step00CausalClosureAxiom`: a mere external cause is not enough to run the
Step00 proof.
-/
abbrev ArbitraryExternalCause : Prop :=
  True

/--
What is needed is not arbitrary causality, but causality in the precise Step00
same-key generated-flow sense.
-/
abbrev ArbitraryCauseIsNotTheStep00Axiom : Prop :=
  ArbitraryExternalCause ∧
  (Step00CausalClosureAxiom → TwinLowers.Infinite)

/--
The project uses the second conjunct, not the first.
-/
theorem arbitraryCause_marker_and_preciseAxiom_suffices :
    ArbitraryCauseIsNotTheStep00Axiom := by
  exact ⟨trivial, twinLowersInfinite_of_strictCausalClosureAxiom⟩

/-#############################################################################
  §6. Final slogan theorem
#############################################################################-/

/--
Final strict formulation:

  a precise Step00 causal-closure package is equivalent to the last axiom;
  from it every audited Step00 consequence follows;
  in particular, lower twin centres are infinite.
-/
theorem strictCausalClosureAxiom_final_slogan :
    (StrictStep00CausalClosurePackageExists ↔ Step00CausalClosureAxiom) ∧
    TwinLowers.Infinite ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure := by
  exact ⟨
    strictStep00CausalClosurePackageExists_iff_axiom,
    twinLowersInfinite_from_acceptedStrictPackage,
    no_internalSelfDerivation_step00CausalClosure
  ⟩

/-! Машинная честность package-формы -/

/-- Пакет ⟺ старый узел (через семью эквивалентностей). -/
theorem strictPackageExists_iff_lastStep00Obligation :
    StrictStep00CausalClosurePackageExists ↔ TheLastStep00Obligation :=
  strictStep00CausalClosurePackageExists_iff_axiom.trans
    strictLastStep00Obligation_iff_lastStep00Obligation

/-- Пакет на каждом масштабе предъявляет twin (детектор). -/
theorem twin_above_of_strictPackage
    (C : StrictStep00CausalClosurePackage) (M0 : ℕ) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_strictResolves (C.projOf M0) (C.resolves M0)

/-- СУЖЕНИЕ БЬЁТ ПО ПОЛЮ: у ЛЮБОГО strict-пакета масштаб A ≥ 5
    (ветвь A ≤ 4 машинно опровергнута 5-адической цепью). -/
theorem strictPackage_scale_ge_five
    (C : StrictStep00CausalClosurePackage) : 5 ≤ C.A := by
  by_contra hA
  exact no_projection_resolves_at_smallScale (by omega) (C.projOf 1)
    (strictSemanticExtended_resolves_old (C.resolves 1))



/-#############################################################################
  ГОРИЗОНТ СОБЫТИЙ + СИНГУЛЯРНОСТЬ НАЧАЛА (кирпичи: step00_event_horizon +
  step00_origin_singularity). Граница Step00-интерпретируемости: внутри —
  возврат в интерфейс (⟹ двигатель ⟹ пусто), за горизонтом — подлинно
  новая не-Step00 информация; «0 → 1» — внешнее граничное событие, не
  RealStep; интернализация границы = запрещённый self-cause. Accepted-ветки
  используют аксиому (AXIOM-TAINTED). Машинная честность: горизонт =
  переименование пустоты/непустоты сертификатов; альтернатива коллапсирует
  в 3-дизъюнкцию; «событие 0→1» ⟺ сама аксиома (маркеры — True).
#############################################################################-/

/-#############################################################################
  §1. The Step00 event horizon
#############################################################################-/

/--
A proof route is inside the Step00 event horizon exactly when it returns to the
Step00 internal proof interface.
-/
abbrev InsideStep00ProofHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ProofReturnsToStep00Architecture T φ

/--
A refutation route is inside the Step00 event horizon exactly when it returns to
the Step00 internal refutation interface.
-/
abbrev InsideStep00RefutationHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  RefutationReturnsToStep00Architecture T φ

/--
A proof route is beyond the Step00 event horizon exactly when it genuinely
escapes the Step00 proof interface.
-/
abbrev BeyondStep00ProofHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ProofEscapesStep00Architecture T φ

/--
A refutation route is beyond the Step00 event horizon exactly when it genuinely
escapes the Step00 refutation interface.
-/
abbrev BeyondStep00RefutationHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  RefutationEscapesStep00Architecture T φ

/--
Being inside and being beyond the proof horizon are definitionally exclusive.
-/
theorem not_inside_and_beyond_proof_horizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00ProofHorizon T φ)
    (hBeyond : BeyondStep00ProofHorizon T φ) : False := by
  exact hBeyond hInside

/--
Being inside and being beyond the refutation horizon are definitionally
exclusive.
-/
theorem not_inside_and_beyond_refutation_horizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00RefutationHorizon T φ)
    (hBeyond : BeyondStep00RefutationHorizon T φ) : False := by
  exact hBeyond hInside

/-#############################################################################
  §2. What happens inside the horizon
#############################################################################-/

/--
An actual proof that remains inside the Step00 proof horizon constructs the
forbidden engine; hence no such proof certificate exists in the audited
no-engine architecture.
-/
theorem insideProofHorizon_has_no_actualProof
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00ProofHorizon T φ) :
    IsEmpty (T.proves φ) :=
  no_externalProof_under_proofReturn hInside

/--
An actual refutation that remains inside the Step00 refutation horizon also
constructs the forbidden engine; hence no such refutation certificate exists in
the audited no-engine architecture.
-/
theorem insideRefutationHorizon_has_no_actualRefutation
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00RefutationHorizon T φ) :
    IsEmpty (T.refutes φ) :=
  no_externalRefutation_under_refutationReturn hInside

/--
Explicit contradiction form for an actual proof inside the Step00 horizon.
-/
theorem actualProof_insideHorizon_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ)
    (hInside : InsideStep00ProofHorizon T φ) : False := by
  have hEmpty := insideProofHorizon_has_no_actualProof hInside
  exact (IsEmpty.false p)

/--
Explicit contradiction form for an actual refutation inside the Step00 horizon.
-/
theorem actualRefutation_insideHorizon_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ)
    (hInside : InsideStep00RefutationHorizon T φ) : False := by
  have hEmpty := insideRefutationHorizon_has_no_actualRefutation hInside
  exact (IsEmpty.false r)

/--
Equivalently: any actual external proof must live beyond the Step00 proof
horizon.
-/
theorem actualProof_must_cross_eventHorizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ) :
    BeyondStep00ProofHorizon T φ :=
  existing_externalProof_forces_proofEscape p

/--
Equivalently: any actual external refutation must live beyond the Step00
refutation horizon.
-/
theorem actualRefutation_must_cross_eventHorizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ) :
    BeyondStep00RefutationHorizon T φ :=
  existing_externalRefutation_forces_refutationEscape r

/-#############################################################################
  §3. The external causal boundary
#############################################################################-/

/--
The precise external boundary condition that closes Step00 is not a vague
"external cause".  It is exactly `Step00CausalClosureAxiom` accepted from outside
the internal no-engine derivation interface.
-/
abbrev Step00CausalClosureBeyondHorizon : Prop :=
  ExternalUniverseCause Step00CausalClosureAxiom

/--
Crossing the horizon by accepting the precise causal-closure boundary gives
infinitude of lower twin centres.
-/
theorem causalClosureBeyondHorizon_generates_twins
    (H : Step00CausalClosureBeyondHorizon) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation H

/--
The previously declared external axiom is one instance of the causal boundary
beyond the Step00 horizon.
-/
theorem acceptedStep00CausalClosure_is_beyondHorizon :
    Step00CausalClosureBeyondHorizon :=
  step00CausalClosure

/--
Therefore the accepted external boundary generates infinitude of lower twin
centres.
-/
theorem acceptedBoundary_generates_twins :
    TwinLowers.Infinite :=
  causalClosureBeyondHorizon_generates_twins
    acceptedStep00CausalClosure_is_beyondHorizon

/-#############################################################################
  §4. Why the boundary cannot be internalised
#############################################################################-/

/--
Trying to make the horizon boundary into an internal cause is exactly the
forbidden self-supporting case already audited.
-/
abbrev InternalisedStep00HorizonBoundary : Prop :=
  InternalUniverseCause Step00CausalClosureAxiom

/--
Any internalised horizon boundary builds the forbidden Euclidean engine.
-/
theorem internalisedHorizonBoundary_builds_engine
    (H : InternalisedStep00HorizonBoundary) :
    SomeConcreteEuclideanEngine :=
  internalUniverseCause_builds_engine H

/--
Therefore the Step00 horizon boundary cannot be internalised in the stable
no-engine architecture.
-/
theorem no_internalisedHorizonBoundary :
    ¬ InternalisedStep00HorizonBoundary :=
  no_internalUniverseCause

/--
If the external causal boundary is also claimed to be internally caused, the
claim self-destructs by the forbidden-engine contradiction.
-/
theorem boundary_insideHorizon_selfDestructs
    (H : InternalisedStep00HorizonBoundary) : False :=
  no_internalisedHorizonBoundary H

/-#############################################################################
  §5. Complete local alternative at the horizon
#############################################################################-/

/--
The local alternatives at the Step00 event horizon for an external sentence.

`acceptedBoundary` is the precise causal-closure axiom route.
`proofBeyond` and `refutationBeyond` are genuine non-Step00 escapes.
`engine` is the forbidden returned route.
-/
inductive Step00EventHorizonAlternative
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop where
  | acceptedBoundary :
      Step00CausalClosureBeyondHorizon →
      Step00EventHorizonAlternative T φ
  | proofBeyond :
      BeyondStep00ProofHorizon T φ →
      Step00EventHorizonAlternative T φ
  | refutationBeyond :
      BeyondStep00RefutationHorizon T φ →
      Step00EventHorizonAlternative T φ
  | engine :
      SomeConcreteEuclideanEngine →
      Step00EventHorizonAlternative T φ

/--
An actual external proof gives the horizon alternative `proofBeyond`.
-/
theorem actualProof_gives_eventHorizonAlternative
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ) :
    Step00EventHorizonAlternative T φ :=
  Step00EventHorizonAlternative.proofBeyond
    (actualProof_must_cross_eventHorizon p)

/--
An actual external refutation gives the horizon alternative `refutationBeyond`.
-/
theorem actualRefutation_gives_eventHorizonAlternative
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ) :
    Step00EventHorizonAlternative T φ :=
  Step00EventHorizonAlternative.refutationBeyond
    (actualRefutation_must_cross_eventHorizon r)

/--
The accepted causal-closure axiom gives the horizon alternative
`acceptedBoundary`.
-/
theorem acceptedBoundary_gives_eventHorizonAlternative
    (T : ExternalProofTheory) (φ : T.Sentence) :
    Step00EventHorizonAlternative T φ :=
  Step00EventHorizonAlternative.acceptedBoundary
    acceptedStep00CausalClosure_is_beyondHorizon

/--
No forbidden-engine branch can actually be realised.
-/
theorem no_eventHorizon_engine_branch
    {T : ExternalProofTheory} {φ : T.Sentence}
    (E : SomeConcreteEuclideanEngine) : False :=
  no_someConcreteEuclideanEngine E

/-#############################################################################
  §6. Slogan theorem
#############################################################################-/

/--
Formal slogan of this patch.

Inside the horizon, returning proof/refutation mechanisms construct the
forbidden engine.  The Step00-internal successful route is therefore the precise
external causal-closure boundary, and any actual non-axiomatic proof/refutation
must be beyond the Step00 horizon.
-/
abbrev Step00EventHorizonSlogan : Prop :=
  (∀ {T : ExternalProofTheory} {φ : T.Sentence},
      InsideStep00ProofHorizon T φ → IsEmpty (T.proves φ)) ∧
  (∀ {T : ExternalProofTheory} {φ : T.Sentence},
      InsideStep00RefutationHorizon T φ → IsEmpty (T.refutes φ)) ∧
  (Step00CausalClosureBeyondHorizon → TwinLowers.Infinite) ∧
  (¬ InternalisedStep00HorizonBoundary)

/-- The Step00 event-horizon slogan is exactly the already proved audit facts. -/
theorem step00EventHorizon_slogan :
    Step00EventHorizonSlogan := by
  constructor
  · intro T φ hInside
    exact insideProofHorizon_has_no_actualProof hInside
  · constructor
    · intro T φ hInside
      exact insideRefutationHorizon_has_no_actualRefutation hInside
    · constructor
      · intro H
        exact causalClosureBeyondHorizon_generates_twins H
      · exact no_internalisedHorizonBoundary

/--
Scope guard: this is an architecture-relative event horizon, not a claim that
ordinary mathematics itself has an absolute event horizon.
-/
abbrev EventHorizonIsArchitectureRelative : Prop := True

theorem eventHorizonIsArchitectureRelative :
    EventHorizonIsArchitectureRelative := by
  trivial

/-#############################################################################
  §1. Origin markers: zero is not an internal Step00 state
#############################################################################-/

/--
`OriginZero` is a marker for the absence of an already available internal
Step00 causal frame.  It is not a constructor of the concrete Step00 `State`.
-/
abbrev OriginZero : Prop := True

/--
`FirstCausalOne` is a marker for the first admitted causal frame: from this
point on the Step00 language of states, legal steps, ledgers, and ranks is
available.
-/
abbrev FirstCausalOne : Prop := True

/--
The origin singularity is the pre-frame marker.  It carries no internal Step00
edge relation.
-/
abbrev Step00OriginSingularity : Prop := OriginZero

/--
The first causal frame is the post-boundary marker.  It is the first place where
Step00 can speak internally.
-/
abbrev Step00FirstCausalFrame : Prop := FirstCausalOne

/--
The statement that the origin marker is not itself an ordinary internal causal
mechanism is represented by the impossibility of internalising the Step00
horizon boundary.
-/
abbrev OriginZeroIsNotInternalMechanism : Prop :=
  ¬ InternalisedStep00HorizonBoundary

/--
The origin marker is not an internal mechanism of the already-formed Step00
world.
-/
theorem originZero_is_not_internalMechanism :
    OriginZeroIsNotInternalMechanism :=
  no_internalisedHorizonBoundary

/-#############################################################################
  §2. The 0 → 1 transition as an external boundary event
#############################################################################-/

/--
A Step00 origin boundary event consists of the origin marker, the first causal
frame marker, and the precise external causal-closure boundary beyond the
Step00 event horizon.

This is the formal version of: `0 → 1` is a boundary event, not an internal
`RealStep`.
-/
structure Step00OriginBoundaryEvent : Prop where
  origin : Step00OriginSingularity
  firstFrame : Step00FirstCausalFrame
  causalBoundary : Step00CausalClosureBeyondHorizon

/--
The already accepted Step00 causal-closure boundary gives an origin boundary
event.
-/
theorem acceptedStep00OriginBoundaryEvent :
    Step00OriginBoundaryEvent :=
  ⟨trivial, trivial, acceptedStep00CausalClosure_is_beyondHorizon⟩

/--
The origin boundary event generates infinitude of lower twin centres, because
its causal content is exactly the already audited external causal-closure
boundary.
-/
theorem step00OriginBoundaryEvent_generates_twins
    (H : Step00OriginBoundaryEvent) : TwinLowers.Infinite :=
  causalClosureBeyondHorizon_generates_twins H.causalBoundary

/--
Therefore the accepted origin boundary generates infinitude of lower twin
centres.
-/
theorem acceptedOriginBoundary_generates_twins :
    TwinLowers.Infinite :=
  step00OriginBoundaryEvent_generates_twins
    acceptedStep00OriginBoundaryEvent

/-#############################################################################
  §3. Internalising 0 → 1 is the forbidden self-cause
#############################################################################-/

/--
To internalise the origin event is to claim that the Step00 horizon boundary is
caused by an internal Step00 mechanism.  This is exactly the dangerous
self-cause case.
-/
abbrev InternalisedStep00OriginEvent : Prop :=
  InternalisedStep00HorizonBoundary

/--
Any internalised origin event builds the forbidden concrete Euclidean engine.
-/
theorem internalisedOriginEvent_builds_engine
    (H : InternalisedStep00OriginEvent) : SomeConcreteEuclideanEngine :=
  internalisedHorizonBoundary_builds_engine H

/--
No internalised origin event exists in the audited no-engine Step00
architecture.
-/
theorem no_internalisedOriginEvent :
    ¬ InternalisedStep00OriginEvent :=
  no_internalisedHorizonBoundary

/--
The explicit contradiction form: if `0 → 1` is treated as an ordinary internal
Step00 causal step, the horizon-boundary self-cause contradiction follows.
-/
theorem internalisedOriginEvent_contradiction
    (H : InternalisedStep00OriginEvent) : False :=
  no_internalisedOriginEvent H

/--
No forbidden-engine branch can be realised from an internalised origin event.
-/
theorem internalisedOriginEngine_impossible
    (H : InternalisedStep00OriginEvent) : False := by
  exact internalisedOriginEvent_contradiction H

/-#############################################################################
  §4. Boundary event versus internal step
#############################################################################-/

/--
The origin transition is external/boundary-like when it is supplied as a
`Step00OriginBoundaryEvent` and is not internalised.
-/
abbrev OriginTransitionIsBoundaryEvent : Prop :=
  Step00OriginBoundaryEvent ∧ ¬ InternalisedStep00OriginEvent

/--
The accepted origin transition is a boundary event and not an internal self-
cause.
-/
theorem acceptedOriginTransition_is_boundaryEvent :
    OriginTransitionIsBoundaryEvent :=
  ⟨acceptedStep00OriginBoundaryEvent, no_internalisedOriginEvent⟩

/--
The origin transition cannot be both boundary-initialised and internally
self-caused, because the internalised part is already impossible.
-/
theorem originTransition_cannot_be_internal_selfCause
    (H : OriginTransitionIsBoundaryEvent)
    (I : InternalisedStep00OriginEvent) : False :=
  H.2 I

/--
If one insists that the first causal frame causes itself internally, one has not
explained the origin; one has built the forbidden engine.
-/
theorem selfCausedFirstFrame_builds_engine
    (H : InternalisedStep00OriginEvent) : SomeConcreteEuclideanEngine :=
  internalisedOriginEvent_builds_engine H

/--
Consequently, a self-caused first causal frame is impossible.
-/
theorem no_selfCausedFirstFrame :
    ¬ InternalisedStep00OriginEvent :=
  no_internalisedOriginEvent

/-#############################################################################
  §5. Origin slogan
#############################################################################-/

/--
Formal slogan of the patch.

`0` is not an internal Step00 state/mechanism; `1` is the first causal frame;
`0 → 1` is an external boundary-origin event; making it internal produces the
forbidden engine; the accepted boundary gives `TwinLowers.Infinite`.
-/
abbrev Step00OriginSlogan : Prop :=
  Step00OriginSingularity ∧
  Step00FirstCausalFrame ∧
  OriginTransitionIsBoundaryEvent ∧
  (InternalisedStep00OriginEvent → SomeConcreteEuclideanEngine) ∧
  (¬ InternalisedStep00OriginEvent) ∧
  TwinLowers.Infinite

/-- The origin slogan is exactly the already established event-horizon audit. -/
theorem step00Origin_slogan :
    Step00OriginSlogan := by
  constructor
  · trivial
  · constructor
    · trivial
    · constructor
      · exact acceptedOriginTransition_is_boundaryEvent
      · constructor
        · intro H
          exact internalisedOriginEvent_builds_engine H
        · constructor
          · exact no_internalisedOriginEvent
          · exact acceptedOriginBoundary_generates_twins

/--
Scope guard: the `0 → 1` terminology is architecture-relative causal-ledger
language, not a theorem of physical cosmology.
-/
abbrev OriginInterpretationIsArchitectureRelative : Prop := True

/-- The scope guard is immediate. -/
theorem originInterpretationIsArchitectureRelative :
    OriginInterpretationIsArchitectureRelative := by
  trivial

/-! Машинная честность horizon/origin-форм -/

/-- «Внутри горизонта» ⟺ пустота доказательств (переименование). -/
theorem insideProofHorizon_iff_noProofs
    {T : ExternalProofTheory} {φ : T.Sentence} :
    InsideStep00ProofHorizon T φ ↔ IsEmpty (T.proves φ) :=
  proofReturns_iff_noProofs

/-- «За горизонтом» ⟺ существование доказательства (переименование). -/
theorem beyondProofHorizon_iff_proofExists
    {T : ExternalProofTheory} {φ : T.Sentence} :
    BeyondStep00ProofHorizon T φ ↔ Nonempty (T.proves φ) :=
  proofEscapes_iff_proofExists

/-- Горизонт-альтернатива КОЛЛАПСИРУЕТ в 3-дизъюнкцию (двигатель сожжён):
    аксиома ∨ есть доказательство ∨ есть опровержение. -/
theorem eventHorizonAlternative_iff
    {T : ExternalProofTheory} {φ : T.Sentence} :
    Step00EventHorizonAlternative T φ ↔
      (Step00CausalClosureAxiom ∨
        Nonempty (T.proves φ) ∨ Nonempty (T.refutes φ)) := by
  constructor
  · intro H
    cases H with
    | acceptedBoundary h => exact Or.inl h
    | proofBeyond h => exact Or.inr (Or.inl (proofEscapes_iff_proofExists.mp h))
    | refutationBeyond h =>
        exact Or.inr (Or.inr (refutationEscapes_iff_refutationExists.mp h))
    | engine h => exact (no_someConcreteEuclideanEngine h).elim
  · rintro (h | hp | hr)
    · exact Step00EventHorizonAlternative.acceptedBoundary h
    · exact Step00EventHorizonAlternative.proofBeyond
        (proofEscapes_iff_proofExists.mpr hp)
    · exact Step00EventHorizonAlternative.refutationBeyond
        (refutationEscapes_iff_refutationExists.mpr hr)

/-- «Событие 0 → 1» ⟺ сама аксиома: маркеры origin/firstFrame — True,
    содержание граничного события — ровно causal-closure. -/
theorem step00OriginBoundaryEvent_iff :
    Step00OriginBoundaryEvent ↔ Step00CausalClosureAxiom :=
  ⟨fun H => H.causalBoundary, fun h => ⟨trivial, trivial, h⟩⟩



/-#############################################################################
  §8. ЭПИСТЕМИКА ПЕРВОПРИЧИНЫ: есть — узнать нельзя — знание финитизирует
  (по замыслу автора; вся секция, кроме двух помеченных теорем, АКСИОМО-СВОБОДНА)
#############################################################################-/

/-- «Внутреннее знание причины» = внутреннее выведение границы (self-proof). -/
abbrev InternalKnowledgeOfCause : Prop := InternalisedStep00HorizonBoundary

/-- **«УЗНАТЬ НЕЛЬЗЯ» — ТЕОРЕМА (аксиомо-свободна):** внутреннее знание
    первопричины строило бы вечный двигатель — а их нет (lexRank). -/
theorem cause_unknowable : ¬ InternalKnowledgeOfCause :=
  no_internalisedHorizonBoundary

/-- Знание причины строит вечный двигатель (аксиомо-свободно). -/
theorem knowledge_builds_perpetualEngine :
    InternalKnowledgeOfCause → SomeConcreteEuclideanEngine :=
  internalisedHorizonBoundary_builds_engine

/-- **ЦЕЛЕВАЯ ТЕОРЕМА (замысел автора):** знание причины финитизирует близнецов.
    ⚠️ ЧЕСТНОСТЬ: доказательство идёт ЧЕРЕЗ невозможный двигатель (ex falso) —
    см. обязательный companion ниже. -/
theorem knowledge_finitizes_twins :
    InternalKnowledgeOfCause → ¬ EuclidsPath.TwinLowers.Infinite :=
  fun hK _ => no_someConcreteEuclideanEngine (knowledge_builds_perpetualEngine hK)

/-- COMPANION (машинная честность): из знания следует и бесконечность —
    знание взрывает всё; несущая часть конструкции — сама непознаваемость. -/
theorem knowledge_proves_anything :
    InternalKnowledgeOfCause → EuclidsPath.TwinLowers.Infinite :=
  fun hK => (no_someConcreteEuclideanEngine (knowledge_builds_perpetualEngine hK)).elim

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ (без ex falso в утверждении): либо причина
    непознаваема, либо близнецы конечны. Левый дизъюнкт — теорема. -/
theorem unknowable_or_twins_finite :
    ¬ InternalKnowledgeOfCause ∨ ¬ EuclidsPath.TwinLowers.Infinite :=
  Or.inl cause_unknowable

/-- «Двигателей нет ⟹ узнать нельзя» — подлинная контрапозиция (не взрыв). -/
theorem unknowable_of_noEngine
    (hNoEngine : ¬ SomeConcreteEuclideanEngine) : ¬ InternalKnowledgeOfCause :=
  fun hK => hNoEngine (knowledge_builds_perpetualEngine hK)

/-- **СУТЬ, машинно (аксиомо-свободно): «близнецы бесконечны, потому что узнать
    нельзя».** Отсутствие двигателей (= непознаваемость) + принятая причинная
    граница ⟹ близнецы бесконечны. Гипотеза hNoEngine ПОТРЕБЛЯЕТСЯ
    по-настоящему: из twin-bound строится ∞-семья, из неё — коллизия, из
    коллизии — двигатель-СВИДЕТЕЛЬ, и убивает его именно hNoEngine. -/
theorem twins_infinite_of_noEngine_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : Step00CausalClosureAxiom) :
    EuclidsPath.TwinLowers.Infinite := by
  by_contra hfin
  obtain ⟨M0, hBound⟩ := exists_twinBoundAbove_of_not_twinLowersInfinite hfin
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hStable : NoEnergyStableUniverse (projOf M0) :=
    (noEnergyStableUniverse_iff_resolves (projOf M0)).mpr
      (strictSemanticExtended_resolves_old (hres M0))
  obtain ⟨𝓕, h𝓕⟩ := twinBoundForcesInfiniteExtendedGeneratedFlows_closed hBound
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hNoEngine ⟨A, M0, hEngine⟩

/-- «В этом суть»: lexRank поставляет отсутствие двигателей как теорему —
    непознаваемость и близнецы суть ДВА СЛЕДСТВИЯ ОДНОЙ ПРИЧИНЫ, и вывод
    близнецов видимо проходит через непознаваемость. ⚠️ AXIOM-TAINTED
    (через принятую границу; несущая лемма — аксиомо-свободная выше). -/
theorem twins_because_unknowable : EuclidsPath.TwinLowers.Infinite :=
  twins_infinite_of_noEngine_and_boundary
    no_someConcreteEuclideanEngine step00CausalClosure

/-- Итоговый эпистемический статус первопричины: ЕСТЬ (аксиома, принята),
    ЗНАТЬ нельзя (теорема), ПРИНЯТИЕ даёт близнецов (условно),
    ЗНАНИЕ финитизировало бы их (через коллапс двигателя).
    ⚠️ AXIOM-TAINTED (первый и третий конъюнкты — декрет). -/
theorem epistemicFirstCauseStatus :
    Step00FirstCause ∧
    (¬ InternalKnowledgeOfCause) ∧
    EuclidsPath.TwinLowers.Infinite ∧
    (InternalKnowledgeOfCause → ¬ EuclidsPath.TwinLowers.Infinite) :=
  ⟨step00FirstCause, cause_unknowable,
   twinLowersInfinite_from_step00CausalClosure, knowledge_finitizes_twins⟩

/-#############################################################################
  §9. Растяжки непротиворечивости: точка взрыва машинно видима
#############################################################################-/

/-- **РАСТЯЖКА:** если узел когда-либо будет опровергнут (атаку `A ≤ 4`
    продлят на все `A`), карантин противоречив — False выводимо ИМЕННО здесь.
    Непротиворечивость `T + step00FirstCause` ⟺ неопровержимость узла в базе.
    ⚠️ AXIOM-TAINTED (намеренно: это и есть детектор взрыва). -/
theorem quarantine_inconsistent_if_node_refuted
    (h : ¬ TheStrictLastStep00Obligation) : False :=
  h step00CausalClosure

/-- Та же растяжка через старый узел (замыкает семью форм). ⚠️ AXIOM-TAINTED. -/
theorem quarantine_inconsistent_if_lastObligation_refuted
    (h : ¬ TheLastStep00Obligation) : False :=
  h (strictLastStep00Obligation_iff_lastStep00Obligation.mp step00CausalClosure)

/-#############################################################################
  §10. РИМАН ЧЕРЕЗ ПЕРВОПРИЧИНУ: вторая граница декрета
  (та же машина, что близнецы: отклонение → манифестация → коллизия →
  двигатель → lexRank; зелёная цепь — Engine/RiemannManifestationFront)
#############################################################################-/

/-- Римановский закон манифестации, спроецированный из первопричины:
    каждое off-critical отклонение обязано проявиться неоплатимой поставкой
    потоков там, где леджер сводит книги. ⚠️ AXIOM-TAINTED (это и есть
    принятая вторая граница декрета). -/
theorem riemannManifestationLaw : RiemannManifestationLaw :=
  step00FirstCause.riemannBoundary

/-- **RH ИЗ ЕДИНОГО РАСШИРЕННОГО ДЕКРЕТА.** ⚠️ AXIOM-TAINTED: это НЕ
    доказательство гипотезы Римана — это редукция, закрытая расширенной
    первопричиной. Цепь честно ранговая (та же, что у близнецов): нуль вне
    критической прямой — неоплаченное отклонение; принятая граница близнецов
    сводит книги на масштабе высоты нуля; закон манифестации заставляет
    отклонение проявиться бесконечной поставкой потоков; коллизия
    конечноключевой проекции строит запрещённый двигатель; lexRank его
    убивает — нуля нет. Классификация тривиальных нулей — доказанная теорема
    (`trivialBelowZeroClassification`). -/
theorem riemannHypothesis_from_firstCause : RiemannHypothesis :=
  riemannHypothesis_of_manifestation_and_boundary
    no_someConcreteEuclideanEngine step00CausalClosure riemannManifestationLaw

/-- **ЧЕСТНОСТЬ (машинно, зеркало
    `causalClosureAxiom_asserts_twins_at_every_scale`):** при принятой twin-
    границе римановская граница ⟺ RH — вторая граница декрета ровно RH-силы:
    принять расширенную первопричину = принять RH. Декрет не слабее вывода.
    ⚠️ AXIOM-TAINTED (через twin-границу). -/
theorem riemannManifestation_asserts_RH :
    RiemannManifestationLaw ↔ RiemannHypothesis :=
  manifestationLaw_iff_RH_of_boundary step00CausalClosure

/-- **РАСТЯЖКА (Риман):** если off-critical нуль когда-либо будет предъявлен,
    карантин противоречив — False выводимо ИМЕННО здесь. ⚠️ AXIOM-TAINTED
    (намеренно: детектор взрыва). -/
theorem quarantine_inconsistent_if_offCriticalZero_exhibited
    (Z : RiemannOffCriticalZero) : False :=
  noOffCriticalZero_of_manifestation_and_boundary
    no_someConcreteEuclideanEngine step00CausalClosure riemannManifestationLaw
    ⟨Z⟩

/-- **РАСТЯЖКА (Риман):** если ¬RH когда-либо будет доказана, карантин
    противоречив. Непротиворечивость `T + step00FirstCause` теперь требует
    ещё и неопровержимости RH в базе. ⚠️ AXIOM-TAINTED. -/
theorem quarantine_inconsistent_if_RH_refuted
    (h : ¬ RiemannHypothesis) : False := by
  obtain ⟨Z⟩ :=
    EuclidsPath.RiemannImpossibleEngineOff.offCriticalZero_of_not_RH h
  exact quarantine_inconsistent_if_offCriticalZero_exhibited Z

/-- **РАСТЯЖКА (Риман):** опровержение самого закона манифестации — False
    ровно здесь. ⚠️ AXIOM-TAINTED. -/
theorem quarantine_inconsistent_if_manifestation_refuted
    (h : ¬ RiemannManifestationLaw) : False :=
  h riemannManifestationLaw

-- Машинная видимость нового таинта прямо в build-логе: у RH-редукции в списке
-- аксиом ОБЯЗАН стоять step00FirstCause (и только он сверх стандартных).
#print axioms riemannHypothesis_from_firstCause

/-#############################################################################
  §11. P/NP-ЯЗЫК ДЕКРЕТА: раскол по масштабам (третьей границы НЕТ — намеренно)

  Сепарация в авторском прочтении — ЗЕЛЁНАЯ теорема на A ≤ 4
  (`pnp_rank_separation_smallScale`, Engine/PNPRankPaymentFront) и декрету
  НЕ принадлежит. Ниже — только то, что декрет УЖЕ утверждает на СВОЁМ
  масштабе A ≥ 5 через существующую twin-границу, плюс растяжка.
  Трилемма (там же, зелёно): универсальный/decider-gated кандидаты третьего
  поля опровержимы, экзистенциальный уже доказан — честного третьего поля
  не существует.
#############################################################################-/

/-- ⚠️ AXIOM-TAINTED: декрет УЖЕ даёт локальный P-успех на своём масштабе
    (обязательно A ≥ 5) на каждом M0 — там конечный ключ разрешает коллизии. -/
theorem decreedScale_localPSuccess :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      EuclidsPath.LocalPNP.LocalPSuccess
        (EuclidsPath.LocalPNP.Concrete.concreteProblem A M0) :=
  EuclidsPath.PNPRankPayment.boundary_forces_localPSuccess_at_decreed_scale
    step00CausalClosure

/-- ⚠️ AXIOM-TAINTED: на декретном масштабе первопричина ПЛАТИТ ВСЕ
    сертификаты ранга (полная оплата в авторском смысле). -/
theorem decreedScale_fullPayment :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      EuclidsPath.PNPRankPayment.FullRankCertificatePayment
        (EuclidsPath.LocalPNP.Concrete.concreteFamily A M0) :=
  EuclidsPath.PNPRankPayment.boundary_forces_fullPayment_at_decreed_scale
    step00CausalClosure

/-- ⚠️ AXIOM-TAINTED: на декретном масштабе поставка сертификатов ОГРАНИЧЕНА —
    книги сводятся, потому что поставка конечноключево учётна. -/
theorem decreedScale_supply_bounded :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      ¬ EuclidsPath.PNPRankPayment.UnboundedCertificateSupply
        (EuclidsPath.LocalPNP.Concrete.concreteFamily A M0) :=
  EuclidsPath.PNPRankPayment.boundary_bounds_supply_at_decreed_scale
    step00CausalClosure

/-- **РАСТЯЖКА (P/NP):** если малую несжимаемость когда-либо распространят
    на ВСЕ масштабы, карантин противоречив — False выводимо ИМЕННО здесь.
    ⚠️ AXIOM-TAINTED (намеренно: детектор взрыва). -/
theorem quarantine_inconsistent_if_incompressible_at_all_scales
    (h : ∀ A M0 : ℕ, EuclidsPath.LocalPNP.LocalSearchIncompressible
      (EuclidsPath.LocalPNP.Concrete.concreteProblem A M0)) : False := by
  obtain ⟨A, _, hLP⟩ := decreedScale_localPSuccess
  exact h A 0 (hLP 0)

-- Машинная видимость: P/NP-язык декрета заражён ровно step00FirstCause.
#print axioms decreedScale_localPSuccess

/-#############################################################################
  §12. ЯНГ–МИЛЛС-ЯЗЫК ДЕКРЕТА: гэп его собственного мира
  (четвёртой границы НЕТ — намеренно; трилемма: Engine/YangMillsFront §7;
  per-model закон ⟺ гэп зелёно — декретировать было бы = декретировать цель;
  мир декрета интринзично квантован (lexRank : ℕ) — ниже только то, что
  декрет утверждает САМ.)
#############################################################################-/

/-- ⚠️ AXIOM-TAINTED: на декретном масштабе (обязательно A ≥ 5) поставка
    отклонений ОТСУТСТВУЕТ на каждом M0 — в мире первопричины нет бесконечной
    башни сколь-угодно-дешёвых возбуждений: декрет гэпнут в языке поставок. -/
theorem decreedScale_no_deviationSupply :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ, ¬ DeviationFlowSupply A M0 :=
  EuclidsPath.YangMills.boundary_refuses_deviationSupply_at_decreed_scale
    step00CausalClosure

/-- **РАСТЯЖКА (Янг–Миллс):** если поставку отклонений когда-либо предъявят
    на ВСЕХ масштабах (включая декретный A ≥ 5), карантин противоречив —
    False выводимо ИМЕННО здесь. Безопасность растяжки: зелёный мир знает
    поставку только при A ≤ 4 (`smallScale_deviationSupply`); кованые
    спектральные модели Янга–Миллса живут в спектральном мире и этого
    утверждения не касаются. ⚠️ AXIOM-TAINTED (намеренно: детектор взрыва). -/
theorem quarantine_inconsistent_if_supply_at_every_scale
    (h : ∀ A M0 : ℕ, DeviationFlowSupply A M0) : False := by
  obtain ⟨A, _, hNo⟩ := decreedScale_no_deviationSupply
  exact hNo 0 (h A 0)

-- Машинная видимость: ЯМ-язык декрета заражён ровно step00FirstCause.
#print axioms decreedScale_no_deviationSupply

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
