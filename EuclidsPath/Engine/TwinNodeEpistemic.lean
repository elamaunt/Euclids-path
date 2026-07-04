/-
  TwinNodeEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ ГЛАВНОГО УЗЛА (близнецы),
  зеркало CollatzFirstCause / PNPFirstCause. Зелёная машина: Engine/ConcreteStep00Graph.lean.

  ЧТО ЭТО. Финальный узел близнецов — TheLastStep00Obligation: «существует масштаб A и
  проекции леджера на все базы M0, резолвящие каждую same-key коллизию генеалогий».
  «Решить узел изнутри на собственном горизонте» = предъявить A-срез узла при зелёно
  видимом горизонте системы A ≤ 4. Это самоуничтожается НЕ подстановкой P ∧ ¬P, а
  настоящим пижонхолом: 5-адическая цепь даёт бесконечную инъективную admissible-поставку
  (`fiveAdicChainFlow`, инъективность через `fiveAdicChain_strictMono`), и
  `Finite.exists_ne_map_eq_of_infinite` выбивает same-key пару из любого конечного ключа
  (`no_projection_resolves_at_smallScale`) — ровно та же валюта, что
  `no_fullPayment_of_unboundedSupply` у P/NP и стена вечного двигателя у Коллатца.

  ЧЕСТНОСТЬ. Это модель-внутренняя эпистемическая непознаваемость, а НЕ доказательство
  и НЕ опровержение гипотезы близнецов, и НЕ Гёдель (пижонхол-самоуничтожение, а не
  теорема о неполноте). Содержательность РАСКОЛОТА ПО МАСШТАБАМ: при A ≤ 4 связка
  `ground` + `beyondOwnHorizon` содержательна (противоречие — теорема, оплаченная
  пижонхолом); при A ≥ 5 структура `InternalisedTwinGround` пуста уже по полю горизонта
  (A ≤ 4), т.е. там связка ФОРМАЛЬНА — и так и должно быть: зелёного противоречия при
  A ≥ 5 нет и быть не может, иначе узел был бы решён. Непознаваемость twin-узла машинно
  видима именно как этот раскол. В отличие от Коллатца, «опровержение ⟹ двигатель»
  у близнецов НЕ безусловно: двигатель строится лишь в стабильной вселенной
  (`NoEnergyStableUniverse`) — стабильность леджера и есть то, что открыто при A ≥ 5
  и в карантинном слое поставляется декретом.

  Файл ЦЕЛИКОМ ЗЕЛЁНЫЙ: не импортирует Engine/CausalClosureAxiom (карантин),
  не трогает аксиому step00FirstCause и таинт-список из 52 деклараций.
-/

import EuclidsPath.Engine.ConcreteStep00Graph

set_option autoImplicit false

namespace EuclidsPath.ConcreteStep00Graph.Epistemic

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-! ## (а) Опровержение близнецов несёт безусловную бесконечную поставку (🟢) -/

/-- **«ОПРОВЕРЖЕНИЕ ПРЕДЪЯВЛЯЕТ ПОСТАВКУ» (зелёная, безусловная).** Если множество
    нижних близнецов конечно, то существует twin-bound `M0`, и на КАЖДОМ масштабе `A`
    из него строится бесконечная admissible-поставка генеалогий — аналог
    `UnboundedCertificateSupply` у P/NP. Подлинная конструкция через
    cofactor-normalizer (`twinBoundForcesInfiniteExtendedGeneratedFlows_closed`),
    не пустышка. ЧЕСТНОСТЬ: сама по себе поставка двигателя ещё НЕ строит —
    см. следующую теорему и её цену. -/
theorem twinBound_carries_unbounded_supply
    (hfin : ¬ TwinLowers.Infinite) :
    ∃ M0 : ℕ, ∀ A : ℕ,
      ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
        InfiniteExtendedGeneratedFlowFamily A M0 𝓕 := by
  obtain ⟨M0, hBound⟩ := exists_twinBoundAbove_of_not_twinLowersInfinite hfin
  exact ⟨M0, fun A =>
    twinBoundForcesInfiniteExtendedGeneratedFlows_closed hBound⟩

/-! ## (б) Опровержение в стабильной вселенной строит двигатель (🟢, условная) -/

/-- **«ОПРОВЕРЖЕНИЕ В СТАБИЛЬНОЙ ВСЕЛЕННОЙ СТРОИТ ДВИГАТЕЛЬ» (зелёная).**
    Конечность близнецов + стабильный no-energy леджер на каждом срезе ⟹
    конкретный евклидов двигатель (`SomeConcreteEuclideanEngine`), который запрещён
    (`no_someConcreteEuclideanEngine`, lexRank строго падает).
    ЧЕСТНОСТЬ (три оговорки):
    (1) это НЕ безусловное «опровержение = двигатель», как у Коллатца
        (`nonHalting_carries_perpetual_engine`): нужна гипотеза `NoEnergyStableUniverse`,
        и именно стабильность леджера — то, что открыто при A ≥ 5 и в карантинном
        слое поставляется декретом;
    (2) эта цепь дословно прогнана внутри `twins_infinite_of_noEngine_and_boundary`
        (CausalClosureAxiom.lean, §8) — здесь ВЫНОС ЗЕЛЁНОГО ИМЕНИ из карантинного
        файла в чистый модуль, а не новое содержание;
    (3) половина «поставка + стабильность ⟹ двигатель» — тонкая обёртка над
        существующей `infiniteFlows_in_stableNoEnergy_build_engine`. -/
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

/-! ## (в) Сужение узла в точной strict-форме декрета (🟢) -/

/-- **СУЖЕНИЕ УЗЛА, STRICT-ФОРМА.** `TheStrictLastStep00Obligation` — ровно та форма,
    которую утверждает `causalBoundary` декрета (в карантинном слое; здесь сам декрет
    НЕ используется) — машинно загнана в `A ≥ 5`: срез A ≤ 4 опровергнут 5-адической
    цепью. Тривиальная композиция iff-моста
    `strictLastStep00Obligation_iff_lastStep00Obligation` и уже доказанного сужения
    `lastStep00Obligation_forces_scale_ge_five`; уточняет растяжку
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

/-! ## (г) Модель: внутреннее решение узла = самообоснование за горизонтом -/

/-- **Внутреннее самообоснование twin-узла на собственном горизонте.** Несёт
    (a) `ground` — A-срез финального узла: проекции на все базы `M0` резолвят каждую
    коллизию (слайс `TheLastStep00Obligation` на фиксированном масштабе), и
    (b) `beyondOwnHorizon` — сам масштаб лежит в зелёно видимом горизонте системы
    (A ≤ 4, где работает 5-адическая цепь).
    СОДЕРЖАТЕЛЬНОСТЬ: `ground` и `beyondOwnHorizon` — не `P` и `¬P`; противоречие
    поставляет пижонхол `no_projection_resolves_at_smallScale`
    (`Finite.exists_ne_map_eq_of_infinite` на инъективной семье `fiveAdicChainFlow`).
    ЧЕСТНОСТЬ: при A ≥ 5 структура пуста уже по полю `beyondOwnHorizon` — там связка
    формальна, и это правильно: зелёного противоречия при A ≥ 5 нет (иначе узел был
    бы решён); непознаваемость видима как раскол по масштабам. -/
structure InternalisedTwinGround (A : ℕ) : Prop where
  ground : ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0)
  beyondOwnHorizon : A ≤ 4

/-- «Внутреннее знание причины близнецов» = внутреннее самообоснование узла. -/
abbrev InternalKnowledgeOfTwinCause (A : ℕ) : Prop := InternalisedTwinGround A

/-- Самообоснование самоуничтожается — оплачено пижонхолом
    `no_projection_resolves_at_smallScale` (через
    `smallScale_branch_of_lastStep00Obligation_refuted`), НЕ тавтологией. ЗЕЛЁНАЯ. -/
theorem no_internalisedTwinGround {A : ℕ} :
    InternalisedTwinGround A → False :=
  fun H =>
    smallScale_branch_of_lastStep00Obligation_refuted H.beyondOwnHorizon H.ground

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `collatzCause_unknowable`,
    `pnpCause_unknowable`): внутреннее решение twin-узла на собственном горизонте
    невозможно. ЗЕЛЁНАЯ, вообще без гипотез. -/
theorem twinNode_unknowable {A : ℕ} : ¬ InternalKnowledgeOfTwinCause A :=
  no_internalisedTwinGround

/-! ## Сводки: решение заперто за двигателем (🟢) -/

/-- **«РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» — 3-РАЗВИЛКА (зелёная; зеркало
    `collatz_no_internal_decision_without_engine`, `pnp_no_internal_decision_without_engine`):**
    (1) ОПРОВЕРГНУТЬ близнецов против стабильного леджера = построить двигатель
        (twin-bound ⟹ бесконечная поставка ⟹ same-key коллизия ⟹ `LegalCycle`,
        запрещённый lexRank); цена честно видна: нужна `NoEnergyStableUniverse`;
    (2) САМООБОСНОВАТЬ узел на своём горизонте — самоуничтожается
        (`no_internalisedTwinGround`, пижонхол);
    (3) единственный путь — ВНЕШНЯЯ ГРАНИЦА: strict-узел, честно принятый снаружи,
        влечёт бесконечность близнецов (`twinLowersInfinite_of_strictLastStep00Obligation`,
        зелёная условная стрелка; сам strict-узел здесь НЕ утверждается).
    НЕ утверждается гёделевская независимость и НЕ решение гипотезы близнецов —
    только: оба внутренних решения стоят вечного двигателя. -/
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

/-- Итоговый эпистемический статус twin-узла (зелёный; зеркало
    `pnp_locked_behind_engine_status` — БЕЗ декрет-конъюнкта: жёлтая версия с
    `step00FirstCause` добавила бы новые заражённые декларации и сюда не входит):
    (1) поставка при A ≤ 4 существует безусловно (5-адическая цепь, инъективность);
    (2) узел непознаваем изнутри (теорема);
    (3) узел загнан в A ≥ 5 (`lastStep00Obligation_forces_scale_ge_five`);
    (4) опровержение близнецов в стабильной вселенной строит двигатель;
    (5) двигатель запрещён (`no_someConcreteEuclideanEngine`, lexRank).
    Вместе (4)+(5) дают условную бесконечность близнецов в стабильной вселенной —
    зелёное содержание, уже записанное как `twins_infinite_of_noEngine_and_boundary`
    в карантинном файле; здесь оно живёт без карантина. -/
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

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка), таинт репо НЕ меняется -/
#print axioms twinBound_carries_unbounded_supply
#print axioms twinRefutation_in_stableUniverse_builds_engine
#print axioms strictLastStep00Obligation_forces_scale_ge_five
#print axioms no_internalisedTwinGround
#print axioms twinNode_unknowable
#print axioms twin_no_internal_decision_without_engine
#print axioms twin_locked_behind_engine_status

end EuclidsPath.ConcreteStep00Graph.Epistemic
