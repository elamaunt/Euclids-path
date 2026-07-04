/-
  PolignacEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ ПОЛИНЬЯКА (кузены p, p+4 и
  секси p, p+6 — случаи 4 и 6 гипотезы Полиньяка). Программа Яруса 1.
  Зелёная машина обеих семей: Engine/PolignacManifestationFront.lean (M1–M9).
  Ряд эталонов: CollatzFirstCause (эпистемика пост-мортема), PNPFirstCause
  (комплемент P/NP); twin-версия живёт в §8 карантина и сюда НЕ импортируется.

  ЧТО ЭТО. «Решить случай 4/6 изнутри» моделируется трёхполевой связкой
  `InternalisedCousinGround` / `InternalisedSexyGround`: закон манифестации
  (`ground`), свидетель отсутствия центров не выше леджер-масштаба (`absence`)
  и сведённые книги на этом масштабе (`beyondOwnHorizon`). Тройка НЕСОВМЕСТИМА
  зелёно: она напрямую собирает вечный двигатель (`cousinRefutation_carries_engine` /
  `sexyRefutation_carries_engine` — подлинная конструкция через
  `infiniteFlows_in_stableNoEnergy_build_engine`, НЕ ex falso) — и гибнет об
  зелёную стену `no_someConcreteEuclideanEngine` (lexRank строго падает).

  ЧЕСТНОСТЬ (все оговорки раскрыты и в докстроках):
  * это МОДЕЛЬ-ВНУТРЕННЯЯ эпистемика — НЕ доказательство и НЕ опровержение
    случаев 4/6 Полиньяка (они открыты) и НЕ Гёдель (самоуничтожение об
    lexRank-стену, а не теорема о неполноте/неподвижной точке);
  * связка трёхполевая и ни одно поле не есть отрицание другого — это СТИЛЬ
    P/NP, но НЕ арность: эталон `InternalisedPNPGround` сам ДВУХполевой
    (resolves + beyondOwnHorizon); общая родословная — не-тавтологичность
    пары/тройки, в отличие от честно помеченного тавтологичным двуполевого
    `InternalisedCollatzGround` (ground + ¬ground = P ∧ ¬P);
  * закон `CousinManifestationLaw` / `SexyManifestationLaw` ГЕЙЧЕН свидетелем
    отсутствия (∀ P, свидетель → манифестация) и НЕ декретирован (полей
    cousinBoundary/sexyBoundary в Step00FirstCause нет — вердикт §17, при
    ПОЛОЖИТЕЛЬНОМ знаке Харди–Литтлвуда): оплата противоречия УСЛОВНА на
    не-декретированный закон и сведённые книги — слабее безусловного
    `nonHalting_carries_perpetual_engine` Коллатца и зелёного пижонхола
    `no_fullPayment_of_unboundedSupply` P/NP;
  * НИ ОДНО из трёх полей зелёно не обитаемо (у P/NP `beyondOwnHorizon`
    зелёно-обитаем — `concreteSupply_unbounded_smallScale`): связка есть
    зелёная НЕСОВМЕСТИМОСТЬ трёх порознь-неизвестных полей;
  * граница появляется ТОЛЬКО гипотезой `TheStrictLastStep00Obligation`
    (в конъюнктах вида «граница → (закон ↔ неограниченность)»): модуль
    карантин не импортирует, целиком зелёный, таинт репозитория не меняется.
-/

import EuclidsPath.Engine.PolignacManifestationFront

set_option autoImplicit false

namespace EuclidsPath.Polignac.Epistemic

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.PolignacBranch

/-! ## Модель: внутреннее решение = самообоснование за собственным горизонтом

Для КАЖДОЙ из двух семей (кузены — случай 4, секси — случай 6) связка
параметрична по леджер-масштабу `(A, M0)` — тому самому, на котором
`cousinRefutation_carries_engine` собирает двигатель. -/

/-- **Внутреннее самообоснование решения случая 4 (кузены `p, p+4`).** Несёт
    (a) закон манифестации `ground` — ГЕЙЧЕННЫЙ свидетелем и НЕ декретированный
    (§17); (b) свидетель отсутствия кузен-центров не выше масштаба `absence`;
    (c) сведённые книги на этом масштабе `beyondOwnHorizon`. Ни одно поле не
    есть отрицание другого (стиль P/NP; но эталон `InternalisedPNPGround` сам
    ДВУХполевой — общее здесь СТИЛЬ, не арность), и ни одно поле зелёно не
    обитаемо (в отличие от зелёно-обитаемого `beyondOwnHorizon` у P/NP):
    содержательность связки — зелёная НЕСОВМЕСТИМОСТЬ трёх порознь-неизвестных
    полей, оплаченная подлинной двигательной конструкцией
    `cousinRefutation_carries_engine` об стену `no_someConcreteEuclideanEngine`. -/
structure InternalisedCousinGround (A M0 : ℕ) : Prop where
  ground : CousinManifestationLaw
  absence : ∃ P : ℕ, P ≤ M0 ∧ CousinAbsenceAbove P
  beyondOwnHorizon : ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
    SemanticExtendedFlowLedgerCollisionResolves proj

/-- «Внутреннее знание причины случая 4» = внутреннее самообоснование. -/
abbrev InternalKnowledgeOfCousinCause (A M0 : ℕ) : Prop :=
  InternalisedCousinGround A M0

/-- **Внутреннее самообоснование решения случая 6 (секси `p, p+6`)** — зеркало
    кузенов; свидетель `SexyAbsenceAbove` ДВУСТОРОННИЙ (гейт по Or минус/плюс
    пар — сильнее каждой стороны порознь, раскрыто во фронте). Те же честные
    оговорки, что у `InternalisedCousinGround`. -/
structure InternalisedSexyGround (A M0 : ℕ) : Prop where
  ground : SexyManifestationLaw
  absence : ∃ P : ℕ, P ≤ M0 ∧ SexyAbsenceAbove P
  beyondOwnHorizon : ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
    SemanticExtendedFlowLedgerCollisionResolves proj

/-- «Внутреннее знание причины случая 6» = внутреннее самообоснование. -/
abbrev InternalKnowledgeOfSexyCause (A M0 : ℕ) : Prop :=
  InternalisedSexyGround A M0

/-! ## Ядро: самообоснование строит двигатель и гибнет об lexRank-стену (🟢) -/

/-- **Самообоснование случая 4 СТРОИТ двигатель** — прямая композиция
    `cousinRefutation_carries_engine` (подлинная конструкция: закон поставляет
    семью потоков, стабильная вселенная превращает её в двигатель-СВИДЕТЕЛЬ),
    НЕ ex falso — в отличие от `internalisedPNPGround_builds_engine`, где
    маршрут ex falso. Цена честности: конструкция УСЛОВНА на гейченный
    не-декретированный закон и сведённые книги — оба поля порознь неизвестны. -/
theorem internalisedCousinGround_builds_engine {A M0 : ℕ}
    (H : InternalisedCousinGround A M0) : SomeConcreteEuclideanEngine := by
  obtain ⟨P, hPM, hAbs⟩ := H.absence
  obtain ⟨proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, cousinRefutation_carries_engine H.ground hAbs hPM proj hres⟩

/-- Самообоснование случая 4 самоуничтожается: построенный двигатель гибнет об
    зелёную стену `no_someConcreteEuclideanEngine` (lexRank строго падает).
    ЗЕЛЁНАЯ, стандартная тройка. -/
theorem no_internalisedCousinGround {A M0 : ℕ} :
    InternalisedCousinGround A M0 → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedCousinGround_builds_engine H)

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА для случая 4** (зеркало
    `collatzCause_unknowable` / `pnpCause_unknowable`): внутреннее знание
    причины кузенов невозможно ни на каком леджер-масштабе. НЕ утверждение о
    самих кузенах: случай 4 открыт, закон не декретирован. -/
theorem cousinCause_unknowable {A M0 : ℕ} :
    ¬ InternalKnowledgeOfCousinCause A M0 :=
  no_internalisedCousinGround

/-- **Самообоснование случая 6 СТРОИТ двигатель** — те же оговорки, что у
    кузенов (подлинная конструкция, условная на гейченный закон и книги). -/
theorem internalisedSexyGround_builds_engine {A M0 : ℕ}
    (H : InternalisedSexyGround A M0) : SomeConcreteEuclideanEngine := by
  obtain ⟨P, hPM, hAbs⟩ := H.absence
  obtain ⟨proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, sexyRefutation_carries_engine H.ground hAbs hPM proj hres⟩

/-- Самообоснование случая 6 самоуничтожается об ту же lexRank-стену. -/
theorem no_internalisedSexyGround {A M0 : ℕ} :
    InternalisedSexyGround A M0 → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedSexyGround_builds_engine H)

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА для случая 6.** -/
theorem sexyCause_unknowable {A M0 : ℕ} :
    ¬ InternalKnowledgeOfSexyCause A M0 :=
  no_internalisedSexyGround

/-! ## Развилки: решение заперто за двигателем (🟢) -/

/-- **3-развилка случая 4 (зеркало `pnp_no_internal_decision_without_engine`):**
    (1) САМООБОСНОВАТЬ изнутри = построить двигатель (подлинная конструкция);
    (2) построенное самоуничтожается об lexRank-стену;
    (3) единственный оставшийся путь — ВНЕШНИЙ декрет: при границе-ГИПОТЕЗЕ
        `TheStrictLastStep00Obligation` закон ⟺ неограниченность кузен-центров
        (M7: поле стоило бы ровно случая 4) — и это поле НАМЕРЕННО не взято.
    НЕ гёделевская независимость и НЕ решение случая 4 — только: внутреннее
    решение стоит вечного двигателя, а внешняя дверь не декретирована. -/
theorem cousin_no_internal_decision_without_engine {A M0 : ℕ} :
    (InternalisedCousinGround A M0 → SomeConcreteEuclideanEngine) ∧
    (InternalisedCousinGround A M0 → False) ∧
    (TheStrictLastStep00Obligation →
        (CousinManifestationLaw ↔ CousinCentersUnbounded)) :=
  ⟨internalisedCousinGround_builds_engine,
   no_internalisedCousinGround,
   cousinManifestationLaw_iff_unbounded_of_boundary⟩

/-- **3-развилка случая 6** — секси-зеркало (M7: поле стоило бы ровно случая 6). -/
theorem sexy_no_internal_decision_without_engine {A M0 : ℕ} :
    (InternalisedSexyGround A M0 → SomeConcreteEuclideanEngine) ∧
    (InternalisedSexyGround A M0 → False) ∧
    (TheStrictLastStep00Obligation →
        (SexyManifestationLaw ↔ SexyCentersUnbounded)) :=
  ⟨internalisedSexyGround_builds_engine,
   no_internalisedSexyGround,
   sexyManifestationLaw_iff_unbounded_of_boundary⟩

/-- **«РЕШЕНИЕ ПОЛИНЬЯКА-4/6 ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» — обе семьи разом**
    (зеркало `pnp_no_internal_decision_without_engine`, две развилки одной
    теоремой). Граница — только гипотеза; закон — только гейт; модуль зелёный. -/
theorem polignac_no_internal_decision_without_engine {A M0 : ℕ} :
    ((InternalisedCousinGround A M0 → SomeConcreteEuclideanEngine) ∧
     (InternalisedCousinGround A M0 → False) ∧
     (TheStrictLastStep00Obligation →
         (CousinManifestationLaw ↔ CousinCentersUnbounded))) ∧
    ((InternalisedSexyGround A M0 → SomeConcreteEuclideanEngine) ∧
     (InternalisedSexyGround A M0 → False) ∧
     (TheStrictLastStep00Obligation →
         (SexyManifestationLaw ↔ SexyCentersUnbounded))) :=
  ⟨cousin_no_internal_decision_without_engine,
   sexy_no_internal_decision_without_engine⟩

/-! ## Сводки статуса: без декрет-конъюнкта — поля-границы у Полиньяка НЕТ (🟢) -/

/-- Итоговый эпистемический статус случая 4 (зеркало
    `pnp_locked_behind_engine_status`, БЕЗ декрет-конъюнкта — вердикт §17):
    внутреннее знание невозможно (теорема) / всякий свидетель отсутствия сидит
    не ниже 37 — кузен-центр 37 = пара (223, 227) зелёно существует (M8) /
    при границе-гипотезе закон ⟺ неограниченность (M7 — цена недекретированного
    поля) / неограниченность довела бы до цели программы: пары кузенов
    бесконечны (честный мост ветви). ЗЕЛЁНАЯ целиком. -/
theorem cousin_locked_behind_engine_status {A M0 : ℕ} :
    (¬ InternalKnowledgeOfCousinCause A M0) ∧
    (∀ P : ℕ, CousinAbsenceAbove P → 37 ≤ P) ∧
    (TheStrictLastStep00Obligation →
        (CousinManifestationLaw ↔ CousinCentersUnbounded)) ∧
    (CousinCentersUnbounded → CousinLowers.Infinite) :=
  ⟨cousinCause_unknowable,
   fun _P hAbs => cousinAbsenceBound_ge_37 hAbs,
   cousinManifestationLaw_iff_unbounded_of_boundary,
   cousinLowersInfinite_of_unbounded⟩

/-- Итоговый эпистемический статус случая 6 (порог M8 = 17: минус-пара
    (101, 107) при m = 17; свидетель двусторонний). ЗЕЛЁНАЯ целиком. -/
theorem sexy_locked_behind_engine_status {A M0 : ℕ} :
    (¬ InternalKnowledgeOfSexyCause A M0) ∧
    (∀ P : ℕ, SexyAbsenceAbove P → 17 ≤ P) ∧
    (TheStrictLastStep00Obligation →
        (SexyManifestationLaw ↔ SexyCentersUnbounded)) ∧
    (SexyCentersUnbounded → SexyLowers.Infinite) :=
  ⟨sexyCause_unknowable,
   fun _P hAbs => sexyAbsenceBound_ge_17 hAbs,
   sexyManifestationLaw_iff_unbounded_of_boundary,
   sexyLowersInfinite_of_unbounded⟩

/-- **Итоговый эпистемический статус Полиньяка-4/6 — обе семьи разом**
    (без декрет-конъюнкта: полей cousinBoundary/sexyBoundary в
    Step00FirstCause не существует — §17, при положительном знаке эвристики).
    Случаи 4 и 6 остаются 🔴 открытыми; здесь лишь машинно видимая цена:
    изнутри — двигатель, снаружи — недекретированный закон ровно гипотезной
    силы. ЗЕЛЁНАЯ целиком, таинт не меняется. -/
theorem polignac_locked_behind_engine_status {A M0 : ℕ} :
    ((¬ InternalKnowledgeOfCousinCause A M0) ∧
     (∀ P : ℕ, CousinAbsenceAbove P → 37 ≤ P) ∧
     (TheStrictLastStep00Obligation →
         (CousinManifestationLaw ↔ CousinCentersUnbounded)) ∧
     (CousinCentersUnbounded → CousinLowers.Infinite)) ∧
    ((¬ InternalKnowledgeOfSexyCause A M0) ∧
     (∀ P : ℕ, SexyAbsenceAbove P → 17 ≤ P) ∧
     (TheStrictLastStep00Obligation →
         (SexyManifestationLaw ↔ SexyCentersUnbounded)) ∧
     (SexyCentersUnbounded → SexyLowers.Infinite)) :=
  ⟨cousin_locked_behind_engine_status,
   sexy_locked_behind_engine_status⟩

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка),
    БЕЗ step00FirstCause — таинт репозитория НЕ меняется -/
#print axioms internalisedCousinGround_builds_engine
#print axioms no_internalisedCousinGround
#print axioms cousinCause_unknowable
#print axioms internalisedSexyGround_builds_engine
#print axioms no_internalisedSexyGround
#print axioms sexyCause_unknowable
#print axioms cousin_no_internal_decision_without_engine
#print axioms sexy_no_internal_decision_without_engine
#print axioms polignac_no_internal_decision_without_engine
#print axioms cousin_locked_behind_engine_status
#print axioms sexy_locked_behind_engine_status
#print axioms polignac_locked_behind_engine_status

end EuclidsPath.Polignac.Epistemic
