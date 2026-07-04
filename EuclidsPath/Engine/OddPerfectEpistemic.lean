/-
  OddPerfectEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ нечётных совершенных чисел
  (зеркало CollatzFirstCause / PNPFirstCause). Зелёная машина фронта:
  Engine/OddPerfectManifestationFront.lean; ветвь: Engine/PerfectNumberBranch.lean.

  ЧТО ЭТО. «Решить изнутри» вопрос о нечётном совершенном числе = предъявить
  свидетеля ВНУТРИ собственного проверенного горизонта (`ground`: ∃ W, W.1 < 101),
  неся при этом машинную развёртку этого самого горизонта (`beyondOwnHorizon`:
  все нечётные ЧИСЛА ниже 101 отсеяны kernel-вычислением). Ноги НЕ являются
  логическими дополнениями друг друга: `ground` говорит о СВИДЕТЕЛЯХ
  (subtype `OddPerfectNumber`), `beyondOwnHorizon` — сырой decide-факт о числах;
  противоречие требует реальной медиации (распаковка subtype + `Nat.odd_iff`),
  и kernel-оплата входит в само опровержение.

  ЧЕМ ОПЛАЧЕНА СОДЕРЖАТЕЛЬНОСТЬ (честно, по пунктам). (1) Вторая нога ЗЕЛЁНО
  ОБИТАЕМА: `oddPerfect_horizon_swept` — kernel-развёртка горизонта, ровно
  внутренность доказательства `oddPerfect_ge_101` (поточечная разрешимость
  `DecidablePred Nat.Perfect` в действии). Это лучше Коллатца (там
  `InternalisedCollatzGround` — голая пара закон/не-закон, оплаченная декретом
  `collatzBoundary`; здесь декрета нет — §17-вердикт — и он не нужен), но
  СЛАБЕЕ пижонхола P/NP: у `no_fullPayment_of_unboundedSupply` противоречие
  несёт отдельная зелёная теорема о бесконечном против конечного, здесь —
  конечное kernel-вычисление. Закон-форма ground := закон / ¬закон здесь
  ВЫРОЖДАЕТСЯ в тавтологию (отождествляющего декрета нет) — она сознательно
  НЕ взята. (2) Двигательная сторона (`oddPerfectWitness_carries_engine`)
  УСЛОВНА на закон манифестации (`hLaw : OddPerfectManifestationLaw` — живёт
  определением, поле НЕ декретировано) и на сведённые книги: безусловного
  аналога `nonHalting_carries_perpetual_engine` у этого фронта НЕТ и быть не
  может без решения самой задачи — гипотезы всюду оставлены явными.

  ЧЕСТНОСТЬ. Это модель-внутренняя эпистемика, НЕ решение старейшей открытой
  задачи математики и НЕ Гёдель (никакой независимости и неподвижной точки —
  только вычислительный отсев и стена вечного двигателя). Пуант, уникальный
  для этого фронта: «внешняя проверка» — буквально `DecidablePred Nat.Perfect`,
  сильнейшая форма среди всех фронтов (всякая фальшивка умирает decide'ом,
  ср. `not_perfect_945`); предъявить НАСТОЯЩЕГО свидетеля при законе и книгах =
  предъявить двигатель — потому свидетель зелёно непредъявим
  (`oddPerfectWitness_green_unpresentable`). Модуль ЦЕЛИКОМ ЗЕЛЁНЫЙ:
  карантин НЕ импортируется, axiom/sorry/native_decide нет, таинт 52 не меняется.
-/

import EuclidsPath.Engine.OddPerfectManifestationFront

set_option autoImplicit false

namespace EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic

open EuclidsPath.PerfectNumberBranch

/-! ## Развёртка горизонта: зелёная обитаемость второй ноги (🟢) -/

/-- **Развёртка собственного проверенного горизонта (зелёная, kernel-вычисление):**
    все нечётные числа ниже 101 машинно отсеяны поточечной проверкой
    совершенности — ровно внутренность доказательства `oddPerfect_ge_101`
    (`PerfectNumberBranch`), вынесенная в именованный факт о ЧИСЛАХ (не о
    свидетелях). Именно этой обитаемостью — как `concreteSupply_unbounded_smallScale`
    у P/NP — оплачена содержательность связки ниже; у Коллатца аналога нет. -/
theorem oddPerfect_horizon_swept :
    ∀ M : ℕ, M < 101 → M % 2 = 1 → ¬ Nat.Perfect M := by decide

/-! ## Модель: внутреннее решение = свидетель внутри собственного горизонта -/

/-- **Внутреннее самообоснование решения о нечётном совершенном.** Несёт
    (a) свидетеля ВНУТРИ собственного проверенного горизонта (`ground`) и
    (b) машинную развёртку этого горизонта (`beyondOwnHorizon`) — сырой
    decide-факт о числах, зелёно обитаемый (`oddPerfect_horizon_swept`).
    Ноги НЕ дополнения друг друга (CORR-фикс скептика: наивная пара
    ∃ W, W.1 < 101 / ∀ W, 101 ≤ W.1 сворачивалась бы в кванторную тавтологию
    `Nat.not_le`): противоречие ниже добывается медиацией — распаковкой
    subtype-свидетеля и переводом `Odd` в `% 2 = 1`. Это «дотянуться взглядом»
    за собственный проверенный горизонт, неся его развёртку в руках. -/
structure InternalisedOddPerfectGround : Prop where
  ground : ∃ W : OddPerfectNumber, W.1 < 101
  beyondOwnHorizon : ∀ M : ℕ, M < 101 → M % 2 = 1 → ¬ Nat.Perfect M

/-- «Внутреннее знание причины» = внутреннее самообоснование решения
    (зеркало `InternalKnowledgeOfCollatzCause` / `InternalKnowledgeOfPNPCause`). -/
abbrev InternalKnowledgeOfOddPerfectCause : Prop := InternalisedOddPerfectGround

/-! ## Ядро: самообоснование самоуничтожается (🟢) -/

/-- Самообоснование самоуничтожается: свидетель из `ground` распаковывается
    в число `N < 101` с `Odd N` и `Nat.Perfect N`, а `beyondOwnHorizon` — его
    же развёртка горизонта — это число убивает. Медиация настоящая (subtype +
    `Nat.odd_iff`), не подстановка `H.beyondOwnHorizon H.ground`. ЗЕЛЁНАЯ. -/
theorem no_internalisedOddPerfectGround : InternalisedOddPerfectGround → False := by
  rintro ⟨⟨⟨N, hodd, hperf⟩, hlt⟩, hsweep⟩
  exact hsweep N hlt (Nat.odd_iff.mp hodd) hperf

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `collatzCause_unknowable` /
    `pnpCause_unknowable`, twin-`cause_unknowable`): внутреннее знание причины
    для нечётных совершенных невозможно. НЕ утверждение о (не)существовании
    нечётного совершенного числа — только о невозможности самообоснования
    внутри собственного проверенного горизонта. ЗЕЛЁНАЯ. -/
theorem oddPerfectCause_unknowable : ¬ InternalKnowledgeOfOddPerfectCause :=
  no_internalisedOddPerfectGround

/-- **Свидетель ниже горизонта невозможен безусловно (🟢):** здесь sweep
    платит напрямую — `oddPerfect_ge_101` есть in-repo теорема, и никакой
    нечётный совершенный свидетель не помещается ниже 101. Дополнение
    CORR-3 скептика: та же стена, что в `no_internalisedOddPerfectGround`,
    но без структуры самообоснования. -/
theorem no_oddPerfectWitness_below_horizon :
    ¬ ∃ W : OddPerfectNumber, W.1 < 101 :=
  fun ⟨W, h⟩ => absurd (oddPerfect_ge_101 W) (Nat.not_le.mpr h)

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ (без ex falso в утверждении): либо причина
    непознаваема изнутри, либо свидетель есть ниже проверенного горизонта.
    Левый дизъюнкт — теорема; правый безусловно убит
    `no_oddPerfectWitness_below_horizon` — оба факта зелёные. -/
theorem unknowable_or_oddPerfect_below_horizon :
    (¬ InternalKnowledgeOfOddPerfectCause) ∨
      ∃ W : OddPerfectNumber, W.1 < 101 :=
  Or.inl oddPerfectCause_unknowable

/-- Ex-falso companion («несёт двигатель», зеркало
    `internalisedPNPGround_builds_engine`): из самообоснования (уже ложного)
    выводится и сам двигатель. ЧЕСТНОСТЬ: маршрут ex falso; несущая часть —
    сама невозможность (`no_internalisedOddPerfectGround`); подлинная
    двигательная конструкция — условная `oddPerfectWitness_carries_engine`. -/
theorem internalisedOddPerfectGround_builds_engine :
    InternalisedOddPerfectGround → SomeConcreteEuclideanEngine :=
  fun H => (no_internalisedOddPerfectGround H).elim

/-! ## Свидетель зелёно непредъявим: предъявить = предъявить двигатель -/

/-- **«ПРЕДЪЯВИТЬ СВИДЕТЕЛЯ = ПРЕДЪЯВИТЬ ДВИГАТЕЛЬ — ПОТОМУ НЕПРЕДЪЯВИМ»
    (условная зелёная сводка):** при законе манифестации и принятой границе
    тип нечётных совершенных свидетелей пуст — потому что любой предъявленный
    свидетель предъявил бы вечный двигатель (`oddPerfectWitness_carries_engine`),
    а двигателей зелёно нет (`no_someConcreteEuclideanEngine`).
    ЧЕСТНОСТЬ: обе гипотезы ЯВНЫЕ — закон живёт определением (поле НЕ
    декретировано, §17-вердикт), граница подаётся снаружи; безусловной формы
    у этого фронта нет и быть не может без решения самой задачи. -/
theorem oddPerfectWitness_green_unpresentable
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : OddPerfectManifestationLaw) :
    ¬ Nonempty OddPerfectNumber :=
  noOddPerfect_iff_no_witness.mp
    (noOddPerfect_of_manifestation_and_boundary
      no_someConcreteEuclideanEngine hBoundary hLaw)

/-! ## Сводки: решение заперто за двигателем; проверка, а не вывод (🟢) -/

/-- **«РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» (зелёная 3-развилка; зеркало
    `collatz_no_internal_decision_without_engine` / `pnp_no_internal_decision_without_engine`):**
    (1) ПРЕДЪЯВИТЬ свидетеля при законе и сведённых книгах = предъявить
        двигатель как объект (`oddPerfectWitness_carries_engine`; условность
        закона раскрыта — гипотеза явная);
    (2) САМООБОСНОВАТЬ решение изнутри — самоуничтожается
        (`no_internalisedOddPerfectGround`);
    (3) без-двигательный путь — ВНЕШНЯЯ граница: закон + граница + зелёное
        отсутствие двигателей дают `NoOddPerfect`
        (`noOddPerfect_of_manifestation_and_boundary`).
    НЕ утверждается гёделевская независимость и НЕ решается сама задача —
    только: оба внутренних решения стоят вечного двигателя. -/
theorem oddPerfect_no_internal_decision_without_engine :
    (∀ (A M0 : ℕ), OddPerfectManifestationLaw →
        ∀ W : OddPerfectNumber, W.1 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) ∧
    (InternalisedOddPerfectGround → False) ∧
    (TheStrictLastStep00Obligation → OddPerfectManifestationLaw → NoOddPerfect) :=
  ⟨fun _A _M0 hLaw W hM proj hres =>
     oddPerfectWitness_carries_engine hLaw W hM proj hres,
   no_internalisedOddPerfectGround,
   fun hBoundary hLaw =>
     noOddPerfect_of_manifestation_and_boundary
       no_someConcreteEuclideanEngine hBoundary hLaw⟩

/-- **«ПРОВЕРКА, А НЕ ВЫВОД» (зеркало `collatz_verification_not_derivation` /
    `pnp_verification_not_derivation`) — с уникальным пуантом фронта:**
    (1) внутреннее знание причины невозможно (`oddPerfectCause_unknowable`);
    (2) свидетель ниже проверенного горизонта невозможен безусловно —
        sweep платит напрямую;
    (3) «внешняя проверка» здесь — БУКВАЛЬНО поточечная разрешимость:
        каждый кандидат решается вычислением (третий конъюнкт доказан из
        instance `DecidablePred Nat.Perfect`, БЕЗ `Classical.em`) — решение
        находимо ровно настолько далеко, насколько досчитывает ядро.
    ЧЕСТНОСТЬ: конъюнкт (3) классически тривиален; его машинное содержание —
    маршрут доказательства через разрешающий instance, а не сила утверждения. -/
theorem oddPerfect_verification_not_derivation :
    (¬ InternalKnowledgeOfOddPerfectCause) ∧
    (¬ ∃ W : OddPerfectNumber, W.1 < 101) ∧
    (∀ M : ℕ, Nat.Perfect M ∨ ¬ Nat.Perfect M) :=
  ⟨oddPerfectCause_unknowable,
   no_oddPerfectWitness_below_horizon,
   fun M => if h : Nat.Perfect M then Or.inl h else Or.inr h⟩

/-- Итоговый эпистемический статус нечётного фронта (зеркало
    `pnp_locked_behind_engine_status`, НЕ `collatz_locked_behind_engine_status`:
    декрет-конъюнкта НЕТ — поле сознательно не добавлено, §17-вердикт):
    свидетель ≥ 101 (теорема, kernel-sweep) / внутреннее знание невозможно
    (теорема) / закон + граница ⟹ NoOddPerfect (условно — гипотезы явные) /
    свидетель + закон + книги ⟹ двигатель (условно — гипотезы явные).
    ЗЕЛЁНАЯ целиком; открытую задачу НЕ решает. -/
theorem oddPerfect_locked_behind_engine_status :
    (∀ W : OddPerfectNumber, 101 ≤ W.1) ∧
    (¬ InternalKnowledgeOfOddPerfectCause) ∧
    (TheStrictLastStep00Obligation → OddPerfectManifestationLaw → NoOddPerfect) ∧
    (∀ (A M0 : ℕ), OddPerfectManifestationLaw →
        ∀ W : OddPerfectNumber, W.1 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) :=
  ⟨oddPerfect_ge_101,
   oddPerfectCause_unknowable,
   fun hBoundary hLaw =>
     noOddPerfect_of_manifestation_and_boundary
       no_someConcreteEuclideanEngine hBoundary hLaw,
   fun _A _M0 hLaw W hM proj hres =>
     oddPerfectWitness_carries_engine hLaw W hM proj hres⟩

/-! ## Аудит аксиом: весь модуль зелёный (не более стандартной тройки),
    таинт репо НЕ меняется -/
#print axioms oddPerfect_horizon_swept
#print axioms no_internalisedOddPerfectGround
#print axioms oddPerfectCause_unknowable
#print axioms no_oddPerfectWitness_below_horizon
#print axioms unknowable_or_oddPerfect_below_horizon
#print axioms internalisedOddPerfectGround_builds_engine
#print axioms oddPerfectWitness_green_unpresentable
#print axioms oddPerfect_no_internal_decision_without_engine
#print axioms oddPerfect_verification_not_derivation
#print axioms oddPerfect_locked_behind_engine_status

end EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic
