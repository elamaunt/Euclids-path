/-
  PNPFirstCause — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ P/NP (зеркало CollatzFirstCause).
  Разбор: prose/56_CollatzFirstCause.md (секция «P/NP за тем же горизонтом»).
  Зелёная машина ранго-оплаты: Engine/PNPRankPaymentFront.lean.

  ЧТО ЭТО. Проверяющая машина — «компьютер в чистом виде на конечном топливе» со
  строгими правилами: это `RankedForwardGraph` (правила = `Step`, топливо = `lexRank`,
  закон топлива = `RankFastTraversal`), стартующий из ПРОИЗВОЛЬНОЙ (случайной) позиции
  (5-адическая цепь при A ≤ 4). «Решить P/NP изнутри» = оплатить инъективно конечным
  ключом КАЖДЫЙ сертификат НЕОГРАНИЧЕННОЙ поставки (`FullRankCertificatePayment`
  неограниченного `UnboundedCertificateSupply`). Это то же противоречие вечного
  двигателя, что у Коллатца: «непадающий хвост = двигатель» ↦ «полная оплата
  неограниченной поставки = двигатель». Оба гибнут об одну стену вполне-фундированности
  (пижонхол = нет инъекции бесконечного в конечное = нет ℕ-спуска, `no_perpetual_engine_on_nat`).

  ЧЕСТНОСТЬ. Это модель-внутренняя эпистемическая непознаваемость (как
  `collatzCause_unknowable`), а НЕ доказательство классического P≠NP (фрейм-слой
  пластичен — `allPFrame`/`constantsFrame`, из него о настоящем P/NP ничего не следует)
  и НЕ Гёдель (это пижонхол-самоуничтожение, а не теорема о неполноте/неподвижной точке).
  КЛЮЧЕВОЕ ОТЛИЧИЕ ОТ КОЛЛАТЦА: у P/NP декрета НЕТ — трилемма (`pnpLawUniversal_refuted`,
  `pnpLawExistential_green`) машинно доказала, что честной третьей границы `step00FirstCause`
  не существует. Поэтому весь этот файл ЗЕЛЁНЫЙ, БЕЗ импорта карантина, без `step00FirstCause`:
  таинт репозитория НЕ меняется. Безусловное ядро — при A ≤ 4 (граница
  `PNPRankPaymentFront`); расширение в конце файла добавляет точный закон оплаты
  (`fullPayment_iff_boundedSupply`) и замки на ВИДИМЫХ гипотезах — twin-bound на
  всех масштабах и декретный масштаб A ≥ 5 (граница гипотезой, стиль L14–L16).
-/

import EuclidsPath.Engine.PNPRankPaymentFront
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.PNPRankPayment.FirstCause

open EuclidsPath.PNPRankPayment
open EuclidsPath.LocalPNP
open EuclidsPath.LocalPNP.Concrete
open EuclidsPath.UniversalEngine

/-! ## Модель: внутреннее решение = самообоснование за собственным горизонтом -/

/-- **Внутреннее самообоснование решения P/NP на конечном топливе.** Машина
    одновременно (a) ОПЛАЧИВАЕТ инъективно конечным ключом всю поставку сертификатов
    (`resolves`) и (b) эта поставка НЕОГРАНИЧЕНА (`beyondOwnHorizon`).
    ЧЕСТНОСТЬ (уточнена после точного закона `fullPayment_iff_boundedSupply` ниже):
    поля ДОКАЗУЕМО точные дополнения, семантически структура эквивалентна паре
    «оплата ∧ ¬оплата» (машинно: `internalisedPNPGround_semantically_selfNegating`).
    Содержательность живёт НЕ в форме структуры, а в том, чем контрадикция ОПЛАЧЕНА:
    `beyondOwnHorizon` — независимо доказанный зелёный факт (5-адическая цепь
    `fiveAdicChainFlow_injective`), противоречие поставляет пижонхол
    `no_fullPayment_of_unboundedSupply`. Это в точности попытка «дотянуться
    взглядом» за собственный конечнотопливный горизонт. -/
structure InternalisedPNPGround {G : RankedForwardGraph} (F : GenealogyFamily G) : Prop where
  resolves : FullRankCertificatePayment F
  beyondOwnHorizon : UnboundedCertificateSupply F

/-- «Внутреннее знание причины P/NP» = внутреннее самообоснование решения. -/
abbrev InternalKnowledgeOfPNPCause {G : RankedForwardGraph} (F : GenealogyFamily G) : Prop :=
  InternalisedPNPGround F

/-- Конкретная честная инстанция при A ≤ 4 (5-адическая цепь, без единой гипотезы). -/
abbrev InternalPNPDecision (A : ℕ) : Prop := InternalisedPNPGround (concreteFamily A 1)

/-! ## Ядро: самообоснование самоуничтожается = стена вечного двигателя (🟢) -/

/-- Самообоснование самоуничтожается — ровно `fun H => H.beyondOwnHorizon H.ground`
    Коллатца, только отрицание поставляет пижонхол. ЗЕЛЁНАЯ. -/
theorem no_internalisedPNPGround {G : RankedForwardGraph} {F : GenealogyFamily G} :
    InternalisedPNPGround F → False :=
  fun H => no_fullPayment_of_unboundedSupply H.beyondOwnHorizon H.resolves

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `collatzCause_unknowable`,
    twin-`cause_unknowable`): внутреннее конечнотопливное решение P/NP невозможно.
    ЗЕЛЁНАЯ, вообще без аксиом. -/
theorem pnpCause_unknowable {G : RankedForwardGraph} {F : GenealogyFamily G} :
    ¬ InternalKnowledgeOfPNPCause F :=
  no_internalisedPNPGround

/-- **ТО ЖЕ ПРОТИВОРЕЧИЕ ВЕЧНОГО ДВИГАТЕЛЯ (зелёно):** невозможность внутреннего решения
    P/NP И невозможность вечного двигателя на ℕ — ОДНА стена вполне-фундированности
    (зеркало `UniversalEngine.discrete_forbids_continuous_realizes`: конечное топливо на
    ℕ бутылочит спуск). Оплатить неограниченную поставку конечным ключом = впихнуть
    бесконечный индекс в конечный = тот же ℕ-запрет. -/
theorem internalPNPDecision_carries_perpetual_engine {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    (InternalisedPNPGround F → False) ∧ ¬ PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  ⟨no_internalisedPNPGround, no_perpetual_engine_on_nat⟩

/-- Ex-falso companion («несёт двигатель»): из самообоснования (уже ложного) выводится и
    сам вечный двигатель на ℕ — самообоснование взрывает всё. ЧЕСТНОСТЬ: маршрут ex falso;
    несущая часть — сама невозможность (`no_internalisedPNPGround`). -/
theorem internalisedPNPGround_builds_engine {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    InternalisedPNPGround F → PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  fun H => (no_internalisedPNPGround H).elim

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ (без ex falso в утверждении): либо причина непознаваема
    изнутри, либо неограниченная поставка полностью оплачиваема. Левый дизъюнкт — теорема. -/
theorem unknowable_or_pnp_fullyPayable {A : ℕ} :
    (¬ InternalKnowledgeOfPNPCause (concreteFamily A 1)) ∨
      FullRankCertificatePayment (concreteFamily A 1) :=
  Or.inl pnpCause_unknowable

/-! ## Сводки: решение заперто за двигателем; проверка, а не вывод (🟢) -/

/-- **«РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» (зелёная; зеркало
    `collatz_no_internal_decision_without_engine`):**
    (1) ОПЛАТИТЬ ИЗНУТРИ неограниченную поставку = стена вечного двигателя (пижонхол,
        `concrete_noFullPayment_smallScale`) — внутреннее решение невозможно;
    (2) САМООБОСНОВАТЬ решение изнутри — самоуничтожается (`no_internalisedPNPGround`);
    (3) единственный без-двигательный путь — ВНЕШНЯЯ ПРОВЕРКА: локальный P-успех влечёт
        полную оплату (`concrete_localPSuccess_iff_fullPayment`), то есть решают проверкой,
        а не внутренним выводом.
    НЕ утверждается гёделевская независимость и НЕ P≠NP — только: оба внутренних решения
    стоят вечного двигателя. -/
theorem pnp_no_internal_decision_without_engine {A : ℕ} (hA : A ≤ 4) :
    (FullRankCertificatePayment (concreteFamily A 1) → False) ∧
    (InternalisedPNPGround (concreteFamily A 1) → False) ∧
    (∀ M0 : ℕ, LocalPSuccess (concreteProblem A M0) →
        FullRankCertificatePayment (concreteFamily A M0)) :=
  ⟨concrete_noFullPayment_smallScale hA,
   no_internalisedPNPGround,
   fun M0 hP => (concrete_localPSuccess_iff_fullPayment A M0).mp hP⟩

/-- **«ПРОВЕРКА, А НЕ ВЫВОД» (зеркало `collatz_verification_not_derivation`):**
    (1) внутреннее решение P/NP непознаваемо (`pnpCause_unknowable`);
    (2) оплатить неограниченную поставку изнутри невозможно — стена двигателя;
    (3) значит решение доступно лишь ПРОВЕРКОЙ (локальный успех ⟹ полная оплата),
        находимой ровно настолько далеко, насколько достаёт конечнотопливный горизонт. -/
theorem pnp_verification_not_derivation {A : ℕ} (hA : A ≤ 4) :
    (¬ InternalPNPDecision A) ∧
    (FullRankCertificatePayment (concreteFamily A 1) → False) ∧
    (∀ M0 : ℕ, LocalPSuccess (concreteProblem A M0) →
        FullRankCertificatePayment (concreteFamily A M0)) :=
  ⟨pnpCause_unknowable,
   concrete_noFullPayment_smallScale hA,
   fun M0 hP => (concrete_localPSuccess_iff_fullPayment A M0).mp hP⟩

/-- Итоговый эпистемический статус P/NP-горизонта (зеркало
    `collatz_locked_behind_engine_status`, но БЕЗ декрет-конъюнкта — у P/NP границы нет):
    двигатель проезжает ранг быстро / поставка неограниченна / решить изнутри нельзя
    (теорема) / полная оплата = стена двигателя (теорема). ЗЕЛЁНАЯ целиком. -/
theorem pnp_locked_behind_engine_status {A : ℕ} (hA : A ≤ 4) :
    RankFastTraversal (concreteGraph A 1) ∧
    UnboundedCertificateSupply (concreteFamily A 1) ∧
    (¬ InternalPNPDecision A) ∧
    (FullRankCertificatePayment (concreteFamily A 1) → False) :=
  ⟨concrete_rankFastTraversal A 1,
   concreteSupply_unbounded_smallScale hA,
   pnpCause_unknowable,
   concrete_noFullPayment_smallScale hA⟩

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка), таинт репо НЕ меняется -/
#print axioms no_internalisedPNPGround
#print axioms pnpCause_unknowable
#print axioms internalPNPDecision_carries_perpetual_engine
#print axioms internalisedPNPGround_builds_engine
#print axioms unknowable_or_pnp_fullyPayable
#print axioms pnp_no_internal_decision_without_engine
#print axioms pnp_verification_not_derivation
#print axioms pnp_locked_behind_engine_status

/-! ## Расширение: точный закон оплаты и замки на видимых гипотезах (🟢)

Карантин по-прежнему НЕ импортируется: `TwinBoundAbove` и
`TheStrictLastStep00Obligation` входят ниже только как ВИДИМЫЕ гипотезы
(стиль L14–L16 фронта `PNPRankPaymentFront`) — таинт репозитория не меняется. -/

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-- **Оплата ограничивает поставку** — контрапозиция пижонхол-сердца
    `no_fullPayment_of_unboundedSupply`: полная инъективная конечноключевая
    оплата семьи сертификатов несовместима с её неограниченностью. ЗЕЛЁНАЯ,
    для любого ранжированного графа и любой семьи. -/
theorem fullPayment_implies_boundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    FullRankCertificatePayment F → ¬ UnboundedCertificateSupply F :=
  fun hPay hInf => no_fullPayment_of_unboundedSupply hInf hPay

/-- **ТОЧНЫЙ ЗАКОН ОПЛАТЫ (пижонхол становится iff):** оплатить всю семью
    инъективным конечным ключом МОЖНО ⟺ поставка сертификатов ОГРАНИЧЕНА.
    Прямая стрелка — контрапозиция сердца L5 (`fullPayment_implies_boundedSupply`);
    обратная — конструкция: при конечном `F.Index` ключом служит сам индекс
    (`Key := F.Index`, `keyOf := id`, инъективность даром). ЧЕСТНОСТЬ:
    (1) обратная сторона использует `Fintype.ofFinite` (noncomputable) — внутри
    ∃-Prop это законно, классический выбор входит в стандартную тройку аксиом;
    (2) это модель-внутренний закон ранговой машины — о классическом P/NP
    НИЧЕГО не утверждается (фрейм-слой пластичен: `allPFrame`/`constantsFrame`). -/
theorem fullPayment_iff_boundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    FullRankCertificatePayment F ↔ ¬ UnboundedCertificateSupply F := by
  classical
  constructor
  · exact fullPayment_implies_boundedSupply
  · intro hBound
    haveI : Finite F.Index := not_infinite_iff_finite.mp hBound
    exact ⟨⟨F.Index, Fintype.ofFinite F.Index, id⟩, Function.injective_id⟩

/-- **Самообоснование — семантически «оплата ∧ ¬оплата» (машинная честность):**
    после точного закона `fullPayment_iff_boundedSupply` поля
    `resolves`/`beyondOwnHorizon` — доказуемо точные дополнения, и вся структура
    `InternalisedPNPGround` эквивалентна контрадикторной паре. Содержательность
    живёт НЕ в форме, а в оплате контрадикции: зелёный iff + 5-адическая цепь
    (`fiveAdicChainFlow_injective`). Обратная стрелка — ex falso (честно). -/
theorem internalisedPNPGround_semantically_selfNegating {G : RankedForwardGraph}
    {F : GenealogyFamily G} :
    InternalisedPNPGround F ↔
      (FullRankCertificatePayment F ∧ ¬ FullRankCertificatePayment F) :=
  ⟨fun H => ⟨H.resolves, no_fullPayment_of_unboundedSupply H.beyondOwnHorizon⟩,
   fun h => (h.2 h.1).elim⟩

/-- **ЭПИСТЕМИЧЕСКИЙ ЗАМОК НА ВСЕХ МАСШТАБАХ (twin-условный):** при
    `TwinBoundAbove M0` (выше M0 центров близнецов нет) на ЛЮБОМ масштабе (A, M0):
    двигатель проезжает ранг быстро / поставка неограниченна / решить изнутри
    нельзя / полная оплата — стена двигателя. ЧЕСТНОСТЬ (обязательная): конъюнкты
    1 и 3 БЕЗУСЛОВНЫ (`concrete_rankFastTraversal` и `pnpCause_unknowable` — без
    единой гипотезы); twin-гипотеза питает ТОЛЬКО конъюнкты 2 и 4 — это бандлинг
    существующих фактов, вскрытый прямо. Ценность пары: машинно видно, что
    единственный вход, разблокирующий ОПЛАТУ на больших масштабах, —
    бесконечность близнецов (сторона декрета), а непознаваемость изнутри
    (конъюнкт 3) не разблокируется вообще ничем. -/
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

/-- **ДЕКРЕТ ПЛАТИТ, НО НЕ САМООБОСНОВЫВАЕТ (жёлтая по видимой гипотезе):** даже
    на декретно-оплаченном масштабе A ≥ 5, где `TheStrictLastStep00Obligation`
    принуждает полную оплату на каждом M0
    (`boundary_forces_fullPayment_at_decreed_scale`), внутреннее самообоснование
    остаётся невозможным. ЧЕСТНОСТЬ: второй конъюнкт БЕЗУСЛОВЕН
    (`no_internalisedPNPGround` — без гипотез); содержание — в ПАРЕ: оплата без
    неограниченного горизонта НЕ есть самообоснование, непознаваемость держит
    ОБА берега раскола по масштабам. Карантин НЕ импортирован — граница входит
    гипотезой. -/
theorem decree_pays_but_no_selfGrounding
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      FullRankCertificatePayment (concreteFamily A M0) ∧
      ¬ InternalisedPNPGround (concreteFamily A M0) := by
  obtain ⟨A, hA, hPay⟩ := boundary_forces_fullPayment_at_decreed_scale hBoundary
  exact ⟨A, hA, fun M0 => ⟨hPay M0, no_internalisedPNPGround⟩⟩

/-- **ЭПИСТЕМИЧЕСКИЙ ЗАМОК НА ДЕКРЕТНОМ МАСШТАБЕ (жёлтая по видимой гипотезе;
    зеркало `pnp_locked_behind_engine_status` на ДРУГОМ берегу раскола):** на
    масштабе декрета A ≥ 5 двигатель по-прежнему проезжает ранг быстро, оплата
    ПРИНУЖДЕНА границей, поставка потому ОГРАНИЧЕНА (точный закон
    `fullPayment_iff_boundedSupply` в форме `fullPayment_implies_boundedSupply`),
    и всё же решить ИЗНУТРИ нельзя. ЧЕСТНОСТЬ: конъюнкты 1 и 4 безусловны
    (`concrete_rankFastTraversal`, `pnpCause_unknowable`); гипотеза границы питает
    конъюнкты 2–3. НЕ Гёдель и НЕ P≠NP: модель-внутренняя эпистемика, граница —
    видимая гипотеза (стиль L14–L16), карантин не импортирован, таинт не меняется. -/
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

/-! ## Аудит аксиом расширения: максимум стандартная тройка, таинт НЕ меняется -/
#print axioms fullPayment_implies_boundedSupply
#print axioms fullPayment_iff_boundedSupply
#print axioms internalisedPNPGround_semantically_selfNegating
#print axioms pnp_locked_behind_engine_status_of_twinBound
#print axioms decree_pays_but_no_selfGrounding
#print axioms pnp_locked_behind_engine_status_at_decreed_scale

end EuclidsPath.PNPRankPayment.FirstCause
