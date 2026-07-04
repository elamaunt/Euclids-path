/-
  BSDEpistemic — эпистемический раздел BSD: ЧЕСТНАЯ ФИКСАЦИЯ ВЫРОЖДЕНИЯ ОСИ.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ГЛАВНЫЙ CORR СКЕПТИКА ЗАПИСАН ТЕОРЕМОЙ: у BSD НОВОЙ ЭПИСТЕМИЧЕСКОЙ ОСИ НЕТ. │
  └───────────────────────────────────────────────────────────────────────────┘

  ЧТО ЭТО. Для семи фронтов эпистемический слой строился парой
  `ground` / `beyondOwnHorizon` (CollatzFirstCause, PNPFirstCause, TwinNodeEpistemic,
  OddPerfectEpistemic): «решить изнутри» = нести оба факта сразу, и противоречие
  оплачивается настоящей зелёной стеной. Для BSD предлагалась та же пара:
  `ground := PerpetualEngine M.descentStep` (внутреннее дообоснование ранга
  предъявлением бесконечного спуска), `beyondOwnHorizon := строгое убывание высоты`.
  ЭТА ПАРА ВЫРОЖДАЕТСЯ, и вырождение здесь зафиксировано МАШИННО, а не в комментарии:
  вторая нога — буквально поле `M.descent_decreases` модели `BSDHeightModel`,
  обитаемое для ЛЮБОЙ `M` всегда. Отсюда две теоремы-раскрытия:

   · `bsdGround_coincides_with_engine` — `InternalisedBSDGround M ↔
     PerpetualEngine M.descentStep`: структура эквивалентна ОДНОЙ своей ноге;
   · `bsdCause_unknowable_iff_no_engine` — «непознаваемость изнутри» экстенсионально
     СОВПАДАЕТ с уже существующей `bsd_descent_has_no_engine` (BSDFront): пакет —
     дефинициональная переупаковка старой теоремы, а не новая ось.

  ЧЕМ ОПЛАЧЕНО (честно). Оплата противоречия РЕАЛЬНА: `bsdCause_unknowable` гибнет
  об `UniversalEngine.no_perpetual_engine_of_natRank` — настоящую стену
  фундированности ℕ (та же семья, что пижонхол `no_fullPayment_of_unboundedSupply`
  у P/NP), потребляющую зелёное поле `descent_decreases` на РЕАЛЬНОМ носителе
  `W.toAffine.Point`. Но — в отличие от эталона P/NP, где ОБЕ ноги независимые
  нетривиальные предикаты, — вторая нога здесь СВОБОДНА ПО ПОСТРОЕНИЮ. Поэтому
  формула честности такова: «оплата реальна, но вторая нога свободна по построению»,
  и весь эпистемический слой BSD сводится к запрету двигателя спуска. Это НЕ дефект,
  а результат: сама попытка построить BSD отдельную эпистемическую ось доказуемо
  коллапсирует в терминацию спуска Морделла–Вейля.

  ДВЕ ЛЕММЫ ЧЕСТНОСТИ ОТЧЁТА (тоже машинно):
   · `analyticRank_gate_satisfiable` + `weakBSD_reduces_to_bare_equality` —
     🔴-ворота `AnalyticRank` (BSDFront §3) СВОБОДНО ВЫПОЛНИМЫ выбором
     (`⟨W.LSeries, rfl, 0 ≤ aRank⟩`): это маркер цитирования реальной
     `WeierstrassCurve.LSeries`, а не ограничение; `WeakBSD` доказуемо сводится
     к голому равенству `algRank = aRank`. Вакуумность ворот видна машине,
     а не только в комментарии.
   · `parity_bridge_inhabited_per_rank` — мост чётности `bsd_parity_is_rankParity`
     обитаем для КАЖДОГО ранга r (свидетель n = 2^r,
     `ArithmeticFunction.cardFactors_apply_prime_pow`), включая открытый
     классически режим r ≥ 2. Узел rank-parity (Лиувилль) не вакуумен ни при каком r.

  ЧЕСТНОСТЬ. Это НЕ доказательство и НЕ опровержение BSD (WeakBSD остаётся 🔴 named
  predicate; аналитический мост генуинно вне mathlib) и НЕ Гёдель (никакой
  независимости — только фундированность ℕ и раскрытие дефинициональных совпадений).
  Формальные связки помечены в докстроках и указано, чем каждая оплачена.
  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`; карантин
  (CausalClosureAxiom) НЕ импортируется; таинт репозитория (47) не меняется.
  Грузонесущие — не более стандартной тройки `propext`/`Classical.choice`/`Quot.sound`.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BSDEpistemic.lean → ноль ошибок.

  Родство: Engine/BSDFront.lean (модель, стена, мост, ворота);
    Engine/UniversalEngine.lean (`PerpetualEngine`, `no_perpetual_engine_of_natRank`);
    зеркала эпистемики: Engine/PNPFirstCause.lean, Engine/TwinNodeEpistemic.lean.
-/
import Mathlib
import EuclidsPath.Engine.BSDFront

set_option autoImplicit false

namespace EuclidsPath.BSDFront.Epistemic

open EuclidsPath.UniversalEngine

/-! ################################################################################
    §1  Предложенная эпистемическая пара и её МАШИННОЕ ВЫРОЖДЕНИЕ (а)
    ################################################################################ -/

/-- **Предложенное «внутреннее самообоснование ранга» для BSD** (по шаблону
    `InternalisedPNPGround` / `InternalisedTwinGround`): (a) `ground` — внутреннее
    дообоснование конечности ранга предъявлением бесконечного спуска (двигатель
    на `M.descentStep`), (b) `beyondOwnHorizon` — строгое убывание высоты на шаге.

    ЧЕСТНОСТЬ (главный CORR, обязательная): пара ВЫРОЖДЕНА. `beyondOwnHorizon` —
    буквально поле `M.descent_decreases`, обитаемое для ЛЮБОЙ модели `M`, поэтому
    структура эквивалентна одной своей ноге (`bsdGround_coincides_with_engine` ниже),
    а её невозможность — дефинициональная переупаковка `bsd_descent_has_no_engine`.
    Мы оставляем структуру ИМЕННО ради этой фиксации: у P/NP обе ноги — независимые
    нетривиальные предикаты, у BSD вторая нога свободна по построению. -/
structure InternalisedBSDGround (M : BSDHeightModel) : Prop where
  /-- Внутреннее дообоснование: бесконечная спусковая цепь (вечный двигатель). -/
  ground : PerpetualEngine M.descentStep
  /-- «Взгляд за горизонт»: шаг спуска строго уменьшает высоту. ВЫРОЖДЕНИЕ:
      это поле `M.descent_decreases`, всегда доступное, — нога свободна. -/
  beyondOwnHorizon : ∀ P Q, M.descentStep P Q → M.height P < M.height Q

/-- «Внутреннее знание причины BSD» = внутреннее самообоснование ранга
    (зеркало `InternalKnowledgeOfPNPCause` / `InternalKnowledgeOfTwinCause`). -/
abbrev InternalKnowledgeOfBSDCause (M : BSDHeightModel) : Prop :=
  InternalisedBSDGround M

/-- **ТЕОРЕМА-РАСКРЫТИЕ (главный CORR записан машинно):** предложенная эпистемическая
    структура BSD ЭКВИВАЛЕНТНА одной своей ноге — двигателю на спусковом отношении.
    Обратная стрелка оплачена даром: вторая нога — поле `M.descent_decreases`.
    Значит, никакой НОВОЙ эпистемической связки у BSD нет: `InternalisedBSDGround` —
    это `PerpetualEngine M.descentStep` под другим именем. Вырождение зафиксировано
    машинно — это и есть честность модуля. -/
theorem bsdGround_coincides_with_engine (M : BSDHeightModel) :
    InternalisedBSDGround M ↔ PerpetualEngine M.descentStep :=
  ⟨fun H => H.ground, fun h => ⟨h, M.descent_decreases⟩⟩

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — но БЕЗ НОВОЙ ОСИ:** эпистемика БСД совпадает
    с запретом двигателя спуска — новой оси у БСД нет, и это теорема.
    Формально: следствие раскрытия `bsdGround_coincides_with_engine`; противоречие
    оплачено НЕ формой структуры, а стеной фундированности ℕ
    (`no_perpetual_engine_of_natRank` через `bsd_descent_has_no_engine`), потребляющей
    реальное поле `descent_decreases` на носителе `W.toAffine.Point`. ЧЕСТНОСТЬ:
    это дефинициональная переупаковка `bsd_descent_has_no_engine`, а не аналог
    независимой пары P/NP — оплата реальна, но вторая нога свободна по построению. -/
theorem bsdCause_unknowable (M : BSDHeightModel) :
    ¬ InternalKnowledgeOfBSDCause M :=
  fun H => bsd_descent_has_no_engine M H.ground

/-- **Совпадение осей, экстенсионально:** «непознаваемость изнутри» ⟺ «двигателя
    спуска нет» — т.е. `bsdCause_unknowable` есть УЖЕ СУЩЕСТВУЮЩАЯ
    `bsd_descent_has_no_engine` (BSDFront) с точностью до переименования.
    Тривиальное `not_congr` от раскрытия — формальная связка, оплаченная
    вырождением второй ноги. -/
theorem bsdCause_unknowable_iff_no_engine (M : BSDHeightModel) :
    (¬ InternalKnowledgeOfBSDCause M) ↔ (¬ PerpetualEngine M.descentStep) :=
  not_congr (bsdGround_coincides_with_engine M)

/-- Конкретная инстанция на НЕ-вакуумном свидетеле `bsdHeightModel_inhabited`
    (кривая над ℚ, обитаемый шаг спуска): утверждение не о пустой модели. -/
theorem bsdCause_unknowable_inhabited :
    ¬ InternalKnowledgeOfBSDCause bsdHeightModel_inhabited :=
  bsdCause_unknowable bsdHeightModel_inhabited

/-! ################################################################################
    §2  Лемма честности: 🔴-ворота `AnalyticRank` свободно выполнимы (б)
    ################################################################################ -/

/-- **Ворота `AnalyticRank` СВОБОДНО ВЫПОЛНИМЫ (лемма честности, зелёная):** для
    любой кривой и ЛЮБОГО `aRank` предикат `AnalyticRank W aRank` доказуем выбором
    `⟨W.LSeries, rfl, 0 ≤ aRank⟩`. Машинная фиксация того, что 🔴-ворота BSDFront §3 —
    МАРКЕР ЦИТИРОВАНИЯ реальной `WeierstrassCurve.LSeries`, а не ограничение:
    содержательное «порядок обнуления в s = 1» mathlib не даёт, и предикат его
    не несёт. Та же честность, что у вердикта трилеммы `bsd_parityLaw_satisfiable`:
    вакуумность видна машине, а не только в комментарии. -/
theorem analyticRank_gate_satisfiable {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) (aRank : ℕ) :
    AnalyticRank W aRank :=
  ⟨fun s => WeierstrassCurve.LSeries W s, rfl, Nat.zero_le _⟩

/-- **Следствие для самой гипотезы:** `WeakBSD` доказуемо СВОДИТСЯ к голому равенству
    `algRank = aRank` — аналитический конъюнкт поглощается свободной выполнимостью
    ворот. Формальная связка, оплаченная `analyticRank_gate_satisfiable`; фиксирует,
    что ВСЁ открытое содержание BSD в текущей формализации живёт в одном named
    равенстве, которое мы честно НЕ доказываем. -/
theorem weakBSD_reduces_to_bare_equality {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) (algRank aRank : ℕ) :
    WeakBSD W algRank aRank ↔ algRank = aRank :=
  ⟨fun h => h.2, fun h => ⟨analyticRank_gate_satisfiable W aRank, h⟩⟩

/-! ################################################################################
    §3  Мост чётности обитаем для КАЖДОГО ранга (в)
    ################################################################################ -/

/-- **Мост чётности не вакуумен ни при каком ранге (зелёная):** для каждого `r`
    узел rank-parity предъявляет свидетеля `n = 2^r` — `n ≠ 0`, `Ω(n) = r` и
    `(−1)^r = λ(n)`. Оплачено mathlib-фактом
    `ArithmeticFunction.cardFactors_apply_prime_pow` и мостом
    `bsd_parity_is_rankParity` (BSDFront §2). Покрыт и чётный, и нечётный случай
    сразу — включая классически ОТКРЫТЫЙ режим r ≥ 2: обитаемость моста не зависит
    от того, реализуем ли такой ранг на кривой (об этом мы ничего не утверждаем). -/
theorem parity_bridge_inhabited_per_rank (r : ℕ) :
    ∃ n : ℕ, n ≠ 0 ∧ ArithmeticFunction.cardFactors n = r ∧
      (-1 : ℤ) ^ r = ArithmeticFunction.liouville n :=
  have hn : (2 : ℕ) ^ r ≠ 0 := pow_ne_zero r two_ne_zero
  have hr : ArithmeticFunction.cardFactors (2 ^ r) = r :=
    ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two
  ⟨2 ^ r, hn, hr, bsd_parity_is_rankParity r (2 ^ r) hn hr⟩

/-! ################################################################################
    ИТОГ (LOUD HONEST)
    ################################################################################

  🟢 МАШИННО, В ЭТОМ ФАЙЛЕ:
     · `bsdGround_coincides_with_engine` — предложенная эпистемическая пара BSD
       ВЫРОЖДЕНА: `InternalisedBSDGround M ↔ PerpetualEngine M.descentStep`;
     · `bsdCause_unknowable` (+ `_iff_no_engine`, `_inhabited`) — непознаваемость
       изнутри есть, но она СОВПАДАЕТ с `bsd_descent_has_no_engine`: новой оси нет,
       и это теорема; оплата реальна (`no_perpetual_engine_of_natRank`), но вторая
       нога свободна по построению;
     · `analyticRank_gate_satisfiable` / `weakBSD_reduces_to_bare_equality` —
       🔴-ворота свободно выполнимы; `WeakBSD` ⟺ голое `algRank = aRank`;
     · `parity_bridge_inhabited_per_rank` — мост чётности обитаем для каждого r
       (свидетель 2^r).

  🟢 ПЕРЕИСПОЛЬЗОВАНО (цитируется, НЕ пере-выводится): `BSDHeightModel`,
     `bsd_descent_has_no_engine`, `bsdHeightModel_inhabited`, `AnalyticRank`,
     `WeakBSD`, `bsd_parity_is_rankParity` (BSDFront); `PerpetualEngine`,
     `no_perpetual_engine_of_natRank` (UniversalEngine);
     `ArithmeticFunction.cardFactors_apply_prime_pow` (mathlib).

  🔴 ЧЕСТНО ОТКРЫТО (и НЕ трогается): `WeakBSD` как равенство `algRank = aRank`,
     настоящий аналитический ранг (продолжение L-ряда), настоящее корневое число.
     ЭТО НЕ ДОКАЗАТЕЛЬСТВО BSD И НЕ ГЁДЕЛЬ.

  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`; карантин не
  импортирован; таинт 47 не меняется.
-/

#print axioms bsdGround_coincides_with_engine
#print axioms bsdCause_unknowable
#print axioms bsdCause_unknowable_iff_no_engine
#print axioms bsdCause_unknowable_inhabited
#print axioms analyticRank_gate_satisfiable
#print axioms weakBSD_reduces_to_bare_equality
#print axioms parity_bridge_inhabited_per_rank

end EuclidsPath.BSDFront.Epistemic
