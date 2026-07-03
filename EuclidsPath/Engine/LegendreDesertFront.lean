/-
  LegendreDesertFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль ветви простых
  пустынь (prime deserts) программы вечного двигателя. ДВА БЛОКА:

    БЛОК 1 (namespace EuclidsPath.PrimeDeserts) — БЕЗУСЛОВНОЕ зелёное
    содержание Бертрана и объект-свидетель Лежандра. Уникальная зелёная
    сила этого фронта: постулат Бертрана (mathlib, unconditional) даёт
    ТЕОРЕМУ «пустыня не может удвоиться» (no_desert_doubles): между n и 2n+1
    простое ЕСТЬ всегда (n ≠ 0). Это единственный манифестационный фронт
    программы, у которого несущая арифметика зелёная целиком, а не гейчена
    открытой задачей.

    БЛОК 2 (namespaces EuclidsPath / ConcreteStep00Graph /
    GeneratedFlowFormulation) — манифестационный фронт объект-свидетеля
    Лежандра, зеркало OddPerfectManifestationFront: отклонение — ОБЪЕКТ-ДАННЫЕ
    `V : LegendreViolation` (subtype {n // LegendreViolationAt n}, конкретное
    нарушение гипотезы Лежандра: простая пустыня между n² и (n+1)²). Закон
    ОБЪЕКТ-КВАНТИФИЦИРОВАН (∀ V, Manifests V); якорь масштаба M0 := V.1²
    привязан к самому нарушению; негейченной «взрывной» формы не существует.

  ПОТОЧЕЧНАЯ РАЗРЕШИМОСТЬ (сильнейшая форма непредъявимости):
  LegendreViolationAt разрешим (DecidablePred через bounded-ball форму
  Nat.decidableBallLT) — всякая фальшивка умирает decide'ом
  (legendre_holds_upTo_10: ниже 11 нарушений нет, машинно), а предъявить
  НАСТОЯЩЕГО свидетеля = ОПРОВЕРГНУТЬ гипотезу Лежандра, открытую с 1808 г.
  Литературная граница (проверено далеко за 10^18) НЕ формализована — зелёно
  здесь только ≥ 11 (legendreViolation_ge_11).

  ЧЕСТНОЕ РАСКРЫТИЕ (машинно, legendre_interval_shorter_than_bertrand):
  интервал Лежандра КОРОЧЕ бертрановского — при n ≥ 3 имеем (n+1)² < 2n²,
  тогда как Бертран покрывает лишь [m, 2m]. Потому Бертран НЕ решает Лежандра:
  зелёное «пустыня не удваивается» бессильно на квадратичной щели, и
  NoBertrandToLegendreImplicationClaimed = True явно фиксирует, что НИКАКОЙ
  импликации Бертран ⟹ Лежандр здесь не заявлено.

  ЗНАК ЭВРИСТИКИ — ЗА (нарушений Лежандра нет ожидаемо): квантор закона
  пробегает ожидаемо ПУСТОЙ тип LegendreViolation — закон ожидаемо
  ВАКУУМНО-ИСТИНЕН, точное зеркало RH и нечётных совершенных (Риман был
  ставкой на ожидаемо-истинное; здесь та же ориентация). При границе закон
  ⟺ отсутствие нарушений ⟺ LegendreConjecture (LG7).

  ПОЛЕ НЕ ДОБАВЛЕНО — НАМЕРЕННО (§17-вердикт карантина): серийное расширение
  декрета обесценило бы карантин. Закон живёт здесь ОПРЕДЕЛЕНИЕМ (прецедент
  §16 / Мерсенна); непротиворечивость карантина на него НЕ ставится.

  ОДОЛЖЕННЫЕ L1/L2 (раскрыто): объект поставки DeviationFlowSupply — ТОТ ЖЕ,
  что twin-bound строит зелёно (L1 римановского фронта); Impossible-сторона
  на разрешённых масштабах — зелёная теорема
  no_deviationFlowSupply_at_resolved_scale (переиспользована), НЕ декрет.

  ЗАПРЕТ ВАКУУМНОСТИ: никаких свободных Prop-полей, свободных гейтов и
  переименованных выводов — каждая гипотеза именована арифметически;
  вакуумная обратная сторона закона раскрыта аудитом LG5. Модуль карантин НЕ
  импортирует; axiom/sorry/native_decide нет.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

/-#############################################################################
  БЛОК 1 — namespace EuclidsPath.PrimeDeserts

  Простые пустыни, БЕЗУСЛОВНЫЙ Бертран, объект-свидетель Лежандра.
#############################################################################-/

namespace EuclidsPath
namespace PrimeDeserts

/-- **Простая пустыня между `a` и `b`:** ни одно `p` строго между `a` и `b`
    не является простым. Открытый интервал — граничные точки не участвуют. -/
def PrimeDesertBetween (a b : ℕ) : Prop :=
  ∀ p, a < p → p < b → ¬ p.Prime

/-- Разрешимость пустыни через ограниченную (bounded-ball) переформулировку:
    `∀ p, p < b → a < p → ¬ p.Prime` несёт зелёный `Nat.decidableBallLT`,
    который РЕДУЦИРУЕТСЯ под `decide` (в отличие от наивного Finset-ball,
    чей instance не синтезируется). Порядок гипотез переставлен ровно так,
    чтобы верхняя граница `p < b` шла первой (форма `Nat.decidableBallLT`). -/
instance instDecidablePrimeDesertBetween (a b : ℕ) :
    Decidable (PrimeDesertBetween a b) :=
  decidable_of_iff (∀ p, p < b → a < p → ¬ p.Prime) <| by
    constructor
    · intro h p hlt hpb
      exact h p hpb hlt
    · intro h p hpb hlt
      exact h p hlt hpb

/-#############################################################################
  §1. БЕЗУСЛОВНЫЙ Бертран: пустыня не может удвоиться
#############################################################################-/

/-- **ЗЕЛЁНОЕ (безусловное) содержание Бертрана — ГЛАВНАЯ ТЕОРЕМА блока 1:**
    простая пустыня НЕ МОЖЕТ покрыть удвоение — между `n` и `2n+1` (при
    `n ≠ 0`) простое существует ВСЕГДА. Прямая перепаковка постулата Бертрана
    (`Nat.exists_prime_lt_and_le_two_mul`, mathlib, unconditional). Никакой
    открытой задачи: этот факт — ТЕОРЕМА, а не гейт. -/
theorem no_desert_doubles {n : ℕ} (hn : n ≠ 0) :
    ¬ PrimeDesertBetween n (2 * n + 1) := by
  intro hdes
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  exact hdes p hlt (by omega) hp

/-- Прямая позитивная перепаковка Бертрана: следующее простое после `n`
    не превосходит `2n` (при `n ≠ 0`). Форма-компаньон no_desert_doubles. -/
theorem nextPrime_le_two_mul {n : ℕ} (hn : n ≠ 0) :
    ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  exact ⟨p, hp, hlt, hle⟩

/-#############################################################################
  §2. Объект-свидетель Лежандра и поточечная разрешимость
#############################################################################-/

/-- **Нарушение гипотезы Лежандра в точке `n`:** `1 ≤ n` и между `n²` и
    `(n+1)²` лежит простая пустыня (ни одного простого). Предъявить такое
    `n` = опровергнуть гипотезу Лежандра. -/
def LegendreViolationAt (n : ℕ) : Prop :=
  1 ≤ n ∧ PrimeDesertBetween (n ^ 2) ((n + 1) ^ 2)

/-- Поточечная разрешимость нарушения — прямо из разрешимости пустыни. -/
instance instDecidablePredLegendreViolationAt :
    DecidablePred LegendreViolationAt := fun n =>
  inferInstanceAs (Decidable (1 ≤ n ∧ _))

/-- Тип-свидетель нарушения (subtype — для объект-квантификации и
    bundling-аудита блока 2). Ожидаемо ПУСТОЙ тип (знак эвристики — ЗА). -/
abbrev LegendreViolation : Type := {n // LegendreViolationAt n}

/-- **Гипотеза Лежандра (1808):** между любыми последовательными квадратами
    (`n ≥ 1`) есть простое. Открыта по сей день. -/
def LegendreConjecture : Prop :=
  ∀ n, 1 ≤ n → ∃ p, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- Гипотеза Лежандра ⟺ нарушений нет. Прямая плумбинг-эквивалентность
    (push_neg над определением пустыни). -/
theorem legendreConjecture_iff_no_violation :
    LegendreConjecture ↔ ∀ n, ¬ LegendreViolationAt n := by
  constructor
  · intro hLC n hViol
    obtain ⟨hn, hDesert⟩ := hViol
    obtain ⟨p, hp, hlo, hhi⟩ := hLC n hn
    exact hDesert p hlo hhi hp
  · intro hNo n hn
    by_contra hne
    refine hNo n ⟨hn, fun p hlo hhi hp => ?_⟩
    exact hne ⟨p, hp, hlo, hhi⟩

/-- **LG-machine (поточечная разрешимость в действии):** ниже 11 нарушений
    Лежандра НЕТ — все кандидаты `1 ≤ n < 11` отсеяны машинной проверкой
    (`decide`, БЕЗ native_decide). Фальшивка умирает поточечно. -/
theorem legendre_holds_upTo_10 :
    ∀ n, n < 11 → 1 ≤ n → ¬ LegendreViolationAt n := by decide

/-- **LG8 (локализация домена свидетеля, зеркало M8/OP8):** всякий свидетель
    нарушения Лежандра ≥ 11 — меньшие точки отсеяны машинно
    (`legendre_holds_upTo_10`). Литературная граница НЕ формализована —
    зелёно только это. -/
theorem legendreViolation_ge_11 (V : LegendreViolation) : 11 ≤ V.1 := by
  by_contra h
  exact legendre_holds_upTo_10 V.1 (by omega) V.2.1 V.2

/-#############################################################################
  §3. ЧЕСТНОЕ РАСКРЫТИЕ: интервал Лежандра КОРОЧЕ бертрановского
#############################################################################-/

/-- **ЧЕСТНОСТЬ (машинно проверено):** интервал Лежандра `(n², (n+1)²)`
    КОРОЧЕ бертрановского удвоения при `n ≥ 3`: `(n+1)² < 2n²`. Именно потому
    зелёное `no_desert_doubles` (пустыня не удваивается) НЕ покрывает
    квадратичную щель — Бертран НЕ решает Лежандра. -/
theorem legendre_interval_shorter_than_bertrand {n : ℕ} (h : 3 ≤ n) :
    (n + 1) ^ 2 < 2 * n ^ 2 := by
  nlinarith

/-- **ЯВНЫЙ ОТКАЗ ОТ ЗАВЫШЕННОЙ ЗАЯВКИ:** НИКАКАЯ импликация Бертран ⟹
    Лежандр в этом модуле не заявлена и не доказана. Флаг = True (тривиально):
    честность фронта — в том, что зелёная сила блока 1 (Бертран) остаётся
    строго слабее открытого блока 2 (Лежандр), см.
    legendre_interval_shorter_than_bertrand. -/
abbrev NoBertrandToLegendreImplicationClaimed : Prop := True

theorem noBertrandToLegendreImplicationClaimed_holds :
    NoBertrandToLegendreImplicationClaimed := trivial

-- Машинная видимость чистоты блока 1
-- (ожидаемо [propext, Classical.choice, Quot.sound]):
#print axioms no_desert_doubles
#print axioms legendre_holds_upTo_10
#print axioms legendre_interval_shorter_than_bertrand

end PrimeDeserts
end EuclidsPath

/-#############################################################################
  БЛОК 2 — namespaces EuclidsPath / ConcreteStep00Graph /
           GeneratedFlowFormulation

  Манифестационный фронт объект-свидетеля Лежандра (зеркало
  OddPerfectManifestationFront). Якорь масштаба M0 := V.1² привязан к самому
  нарушению; закон объект-квантифицирован по типу свидетелей.
#############################################################################-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §4. Закон манифестации (объект-квантифицирован; поле НЕ декретировано)
#############################################################################-/

/-- Конкретное нарушение Лежандра манифестирует арифметически: на каждом
    леджер-масштабе не ниже квадрата точки нарушения `V.1²`, всюду где
    проекция сводит книги (коллизии разрешаются), свидетель проявляется
    неоплатимой бесконечной поставкой потоков. Якорь `V.1² ≤ M0` потребляется
    ниже только через `le_refl` (паттерн Римана/ОП: масштаб = высота
    отклонения; здесь высота отклонения — квадрат точки нарушения). Причинная
    форма: «отклонение обязано проявиться там, где книги сведены» — НЕ
    утверждение о (не)существовании нарушений Лежандра. -/
def LegendreDesertManifests (V : EuclidsPath.PrimeDeserts.LegendreViolation) :
    Prop :=
  ∀ (A M0 : ℕ), V.1 ^ 2 ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **ЗАКОН МАНИФЕСТАЦИИ ЛЕЖАНДРА** — объект-квантифицирован по типу
    свидетелей (зеркало `RiemannManifestationLaw` и OddPerfect, а НЕ гейченной
    формы Мерсенна): квантор пробегает ожидаемо ПУСТОЙ тип, закон ожидаемо
    вакуумно-истинен — точное зеркало RH. ПОЛЕ НЕ ДЕКРЕТИРОВАНО (§17-вердикт:
    серийность обесценила бы карантин). -/
def LegendreManifestationLaw : Prop :=
  ∀ V : EuclidsPath.PrimeDeserts.LegendreViolation, LegendreDesertManifests V

/-#############################################################################
  §5. ESSENCE и читаемая форма: предъявление свидетеля предъявляет двигатель
#############################################################################-/

/-- **LG3⁺ — ЧИТАЕМАЯ ФОРМА «предъявить нарушение = предъявить двигатель»:**
    конкретное нарушение Лежандра + закон + сведённые книги на масштабе не
    ниже `V.1²` МАНИФЕСТИРУЮТ вечный двигатель — как ОБЪЕКТ, до убийства
    lexRank'ом. -/
theorem legendreViolation_carries_engine
    (hLaw : LegendreManifestationLaw)
    (V : EuclidsPath.PrimeDeserts.LegendreViolation)
    {A M0 : ℕ} (hM : V.1 ^ 2 ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw V A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **LG3 — ESSENCE (зеркало OP3 и римановской L3):** двигателей нет +
    принятая граница + закон манифестации ⟹ нарушений Лежандра НЕТ. Все три
    гипотезы потребляются ПО-НАСТОЯЩЕМУ: гипотетический свидетель V даёт
    масштаб M0 := V.1², граница — разрешение ровно на нём (le_refl); закон
    поставляет семью 𝓕 (не ex falso); из коллизии строится
    двигатель-СВИДЕТЕЛЬ; убивает его именно hNoEngine. -/
theorem noLegendreViolation_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LegendreManifestationLaw) :
    ¬ Nonempty EuclidsPath.PrimeDeserts.LegendreViolation := by
  rintro ⟨V⟩
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves :
      SemanticExtendedFlowLedgerCollisionResolves (projOf (V.1 ^ 2)) :=
    strictSemanticExtended_resolves_old (hres (V.1 ^ 2))
  exact hNoEngine ⟨A, V.1 ^ 2,
    legendreViolation_carries_engine hLaw V (le_refl (V.1 ^ 2))
      (projOf (V.1 ^ 2)) hResolves⟩

/-- **LG4 — достаточность как ТЕОРЕМА:** та же тройка ⟹ гипотеза Лежандра.
    Отсутствие нарушений (через
    `legendreConjecture_iff_no_violation`) — и есть гипотеза Лежандра;
    ¬Nonempty распаковывается в поточечное отрицание. -/
theorem legendreConjecture_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LegendreManifestationLaw) :
    EuclidsPath.PrimeDeserts.LegendreConjecture := by
  refine EuclidsPath.PrimeDeserts.legendreConjecture_iff_no_violation.mpr ?_
  intro n hViol
  exact noLegendreViolation_of_manifestation_and_boundary
    hNoEngine hBoundary hLaw ⟨⟨n, hViol⟩⟩

/-#############################################################################
  §6. Аудиты честности (LG5–LG9)
#############################################################################-/

/-- **LG5 (вакуумная обратная сторона, зеркало OP5/L5):** отсутствие
    нарушений ⟹ закон — вакуумно: собственные данные свидетеля V.2
    противоречат отсутствию напрямую (тип свидетелей пуст). Несущая сторона —
    LG3, и ей нужна граница. -/
theorem legendreManifestationLaw_of_no_violation
    (H : ∀ n, ¬ EuclidsPath.PrimeDeserts.LegendreViolationAt n) :
    LegendreManifestationLaw := fun V =>
  (H V.1 V.2).elim

/-- **LG6 (точная зелёная характеризация, зеркало OP6/L6):** закон ⟺
    «нарушение Лежандра заморозило бы всякий разрешающий леджер на масштабах
    не ниже своего квадрата». Обратное направление — ex falso от ¬resolves
    (раскрыто); содержательная сторона — прямая (закон + разрешение ⟹
    поставка ⟹ противоречие с зелёной L2). -/
theorem legendreManifestationLaw_iff_no_resolution_above_witness :
    LegendreManifestationLaw ↔
      ∀ (V : EuclidsPath.PrimeDeserts.LegendreViolation) (A M0 : ℕ),
        V.1 ^ 2 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw V A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw V A M0 hle proj hres)
  · intro hFreeze V A M0 hle proj hres
    exact ((hFreeze V A M0 hle proj) hres).elim

/-- **LG7 — ГЛАВНЫЙ АУДИТ ЦЕНЫ (зеркало OP7/M7/L7):** при границе закон ⟺
    гипотеза Лежандра — поле было бы ровно силы задачи, открытой с 1808 г.
    БЕЗ границы «закон ⟹ Лежандр» зелёно не собирается (LG3/LG4 требуют
    границу). Знак эвристики направлен ЗА правую часть этого ⟺ (как у Римана
    и OddPerfect) — и всё же поле не добавлено (§17). -/
theorem legendreManifestationLaw_iff_conjecture_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    LegendreManifestationLaw ↔ EuclidsPath.PrimeDeserts.LegendreConjecture := by
  constructor
  · exact legendreConjecture_of_manifestation_and_boundary
      no_someConcreteEuclideanEngine hBoundary
  · intro hLC
    exact legendreManifestationLaw_of_no_violation
      (EuclidsPath.PrimeDeserts.legendreConjecture_iff_no_violation.mp hLC)

/-- Закон в Bridge-форме над типом свидетелей — здесь ПРЯМАЯ репаковка
    (объект-квантификация и есть Bridge; ср. репаковку у OddPerfect). -/
theorem legendreManifestationLaw_iff_bridge :
    LegendreManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun V : EuclidsPath.PrimeDeserts.LegendreViolation =>
          LegendreDesertManifests V) :=
  ⟨fun hLaw V => hLaw V, fun hB V => hB V⟩

/-- **LG9 (bundling-аудит, инстанциация осуждающей машины):** связка
    Bridge∧Impossible ⟺ «нарушений Лежандра нет» — декретироваться могла бы
    ТОЛЬКО Bridge-сторона; Impossible-сторона на разрешённых масштабах —
    зелёная L2, никогда не декрет. -/
theorem legendreManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun V : EuclidsPath.PrimeDeserts.LegendreViolation =>
          LegendreDesertManifests V) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun V : EuclidsPath.PrimeDeserts.LegendreViolation =>
          LegendreDesertManifests V)) ↔
      ¬ Nonempty EuclidsPath.PrimeDeserts.LegendreViolation :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Машинная видимость чистоты блока 2 в build-логе
-- (ожидаемо [propext, Classical.choice, Quot.sound] — БЕЗ step00FirstCause):
#print axioms noLegendreViolation_of_manifestation_and_boundary
#print axioms legendreConjecture_of_manifestation_and_boundary
#print axioms legendreViolation_carries_engine
#print axioms legendreManifestationLaw_iff_conjecture_of_boundary
#print axioms legendreManifestation_bundling_audit

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
