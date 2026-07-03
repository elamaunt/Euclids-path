/-
  CollatzFirstCause — ПОТРЕБИТЕЛЬ первопричины для КОЛЛАТЦА (зеркало DyadicFirstCause).
  Разбор: prose/F_CollatzFirstCause.md. Зелёная машина: Engine/CollatzTugOfWar.lean.

  СТАТУС (после слияния в основную линию): Коллатц ЗАЗЕМЛЁН на ЕДИНСТВЕННУЮ аксиому
  репозитория `step00FirstCause` — его закон каната стал ЧЕТВЁРТОЙ границей
  `collatzBoundary` структуры `Step00FirstCause` (Engine/CausalClosureAxiom §18).
  Отдельной аксиомы `collatzFirstCause` БОЛЬШЕ НЕТ: этот файл её НЕ объявляет, а
  ПОТРЕБЛЯЕТ границу из первопричины (`step00FirstCause.collatzBoundary`). Дубли
  определений (`T`, `iter`, `RopeCountingLaw`, бюджет окна, эпистемика) ушли в импорт
  `Engine/CollatzTugOfWar`. Всё жёлтое здесь заражено ровно `step00FirstCause` (как
  любая жёлтая декларация репо), НЕ является доказательством гипотезы Коллатца.

  ПОЧЕМУ ДЕКРЕТ ЧЕСТЕН (в отличие от ЯМ/НС/Ходжа): универсальный `RopeCountingLaw`
  пережил бы трилемму — кованого опровержения НЕТ (оно требовало бы траекторию с
  вечно уравновешенными счётами — неизвестно), зелёного доказательства НЕТ (оно
  влекло бы Коллатца). Тот же эпистемический статус, что у twin-узла и римановского
  закона манифестации.

  ЧЕСТНАЯ ЦЕНА (раскрыто, как у НС): доказана только стрелка `граница ⟹ гипотеза`
  (`collatz_from_firstCause`); обратная НЕИЗВЕСТНА — счётный закон может быть строго
  сильнее гипотезы (бюджет окна односторонен; ⟺-формой обладает лишь ценностный
  закон — «мост приговорённого», CollatzTugOfWar.valueLaw_iff_reaches_one). Декрет,
  возможно, ПЕРЕПЛАЧИВАЕТ (`firstCause_implies_but_maybe_overpays`).
-/

import EuclidsPath.Engine.CollatzTugOfWar
import EuclidsPath.Engine.CausalClosureAxiom

set_option autoImplicit false

namespace EuclidsPath.Collatz.FirstCause

open EuclidsPath.Collatz.TugOfWar

/-! ## Проекция границы Коллатца из первопричины (🟡) -/

/-- Проекция ЧЕТВЁРТОЙ границы первопричины (закон каната). ⚠️ AXIOM-TAINTED
    (`step00FirstCause`) — как любая жёлтая декларация репо. -/
theorem collatzRopeBoundary : ∀ n : ℕ, 1 ≤ n → RopeCountingLaw n :=
  EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.step00FirstCause.collatzBoundary

/-- **ГИПОТЕЗА КОЛЛАТЦА ИЗ ПЕРВОПРИЧИНЫ.** ⚠️ AXIOM-TAINTED: это НЕ доказательство
    гипотезы — редукция, закрытая декретом. Цепь честно канатная: граница поставляет
    перевес каната в каждой позиции выше цикла; бюджет окна конвертирует перевес в
    строгий спуск; индукция по потолку стягивает к поглощающему циклу 1→2→1. -/
theorem collatz_from_firstCause :
    ∀ n : ℕ, 1 ≤ n → ∃ K, iter K n = 1 :=
  fun n h1 => reaches_one_of_countingLaw n h1 (collatzRopeBoundary n h1)

/-- **ЧЕСТНАЯ ЦЕНА (раскрытие; отличие от близнецов/Римана):** декрет, возможно,
    ПЕРЕПЛАЧИВАЕТ. Доказана только эта стрелка (граница ⟹ гипотеза); обратная
    («гипотеза ⟹ счётный закон») НЕИЗВЕСТНА — бюджет окна односторонен, и ⟺-формой
    обладает лишь ценностный закон («мост приговорённого»,
    CollatzTugOfWar.valueLaw_iff_reaches_one). ЗЕЛЁНАЯ (не зависит от аксиомы). -/
theorem firstCause_implies_but_maybe_overpays :
    (∀ n : ℕ, 1 ≤ n → RopeCountingLaw n) →
      ∀ n : ℕ, 1 ≤ n → ∃ K, iter K n = 1 :=
  fun law n h1 => reaches_one_of_countingLaw n h1 (law n h1)

/-! ## Растяжки (детекторы взрыва) — 🟡 намеренно -/

/-- **РАСТЯЖКА (Коллатц):** если универсальный закон каната когда-либо будет
    опровергнут, карантин противоречив — False выводимо ИМЕННО здесь. ⚠️ AXIOM-TAINTED. -/
theorem collatzQuarantine_inconsistent_if_law_refuted
    (h : ¬ ∀ n : ℕ, 1 ≤ n → RopeCountingLaw n) : False :=
  h collatzRopeBoundary

/-- **РАСТЯЖКА (Коллатц):** если будет предъявлена несходящаяся траектория (расходимость
    или чужой цикл), False выводимо здесь. Непротиворечивость расширенной теории ⟺
    неопровержимость гипотезы. ⚠️ AXIOM-TAINTED. -/
theorem collatzQuarantine_inconsistent_if_nonconvergence_exhibited
    (n : ℕ) (h1 : 1 ≤ n) (h : ∀ K, iter K n ≠ 1) : False := by
  cases collatz_from_firstCause n h1 with
  | intro K hK => exact h K hK

/-! ## Эпистемика: решение заперто за двигателем (зеркало twin-§8)

Зелёный фронт опровержения (`nonHalting_carries_perpetual_engine`, `exists_min_position`,
`NonDescendingOrbit`) импортирован из CollatzTugOfWar. ЧЕСТНОЕ РАСКРЫТИЕ: та секция
использует `Classical.em` (стандартная тройка аксиом); эпистемика ниже — зелёная. -/

/-- **Внутреннее самообоснование основания закона каната**: несёт сам закон И
    свидетельство, что выведен изнутри — пересекая собственную границу
    (forbidden self-supporting case). ЧЕСТНАЯ ОГОВОРКА (как у twin-версии): форма
    тавтологична — «доказать P, пересекая границу P» сворачивается в P ∧ ¬P;
    содержательно здесь ОТОЖДЕСТВЛЕНИЕ: попытка внутреннего обоснования и есть уже
    сожжённая двигательная конструкция. -/
structure InternalisedCollatzGround : Prop where
  ground : ∀ n : ℕ, 1 ≤ n → RopeCountingLaw n
  beyondOwnHorizon : ¬ ∀ n : ℕ, 1 ≤ n → RopeCountingLaw n

/-- «Внутреннее знание причины» = внутреннее самообоснование границы. -/
abbrev InternalKnowledgeOfCollatzCause : Prop := InternalisedCollatzGround

/-- Самообоснование самоуничтожается. -/
theorem no_internalisedCollatzGround : InternalisedCollatzGround → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **«УЗНАТЬ НЕЛЬЗЯ» — ТЕОРЕМА:** внутреннее знание первопричины Коллатца невозможно
    (зеркало twin-`cause_unknowable`). ЗЕЛЁНАЯ, вообще без аксиом. -/
theorem collatzCause_unknowable : ¬ InternalKnowledgeOfCollatzCause :=
  no_internalisedCollatzGround

/-- Знание опровергло бы Коллатца. ⚠️ ЧЕСТНОСТЬ: маршрут ex falso — см. обязательный
    companion ниже (зеркало twin-§8.4/8.5). -/
theorem knowledge_refutes_collatz :
    InternalKnowledgeOfCollatzCause →
      ∃ n : ℕ, 1 ≤ n ∧ ∀ K, iter K n ≠ 1 :=
  fun hK => (no_internalisedCollatzGround hK).elim

/-- COMPANION (машинная честность): из того же знания следует и Коллатц — знание
    взрывает всё; несущая часть — сама непознаваемость. -/
theorem knowledge_proves_collatz :
    InternalKnowledgeOfCollatzCause →
      ∀ n : ℕ, 1 ≤ n → ∃ K, iter K n = 1 :=
  fun hK => (no_internalisedCollatzGround hK).elim

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ (без ex falso в утверждении): либо причина непознаваема,
    либо Коллатц ложен. Левый дизъюнкт — теорема. -/
theorem unknowable_or_collatz_fails :
    ¬ InternalKnowledgeOfCollatzCause ∨
      ∃ n : ℕ, 1 ≤ n ∧ ∀ K, iter K n ≠ 1 :=
  Or.inl collatzCause_unknowable

/-- **СВОДКА «РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» (зелёная; зеркало
    twin-кирпича no_internal_decision_without_engine):**
    (1) ОПРОВЕРГНУТЬ = построить вечный двигатель — подлинно (хвост от минимума
        предъявляется конструкцией);
    (2) ДОКАЗАТЬ ИЗНУТРИ = самообосновать границу — самоуничтожается (форма P∧¬P);
    (3) единственный без-двигательный путь — принять границу ИЗВНЕ, и тогда остановка
        строга.
    НЕ утверждается гёделевская независимость — только: оба внутренних решения стоят
    вечного двигателя. -/
theorem collatz_no_internal_decision_without_engine :
    (∀ n : ℕ, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) ∧
    (InternalisedCollatzGround → False) ∧
    ((∀ n : ℕ, 1 ≤ n → RopeCountingLaw n) →
        ∀ n : ℕ, 1 ≤ n → ∃ K, iter K n = 1) :=
  ⟨fun n hnh => nonHalting_carries_perpetual_engine n hnh,
   no_internalisedCollatzGround,
   firstCause_implies_but_maybe_overpays⟩

/-- **«ПРОВЕРКА, А НЕ ВЫВОД» (машинно видимый нарратив первопричины Коллатца):**
    (1) бесконечное ВНУТРЕННЕЕ извлечение закона каната НЕВОЗМОЖНО — самообоснование
        границы самоуничтожается (`collatzCause_unknowable`);
    (2) поэтому единственный ВНУТРЕННИЙ след контрпримера — вечный двигатель: хвост
        орбиты от минимума неубывающий и не останавливается
        (`nonHalting_carries_perpetual_engine`);
    (3) значит решение — либо непознаваемо изнутри, либо доступно лишь ПРОВЕРКОЙ орбиты
        (правый дизъюнкт), находимой ровно настолько далеко, насколько мы смотрим.
    ЗЕЛЁНАЯ (вся сила — в непознаваемости; аксиома не нужна). -/
theorem collatz_verification_not_derivation :
    (¬ InternalKnowledgeOfCollatzCause) ∧
    (∀ n : ℕ, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) ∧
    (¬ InternalKnowledgeOfCollatzCause ∨ ∃ n : ℕ, 1 ≤ n ∧ ∀ K, iter K n ≠ 1) :=
  ⟨collatzCause_unknowable,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh,
   unknowable_or_collatz_fails⟩

/-- Итоговый эпистемический статус первопричины Коллатца (зеркало
    twin-`epistemicFirstCauseStatus`): граница каната ПРИНЯТА (поле первопричины) /
    ЗНАТЬ её нельзя (теорема) / ПРИНЯТИЕ даёт остановку (условно) / ОПРОВЕРЖЕНИЕ строило
    бы вечный двигатель (теорема). ⚠️ AXIOM-TAINTED (первый и третий конъюнкты —
    декрет). -/
theorem collatz_locked_behind_engine_status :
    (∀ n : ℕ, 1 ≤ n → RopeCountingLaw n) ∧
    (¬ InternalKnowledgeOfCollatzCause) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ K, iter K n = 1) ∧
    (∀ n : ℕ, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) :=
  ⟨collatzRopeBoundary, collatzCause_unknowable, collatz_from_firstCause,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh⟩

/-! ## Аудит аксиом: зелёная эпистемика чиста (стандартная тройка через em в минимуме
    орбиты), декретный слой заражён ровно step00FirstCause (единственная аксиома репо) -/
#print axioms collatz_from_firstCause
#print axioms collatzRopeBoundary
#print axioms collatzQuarantine_inconsistent_if_law_refuted
#print axioms collatzQuarantine_inconsistent_if_nonconvergence_exhibited
#print axioms firstCause_implies_but_maybe_overpays
#print axioms collatzCause_unknowable
#print axioms unknowable_or_collatz_fails
#print axioms collatz_no_internal_decision_without_engine
#print axioms collatz_verification_not_derivation
#print axioms collatz_locked_behind_engine_status

end EuclidsPath.Collatz.FirstCause
