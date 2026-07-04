/-
  CollatzFirstCause — ПОСТ-МОРТЕМ четвёртой границы (декрет ВЗЯТ И СНЯТ) +
  уцелевшая зелёная эпистемика. Разбор: prose/56_CollatzFirstCause.md.
  Зелёная машина: Engine/CollatzTugOfWar.lean.

  ИСТОРИЯ. Закон каната (`RopeCountingLaw` для всех n ≥ 1) был принят ЧЕТВЁРТОЙ
  границей `collatzBoundary` структуры `Step00FirstCause` — с раскрытой ценой
  «декрет, возможно, ПЕРЕПЛАЧИВАЕТ» (доказана лишь стрелка закон ⟹ гипотеза).
  Затем универсальная форма закона была ОПРОВЕРГНУТА машинно:
  `ropeLaw_universal_refuted` (CollatzTugOfWar; свидетель n = 27, ядро
  [propext, Quot.sound]). Растяжка `collatzQuarantine_inconsistent_if_law_refuted`
  сработала ровно как задумано — поле УДАЛЕНО из первопричины (иначе аксиома
  была бы противоречива). Переплатил до лжи; дисциплина честности отработала.

  СТАТУС ТЕПЕРЬ. Как у Янг–Миллса: трилемма закрыта КОВАНЫМ опровержением —
  декретный путь для Коллатца невозможен машинно. Гипотеза Коллатца — открытый
  🔴 вопрос при зелёном фронте: бюджет окна, УСЛОВНЫЙ per-n герой
  `reaches_one_of_countingLaw`, «опровержение гипотезы = вечный двигатель»
  (`nonHalting_carries_perpetual_engine`) — всё живо. Этот модуль ЦЕЛИКОМ
  ЗЕЛЁНЫЙ: не импортирует карантин, не трогает таинт.
-/

import EuclidsPath.Engine.CollatzTugOfWar

set_option autoImplicit false

namespace EuclidsPath.Collatz.FirstCause

open EuclidsPath.Collatz.TugOfWar

/-! ## Пост-мортем декрета (🟢) -/

/-- **ПОСТ-МОРТЕМ ЧЕТВЁРТОЙ ГРАНИЦЫ (зелёная сводка).** (1) Универсальный закон
    каната ЛОЖЕН (свидетель n = 27) — декретная граница на нём невозможна;
    (2) per-n закон по-прежнему влечёт остановку (условная механика жива);
    (3) опровержение самой гипотезы всё равно несёт вечный двигатель (хвост от
    минимума). Декрет пал, зелёный фронт цел. -/
theorem collatz_decree_postmortem :
    (¬ ∀ n : Nat, 1 ≤ n → RopeCountingLaw n) ∧
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n → ∃ K, iter K n = 1) ∧
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) :=
  ⟨ropeLaw_universal_refuted,
   fun n h1 law => reaches_one_of_countingLaw n h1 law,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh⟩

/-- **Стрелка декрета, которая «возможно, переплачивала» — и переплатила до
    лжи.** Импликация «универсальный закон ⟹ сходимость всюду» остаётся
    зелёной и верной, но её посылка теперь машинно опровергнута
    (`ropeLaw_universal_refuted`): универсально закон никогда не будет подан.
    Содержание живёт в per-n форме (`reaches_one_of_countingLaw`). -/
theorem ropeLaw_would_imply_collatz :
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n) →
      ∀ n : Nat, 1 ≤ n → ∃ K, iter K n = 1 :=
  fun law n h1 => reaches_one_of_countingLaw n h1 (law n h1)

/-! ## Эпистемика: решение заперто за двигателем (зелёная, уцелела)

Непознаваемость внутреннего самообоснования НЕ зависела от декрета и переживает
его падение; более того, теперь основание `ground` само машинно опровергнуто —
внутреннее самообоснование невозможно уже a fortiori. -/

/-- **Внутреннее самообоснование основания закона каната**: несёт сам закон И
    свидетельство, что выведен изнутри — пересекая собственную границу.
    После `ropeLaw_universal_refuted` сторона `ground` сама по себе ложна —
    самообоснование невозможно вдвойне. -/
structure InternalisedCollatzGround : Prop where
  ground : ∀ n : Nat, 1 ≤ n → RopeCountingLaw n
  beyondOwnHorizon : ¬ ∀ n : Nat, 1 ≤ n → RopeCountingLaw n

/-- «Внутреннее знание причины» = внутреннее самообоснование границы. -/
abbrev InternalKnowledgeOfCollatzCause : Prop := InternalisedCollatzGround

/-- Самообоснование самоуничтожается (форма); а после опровержения закона
    невозможно и по содержанию: `ground` ложен. -/
theorem no_internalisedCollatzGround : InternalisedCollatzGround → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **«УЗНАТЬ НЕЛЬЗЯ» — ТЕОРЕМА** (зеркало twin-`cause_unknowable`): внутреннее
    знание первопричины Коллатца невозможно. ЗЕЛЁНАЯ, вообще без аксиом. -/
theorem collatzCause_unknowable : ¬ InternalKnowledgeOfCollatzCause :=
  no_internalisedCollatzGround

/-- А теперь и сильнее: основание непознаваемого знания само ложно —
    прямое следствие опровержения (не через самоуничтожение формы). -/
theorem internalGround_impossible_a_fortiori : InternalisedCollatzGround → False :=
  fun H => ropeLaw_universal_refuted H.ground

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ (без ex falso в утверждении): либо причина
    непознаваема, либо Коллатц ложен. Левый дизъюнкт — теорема. -/
theorem unknowable_or_collatz_fails :
    ¬ InternalKnowledgeOfCollatzCause ∨
      ∃ n : Nat, 1 ≤ n ∧ ∀ K, iter K n ≠ 1 :=
  Or.inl collatzCause_unknowable

/-- **СВОДКА «РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» (зелёная):**
    (1) ОПРОВЕРГНУТЬ гипотезу = построить вечный двигатель — подлинно (хвост от
        минимума предъявляется конструкцией);
    (2) ДОКАЗАТЬ ИЗНУТРИ = самообосновать основание — самоуничтожается;
    (3) per-n закон каната влёк бы остановку per-n — но УНИВЕРСАЛЬНОЙ подачи
        больше нет: универсальный закон опровергнут.
    НЕ утверждается гёделевская независимость — только: оба внутренних решения
    стоят вечного двигателя, а декретная дверь закрыта кованым опровержением. -/
theorem collatz_no_internal_decision_without_engine :
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) ∧
    (InternalisedCollatzGround → False) ∧
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n → ∃ K, iter K n = 1) :=
  ⟨fun n hnh => nonHalting_carries_perpetual_engine n hnh,
   no_internalisedCollatzGround,
   fun n h1 law => reaches_one_of_countingLaw n h1 law⟩

/-- **«ПРОВЕРКА, А НЕ ВЫВОД» (машинно видимый нарратив):**
    (1) внутреннее извлечение закона каната невозможно
        (`collatzCause_unknowable`);
    (2) единственный внутренний след контрпримера — вечный двигатель: хвост
        орбиты от минимума неубывающий и не останавливается;
    (3) значит решение — либо непознаваемо изнутри, либо доступно лишь
        ПРОВЕРКОЙ орбиты, находимой ровно настолько далеко, насколько мы
        смотрим. ЗЕЛЁНАЯ. -/
theorem collatz_verification_not_derivation :
    (¬ InternalKnowledgeOfCollatzCause) ∧
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) ∧
    (¬ InternalKnowledgeOfCollatzCause ∨ ∃ n : Nat, 1 ≤ n ∧ ∀ K, iter K n ≠ 1) :=
  ⟨collatzCause_unknowable,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh,
   unknowable_or_collatz_fails⟩

/-- Итоговый эпистемический статус Коллатца ПОСЛЕ падения декрета (зелёный,
    зеркало `pnp_locked_behind_engine_status` — без декрет-конъюнкта):
    универсальный закон ОПРОВЕРГНУТ (теорема) / внутреннее знание невозможно
    (теорема) / per-n закон влечёт остановку (условно) / опровержение гипотезы
    строило бы вечный двигатель (теорема). -/
theorem collatz_open_status :
    (¬ ∀ n : Nat, 1 ≤ n → RopeCountingLaw n) ∧
    (¬ InternalKnowledgeOfCollatzCause) ∧
    (∀ n : Nat, 1 ≤ n → RopeCountingLaw n → ∃ K, iter K n = 1) ∧
    (∀ n : Nat, (∀ K, iter K n ≠ 1) →
        ∃ j, NonDescendingOrbit (iter j n) ∧ ∀ K, iter K (iter j n) ≠ 1) :=
  ⟨ropeLaw_universal_refuted, collatzCause_unknowable,
   fun n h1 law => reaches_one_of_countingLaw n h1 law,
   fun n hnh => nonHalting_carries_perpetual_engine n hnh⟩

/-! ## Аудит аксиом: модуль ЦЕЛИКОМ зелёный (декретного слоя больше нет) -/
#print axioms collatz_decree_postmortem
#print axioms ropeLaw_would_imply_collatz
#print axioms no_internalisedCollatzGround
#print axioms collatzCause_unknowable
#print axioms internalGround_impossible_a_fortiori
#print axioms unknowable_or_collatz_fails
#print axioms collatz_no_internal_decision_without_engine
#print axioms collatz_verification_not_derivation
#print axioms collatz_open_status

end EuclidsPath.Collatz.FirstCause
