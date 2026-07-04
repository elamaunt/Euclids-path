/-
  BoundedGapsAnchor — якорь ограниченных зазоров: Чжан 2013 / Мейнард–Тао 2014.

  ┌─────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК. ЧТО ЗДЕСЬ ЗЕЛЁНОЕ И ЧТО ЧЕСТНО КРАСНОЕ.     │
  └─────────────────────────────────────────────────────────────────────────┘

  Итан Чжан (2013) доказал: существует B < 70 000 000 такое, что бесконечно
  много пар последовательных простых с зазором ≤ B. Мейнард и Тао (2014,
  независимо; Polymath8b) снизили планку до B = 246. Это ЛУЧШИЙ безусловный
  результат человечества на пути к близнецам (B = 2). НИ ОДИН из этих
  результатов НЕ формализован: в mathlib v4.31 нет ни теоремы Чжана, ни
  Мейнарда–Тао, ни даже метода Гольдстона–Пинца–Йылдырыма. Самое сильное,
  что mathlib реально даёт о зазорах, — постулат Бертрана
  (`Nat.exists_prime_lt_and_le_two_mul`): в (n, 2n] есть простое. Но это зазор
  порядка САМОГО p, а не константа B — от Бертрана до ограниченных зазоров
  пропасть в столетие аналитической теории чисел (BV-теорема, сита GPY/Maynard).
  Поэтому вход здесь — именованный КРАСНЫЙ def-якорь `BoundedGaps B`,
  НЕ теорема, НЕ sorry, НЕ аксиома.

  🔴 КРАСНЫЕ ВХОДЫ (названы, ниоткуда не выводятся):
   · `BoundedGaps B` — «бесконечно много пар простых с зазором ≤ B»;
   · `ZhangAnchor`      = BoundedGaps 70000000 (Zhang 2013);
   · `MaynardTaoAnchor` = BoundedGaps 246      (Maynard–Tao 2014, Polymath8b).

  🟢 ЗЕЛЁНЫЕ МОСТЫ (машинно, std-аксиомы):
   · `boundedGaps_mono` — монотонность по B: ослабление планки бесплатно;
   · `zhangAnchor_of_maynardTao` — 246 ⟹ 70 000 000 (инстанс монотонности);
   · `boundedGaps_two_iff_twins` — ГЛАВНЫЙ АУДИТ НА ПЕРЕИМЕНОВАНИЕ ЦЕЛИ
     (зеркало `offCriticalBridge_iff_RH`): якорь на краю B = 2 РАВНОСИЛЕН
     бесконечности близнецов (`TwinLowers.Infinite` из Step00). Принять
     `BoundedGaps 2` = принять близнецов: это дословное переименование
     гипотезы, и мы раскрываем это машинно, iff-теоремой, а не прячем;
   · `boundedGaps_two_iff_unbounded_twins` — та же равносильность в
     самостоятельной формулировке «∀ N ∃ p > N: p и p+2 просты»;
   · `boundedGaps_four_twins_or_cousins`, `boundedGaps_six_polignac_trichotomy`
     — сетка PolignacBranch: при зазоре ≤ 4 бесконечен хотя бы один из классов
     {близнецы, кузены}; при ≤ 6 — хотя бы один из {близнецы, кузены, секси}.
     Это формальная тень НАСТОЯЩЕГО следствия Мейнарда–Тао: из B = 246
     бесконечен хотя бы ОДИН класс зазоров d ≤ 246 — но КАКОЙ именно,
     неизвестно; дизъюнкция неустранима.

  ⚠️ ГЛАВНАЯ ЧЕСТНОСТЬ: спуск от B = 246 к B = 2 — ОТКРЫТАЯ математика.
  `MaynardTaoAnchor` близнецов НЕ влечёт: из «бесконечно много зазоров ≤ 246»
  никакими зелёными средствами не следует «бесконечно много зазоров ≤ 2» —
  монотонность работает ВВЕРХ по B, не вниз. Маркер:
  `NoDescentFrom246To2Claimed`. Что математика ДОЛЖНА предъявить для спуска:
  уровень распределения простых за пределами Bombieri–Vinogradov (гипотеза
  Эллиотта–Халберстама даёт B = 12, обобщённая EH — B = 6, Polymath8b), а
  ниже 6 сита упираются в parity problem Сельберга — B = 2 не берётся даже
  при GEH, нужна идея другого рода. В mathlib v4.31 нет НИЧЕГО из этого
  списка: нет Bombieri–Vinogradov, нет Selberg sieve в нужной силе, нет ни
  одного proof_wanted про ограниченные зазоры.

  ЭТО НЕ РЕШЕНИЕ ГИПОТЕЗЫ БЛИЗНЕЦОВ И НЕ ГЁДЕЛЕВСКИЙ АРГУМЕНТ. Якорь —
  честная точка стыковки: если внешняя математика предъявит `BoundedGaps 2`,
  зелёный мост немедленно закрывает цель Step00.

  Никакого sorry, никакого admit, никакого native_decide, никакой новой
  аксиомы; карантин (CausalClosureAxiom) НЕ импортируется. Зелёные
  грузонесущие — стандартная тройка propext / Classical.choice / Quot.sound.
  Такса репозитория (таинт 47) этим файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BoundedGapsAnchor.lean
    → ноль ошибок.

  Родство: EuclidsPath/Engine/PolignacBranch.lean (сетка 6m±1, кузены/секси),
  EuclidsPath/Step00_Overview.lean (`TwinLowers`, `IsTwinPair`).
-/
import Mathlib
import EuclidsPath.Engine.PolignacBranch

set_option autoImplicit false

namespace EuclidsPath.BoundedGapsAnchor

open EuclidsPath EuclidsPath.PolignacBranch

/-! ### 🔴 Красные входы: именованные якоря, НЕ теоремы -/

/-- **🔴 КРАСНЫЙ ВХОД — якорь ограниченных зазоров.** «Бесконечно много пар
    простых с зазором ≤ B»: выше любого `N` найдутся простые `p < q ≤ p + B`.

    Известно человечеству (вне mathlib): Zhang 2013 даёт `B = 70 000 000`,
    Maynard–Tao 2014 (и Polymath8b) — `B = 246`. НИ ОДНО из этих значений
    не формализовано: mathlib v4.31 о зазорах умеет лишь постулат Бертрана
    (`Nat.exists_prime_lt_and_le_two_mul`) — зазор ≤ p, растущий, НЕ константа.
    Гипотеза близнецов — ровно `BoundedGaps 2` (см. аудит
    `boundedGaps_two_iff_twins`). Здесь предикат только НАЗВАН. -/
def BoundedGaps (B : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B

/-- **🔴 Якорь Чжана (2013):** бесконечно много зазоров ≤ 70 000 000.
    Доказано человечеством, НЕ формализовано; здесь — только имя. -/
def ZhangAnchor : Prop := BoundedGaps 70000000

/-- **🔴 Якорь Мейнарда–Тао (2014, Polymath8b):** бесконечно много зазоров
    ≤ 246. Лучший безусловный результат; НЕ формализован; здесь — только имя.
    ⚠️ Близнецов НЕ влечёт: спуск 246 → 2 — открытая математика
    (см. `NoDescentFrom246To2Claimed`). -/
def MaynardTaoAnchor : Prop := BoundedGaps 246

/-! ### 🟢 Зелёные мосты -/

/-- **🟢 Монотонность по планке (доказано):** ослабить B бесплатно — та же
    пара свидетелей проходит под более высокой планкой. Работает только
    ВВЕРХ по B; обратного хода (спуска) нет и не утверждается. -/
theorem boundedGaps_mono {B B2 : ℕ} (h : B ≤ B2) (H : BoundedGaps B) :
    BoundedGaps B2 := by
  intro N
  obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H N
  exact ⟨p, q, hN, hp, hq, hlt, by omega⟩

/-- **🟢 246 ⟹ 70 000 000 (доказано):** якорь Мейнарда–Тао влечёт якорь
    Чжана — инстанс монотонности. Исторически стрелка шла в обратную
    сторону (сначала Чжан, потом усиление), логически — в эту. -/
theorem zhangAnchor_of_maynardTao (H : MaynardTaoAnchor) : ZhangAnchor :=
  boundedGaps_mono (by norm_num) H

/-- **🟢 Сантехника (доказано):** бесконечность `TwinLowers` ⟺ неограниченность
    младших членов пар близнецов, «∀ N ∃ p > N: p и p+2 просты». Дешёвый мост
    между репо-формой (Step00) и самостоятельной формулировкой. -/
theorem twinLowers_infinite_iff_unbounded :
    TwinLowers.Infinite ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime := by
  constructor
  · intro H N
    obtain ⟨p, hmem, hlt⟩ := H.exists_gt N
    have hpair : IsTwinPair p := hmem
    exact ⟨p, hlt, hpair.1, hpair.2⟩
  · intro H
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, hlt, hp, hp2⟩ := H C
    have hmem : p ∈ TwinLowers := show IsTwinPair p from ⟨hp, hp2⟩
    exact absurd (hC hmem) (not_le.mpr hlt)

/-- **🟢 ГЛАВНЫЙ АУДИТ НА ПЕРЕИМЕНОВАНИЕ ЦЕЛИ (доказано; зеркало
    `offCriticalBridge_iff_RH`):** якорь на краю `B = 2` РАВНОСИЛЕН
    бесконечности близнецов. Принять `BoundedGaps 2` = принять близнецов:
    дословное переименование гипотезы Step00, раскрытое машинно.

    Прямая: выше `max C 2` оба простых нечётны; из `p < q ≤ p + 2` зазор
    `q − p ∈ {1, 2}`, но `q = p + 1` чётно и > 2 — не простое; остаётся
    `q = p + 2` — пара близнецов. Обратная: сама пара близнецов и есть
    свидетель зазора 2. -/
theorem boundedGaps_two_iff_twins : BoundedGaps 2 ↔ TwinLowers.Infinite := by
  constructor
  · intro H
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H (max C 2)
    have hp2 : 2 < p := lt_of_le_of_lt (le_max_right C 2) hN
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hq_eq : q = p + 2 := by
      rcases (by omega : q = p + 1 ∨ q = p + 2) with h | h
      · exfalso
        have hdvd : 2 ∣ q := by omega
        rcases hq.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega
      · exact h
    have hmem : p ∈ TwinLowers := show IsTwinPair p from ⟨hp, hq_eq ▸ hq⟩
    have hCp : C < p := lt_of_le_of_lt (le_max_left C 2) hN
    exact absurd (hC hmem) (not_le.mpr hCp)
  · intro H N
    obtain ⟨p, hlt, hp, hp2⟩ := twinLowers_infinite_iff_unbounded.mp H N
    exact ⟨p, p + 2, hlt, hp, hp2, by omega, le_refl _⟩

/-- **🟢 Та же равносильность в самостоятельной формулировке (доказано):**
    `BoundedGaps 2` ⟺ «∀ N ∃ p > N: p и p+2 просты» — без ссылки на
    репо-множество, для внешней стыковки. -/
theorem boundedGaps_two_iff_unbounded_twins :
    BoundedGaps 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime :=
  boundedGaps_two_iff_twins.trans twinLowers_infinite_iff_unbounded

/-! ### 🟢 Сетка Полиньяка: дизъюнктивные следствия малых планок

  Формальная тень настоящего следствия Мейнарда–Тао: из `BoundedGaps 246`
  бесконечен хотя бы ОДИН класс зазоров `d ≤ 246`, но КАКОЙ — неизвестно.
  Здесь то же для планок 4 и 6 через классы PolignacBranch. Дизъюнкция
  неустранима: выбрать член дизъюнкции = решить открытую задачу. -/

/-- **🟢 Планка 4 ⟹ близнецы ИЛИ кузены (доказано):** выше 2 оба простых
    нечётны, зазор ≤ 4 означает `q = p + 2` или `q = p + 4`; бесконечно
    объединение `TwinLowers ∪ CousinLowers`, значит бесконечен хотя бы один
    класс. Который — из якоря НЕ извлекается. -/
theorem boundedGaps_four_twins_or_cousins (H : BoundedGaps 4) :
    TwinLowers.Infinite ∨ CousinLowers.Infinite := by
  have hunion : (TwinLowers ∪ CousinLowers).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H (max C 2)
    have hp2 : 2 < p := lt_of_le_of_lt (le_max_right C 2) hN
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
    have hmem : p ∈ TwinLowers ∪ CousinLowers := by
      rcases (by omega : q = p + 2 ∨ q = p + 4) with h | h
      · exact Set.mem_union_left _ (show IsTwinPair p from ⟨hp, h ▸ hq⟩)
      · exact Set.mem_union_right _ ⟨hp, h ▸ hq⟩
    have hCp : C < p := lt_of_le_of_lt (le_max_left C 2) hN
    exact absurd (hC hmem) (not_le.mpr hCp)
  exact Set.infinite_union.mp hunion

/-- **🟢 Планка 6 ⟹ трихотомия Полиньяка (доказано):** зазор ≤ 6 между
    нечётными простыми — это 2, 4 или 6; бесконечен хотя бы один из классов
    {близнецы, кузены, секси}. Миниатюра следствия Мейнарда–Тао: при
    `B = 246` то же с 123 чётными классами — и НИ ОДИН не выбирается. -/
theorem boundedGaps_six_polignac_trichotomy (H : BoundedGaps 6) :
    TwinLowers.Infinite ∨ CousinLowers.Infinite ∨ SexyLowers.Infinite := by
  have hunion : (TwinLowers ∪ (CousinLowers ∪ SexyLowers)).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H (max C 2)
    have hp2 : 2 < p := lt_of_le_of_lt (le_max_right C 2) hN
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
    have hmem : p ∈ TwinLowers ∪ (CousinLowers ∪ SexyLowers) := by
      rcases (by omega : q = p + 2 ∨ q = p + 4 ∨ q = p + 6) with h | h | h
      · exact Set.mem_union_left _ (show IsTwinPair p from ⟨hp, h ▸ hq⟩)
      · exact Set.mem_union_right _ (Set.mem_union_left _ ⟨hp, h ▸ hq⟩)
      · exact Set.mem_union_right _ (Set.mem_union_right _ ⟨hp, h ▸ hq⟩)
    have hCp : C < p := lt_of_le_of_lt (le_max_left C 2) hN
    exact absurd (hC hmem) (not_le.mpr hCp)
  rcases Set.infinite_union.mp hunion with h | h
  · exact Or.inl h
  · exact Or.inr (Set.infinite_union.mp h)

/-! ### Честность -/

/-- **ЧЕСТНОСТЬ (охват):** спуск от `B = 246` к `B = 2` здесь НЕ утверждается
    и ниоткуда не следует: монотонность `boundedGaps_mono` работает только
    вверх по планке. `MaynardTaoAnchor` близнецов НЕ влечёт. Что математика
    должна предъявить для спуска: уровень распределения простых за пределами
    Bombieri–Vinogradov (Elliott–Halberstam даёт B = 12, обобщённая EH —
    B = 6; ниже 6 сита блокирует parity problem Сельберга). Ничего из этого
    в mathlib v4.31 нет. -/
abbrev NoDescentFrom246To2Claimed : Prop := True

theorem noDescentFrom246To2Claimed : NoDescentFrom246To2Claimed := trivial

#print axioms boundedGaps_mono
#print axioms zhangAnchor_of_maynardTao
#print axioms twinLowers_infinite_iff_unbounded
#print axioms boundedGaps_two_iff_twins
#print axioms boundedGaps_two_iff_unbounded_twins
#print axioms boundedGaps_four_twins_or_cousins
#print axioms boundedGaps_six_polignac_trichotomy
#print axioms noDescentFrom246To2Claimed

end EuclidsPath.BoundedGapsAnchor
