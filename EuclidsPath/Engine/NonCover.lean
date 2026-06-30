/-
  Сборочное ядро Multi-Rank Non-Cover (Wave 6). Проза: prose/22_NonCover.md.

  Здесь — ВЕРИФИЦИРОВАННАЯ нециркулярная редукция:
  (1) `survivor_of_not_covered` — если суммарный «плохой» класс меньше carrier, есть выживший;
  (2) `infinite_of_unbounded_centers` — бесконечно много twin-центров ⟹ гипотеза близнецов.

  Это честная граница «до гипотезы»: логическая цепь машинно проверена, а ОТКРЫТЫМ остаётся ровно
  комбинаторное ядро — что «плохие» ранги не покрывают carrier (оценка снизу carrier = `CarrierInput`,
  оценка сверху bad — через fan/cycle), и что выживший имеет ранг (1,1). См. prose/15, prose/22.

  Всё ниже — элементарная Finset/порядковая комбинаторика. Без анализа/распределения/сита.
-/
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath

/--
  **Non-cover ⟹ выживший.** Если размер «плохого» множества меньше размера carrier `Ω`,
  то существует элемент `Ω`, не лежащий в `bad` (кандидат в twin-центр).
  Чистая Finset-комбинаторика (если бы `Ω ⊆ bad`, то `|Ω| ≤ |bad|`).
-/
theorem survivor_of_not_covered {Ω bad : Finset ℕ} (hlt : bad.card < Ω.card) :
    ∃ m ∈ Ω, m ∉ bad := by
  by_contra h
  have hsub : Ω ⊆ bad := by
    intro m hm
    by_contra hmb
    exact h ⟨m, hm, hmb⟩
  have := Finset.card_le_card hsub
  omega

/--
  **Мост к гипотезе.** Если twin-центры неограниченны (для любого `N` есть центр `m > N` с обоими
  простыми `6m±1`), то простых-близнецов бесконечно много (`TwinLowers.Infinite`).
-/
theorem infinite_of_unbounded_centers
    (h : ∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m) : TwinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨m, hmN, hc⟩ := h N
  refine ⟨6 * m - 1, ?_, ?_⟩
  · refine ⟨hc.1, ?_⟩
    have e : 6 * m - 1 + 2 = 6 * m + 1 := by omega
    rw [e]; exact hc.2
  · omega

end EuclidsPath
