/-
  LandauFront — зоо-вход для 4-й проблемы Ландау: простые вида `n² + 1`.

  ЗЕЛЁНЫЙ МОДУЛЬ (в смысле репозитория): всё ниже доказано полностью
  (std аксиомы, без sorry). Но — как и в `PolignacBranch` — здесь НЕ решается
  открытая задача. Двигатель Дирихле из mathlib (`SideInfinitude`) даёт простые
  в арифметических прогрессиях; однако `n² + 1` — это НЕ арифметическая
  прогрессия, а квадратичная форма, поэтому бесконечность простых `n² + 1`
  Дирихле НЕ покрывается и остаётся честным 🔴-гейтом `Landau4thUnbounded`
  (эвристика Харди–Литтлвуда предсказывает бесконечность — знак ЗА, но НЕ
  доказательство).

  ⚠️ ГЛАВНАЯ ЧЕСТНОСТЬ: зелёное здесь — ТОЛЬКО структурный мост
  «неограниченность ⟹ бесконечность множества» (чистая перепаковка через
  `Set.Infinite`, как `cousinLowersInfinite_of_unbounded` в `PolignacBranch`)
  плюс один настоящий зелёный факт о вычетах. Новой теории чисел нет.
  Сама бесконечность простых `n² + 1` — ОТКРЫТА (маркер `NoInfinitudeClaimed`).
  Лучшее известное (Иванец, 1978): бесконечно много `n² + 1` с не более чем
  двумя простыми множителями — но это НЕ бесконечность самих простых `n² + 1`.

  ЧТО ДОКАЗАНО (std аксиомы, без sorry):
    * landauPrimes_infinite_of_unbounded — структурный мост: 🔴-гейт
      `Landau4thUnbounded` ⟹ множество `LandauPrimes` бесконечно
      (форма `Set.Infinite`, чистая перепаковка);
    * oddLandauPrime_even_k — зелёный факт о вычетах: если `k` нечётно, то
      `k² + 1` чётно, поэтому единственное чётное простое такого вида — это
      `2` (при `k = 1`); все простые `k² + 1 > 2` требуют ЧЁТНОГО `k`.
  Бесконечность простых `n² + 1` — НЕ здесь и ниоткуда здесь не выводится.
-/
import Mathlib
set_option autoImplicit false

namespace EuclidsPath.LandauFront

/-- Множество простых Ландау `n² + 1`. -/
def LandauPrimes : Set ℕ := {p | ∃ k : ℕ, p = k ^ 2 + 1 ∧ p.Prime}

/-- 🔴 ГЕЙТ: бесконечно много `k` дают простое `k² + 1` (Харди–Литтлвуд;
    4-я проблема Ландау). ОТКРЫТА — здесь ниоткуда не выводится. -/
def Landau4thUnbounded : Prop := ∀ N : ℕ, ∃ k : ℕ, N < k ∧ (k ^ 2 + 1).Prime

/-- 🟢 **СТРУКТУРНЫЙ МОСТ (доказано):** неограниченность ⟹ множество простых
    Ландау бесконечно. Чистая перепаковка через `Set.Infinite`, без новой
    теории чисел; форма — как у `cousinLowersInfinite_of_unbounded`. -/
theorem landauPrimes_infinite_of_unbounded (H : Landau4thUnbounded) :
    LandauPrimes.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k, hgt, hp⟩ := H B
  have hmem : (k ^ 2 + 1) ∈ LandauPrimes := ⟨k, rfl, hp⟩
  have hBlt : B < k ^ 2 + 1 := by nlinarith [hgt]
  exact absurd (hB hmem) (not_le.mpr hBlt)

/-- 🟢 **ЗЕЛЁНЫЙ ФАКТ О ВЫЧЕТАХ (доказано):** если `k` нечётно, то `k² + 1`
    чётно, значит любое простое такого вида равно `2`; поэтому всякое простое
    `k² + 1 > 2` требует ЧЁТНОГО `k`. Настоящий зелёный факт о структуре формы,
    без всякой связи с открытой бесконечностью. -/
theorem oddLandauPrime_even_k {k : ℕ} (hodd : Odd k) (hp : (k ^ 2 + 1).Prime) :
    k ^ 2 + 1 = 2 := by
  have h2dvd : 2 ∣ k ^ 2 + 1 := by
    obtain ⟨j, hj⟩ := hodd
    refine ⟨2 * j ^ 2 + 2 * j + 1, ?_⟩
    subst hj
    ring
  rcases (hp.eq_one_or_self_of_dvd 2 h2dvd) with h | h
  · omega
  · omega

/-- **ЧЕСТНОСТЬ (охват):** бесконечность простых `n² + 1` здесь НЕ
    утверждается, НЕ доказана и ниоткуда здесь не выводится. Дирихле
    (mathlib, `SideInfinitude`) покрывает лишь арифметические прогрессии;
    `n² + 1` — квадратичная форма, вне досягаемости Дирихле. 4-я проблема
    Ландау ОТКРЫТА; доказанный выше мост условен (вход — 🔴-гейт
    `Landau4thUnbounded`) и открытой задачи не решает. -/
abbrev NoInfinitudeClaimed : Prop := True

theorem noInfinitudeClaimed : NoInfinitudeClaimed := trivial

#print axioms landauPrimes_infinite_of_unbounded
#print axioms oddLandauPrime_even_k

end EuclidsPath.LandauFront
