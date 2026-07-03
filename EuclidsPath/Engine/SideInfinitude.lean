/-
  SideInfinitude — стороны порознь бесконечны (Дирихле); согласование сторон —
  вся открытая суть.

  ЗЕЛЁНЫЙ МОДУЛЬ: всё ниже доказано полностью (std аксиомы, без sorry).
  Двигатель — теорема Дирихле о простых в арифметических прогрессиях из mathlib
  (`Nat.forall_exists_prime_gt_and_modEq`, аналитика L-рядов): каждая из двух
  сторон центра `m` — минус-сторона `6m − 1` (класс `5 mod 6`) и плюс-сторона
  `6m + 1` (класс `1 mod 6`) — ПО ОТДЕЛЬНОСТИ пробегает бесконечно много простых.

  ⚠️ ГЛАВНАЯ ЧЕСТНОСТЬ: одиночки зелёные, но СОГЛАСОВАНИЕ обеих сторон в ОДНОМ
  центре `m` (оба `6m − 1` и `6m + 1` просты одновременно = близнецы) — это ВСЯ
  открытая суть программы. Дирихле даёт две независимые бесконечные шеренги,
  но ничего не говорит о том, что они бесконечно часто выстраиваются напротив
  друг друга. Никакое спаривание здесь НЕ утверждается (маркер
  NoPairingClaimed). Этот модуль — хребет честности, на который ссылаются все
  парные фронты.

  ЧТО ДОКАЗАНО (mathlib Дирихле, std аксиомы, без sorry):
    * minusSide_primes_unbounded / plusSide_primes_unbounded — над любым `n`
      есть простое `p` с `p % 6 = 5` (соотв. `p % 6 = 1`);
    * minusSide_center_unbounded / plusSide_center_unbounded — центровая форма:
      над любым `n` есть центр `m` с простой минус-стороной `6m − 1`
      (соотв. плюс-стороной `6m + 1`);
    * minusSide_primes_infinite / plusSide_primes_infinite — те же факты
      в форме `Set.Infinite`.
  Спаривание сторон (близнецы) — НЕ здесь и не выводится ниоткуда здесь.
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.SideInfinitude

open EuclidsPath

/-- **МИНУС-СТОРОНА НЕОГРАНИЧЕННА (доказано, Дирихле):** над любым `n` найдётся
    простое `p ≡ 5 (mod 6)` — простое вида `6m − 1`. -/
theorem minusSide_primes_unbounded (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ p % 6 = 5 := by
  obtain ⟨p, hgt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (q := 6) (a := 5) (by norm_num) (by decide)
  exact ⟨p, hgt, hp, by simpa [Nat.ModEq] using hmod⟩

/-- **ПЛЮС-СТОРОНА НЕОГРАНИЧЕННА (доказано, Дирихле):** над любым `n` найдётся
    простое `p ≡ 1 (mod 6)` — простое вида `6m + 1`. -/
theorem plusSide_primes_unbounded (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ p % 6 = 1 := by
  obtain ⟨p, hgt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (q := 6) (a := 1) (by norm_num) (by decide)
  exact ⟨p, hgt, hp, by simpa [Nat.ModEq] using hmod⟩

/-- **ЦЕНТРОВАЯ ФОРМА, МИНУС (доказано):** над любым `n` есть центр `m`,
    у которого минус-сторона `6m − 1` проста. Про плюс-сторону ТОГО ЖЕ `m`
    ничего не утверждается — в этом вся честность. -/
theorem minusSide_center_unbounded (n : ℕ) :
    ∃ m, n < m ∧ (6 * m - 1).Prime := by
  obtain ⟨p, hgt, hp, hmod⟩ := minusSide_primes_unbounded (6 * n + 5)
  refine ⟨(p + 1) / 6, by omega, ?_⟩
  have h : 6 * ((p + 1) / 6) - 1 = p := by omega
  rwa [h]

/-- **ЦЕНТРОВАЯ ФОРМА, ПЛЮС (доказано):** над любым `n` есть центр `m`,
    у которого плюс-сторона `6m + 1` проста. Про минус-сторону ТОГО ЖЕ `m`
    ничего не утверждается — в этом вся честность. -/
theorem plusSide_center_unbounded (n : ℕ) :
    ∃ m, n < m ∧ (6 * m + 1).Prime := by
  obtain ⟨p, hgt, hp, hmod⟩ := plusSide_primes_unbounded (6 * n + 1)
  refine ⟨p / 6, by omega, ?_⟩
  have h : 6 * (p / 6) + 1 = p := by omega
  rwa [h]

/-- **БЕСКОНЕЧНОСТЬ МИНУС-СТОРОНЫ (доказано):** множество простых `p ≡ 5 (mod 6)`
    бесконечно — форма `Set.Infinite` от неограниченности выше. -/
theorem minusSide_primes_infinite :
    {p : ℕ | p.Prime ∧ p % 6 = 5}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, hp, hmod⟩ := minusSide_primes_unbounded B
  have hmem : p ∈ {p : ℕ | p.Prime ∧ p % 6 = 5} := ⟨hp, hmod⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- **БЕСКОНЕЧНОСТЬ ПЛЮС-СТОРОНЫ (доказано):** множество простых `p ≡ 1 (mod 6)`
    бесконечно — форма `Set.Infinite` от неограниченности выше. -/
theorem plusSide_primes_infinite :
    {p : ℕ | p.Prime ∧ p % 6 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, hp, hmod⟩ := plusSide_primes_unbounded B
  have hmem : p ∈ {p : ℕ | p.Prime ∧ p % 6 = 1} := ⟨hp, hmod⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- **ЧЕСТНОСТЬ (охват):** обе стороны порознь зелёные (Дирихле, аналитика
    mathlib), но СОГЛАСОВАНИЕ обеих сторон в одном центре `m` — одновременная
    простота `6m − 1` и `6m + 1` — это гипотеза близнецов, и здесь она НЕ
    утверждается, НЕ доказана и ниоткуда здесь не выводится. -/
abbrev NoPairingClaimed : Prop := True

theorem noPairingClaimed : NoPairingClaimed := trivial

#print axioms minusSide_primes_unbounded
#print axioms plusSide_primes_unbounded
#print axioms minusSide_primes_infinite
#print axioms minusSide_center_unbounded

end EuclidsPath.SideInfinitude
