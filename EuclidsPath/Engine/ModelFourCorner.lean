/-
  Модельный four-corner (фрактальная отрицательная ассоциация). Проза: prose/20_Fractality.md.

  Вывод из фрактальной структуры: при ± симметрии (вес на сторону одинаков) и эксклюзивности
  (простой делит ≤ 1 стороны, `Carrier.no_large_shared_divisor`) ранговая производящая функция —
  произведение `∏(c+w(x+y))`, т.е. функция от `s=x+y`. Тогда коэффициенты
      N_{ij} = Q_{i+j} · C(i+j, i),     Q_k = коэф. при s^k.
  В равновесной модели (n простых, вес w): Q_k = C(n,k)·w^k, и four-corner
      N₀₀·N₃₃ ≤ N₀₃·N₃₀
  сводится к биномиальному `20·C(n,6) ≤ C(n,3)²` (20 = C(6,3) — константа из R_CRT=20e₆/e₃²).

  Доказательство ЭЛЕМЕНТАРНО (тождество «выбор-в-выборе» + монотонность). Без распределения/сита.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/--
  **Биномиальный four-corner.** Для всех `n`: `20·C(n,6) ≤ C(n,3)²` (при `n<6` слева 0).
  Ключ: `C(n,6)·C(6,3) = C(n,3)·C(n−3,3)` (выбор-в-выборе) и `C(n−3,3) ≤ C(n,3)`.
-/
theorem four_corner_binom (n : ℕ) : 20 * n.choose 6 ≤ (n.choose 3) ^ 2 := by
  have hid : n.choose 6 * (6 : ℕ).choose 3 = n.choose 3 * (n - 3).choose (6 - 3) :=
    Nat.choose_mul (by norm_num)
  have h20 : (6 : ℕ).choose 3 = 20 := by decide
  have hsub : (6 : ℕ) - 3 = 3 := by norm_num
  rw [h20, hsub] at hid
  -- hid : n.choose 6 * 20 = n.choose 3 * (n-3).choose 3
  have hmono : (n - 3).choose 3 ≤ n.choose 3 := Nat.choose_le_choose 3 (Nat.sub_le n 3)
  calc 20 * n.choose 6 = n.choose 6 * 20 := by ring
    _ = n.choose 3 * (n - 3).choose 3 := hid
    _ ≤ n.choose 3 * n.choose 3 := by gcongr
    _ = (n.choose 3) ^ 2 := by ring

/--
  **Модельный four-corner** (равновесная симметричная эксклюзивная модель, вес `w`).
  Счёты: `N₀₀ = 1`, `N₀₃ = N₃₀ = C(n,3)·w³`, `N₃₃ = 20·C(n,6)·w⁶`. Тогда `N₀₀·N₃₃ ≤ N₀₃·N₃₀`.
-/
theorem model_four_corner (n w : ℕ) :
    1 * (20 * n.choose 6 * w ^ 6) ≤ (n.choose 3 * w ^ 3) * (n.choose 3 * w ^ 3) := by
  have key : 20 * n.choose 6 ≤ (n.choose 3) ^ 2 := four_corner_binom n
  calc 1 * (20 * n.choose 6 * w ^ 6) = (20 * n.choose 6) * w ^ 6 := by ring
    _ ≤ (n.choose 3) ^ 2 * w ^ 6 := by gcongr
    _ = (n.choose 3 * w ^ 3) * (n.choose 3 * w ^ 3) := by ring

end EuclidsPath
