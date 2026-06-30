/-
  «Двигатель не работает назад на двух точках»: точный факт об эксклюзивности.
  Проза: prose/23_NoBackward.md.

  Численная разведка (tools/RESULTS_rank2.md): матрица счётов `N_ij ≈ ранг-1` (независимость
  `r₋ ⊥ r₊`), а four-corner = знак ранг-2 поправки, РОБАСТНО отрицательный на всех масштабах,
  потому что `Cov(r₋,r₊) < 0` всюду. Источник этого знака — ТОЧНАЯ эксклюзивность: простой делит
  не более одной стороны (`Carrier.no_large_shared_divisor`, `shared gcd ∣ 2`).

  Здесь зафиксирован точный механизм: при эксклюзивности `X_p·Y_p = 0` диагональ (тот же простой на
  обеих сторонах = «движение назад на одной точке») ИСЧЕЗАЕТ, и произведение `(Σ X)(Σ Y)` целиком
  внедиагонально. Это и есть «двигатель не работает назад на двух точках»: нет self-перехода 2→2.

  Всё — конечные суммы (Finset). Без анализа/распределения/сита.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/-- **Диагональ исчезает (эксклюзивность).** Если на каждом простом `X_p·Y_p = 0` (делит ≤ 1 стороны),
    то сумма «self»-членов `Σ_p X_p·Y_p = 0` — нет движения назад на одной точке. -/
theorem exclusive_diag_zero {ι : Type*} (s : Finset ι) (X Y : ι → ℕ)
    (hexcl : ∀ i ∈ s, X i * Y i = 0) :
    ∑ i ∈ s, X i * Y i = 0 :=
  Finset.sum_eq_zero hexcl

/--
  **Двигатель не работает назад на двух точках.** При эксклюзивности `X_p·Y_p = 0` произведение
  рангов `(Σ_p X_p)·(Σ_q Y_q)` целиком ВНЕДИАГОНАЛЬНО:
  `(Σ X)·(Σ Y) = Σ_i Σ_{j≠i} X_i·Y_j`. Диагональный (self-) член отсутствует.
  Это точный источник отрицательной ассоциации `(r₋,r₊)` (численно `Cov < 0` всюду).
-/
theorem exclusive_no_backward {ι : Type*} [DecidableEq ι] (s : Finset ι) (X Y : ι → ℕ)
    (hexcl : ∀ i ∈ s, X i * Y i = 0) :
    (∑ i ∈ s, X i) * (∑ j ∈ s, Y j) = ∑ i ∈ s, ∑ j ∈ s.erase i, X i * Y j := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum, ← Finset.add_sum_erase s (fun j => X i * Y j) hi, hexcl i hi, zero_add]

end EuclidsPath
