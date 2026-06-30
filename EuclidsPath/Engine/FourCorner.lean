/-
  Симметрийный переход: four-corner ⟹ N₃₃ < N₀₀ (алгебра).
  Проза: prose/19_FourCorner.md (после зелёного Lean).

  Контекст (intuition «дело в симметрии»): в CRT-модели four-corner-неравенство
      N₀₀·N₃₃ ≤ N₀₃·N₃₀
  доказано через неравенство Маклорена на элементарных симметрических многочленах
  (R_CRT = 20·e₆/e₃² ≤ 20·C(s,6)/C(s,3)² < 1). Это чисто СИММЕТРИЙНЫЙ факт.
  Вместе с side-corner `N₀₃·N₃₀ ≤ N₀₀²` оно даёт `N₃₃ ≤ N₀₀` (строгое — `N₃₃ < N₀₀`, т.е. B₅>0).

  Здесь формализована АЛГЕБРА перехода (элементарно). Сами two inequality для РЕАЛЬНЫХ счётов
  остаются открытыми (модель→реальность — место проблемы чётности; см. prose/19). ± симметрия
  сторон даёт `N₀₃ = N₃₀`, упрощая side-corner до `N₀₃ ≤ N₀₀`.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/--
  **Четырёхугольный переход (нестрогий).** Если `N₀₀ > 0`, four-corner `N₀₀·N₃₃ ≤ N₀₃·N₃₀`
  и side-corner `N₀₃·N₃₀ ≤ N₀₀²`, то `N₃₃ ≤ N₀₀`.
-/
theorem N33_le_N00_of_four_corner {N00 N03 N30 N33 : ℕ} (hpos : 0 < N00)
    (hfc : N00 * N33 ≤ N03 * N30) (hsc : N03 * N30 ≤ N00 * N00) : N33 ≤ N00 := by
  have h : N00 * N33 ≤ N00 * N00 := le_trans hfc hsc
  exact Nat.le_of_mul_le_mul_left h hpos

/--
  **Четырёхугольный переход (строгий) ⟹ B₅ > 0.** Если `N₀₀ > 0`, строгое four-corner
  `N₀₀·N₃₃ < N₀₃·N₃₀` и side-corner `N₀₃·N₃₀ ≤ N₀₀²`, то `N₃₃ < N₀₀`.
-/
theorem N33_lt_N00_of_four_corner {N00 N03 N30 N33 : ℕ} (_hpos : 0 < N00)
    (hfc : N00 * N33 < N03 * N30) (hsc : N03 * N30 ≤ N00 * N00) : N33 < N00 := by
  have h : N00 * N33 < N00 * N00 := lt_of_lt_of_le hfc hsc
  exact lt_of_mul_lt_mul_left h (Nat.zero_le N00)

/--
  **± симметрия упрощает side-corner.** При `N₀₃ = N₃₀` достаточно `N₀₃ ≤ N₀₀`, чтобы получить
  side-corner `N₀₃·N₃₀ ≤ N₀₀²`.
-/
theorem side_corner_of_le {N00 N03 N30 : ℕ} (hsymm : N03 = N30) (h : N03 ≤ N00) :
    N03 * N30 ≤ N00 * N00 := by
  subst hsymm; exact Nat.mul_le_mul h h

end EuclidsPath
