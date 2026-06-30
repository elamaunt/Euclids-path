/-
  Ацикличность (rigidity повторов). Проза: prose/21_Cycle.md (после зелёного Lean).
  Источник: каталог §31/§58 (fuel-law / factor-repeat rigidity): большой множитель на линейном
  train не может повторяться чаще, чем позволяет шаг. Это запрещает «бесконечный повтор» и вместе
  с EPMI даёт ацикличность descent-леса.
  Элементарно (делимость + взаимная простота).
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

/--
  **Factor-repeat rigidity.** Если `ℓ` делит `N₀ + q·n₁` и `N₀ + q·n₂` на линейном train, и
  `(ℓ, q) = 1`, то `ℓ ∣ (n₂ − n₁)`. Большой делитель «привязывает» повтор к шагу — повторов мало.
-/
theorem factor_repeat_rigidity {ℓ q N0 n1 n2 : ℤ}
    (h1 : ℓ ∣ N0 + q * n1) (h2 : ℓ ∣ N0 + q * n2) (hcop : IsCoprime ℓ q) :
    ℓ ∣ (n2 - n1) := by
  have hd : ℓ ∣ q * (n2 - n1) := by
    have hsub := dvd_sub h2 h1
    have e : (N0 + q * n2) - (N0 + q * n1) = q * (n2 - n1) := by ring
    rwa [e] at hsub
  exact hcop.dvd_of_dvd_mul_left hd

/--
  **Fuel-law (перенос двойки между сторонами).** Если `p ∣ B_α` и `p ∣ R_β` на противоположных
  сторонах звёздного прямоугольника (`a·B_α = …`, см. det-форму), то `p ∣ 2 + a·q·(β − α)`.
  Здесь — чистая делимостная форма: из `p ∣ aα + c` и `p ∣ aβ + c − 2` следует `p ∣ a(β−α) − 2`.
-/
theorem cross_side_fuel {p a c α β : ℤ}
    (h1 : p ∣ a * α + c) (h2 : p ∣ a * β + c - 2) :
    p ∣ (a * (β - α) - 2) := by
  have hsub := dvd_sub h2 h1
  have e : (a * β + c - 2) - (a * α + c) = a * (β - α) - 2 := by ring
  rwa [e] at hsub

end EuclidsPath.Engine
