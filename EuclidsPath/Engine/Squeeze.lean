/-
  Самоподобие/сжатие. Проза: prose/20_Squeeze.md (после зелёного Lean).
  Источник: каталог §23 (кубическое сжатие повторного atom): h(1+6h) < A/12 ⟹ h < √(A/72).
  Берём честную целочисленную форму (без √): из 12(h+6h²) < A следует 72h² < A.
  Элементарно (линейная арифметика над атомом h²).
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

/-- **Кубическое сжатие.** `12·(h + 6h²) < A ⟹ 72h² < A` (равносильно `h < √(A/72)`). -/
theorem cubic_squeeze {A h : ℕ} (hsq : 12 * (h + 6 * h ^ 2) < A) : 72 * h ^ 2 < A := by
  omega

/-- Следствие: повтор atom крайне короток — `h² < A` (тем более `h < A`). -/
theorem cubic_squeeze_sq_lt {A h : ℕ} (hsq : 12 * (h + 6 * h ^ 2) < A) : h ^ 2 < A := by
  have := cubic_squeeze hsq; omega

end EuclidsPath.Engine
