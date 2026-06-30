/-
  Descent и «перенос двойки» (boundary-law).
  Проза: prose/18_Descent.md (после зелёного Lean).

  Идея автора: ветвь спуска «платит переносом двойки вперёд». Конкретно: при clean-descent
  сторона `6m−1 = a·U` теряет активный множитель `a>A`, остаётся `U = b·v` (b,v>A простые),
  и `U = 6m'+ε`. Противоположная сторона спущенного центра равна `U − 2ε` — это и есть
  «перенесённая двойка». Малый старый простой `p≤A` НЕ может делить `U` (его множители > A),
  поэтому единственное препятствие (выход из clean-core, boundary-exit ⊥) — делимость
  `p ∣ (U − 2ε)`. Невозможность бесконечного такого переноса — это EPMI (Engine/EPMI).

  Всё элементарно (делимость + кольцо). Запрещённого (анализ/распределение/сито) нет.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

/-- Противоположная сторона спущенного центра: `6m'−ε = U − 2ε`, если `U = 6m'+ε`. «Двойка вперёд». -/
theorem two_carry_opposite {m' U ε : ℤ} (hU : U = 6 * m' + ε) :
    6 * m' - ε = U - 2 * ε := by
  linear_combination -hU

/-- Малый простой `p ≤ A` не делит произведение двух простых, больших `A`. (`U = b·v`, `b,v>A`.) -/
theorem no_small_divisor {A b v p : ℕ} (hb : b.Prime) (hv : v.Prime)
    (hAb : A < b) (hAv : A < v) (hp : p.Prime) (hpA : p ≤ A) : ¬ p ∣ (b * v) := by
  intro hdvd
  rcases hp.dvd_mul.mp hdvd with h | h
  · have : p = b := (Nat.prime_dvd_prime_iff_eq hp hb).mp h
    omega
  · have : p = v := (Nat.prime_dvd_prime_iff_eq hp hv).mp h
    omega

/--
  **Boundary-law = перенос двойки.** Если `p` не делит сторону-произведение `U`, то любое
  препятствие на спущенном центре — это делимость противоположной стороны `U − 2ε`
  (= «перенесённая двойка»), а не дефект самой стороны-произведения.
-/
theorem obstruction_on_opposite {U twoε sideProd sideOpp p : ℤ}
    (hprod : sideProd = U) (_hopp : sideOpp = U - twoε) (hpU : ¬ p ∣ U) :
    (p ∣ sideProd ∨ p ∣ sideOpp) ↔ p ∣ sideOpp := by
  constructor
  · rintro (h | h)
    · rw [hprod] at h; exact absurd h hpU
    · exact h
  · intro h; exact Or.inr h

end EuclidsPath.Engine
