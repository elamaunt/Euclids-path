/-
  Шаг 06 — ВЕЧНЫЙ ДВИГАТЕЛЬ ЕВКЛИДА (ключевой объект).   Проза: prose/06_EuclideanPerpetualEngine.md
  Ключ:
    * звено цепи: XᵢYᵢ - ZᵢWᵢ = 2 (самоподобие);
    * гармоническая высота H(C,D) = C*D/(C+D); нетривиальный ход строго меняет H;
    * clean descent: m' < m/A;  boundary-exit: m' выходит из clean-core ⇔ ∃ p≤A, p ∣ bv-2ε;
    * Теор. 77.1: бесконечной цепочки clean-descents нет (H(S_t) < H(S₀)/Aᵗ < 1).
  Статус: 🟢 локальная невозможность (монотонность высоты);  🔴 глобальный non-cover (BDNC⁺, Step15).

  Намеченная формализация локальной невозможности (строго доказуемо как well-foundedness спуска):
    -- если строго убывающая последовательность натуральных «высот», то она конечна.
    theorem no_infinite_clean_descent
        (H : ℕ → ℕ) (A : ℕ) (hA : 2 ≤ A)
        (hstep : ∀ t, A * H (t+1) < H t) : ∃ t, H t = 0 := by sorry  -- TODO: well-founded/strong induction
  NB: глобальная версия (покрытие всей clean-root mass absorbing-листьями) — ОТКРЫТО, см. Step15.
-/
import EuclidsPath.Step05_DeterminantLaw

namespace EuclidsPath

-- (заготовка) гармоническая высота, descent-оператор, boundary-exit и теорема невозможности.

end EuclidsPath
