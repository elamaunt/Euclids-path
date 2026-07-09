/-
  Шаг 02 — CRT-запрещённые классы.   Проза: prose/02_CRTForbiddenClasses.md
  Ключ: для простого q ≥ 5:  q ∣ (6m-1)(6m+1)  ↔  m ≡ 6⁻¹ ∨ m ≡ -6⁻¹  (mod q).
  Статус: 🟢 строго (модулярная арифметика + CRT).

  TODO: формализовать Лемму 2.1 (один clock запрещает два класса) и Лемму 2.2 (finite CRT survivor).
  Намеченная сигнатура:
    def forbiddenByClock (q m : ℕ) : Prop := q ∣ (6*m - 1) ∨ q ∣ (6*m + 1)
    theorem clock_forbids_two_classes {q : ℕ} (hq : q.Prime) (h : 5 ≤ q) ... -- → sorry (пока не формализовано)
-/
import EuclidsPath.Step01_CenterReduction

namespace EuclidsPath

-- (заготовка) определения и леммы шага 02 будут здесь.

end EuclidsPath
