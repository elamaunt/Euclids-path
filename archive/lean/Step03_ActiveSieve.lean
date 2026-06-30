/-
  Шаг 03 — Активное просеивание до корня.   Проза: prose/03_ActiveSieve.md
  Ключ: m выживает до уровня √(6m+1) ⇒ оба 6m±1 простые (Лемма 4.2);
        Active Twin Hit (Теор. 3.1): не-близнец ⇔ попадание в активную прогрессию 𝓗_q^±.
  Статус: 🟢 строго (ситовой критерий простоты через делители до корня).

  TODO: формализовать survivor-множество 𝓢_z и переход survivor → twin.
    def Survivor (z m : ℕ) : Prop := ∀ q ≤ z, q.Prime → ¬ forbiddenByClock q m
    theorem survivor_root_twin {m : ℕ} (h : Survivor (Nat.sqrt (6*m+1)) m) : IsTwinCenter m -- → sorry
-/
import EuclidsPath.Step02_CRTForbiddenClasses

namespace EuclidsPath

-- (заготовка) определения и леммы шага 03 будут здесь.

end EuclidsPath
