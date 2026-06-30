/-
  «Куда бы ни поехал двигатель — не повернёт назад и всегда остановится.»
  Проза: prose/24_Irreversibility.md.

  Это 2-й закон термодинамики для двигателя Евклида, и он машинно доказан здесь и в соседних модулях:
    * «не повернёт назад» (на одном шаге):  `descent_strict` — высота строго убывает;
    * «никогда не вернётся» (глобально):      `engine_never_returns` — высота строго антимонотонна,
      двигатель не возвращается ни в одно более раннее (более высокое) состояние;
    * «не повернёт назад на двух точках»:      `NoBackward.exclusive_no_backward` — self-член исчезает;
    * «всегда остановится»:                    `no_infinite_descent` / `no_perpetual_engine` — бесконечной
      цепочки нет (`H(S_t) < H(S_0)/Aᵗ < 1`).

  Здесь — объединяющий капстоун. Без анализа/распределения/сита.
-/
import Mathlib
import EuclidsPath.Engine.EPMI

set_option autoImplicit false

namespace EuclidsPath.Engine

/--
  **«Не повернёт назад» (глобально).** Если каждый шаг — успешный `A`-спуск (`A ≥ 1`), то высота
  СТРОГО АНТИМОНОТОННА: `s < t ⟹ H t < H s`. Двигатель никогда не возвращается в более раннее
  (более высокое) состояние — необратимость.
-/
theorem engine_never_returns {A : ℕ} (hA : 1 ≤ A) (H : ℕ → ℕ)
    (hchain : ∀ t, DescentStep A (H t) (H (t + 1))) : StrictAnti H :=
  strictAnti_nat_of_succ_lt (fun n => descent_strict hA (hchain n))

/-
  «Всегда остановится» — это `no_infinite_descent` (Engine/EPMI): бесконечной `A`-спуск-цепочки
  не существует. Вместе с `engine_never_returns` («не повернёт назад») это и есть весь 2-й закон:
  куда бы двигатель ни поехал, он не повернёт назад и всегда остановится.
-/

/-! ### Направленная асимметрия: «+1 — топливо», двигатель едет бесконечно только вверх -/

/--
  **Вниз — конечно.** В `ℕ` нет бесконечно убывающей цепи: любой строго убывающий `f : ℕ → ℕ`
  даёт противоречие (порядковая полнота ℕ = EPMI при `A=1`). Двигатель не может ехать вниз вечно.
-/
theorem no_infinite_engine_descent (f : ℕ → ℕ) (hf : StrictAnti f) : False :=
  no_infinite_descent (le_refl 1) f
    (fun t => by simp only [DescentStep, one_mul]; exact hf (Nat.lt_succ_self t))

/--
  **Вверх — бесконечно («+1 = топливо»).** Successor даёт строго возрастающую цепь: топлива
  (бо́льших центров) всегда хватает, двигатель едет вверх без остановки.
  Вместе с `no_infinite_engine_descent`: двигатель едет бесконечно ТОЛЬКО в одном направлении (вверх).
-/
theorem fuel_ascent_strictMono : StrictMono (fun n : ℕ => n + 1) :=
  fun _ _ h => Nat.add_lt_add_right h 1

/--
  **«Свернёт — остановится» (точная оценка).** Если двигатель свернул в спуск и сделал `k` строгих
  шагов вниз (`H(t+1) < H(t)` для `t < k`), то `k ≤ H 0`: он точно остановится, и не более чем за
  `H 0` шагов. Любой поворот вниз — это конечный путь (порядковая полнота ℕ).
-/
theorem turned_engine_halts (H : ℕ → ℕ) (k : ℕ)
    (hdesc : ∀ t, t < k → H (t + 1) < H t) : k ≤ H 0 := by
  have hbound : ∀ t, t ≤ k → H t + t ≤ H 0 := by
    intro t ht
    induction t with
    | zero => simp
    | succ n ih =>
      have hn : H (n + 1) < H n := hdesc n (by omega)
      have := ih (by omega)
      omega
  have := hbound k (le_refl k)
  omega

end EuclidsPath.Engine
