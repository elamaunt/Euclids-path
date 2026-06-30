/-
  Вечный двигатель Евклида — формальная НЕВОЗМОЖНОСТЬ (EPMI).

  Этот файл САМОДОСТАТОЧЕН: использует только ядро Lean 4 (без mathlib),
  поэтому проверяется компилятором быстро командой:

      lean EuclidsPath/Engine/EPMI.lean

  Проза: prose/06_EuclideanPerpetualEngine.md, prose/16_MultiRankFanCycle.md
  Источник идей: euclidean_perpetual_engine_…29 (Опр. 11.1, Теор. 10.3);
                 BE_UPDATED §73–77 (Теор. 77.1);
                 twin_prime_new_layers_after_BE_update_… §IV, §XI.

  Содержательная суть: «состояние» двигателя сводится к его высоте — натуральному
  индексу центра m. Один успешный clean-descent строго уменьшает высоту в ≥ A раз
  (A·m' < m). Бесконечная цепочка таких спусков невозможна, потому что
  H(S_t) < H(S_0)/Aᵗ < 1 для больших t, а высота — положительное целое.
  Это и есть «нет вечного двигателя Евклида» = бесконечный спуск Ферма.

  (Используем `Nat`, а не нотацию `ℕ`: в prelude без mathlib `ℕ` не подключена.)
-/
set_option autoImplicit false

namespace EuclidsPath.Engine

/-- Один успешный clean-descent: новая высота `h'` в ≥ `A` раз меньше старой `h`. -/
def DescentStep (A h h' : Nat) : Prop := A * h' < h

/-- При `A ≥ 1` шаг descent строго уменьшает высоту: `A·h' < h ⇒ h' < h`. -/
theorem descent_strict {A h h' : Nat} (hA : 1 ≤ A) (hstep : DescentStep A h h') :
    h' < h := by
  have h1 : h' ≤ A * h' := Nat.le_mul_of_pos_left h' hA
  unfold DescentStep at hstep
  omega

/--
  **EPMI (downward), абстрактная форма.**
  Не существует бесконечной последовательности высот `H : Nat → Nat`, каждый шаг которой —
  успешный `A`-спуск (`A ≥ 1`). Т.е. вечный двигатель как бесконечная clean descent chain
  невозможен.
-/
theorem no_infinite_descent {A : Nat} (hA : 1 ≤ A)
    (H : Nat → Nat) (hchain : ∀ t, DescentStep A (H t) (H (t + 1))) : False := by
  -- для каждого шага: H (t+1) ≤ A * H (t+1)
  have hle : ∀ t, H (t + 1) ≤ A * H (t + 1) := fun t => Nat.le_mul_of_pos_left _ hA
  -- величина H t + t не возрастает, значит ограничена H 0
  have hbound : ∀ t, H t + t ≤ H 0 := by
    intro t
    induction t with
    | zero => omega
    | succ n ih =>
      have hc := hchain n
      unfold DescentStep at hc            -- A * H (n+1) < H n
      have hl := hle n                     -- H (n+1) ≤ A * H (n+1)
      omega
  -- при t = H 0 + 1 получаем H(...) + (H 0 + 1) ≤ H 0 — противоречие
  have hbad := hbound (H 0 + 1)
  omega

/-! ### Структурная форма: состояние, descent-оператор, boundary-exit -/

/-- Состояние двигателя. Содержательно — центр `m` пары `(6m-1, 6m+1)`; высота = `m`. -/
structure State where
  height : Nat

/--
  Результат частичного clean descent оператора `D_a`:
  * `clean s'` — успешный спуск в clean-состояние строго меньшей высоты (`A·s'.height < s.height`);
  * `boundary` — поглощающий выход `⊥` (descended center вышел из clean-core).
-/
inductive Step (A : Nat) (s : State) where
  | clean (s' : State) (h : A * s'.height < s.height)
  | boundary

/--
  **EPMI (structured).** Нет бесконечной траектории `run : Nat → State`, в которой каждый шаг —
  именно успешный `clean` спуск. (Boundary-exit обрывает ветвь; см. `Step.boundary`.)
-/
theorem no_perpetual_engine {A : Nat} (hA : 1 ≤ A)
    (run : Nat → State)
    (clean_step : ∀ t, A * (run (t + 1)).height < (run t).height) : False :=
  no_infinite_descent hA (fun t => (run t).height) (fun t => clean_step t)

/--
  Boundary leaf поглощающий: любой шаг — это либо успешный `clean`, либо `boundary`.
  Содержательно это типовая фиксация дихотомии «descended center либо остаётся clean,
  либо выходит на границу `⊥`» (Лемма 74.1 / §4.2). Из `boundary` нет clean-продолжения
  той же ветви — оно потребовало бы успешного `clean`-шага, которым `boundary` не является.
-/
theorem boundary_dichotomy {A : Nat} {s : State} (st : Step A s) :
    (∃ s' h, st = Step.clean s' h) ∨ st = Step.boundary := by
  cases st with
  | clean s' h => exact Or.inl ⟨s', h, rfl⟩
  | boundary => exact Or.inr rfl

end EuclidsPath.Engine
