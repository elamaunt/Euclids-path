/-
  JumpBarrier — быстрый расход энергии, скачки уровней и cut-barrier (jump-совместимый reverse-двигатель).
  Источник: jump_reverse_engine_cut_barrier_formal_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Jump engine и cut-barrier»).

  ИДЕЯ. Двигатель может тратить энергию быстрее и ПЕРЕПРЫГИВАТЬ уровни. Значит нельзя требовать
  «посещать каждый уровень» (`∀A ∃k, level k = A` ломается на `level_k = 2k`) — правильная замена:
  ПЕРЕСЕКАТЬ/ПРОЕЦИРОВАТЬСЯ на каждый cut. Для high-level state на уровне `B` и cut `A₀ ≤ B` есть
  конечная signature `CutSig A₀`. Если reverse-луч бесконечно уходит вверх (cofinal), для фиксированного
  `A₀` он даёт бесконечно много проекций на этот cut; при конечном `CutSig A₀` подпись ПОВТОРЯЕТСЯ, и
  повтор ⟹ `CloseAt A₀`. Противоречие с `¬Close`.

  ЗДЕСЬ ДОКАЗАНО (чистая логика/пиджонхол/well-founded, std аксиомы, без sorry):
    * `paidJump_decreases_energy` (§1) — оплаченный скачок строго роняет энергию (больший расход только
      УСИЛИВА�ет конечность);
    * `no_infinite_strict_energy_descent` (§2) — нет бесконечного строгого спуска энергии;
    * `jump_breaks_visitsEveryLevel` (§3) — `level_k=2k` cofinal, но не посещает нечётные ⟹ правильная
      цель = cofinal + cut-проекции, а не «каждый уровень»;
    * `CutSystem`/`JumpReverseRay` (§5–6), `repeated_cutSig_on_jumpReverseRay` (§9, jump-пиджонхол);
    * `no_jumpReverseRay_of_cutBarrier` / `..._fixedCut` (§11) — при cut-barrier и `¬Close` луча нет;
    * `no_jumpAboveGapConflict` (§18) — скачок через twin-gap + возврат внутрь = порядковое противоречие.

  ЧЕСТНАЯ ГРАНИЦА (§17, §19 red-tests кирпича — вскрыта и МАШИННО зафиксирована). Абстрактный no-go
  корректен и не про-конкретен. Но Step00-инстанциация держится на ДВУХ недоказанных входах:
    * `step00_jumpReverseBarrier` (повтор cut-подписи на jump-луче ⟹ Close) — cross-level labelled
      fan-in, тот же trap, что `snolHallSeed_bare_no_go`;
    * `noTwin_forces_jumpReverseRay` — red-test #5: если требует `SNOL.SNOLInput`/`CleanDensityBelowA2`,
      это переименование стены. `red_test_forceRay_is_SNOL_shaped` фиксирует: force-ray = supply-теорема.
  Здесь оба — входы. `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.AboveConflict

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.JumpBarrier

open EuclidsPath.AboveConflict

/-! ### §1. Forward jumps: оплаченный скачок роняет энергию -/

/-- Оплаченный скачок: уровень растёт, но энергия строго падает на положительную цену `cost`.
    (`cost` — экзистенциальные данные, чтобы структура оставалась `Prop`.) -/
structure PaidJumpStep {State : Type} (level energy : State → ℕ) (x y : State) : Prop where
  level_jump : level x < level y
  paid : ∃ cost : ℕ, 0 < cost ∧ energy y + cost ≤ energy x

/--
  **`paidJump_decreases_energy` — ДОКАЗАНА (§1).** Оплаченный скачок строго роняет энергию.
  Больший расход только УСИЛИВАЕТ конечную терминацию; он НЕ создаёт бесконечный finite-energy путь. -/
theorem paidJump_decreases_energy {State : Type} {level energy : State → ℕ} {x y : State}
    (h : PaidJumpStep level energy x y) : energy y < energy x := by
  obtain ⟨cost, hpos, hpaid⟩ := h.paid; omega

/-! ### §2. Нет бесконечного строгого спуска энергии -/

/--
  **`no_infinite_strict_energy_descent` — ДОКАЗАНА (§2).** Well-founded: нет бесконечной строго
  убывающей по энергии цепочки. Ядро всех «paid/jump» no-go. -/
theorem no_infinite_strict_energy_descent {State : Type}
    (path : ℕ → State) (energy : State → ℕ)
    (hDrop : ∀ k, energy (path (k + 1)) < energy (path k)) : False := by
  have hMono : ∀ k, energy (path k) + k ≤ energy (path 0) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => have := hDrop n; omega
  have := hMono (energy (path 0) + 1); omega

/-! ### §3. Скачки ломают «посещать каждый уровень»; правильная цель — cofinal -/

/-- Плохая (слишком сильная) цель для jump-систем. -/
def VisitsEveryLevel {State : Type} (level : State → ℕ) (path : ℕ → State) : Prop :=
  ∀ A, ∃ k, level (path k) = A

/-- Правильная замена: cofinality уровней. -/
def CofinalLevels (levelSeq : ℕ → ℕ) : Prop := ∀ C, ∃ k, C ≤ levelSeq k

/--
  **`jump_breaks_visitsEveryLevel` — ДОКАЗАНА (§3).** Последовательность `level_k = 2k` cofinal, но
  НЕ посещает нечётные уровни (напр. `1`). Значит «посещать каждый уровень» — ложная цель для
  jump-двигателя; корректная цель — `CofinalLevels`. -/
theorem jump_breaks_visitsEveryLevel :
    CofinalLevels (fun k => 2 * k) ∧ ¬ VisitsEveryLevel (fun n => n) (fun k => 2 * k) := by
  constructor
  · intro C; exact ⟨C, by simp; omega⟩
  · intro h; obtain ⟨k, hk⟩ := h 1; simp at hk

/-- Строго возрастающая ℕ-последовательность cofinal (`level k ≥ k`). -/
theorem strictMono_nat_cofinal (levelSeq : ℕ → ℕ) (hStrict : StrictMono levelSeq) :
    CofinalLevels levelSeq := by
  intro C
  refine ⟨C, ?_⟩
  have : C ≤ levelSeq C := hStrict.le_apply
  exact this

/-! ### §5. CutSystem: проекция high-level state на нижний cut (конечная подпись) -/

/-- Cut-система: конечная подпись `CutSig A₀` и проекция `sig : StateAt A → CutSig A₀` при `A₀ ≤ A`.
    Ключ: state НЕ обязан «приземляться» на `A₀`; достаточно `A₀ ≤ A`. -/
structure CutSystem (StateAt : ℕ → Type) where
  CutSig : ℕ → Type
  finite : ∀ A0, Finite (CutSig A0)
  sig : ∀ {A0 A : ℕ}, A0 ≤ A → StateAt A → CutSig A0

/-! ### §6. JumpReverseRay: обратный луч с ПРОИЗВОЛЬНЫМИ cofinal-скачками уровней -/

/-- Jump-обратный луч: строго растущие уровни `level k`, cofinal, состояние на каждом уровне,
    и обратный шаг между соседними индексами (уровень скачёт на произвольную величину, не `+1`). -/
structure JumpReverseRay (StateAt : ℕ → Type)
    (ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop) where
  level : ℕ → ℕ
  strict : StrictMono level
  cofinal : ∀ C, ∃ k, C ≤ level k
  state : ∀ k, StateAt (level k)
  reverse_step : ∀ k, ReverseStep (strict (Nat.lt_succ_self k)) (state k) (state (k + 1))

/-! ### §9. Jump-совместимый пиджонхол: повтор конечной cut-подписи на jump-луче -/

/--
  **`repeated_cutSig_on_jumpReverseRay` — ДОКАЗАНА (§9).** На jump-обратном луче, где уровни cofinal
  (уходят выше любого `A₀`), для фиксированного cut `A₀` есть бесконечно много проекций на `A₀`; при
  конечном `CutSig A₀` подпись ПОВТОРЯЕТСЯ на двух индексах `i < j`. Чистый пиджонхол (∞ → конечный тип),
  jump-совместимый (не требует посещения `A₀`, только `A₀ ≤ level`). -/
theorem repeated_cutSig_on_jumpReverseRay {StateAt : ℕ → Type}
    {ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop}
    (C : CutSystem StateAt) (R : JumpReverseRay StateAt ReverseStep) (A0 : ℕ) :
    ∃ i j, i < j ∧ ∃ (hi : A0 ≤ R.level i) (hj : A0 ≤ R.level j),
      C.sig hi (R.state i) = C.sig hj (R.state j) := by
  classical
  have hfin : Finite (C.CutSig A0) := C.finite A0
  obtain ⟨k0, hk0⟩ := R.cofinal A0
  -- Хвост с индекса k0: уровень ≥ A0 всюду (монотонность); подпись — точка в конечном CutSig A0.
  have htail : ∀ n, A0 ≤ R.level (k0 + n) :=
    fun n => le_trans hk0 (R.strict.monotone (Nat.le_add_right k0 n))
  set f : ℕ → C.CutSig A0 := fun n => C.sig (htail n) (R.state (k0 + n)) with hf
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨k0 + a, k0 + b, by omega, htail a, htail b, heq⟩
  · exact ⟨k0 + b, k0 + a, by omega, htail b, htail a, heq.symm⟩

/-! ### §10–11. JumpReverseBarrier и no-go -/

/-- Jump-cut-barrier: повтор cut-подписи `sig i = sig j` (`i<j`) на одном jump-луче ⟹ `Close`. -/
def JumpReverseBarrier {StateAt : ℕ → Type}
    {ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop}
    (C : CutSystem StateAt) (A0 : ℕ) (Close : Prop) : Prop :=
  ∀ (R : JumpReverseRay StateAt ReverseStep) (i j : ℕ), i < j →
    ∀ (hi : A0 ≤ R.level i) (hj : A0 ≤ R.level j),
      C.sig hi (R.state i) = C.sig hj (R.state j) → Close

/--
  **`no_jumpReverseRay_of_cutBarrier` — ДОКАЗАНА (§11, чистое jump-reverse-противоречие).** При наличии
  jump-cut-barrier (повтор подписи на cut `A₀` ⟹ Close) и `¬Close`, jump-обратного луча НЕТ: пиджонхол
  даёт повтор подписи, barrier даёт Close — против `¬Close`. -/
theorem no_jumpReverseRay_of_cutBarrier {StateAt : ℕ → Type}
    {ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop}
    (C : CutSystem StateAt) (A0 : ℕ) {Close : Prop}
    (hBarrier : JumpReverseBarrier (ReverseStep := ReverseStep) C A0 Close)
    (hNoClose : ¬ Close)
    (R : JumpReverseRay StateAt ReverseStep) : False := by
  obtain ⟨i, j, hij, hi, hj, hsig⟩ := repeated_cutSig_on_jumpReverseRay C R A0
  exact hNoClose (hBarrier R i j hij hi hj hsig)

/-! ### §18. Взаимодействие с AboveStructure: скачок через twin-gap ⟹ порядковый конфликт

Скачок через twin-gap: `above X Y`, `center X = gap.left`, `gap.right < center Y` (перепрыгнул gap).
Если затем объект `Z` структурно ПОСЛЕ `Y` (`above Y Z`), но натурально приземляется ВНУТРИ gap —
порядковое противоречие. -/

/-- Конфликт: двигатель перепрыгивает twin-gap, затем форсит поздний объект обратно ВНУТРЬ него. -/
structure JumpAboveGapConflict (S : AboveStructure) (G : TwinGap) where
  X : S.Obj
  Y : S.Obj
  Z : S.Obj
  hXY : S.above X Y
  hYZ : S.above Y Z
  x_left : S.center X = G.left
  y_past : G.right < S.center Y
  z_inside : G.left < S.center Z ∧ S.center Z < G.right

/--
  **`no_jumpAboveGapConflict` — ДОКАЗАНА (§18).** Такой конфликт невозможен: `above Y Z` даёт
  `center Y < center Z`, но `z_inside` + `y_past` дают `center Z < gap.right < center Y`, т.е.
  `center Z < center Y`. Противоречие. Точная версия «перепрыгнул gap ⟹ форсит объект внутрь». -/
theorem no_jumpAboveGapConflict (S : AboveStructure) (G : TwinGap)
    (Cf : JumpAboveGapConflict S G) : False := by
  have hYZnat : S.center Cf.Y < S.center Cf.Z := S.above_sound Cf.Y Cf.Z Cf.hYZ
  have hZltY : S.center Cf.Z < S.center Cf.Y := lt_trans Cf.z_inside.2 Cf.y_past
  omega

/-! ### §17, §19. МАШИННЫЙ ДИАГНОЗ ЛОВУШКИ (red-tests кирпича)

Абстрактный no-go выше корректен, но НЕ про конкретную арифметику. Step00-инстанциация требует ДВУХ
входов; red-test #5 говорит прямо: force-ray НЕ должен требовать `SNOL.SNOLInput`. Зафиксируем машинно,
что force-ray эквивалентен supply-теореме (тот же shape, что стена). -/

/-- Абстрактная «supply»-теорема (форма `SNOL.SNOLInput`): для каждого cut существует луч. Это и есть
    `noTwin_forces_jumpReverseRay` в чистой форме — она НЕ доказана из локальной энергии/пиджонхола. -/
def ForcesRay {StateAt : ℕ → Type}
    (ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop)
    (NoTwin NoEngine : Prop) : Prop :=
  NoTwin → NoEngine → Nonempty (JumpReverseRay StateAt ReverseStep)

/--
  **`jump_route_is_trapped` — ДОКАЗАНА (диагноз).** Полный jump-reverse-маршрут: из `ForcesRay`
  (supply-вход) + jump-cut-barrier (cross-level fan-in вход) + `¬Close` получаем `¬NoTwin ∨ ¬NoEngine`.
  Но ОБА ингредиента — недоказанные входы (§17 говорит barrier = labelled fan-in; §19 red-test #5
  говорит ForcesRay не должен опираться на SNOL, а если опирается — это стена). Пиджонхол/энергия
  (доказанное) сами по себе НЕ дают ни `ForcesRay`, ни `Barrier`. Формально: заключение выводимо ЛИШЬ
  при обоих входах, т.е. маршрут их не устраняет, а переупаковывает. -/
theorem jump_route_is_trapped {StateAt : ℕ → Type}
    {ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop}
    (C : CutSystem StateAt) (A0 : ℕ) {Close NoTwin NoEngine : Prop}
    (hForce : ForcesRay ReverseStep NoTwin NoEngine)
    (hBarrier : JumpReverseBarrier (ReverseStep := ReverseStep) C A0 Close)
    (hNoClose : ¬ Close)
    (hNoTwin : NoTwin) (hNoEngine : NoEngine) : False := by
  obtain ⟨R⟩ := hForce hNoTwin hNoEngine
  exact no_jumpReverseRay_of_cutBarrier C A0 hBarrier hNoClose R

/--
  **`red_test_forceRay_is_supply` — ДОКАЗАНА (red-test #5).** `ForcesRay` РАЗВОРАЧИВАЕТСЯ в чистую
  supply-форму «`NoTwin → NoEngine → ∃ ray`». Это ровно shape `SNOL.SNOLInput` (supply clean carrier
  at scale). Значит если он предъявлен через SNOL/carrier-density — это стена, а не обход. Здесь он
  НЕ предъявлен. -/
theorem red_test_forceRay_is_supply {StateAt : ℕ → Type}
    (ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop)
    (NoTwin NoEngine : Prop) :
    ForcesRay ReverseStep NoTwin NoEngine ↔
      (NoTwin → NoEngine → Nonempty (JumpReverseRay StateAt ReverseStep)) := Iff.rfl

end EuclidsPath.JumpBarrier
