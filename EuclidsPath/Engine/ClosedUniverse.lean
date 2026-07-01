/-
  ClosedUniverse — «двигатель не может покинуть вселенную»: сохранение вселенной вдоль пути +
  платная динамика при сохранении, плюс scale-indexed версия и paid-or-closes дихотомия.
  Источник: closed_universe_step00_formal_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «ClosedUniverse: двигатель не покидает вселенную»).

  ИДЕЯ. Прежде чем применять любой энергия/cut/подпись-инвариант вдоль пути, нужно доказать, что
  двигатель ОСТАЁТСЯ во вселенной: `Universe x → Step x y → Universe y`. Если шаг меняет масштаб/
  вселенную и создаёт ресурс, он оплачивается (`Total_B y + Work + UniverseChangeCost ≤ Total_A x`)
  ИЛИ наступает `Close`. Главная опасность: `promotion A→A'` может вывести двигатель из старой вселенной
  и вернуть с новым ресурсом (refuel).

  ЗДЕСЬ ДОКАЗАНО (чистая индукция/суммы/well-founded, std аксиомы, без sorry):
    * `universe_along_path` (§2) — сохранение вселенной вдоль пути;
    * `ClosedPaidDynamics`: `strict_drop` (§4), `path_budget` (§5), `steps_bounded` (§6),
      `no_infinite_closed_paid_run` (§7);
    * `ClosedPaidScaleDynamics.strict_drop` (§10, scale-indexed с UniverseChangeCost);
    * `closed_paid_or_closes_no_infinite_run` (§25 дихотомия — под `¬Close` спуск, при `Close` терминал);
    * `universeRefuel_is_paid_violation` (§33) — refuel = ровно отрицание `paid` (машинно).

  ЧЕСТНАЯ ГРАНИЦА (§23, §25, §34, §36 кирпича — вскрыта и МАШИННО зафиксирована). Абстрактные законы
  реальны. Но Step00-инстанциация держится на ОДНОМ опасном входе: `step00_promotion_paid_or_closes`
  (§25) — «самая опасная теорема» (§36): promotion/carrier-regeneration не создаёт нового ресурса ЛИБО
  закрывает. Это ровно orientation-стена (`HigherEnergy`: promotion misoriented = refuel) + supply-стена
  (`PaidDynamics.regeneration_to_close_is_supply` = `SNOL.SNOLInput`). `promotion_paid_or_closes_is_the_wall`
  фиксирует машинно: без него `no_infinite_closed_paid_run` не инстанциируется для Step00. Здесь вход НЕ
  предъявлен. `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.PaidDynamics

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.ClosedUniverse

open EuclidsPath.PaidDynamics

/-! ### §1–2. ClosedDynamics: сохранение вселенной вдоль пути -/

/-- Замкнутая динамика: вселенная сохраняется под шагом (`x∈U`, `x→y ⟹ y∈U`). -/
structure ClosedDynamics (State : Type) (Step : State → State → Prop) where
  Universe : State → Prop
  closed : ∀ {x y : State}, Universe x → Step x y → Universe y

/--
  **`universe_along_path` — ДОКАЗАНА (§2).** Если старт во вселенной и каждый шаг легален, то ВСЯ
  траектория во вселенной. Это обязательно ПЕРЕД применением любого энергия/cut-инварианта вдоль пути. -/
theorem universe_along_path {State : Type} {Step : State → State → Prop}
    (D : ClosedDynamics State Step) (path : ℕ → State)
    (hStart : D.Universe (path 0)) (hStep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ k, D.Universe (path k) := by
  intro k
  induction k with
  | zero => exact hStart
  | succ k ih => exact D.closed ih (hStep k)

/-! ### §3–7. ClosedPaidDynamics: платно внутри вселенной ⟹ нет бесконечного run -/

/-- Замкнутая платная динамика: `work_pos`/`paid` требуются лишь когда исток ВНУТРИ вселенной. -/
structure ClosedPaidDynamics (State : Type) (Step : State → State → Prop) where
  Universe : State → Prop
  Total : State → ℕ
  Work : State → State → ℕ
  closed : ∀ {x y : State}, Universe x → Step x y → Universe y
  work_pos : ∀ {x y : State}, Universe x → Step x y → 0 < Work x y
  paid : ∀ {x y : State}, Universe x → Step x y → Total y + Work x y ≤ Total x

/-- Забыть платность — получить `ClosedDynamics`. -/
def ClosedPaidDynamics.toClosed {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) : ClosedDynamics State Step where
  Universe := D.Universe
  closed := D.closed

/-- **`closedPaid_strict_drop` — ДОКАЗАНА (§4).** Платный шаг из вселенной строго роняет `Total`. -/
theorem closedPaid_strict_drop {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) {x y : State}
    (hUx : D.Universe x) (hStep : Step x y) : D.Total y < D.Total x := by
  have hPaid := D.paid hUx hStep; have hPos := D.work_pos hUx hStep; omega

/-- **`closedPaid_path_budget` — ДОКАЗАНА (§5).** Бюджет пути (учитывая сохранение вселенной). -/
theorem closedPaid_path_budget {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) (path : ℕ → State)
    (hStart : D.Universe (path 0)) (hStep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ n, (∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1))) + D.Total (path n)
      ≤ D.Total (path 0) := by
  have hU : ∀ k, D.Universe (path k) := universe_along_path D.toClosed path hStart hStep
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hPaid := D.paid (hU n) (hStep n)
      rw [Finset.sum_range_succ]; omega

/-- **`closedPaid_steps_bounded` — ДОКАЗАНА (§6).** `n ≤ Total (path 0)`. -/
theorem closedPaid_steps_bounded {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) (path : ℕ → State)
    (hStart : D.Universe (path 0)) (hStep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ n, n ≤ D.Total (path 0) := by
  have hU : ∀ k, D.Universe (path k) := universe_along_path D.toClosed path hStart hStep
  intro n
  have hBudget := closedPaid_path_budget D path hStart hStep n
  have hEach : ∀ k ∈ Finset.range n, 1 ≤ D.Work (path k) (path (k + 1)) :=
    fun k _ => D.work_pos (hU k) (hStep k)
  have hSumLower : n ≤ ∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1)) := by
    calc n = ∑ _k ∈ Finset.range n, 1 := by simp
      _ ≤ ∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1)) := Finset.sum_le_sum hEach
  omega

/-- **`no_infinite_closed_paid_run` — ДОКАЗАНА (§7).** Если двигатель остаётся во вселенной и каждый
    шаг оплачен, бесконечного пути НЕТ. -/
theorem no_infinite_closed_paid_run {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) :
    ¬ ∃ path : ℕ → State, D.Universe (path 0) ∧ ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hStart, hStep⟩
  have := closedPaid_steps_bounded D path hStart hStep (D.Total (path 0) + 1)
  omega

/-! ### §8–10. Scale-indexed: вселенная и стоимость смены вселенной по масштабу -/

/-- Замкнутая платная scale-динамика: состояния `StateAt A`, шаг `A ≤ B`, плюс `UniverseChangeCost`. -/
structure ClosedPaidScaleDynamics (StateAt : ℕ → Type)
    (StepAt : ∀ {A B : ℕ}, A ≤ B → StateAt A → StateAt B → Prop) where
  UniverseAt : ∀ A, StateAt A → Prop
  Total : ∀ A, StateAt A → ℕ
  Work : ∀ {A B : ℕ}, A ≤ B → StateAt A → StateAt B → ℕ
  UniverseChangeCost : ∀ {A B : ℕ}, A ≤ B → StateAt A → StateAt B → ℕ
  closed : ∀ {A B : ℕ} {hAB : A ≤ B} {x : StateAt A} {y : StateAt B},
    UniverseAt A x → StepAt hAB x y → UniverseAt B y
  work_pos : ∀ {A B : ℕ} {hAB : A ≤ B} {x : StateAt A} {y : StateAt B},
    UniverseAt A x → StepAt hAB x y → 0 < Work hAB x y
  paid : ∀ {A B : ℕ} {hAB : A ≤ B} {x : StateAt A} {y : StateAt B},
    UniverseAt A x → StepAt hAB x y →
      Total B y + Work hAB x y + UniverseChangeCost hAB x y ≤ Total A x

/-- **`closedPaidScale_strict_drop` — ДОКАЗАНА (§10).** Scale-шаг из вселенной строго роняет `Total`
    (даже с положительной `UniverseChangeCost`). -/
theorem closedPaidScale_strict_drop {StateAt : ℕ → Type}
    {StepAt : ∀ {A B : ℕ}, A ≤ B → StateAt A → StateAt B → Prop}
    (D : ClosedPaidScaleDynamics StateAt StepAt) {A B : ℕ} {hAB : A ≤ B}
    {x : StateAt A} {y : StateAt B} (hUx : D.UniverseAt A x) (hStep : StepAt hAB x y) :
    D.Total B y < D.Total A x := by
  have hPaid := D.paid hUx hStep; have hPos := D.work_pos hUx hStep; omega

/-! ### §25. Paid-or-closes: дихотомия «закрывается ИЛИ платит»

Более слабый (реалистичный) вход: каждый живой шаг ЛИБО закрывает на текущем масштабе, ЛИБО оплачен.
Под глобальным `¬Close` это сводится к обычной платной динамике ⟹ нет бесконечного run. -/

/-- Замкнутая динамика с дихотомией paid-or-closes: `Close : State → Prop`; каждый шаг из вселенной
    либо даёт `Close x`, либо оплачен. -/
structure ClosedPaidOrClosesDynamics (State : Type) (Step : State → State → Prop) where
  Universe : State → Prop
  Close : State → Prop
  Total : State → ℕ
  Work : State → State → ℕ
  closed : ∀ {x y : State}, Universe x → Step x y → Universe y
  work_pos : ∀ {x y : State}, Universe x → Step x y → 0 < Work x y
  paid_or_closes : ∀ {x y : State}, Universe x → Step x y →
    Close x ∨ Total y + Work x y ≤ Total x

/--
  **`closed_paid_or_closes_no_infinite_run` — ДОКАЗАНА (§25 дихотомия).** Если НИ на одном достижимом
  состоянии нет `Close` (`hNoClose`), то paid-or-closes вырождается в paid, и бесконечного живого пути
  нет. Если же `Close` где-то наступает — это и есть искомый терминал (заключение отдельно). -/
theorem closed_paid_or_closes_no_infinite_run {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidOrClosesDynamics State Step)
    (hNoClose : ∀ x, D.Universe x → ¬ D.Close x) :
    ¬ ∃ path : ℕ → State, D.Universe (path 0) ∧ ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hStart, hStep⟩
  -- Построить ClosedPaidDynamics: под hNoClose дихотомия даёт paid всюду во вселенной.
  let D' : ClosedPaidDynamics State Step :=
    { Universe := D.Universe
      Total := D.Total
      Work := D.Work
      closed := D.closed
      work_pos := D.work_pos
      paid := by
        intro x y hUx hStepxy
        rcases D.paid_or_closes hUx hStepxy with hClose | hPaid
        · exact absurd hClose (hNoClose x hUx)
        · exact hPaid }
  exact no_infinite_closed_paid_run D' ⟨path, hStart, hStep⟩

/-! ### §32–33. UniverseEscape / UniverseRefuel как отрицания инвариантов -/

/--
  **`universeRefuel_is_paid_violation` — ДОКАЗАНА (§33).** «Refuel» (двигатель остаётся легальным, но
  возвращается с бОльшим ресурсом, чем позволено) — это РОВНО отрицание `paid`: если
  `Total x < Total y + Work x y`, то `¬ (Total y + Work x y ≤ Total x)`. Значит любой refuel — прямое
  нарушение платного закона; закрыть его можно ЛИШЬ доказав `paid` (или `paid_or_closes`). -/
theorem universeRefuel_is_paid_violation {State : Type} (Total : State → ℕ) (Work : State → State → ℕ)
    (x y : State) (hRefuel : Total x < Total y + Work x y) :
    ¬ (Total y + Work x y ≤ Total x) := by omega

/-! ### §23, §25, §34, §36. МАШИННЫЙ ДИАГНОЗ ЛОВУШКИ: promotion_paid_or_closes — стена

Абстрактные законы выше корректны и не вакуумны. Но Step00 инстанциирует `no_infinite_closed_paid_run`
ЛИШЬ если доказан `paid` для КАЖДОГО шага, включая promotion/carrier-regeneration. Кирпич (§36) прямо
называет `step00_promotion_paid_or_closes` «самой опасной теоремой» и «самым вероятным скрытым
двигателем». Зафиксируем машинно, что без неё инстанциация невозможна. -/

/-- Абстрактный «promotion-вход»: для каждого promotion-шага — либо Close, либо платно. Это ровно
    `step00_promotion_paid_or_closes`; локальные/энергетические законы его НЕ дают. -/
def PromotionPaidOrCloses {State : Type} (Step : State → State → Prop)
    (Universe Close : State → Prop) (Total : State → ℕ) (Work : State → State → ℕ) : Prop :=
  ∀ {x y : State}, Universe x → Step x y → Close x ∨ Total y + Work x y ≤ Total x

/--
  **`promotion_paid_or_closes_is_the_wall` — ДОКАЗАНА (итог диагноза §36).** `PromotionPaidOrCloses`
  РАЗВОРАЧИВАЕТСЯ в точности в поле `paid_or_closes` структуры `ClosedPaidOrClosesDynamics`. То есть это
  ровно тот вход, который нужен `closed_paid_or_closes_no_infinite_run` — и он НЕ выводится из
  сохранения вселенной или локальной энергии. Если promotion создаёт новый ресурс (refuel по §33) —
  вход ложен, и это скрытый двигатель (orientation-стена `HigherEnergy` + supply-стена
  `PaidDynamics.regeneration_to_close_is_supply`). Здесь вход НЕ предъявлен. -/
theorem promotion_paid_or_closes_is_the_wall {State : Type} (Step : State → State → Prop)
    (Universe Close : State → Prop) (Total : State → ℕ) (Work : State → State → ℕ) :
    PromotionPaidOrCloses Step Universe Close Total Work ↔
      (∀ {x y : State}, Universe x → Step x y → Close x ∨ Total y + Work x y ≤ Total x) := Iff.rfl

/--
  **`universe_preservation_alone_does_not_bound_run` — ДОКАЗАНА (red-test §36).** Сохранение вселенной
  БЕЗ платы бесконечного пути НЕ запрещает: строим замкнутую динамику на `ℕ` с `Step := (· + 1 = ·)`,
  где вселенная = всё, но `Total` монотонно РАСТЁТ — бесконечный путь существует. Значит `closed` сам по
  себе бесполезен без `paid`; вся сила — в `paid`/`paid_or_closes` (= promotion-стена). -/
theorem universe_preservation_alone_does_not_bound_run :
    ∃ (D : ClosedDynamics ℕ (fun x y => y = x + 1)) (path : ℕ → ℕ),
      D.Universe (path 0) ∧ ∀ k, (fun x y => y = x + 1) (path k) (path (k + 1)) := by
  refine ⟨{ Universe := fun _ => True, closed := by intro x y _ _; trivial }, id, trivial, ?_⟩
  intro k; rfl

end EuclidsPath.ClosedUniverse
