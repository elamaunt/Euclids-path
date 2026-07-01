/-
  PaidDynamics — платная динамика: нет бесплатной инерции, нет ускорения оплаченными скачками,
  нет бесплатного клонирования ветвей; скрытый двигатель как carrier-регенерация.
  Источник: hidden_engine_paid_dynamics_no_cloning_formal_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Скрытый двигатель и платная динамика»).

  ИДЕЯ. Если Step00 не закрывается локально, «второй двигатель» может прятаться в: (1) промоушене
  масштаба `A→A'`, (2) регенерации carrier, (3) неучтённой инерции/кредите, (4) клонировании ветвей.
  Против каждого — платный закон: если КАЖДЫЙ шаг/скачок/split оплачен из общего потенциала `Total`,
  бесконечного/cofinal/клонирующего движения нет. Остаётся ЕДИНСТВЕННЫЙ содержательный вход —
  `regeneration_forces_close` — и кирпич сам (§6, §34, §36) говорит: это ровно `SNOL.SNOLInput`/carrier-
  density стена.

  ЗДЕСЬ ДОКАЗАНО (чистая well-founded/суммы, std аксиомы, без sorry) — платные законы:
    * `PaidDynamics`: `strict_drop` (§8), `path_budget` (§9), `steps_bounded` (§10),
      `no_infinite_paid_run` (§10), `no_step_from_zero_total` (§13);
    * `monotone_nat_telescope_sub_le_sum_sub` (§16, телескоп — sorry кирпича закрыт);
    * `PaidJumpDynamics`: `total_level_gain_bound` (§16), `no_cofinal_paid_jump_path` (§17);
    * `NoFreeInertia`: `no_infinite_noFreeInertia_run` (§12);
    * `NoFreeCloning`: `no_two_live_children_from_unit` (§23, один live-юнит ≠ два live-юнита);
    * `contradiction_from_regeneration` (§5) — АБСТРАКТНАЯ сборка (при force + regeneration-to-close).

  ЧЕСТНАЯ ГРАНИЦА (§6, §34, §36 кирпича — вскрыта и МАШИННО зафиксирована). Платные законы реальны и
  доказаны. Но они лишь ЛОКАЛИЗУЮТ скрытый двигатель: любой бесконечный Step00-механизм обязан
  использовать `regeneration_forces_close` (`InfiniteCarrierRegeneration ⟹ ∃A, CloseAt`). Кирпич
  прямо (§6, §36, «carrier/density wall») говорит: этот вход = supply clean carrier at scale =
  `SNOL.SNOLInput`. `regeneration_to_close_is_supply` фиксирует это машинно. Здесь вход НЕ предъявлен.
  `Step00` остаётся `sorry`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.PaidDynamics

/-! ### §7–8. Абстрактная платная динамика: строгий спад -/

/-- Платная динамика: каждый шаг тратит положительную работу `Work` из общего потенциала `Total`,
    `Total y + Work x y ≤ Total x`. -/
structure PaidDynamics (State : Type) (Step : State → State → Prop) where
  Total : State → ℕ
  Work : State → State → ℕ
  work_pos : ∀ {x y}, Step x y → 0 < Work x y
  paid : ∀ {x y}, Step x y → Total y + Work x y ≤ Total x

/--
  **`paidDynamics_strict_drop` — ДОКАЗАНА (§8).** Платный шаг строго роняет `Total`. Нет бесплатного
  инерционного шага. -/
theorem paidDynamics_strict_drop {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) {x y : State} (hStep : Step x y) : D.Total y < D.Total x := by
  have hPaid := D.paid hStep; have hPos := D.work_pos hStep; omega

/-! ### §9. Бюджет пути: сумма работ + текущий Total ≤ начальный Total -/

/--
  **`paidDynamics_path_budget` — ДОКАЗАНА (§9).** Для платного пути сумма всех работ до шага `n` плюс
  `Total (path n)` не превосходит `Total (path 0)`. -/
theorem paidDynamics_path_budget {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) (path : ℕ → State)
    (hStep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ n, (∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1))) + D.Total (path n)
      ≤ D.Total (path 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hPaid := D.paid (hStep n)
      rw [Finset.sum_range_succ]; omega

/-! ### §10. Число шагов ограничено начальным Total; нет бесконечного платного пути -/

/-- **`paidDynamics_steps_bounded` — ДОКАЗАНА (§10).** `n ≤ Total (path 0)` для любого `n`. -/
theorem paidDynamics_steps_bounded {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) (path : ℕ → State)
    (hStep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ n, n ≤ D.Total (path 0) := by
  intro n
  have hBudget := paidDynamics_path_budget D path hStep n
  have hEach : ∀ k ∈ Finset.range n, 1 ≤ D.Work (path k) (path (k + 1)) :=
    fun k _ => D.work_pos (hStep k)
  have hSumLower : n ≤ ∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1)) := by
    calc n = ∑ _k ∈ Finset.range n, 1 := by simp
      _ ≤ ∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1)) :=
        Finset.sum_le_sum hEach
  omega

/-- **`no_infinite_paid_run` — ДОКАЗАНА (§10).** Нет бесконечного платного пути. -/
theorem no_infinite_paid_run {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) :
    ¬ ∃ path : ℕ → State, ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hStep⟩
  have := paidDynamics_steps_bounded D path hStep (D.Total (path 0) + 1)
  omega

/-- **`no_step_from_zero_total` — ДОКАЗАНА (§13).** `Total x = 0 ⟹` терминал (нет шага из `x`). -/
theorem no_step_from_zero_total {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) {x : State} (hZero : D.Total x = 0) :
    ¬ ∃ y, Step x y := by
  rintro ⟨y, hStep⟩
  have := paidDynamics_strict_drop D hStep; omega

/-! ### §11–12. NoFreeInertia: инерция/кредиты внутри Total ⟹ нет бесплатной инерции -/

/-- Потенциал = топливо + инерция + скрытый кредит (все ресурсы учтены в `Total`). -/
structure FuelInertiaPotential (State : Type) where
  fuel : State → ℕ
  inertia : State → ℕ
  hiddenCredit : State → ℕ
  Total : State → ℕ
  total_eq : ∀ x, Total x = fuel x + inertia x + hiddenCredit x

/-- No-free-inertia: платная динамика на полном потенциале (fuel+inertia+hiddenCredit). -/
structure NoFreeInertiaDynamics (State : Type) (Step : State → State → Prop) where
  P : FuelInertiaPotential State
  Work : State → State → ℕ
  work_pos : ∀ {x y}, Step x y → 0 < Work x y
  paid : ∀ {x y}, Step x y → P.Total y + Work x y ≤ P.Total x

/-- Свести к платной динамике. -/
def NoFreeInertiaDynamics.toPaidDynamics {State : Type} {Step : State → State → Prop}
    (D : NoFreeInertiaDynamics State Step) : PaidDynamics State Step where
  Total := D.P.Total
  Work := D.Work
  work_pos := D.work_pos
  paid := D.paid

/-- **`no_infinite_noFreeInertia_run` — ДОКАЗАНА (§12).** Нельзя купить инерцию и ехать бесплатно,
    если инерция/кредит учтены в `Total`. -/
theorem no_infinite_noFreeInertia_run {State : Type} {Step : State → State → Prop}
    (D : NoFreeInertiaDynamics State Step) :
    ¬ ∃ path : ℕ → State, ∀ k, Step (path k) (path (k + 1)) :=
  no_infinite_paid_run D.toPaidDynamics

/-! ### §14–17. PaidJumpDynamics: нет ускорения к cofinal-уровням оплаченными скачками -/

/-- Платная jump-динамика: помимо `paid`, каждый скачок уровня оплачен работой (`level y − level x ≤ Work`). -/
structure PaidJumpDynamics (State : Type) (Step : State → State → Prop) where
  level : State → ℕ
  Total : State → ℕ
  Work : State → State → ℕ
  work_pos : ∀ {x y}, Step x y → 0 < Work x y
  paid : ∀ {x y}, Step x y → Total y + Work x y ≤ Total x
  jump_paid : ∀ {x y}, Step x y → level y - level x ≤ Work x y

def PaidJumpDynamics.toPaidDynamics {State : Type} {Step : State → State → Prop}
    (D : PaidJumpDynamics State Step) : PaidDynamics State Step where
  Total := D.Total
  Work := D.Work
  work_pos := D.work_pos
  paid := D.paid

/-- Cofinal путь по уровням. -/
def CofinalPath {State : Type} (level : State → ℕ) (path : ℕ → State) : Prop :=
  ∀ C, ∃ k, C ≤ level (path k)

/--
  **`monotone_nat_telescope_sub_le_sum_sub` — ДОКАЗАНА (§16, sorry кирпича закрыт).** Телескоп:
  `a n − a 0 ≤ ∑_{k<n} (a(k+1) − a k)` для монотонной `a : ℕ → ℕ`. -/
theorem monotone_nat_telescope_sub_le_sum_sub (a : ℕ → ℕ) (hMono : ∀ k, a k ≤ a (k + 1)) :
    ∀ n, a n - a 0 ≤ ∑ k ∈ Finset.range n, (a (k + 1) - a k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hMono n
      omega

/--
  **`paidJump_total_level_gain_bound` — ДОКАЗАНА (§16).** Суммарный прирост уровня ограничен начальным
  `Total`: `level (path n) − level (path 0) ≤ Total (path 0)`. -/
theorem paidJump_total_level_gain_bound {State : Type} {Step : State → State → Prop}
    (D : PaidJumpDynamics State Step) (path : ℕ → State)
    (hStep : ∀ k, Step (path k) (path (k + 1)))
    (hLevelMono : ∀ k, D.level (path k) ≤ D.level (path (k + 1))) :
    ∀ n, D.level (path n) - D.level (path 0) ≤ D.Total (path 0) := by
  intro n
  have hBudget : (∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1))) + D.Total (path n)
      ≤ D.Total (path 0) := paidDynamics_path_budget D.toPaidDynamics path hStep n
  have hTele := monotone_nat_telescope_sub_le_sum_sub (fun k => D.level (path k)) hLevelMono n
  -- каждый телескоп-член ≤ соответствующей работе
  have hStepLe : ∀ k ∈ Finset.range n,
      D.level (path (k + 1)) - D.level (path k) ≤ D.Work (path k) (path (k + 1)) :=
    fun k _ => D.jump_paid (hStep k)
  have hJumpSum : D.level (path n) - D.level (path 0)
      ≤ ∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1)) :=
    le_trans hTele (Finset.sum_le_sum hStepLe)
  omega

/-- **`no_cofinal_paid_jump_path` — ДОКАЗАНА (§17).** Нет ускорения к cofinal-уровням: монотонный
    платный jump-путь НЕ может быть cofinal. -/
theorem no_cofinal_paid_jump_path {State : Type} {Step : State → State → Prop}
    (D : PaidJumpDynamics State Step) (path : ℕ → State)
    (hStep : ∀ k, Step (path k) (path (k + 1)))
    (hLevelMono : ∀ k, D.level (path k) ≤ D.level (path (k + 1))) :
    ¬ CofinalPath D.level path := by
  intro hCofinal
  obtain ⟨k, hk⟩ := hCofinal (D.level (path 0) + D.Total (path 0) + 1)
  have hGain := paidJump_total_level_gain_bound D path hStep hLevelMono k
  omega

/-! ### §21–23. NoFreeCloning: один live-юнит не превращается в два live-юнита -/

/-- Нет бесплатного клонирования: сумма потенциалов детей ≤ потенциала родителя; живые дети имеют
    положительный потенциал. -/
structure NoFreeCloning (State : Type) [DecidableEq State] where
  Live : State → Prop
  Total : State → ℕ
  Split : State → Finset State → Prop
  paid : ∀ {x kids}, Split x kids → (∑ y ∈ kids, Total y) ≤ Total x
  live_positive : ∀ x, Live x → 0 < Total x
  children_live : ∀ {x kids y}, Split x kids → y ∈ kids → Live y

/--
  **`no_two_live_children_from_unit` — ДОКАЗАНА (§23).** Юнит с `Total = 1` не может раздвоиться в
  два и более live-ребёнка: каждый live-ребёнок имеет `Total ≥ 1`, значит `∑ ≥ 2 > 1 = Total`.
  «Один live-юнит не становится двумя live-юнитами.» -/
theorem no_two_live_children_from_unit {State : Type} [DecidableEq State]
    (H : NoFreeCloning State) {x : State} (hTotal : H.Total x = 1)
    {kids : Finset State} (hSplit : H.Split x kids) (hTwo : 2 ≤ kids.card) : False := by
  have hEach : ∀ y ∈ kids, 1 ≤ H.Total y :=
    fun y hy => H.live_positive y (H.children_live hSplit hy)
  have hSumCard : kids.card ≤ ∑ y ∈ kids, H.Total y := by
    calc kids.card = ∑ _y ∈ kids, 1 := by simp
      _ ≤ ∑ y ∈ kids, H.Total y := Finset.sum_le_sum hEach
  have hPaid := H.paid hSplit
  omega

/-! ### §1–5. Скрытый двигатель как carrier-регенерация: абстрактная сборка

`CloseAt A` = `Step00.EuclideanEngine A ∨ TwinAbove` — здесь абстрактно как дизъюнкция входов. -/

/-- Абстрактный «скрытый двигатель»: бесконечная carrier-регенерация (внешний scale-двигатель). -/
structure InfiniteCarrierRegeneration (RegState : Type) where
  state : ℕ → RegState
  scaleOf : RegState → ℕ
  scale_grows : ∀ k, scaleOf (state k) < scaleOf (state (k + 1))
  cofinal : ∀ A, ∃ k, A ≤ scaleOf (state k)

/--
  **`contradiction_from_regeneration` — ДОКАЗАНА (§5, абстрактная сборка).** При (1) force-теореме
  `NoTwin → NoEngine → InfiniteCarrierRegeneration`, (2) regeneration-to-close
  `InfiniteCarrierRegeneration → EngineFound ∨ TwinFound`, и посылках `NoTwin`/`NoEngine` c барьерами
  `¬EngineFound из NoEngine`, `¬TwinFound из NoTwin`, получаем `False`. Вся сила — в (2). -/
theorem contradiction_from_regeneration {RegState : Type}
    {NoTwin NoEngine EngineFound TwinFound : Prop}
    (hForce : NoTwin → NoEngine → InfiniteCarrierRegeneration RegState)
    (hRegClose : InfiniteCarrierRegeneration RegState → EngineFound ∨ TwinFound)
    (hEngineBar : NoEngine → ¬ EngineFound)
    (hTwinBar : NoTwin → ¬ TwinFound)
    (hNoTwin : NoTwin) (hNoEngine : NoEngine) : False := by
  have R := hForce hNoTwin hNoEngine
  rcases hRegClose R with hE | hT
  · exact hEngineBar hNoEngine hE
  · exact hTwinBar hNoTwin hT

/-! ### §6, §34, §36. МАШИННЫЙ ДИАГНОЗ ЛОВУШКИ: regeneration-to-close = SNOL/carrier-density стена

Платные законы выше локализуют скрытый двигатель, но не устраняют. Единственный содержательный вход —
`regeneration_forces_close` (`InfiniteCarrierRegeneration ⟹ CloseAt`). Кирпич сам говорит (§6, §36),
что это supply clean carrier at scale = `SNOL.SNOLInput`. Зафиксируем машинно. -/

/-- Абстрактная supply-теорема (форма `SNOL.SNOLInput`): регенерация ⟹ найден engine или twin. Это
    ровно `regeneration_forces_close`. -/
def RegenerationToClose {RegState : Type} (EngineFound TwinFound : Prop) : Prop :=
  InfiniteCarrierRegeneration RegState → EngineFound ∨ TwinFound

/--
  **`regeneration_to_close_is_supply` — ДОКАЗАНА (red-test §6/§36).** `RegenerationToClose`
  РАЗВОРАЧИВАЕТСЯ в чистую supply-импликацию «регенерация ⟹ close». Платные законы (доказанные) её НЕ
  дают: они лишь ограничивают локальное/jump/split движение, но НЕ предъявляют close из внешней
  scale-регенерации. Значит если её предъявить через `SNOL.SNOLInput`/carrier-density — это стена, не
  обход. Здесь она НЕ предъявлена. -/
theorem regeneration_to_close_is_supply {RegState : Type} (EngineFound TwinFound : Prop) :
    RegenerationToClose (RegState := RegState) EngineFound TwinFound ↔
      (InfiniteCarrierRegeneration RegState → EngineFound ∨ TwinFound) := Iff.rfl

/--
  **`paid_laws_do_not_close_regeneration` — ДОКАЗАНА (итог диагноза).** Формально: `InfiniteCarrierRegeneration`
  требует лишь `scale_grows` + `cofinal` — в ней НЕТ поля `Total`/`Work`, поэтому платные законы
  (`no_infinite_paid_run` и т.п.) к ней НЕ применимы: регенерация — это внешний scale-двигатель, а не
  платный локальный путь. Демонстрируем это, построив нетривиальную регенерацию (scale k = k) — она
  существует, значит сами по себе платные законы её не запрещают; запрет может дать ЛИШЬ
  `RegenerationToClose` (supply-вход). -/
theorem paid_laws_do_not_close_regeneration :
    Nonempty (InfiniteCarrierRegeneration ℕ) := by
  refine ⟨{ state := id, scaleOf := id, scale_grows := ?_, cofinal := ?_ }⟩
  · intro k; simp
  · intro A; exact ⟨A, le_rfl⟩

end EuclidsPath.PaidDynamics
