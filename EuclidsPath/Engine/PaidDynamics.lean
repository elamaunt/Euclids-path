/-
  PaidDynamics — paid dynamics: no free inertia, no acceleration via paid jumps,
  no free cloning of branches; hidden engine as carrier-regeneration.
  Source: hidden_engine_paid_dynamics_no_cloning_formal_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section "Hidden engine and paid dynamics").

  IDEA. If Step00 does not close locally, the "second engine" may hide in: (1) scale promotion
  `A→A'`, (2) carrier regeneration, (3) unaccounted inertia/credit, (4) branch cloning.
  Against each — a paid law: if EVERY step/jump/split is paid from the shared potential `Total`,
  there is no infinite/cofinal/cloning motion. The ONLY substantive input that remains is
  `regeneration_forces_close` — and the brick itself (§6, §34, §36) says: this is exactly `SNOL.SNOLInput`/carrier-
  density wall.

  PROVED HERE (pure well-founded/sums, std axioms, no sorry) — paid laws:
    * `PaidDynamics`: `strict_drop` (§8), `path_budget` (§9), `steps_bounded` (§10),
      `no_infinite_paid_run` (§10), `no_step_from_zero_total` (§13);
    * `monotone_nat_telescope_sub_le_sum_sub` (§16, telescope — brick sorry closed);
    * `PaidJumpDynamics`: `total_level_gain_bound` (§16), `no_cofinal_paid_jump_path` (§17);
    * `NoFreeInertia`: `no_infinite_noFreeInertia_run` (§12);
    * `NoFreeCloning`: `no_two_live_children_from_unit` (§23, one live unit ≠ two live units);
    * `contradiction_from_regeneration` (§5) — ABSTRACT assembly (given force + regeneration-to-close).

  HONEST BOUNDARY (§6, §34, §36 of the brick — exposed and MACHINE-FIXED). The paid laws are real and
  proved. But they only LOCALIZE the hidden engine: any infinite Step00 mechanism must
  use `regeneration_forces_close` (`InfiniteCarrierRegeneration ⟹ ∃A, CloseAt`). The brick
  states directly (§6, §36, "carrier/density wall"): this input = supply clean carrier at scale =
  `SNOL.SNOLInput`. `regeneration_to_close_is_supply` fixes this machine-formally. The input is NOT supplied here.
  `Step00` remains `sorry`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.PaidDynamics

/-! ### §7–8. Abstract paid dynamics: strict drop -/

/-- Paid dynamics: each step spends positive work `Work` from the shared potential `Total`,
    `Total y + Work x y ≤ Total x`. -/
structure PaidDynamics (State : Type) (Step : State → State → Prop) where
  Total : State → ℕ
  Work : State → State → ℕ
  work_pos : ∀ {x y}, Step x y → 0 < Work x y
  paid : ∀ {x y}, Step x y → Total y + Work x y ≤ Total x

/--
  **`paidDynamics_strict_drop` — PROVED (§8).** A paid step strictly drops `Total`. No free
  inertial step. -/
theorem paidDynamics_strict_drop {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) {x y : State} (hStep : Step x y) : D.Total y < D.Total x := by
  have hPaid := D.paid hStep; have hPos := D.work_pos hStep; omega

/-! ### §9. Path budget: sum of work + current Total ≤ initial Total -/

/--
  **`paidDynamics_path_budget` — PROVED (§9).** For a paid path the sum of all work up to step `n` plus
  `Total (path n)` does not exceed `Total (path 0)`. -/
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

/-! ### §10. Step count bounded by initial Total; no infinite paid path -/

/-- **`paidDynamics_steps_bounded` — PROVED (§10).** `n ≤ Total (path 0)` for any `n`. -/
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

/-- **`no_infinite_paid_run` — PROVED (§10).** No infinite paid path exists. -/
theorem no_infinite_paid_run {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) :
    ¬ ∃ path : ℕ → State, ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hStep⟩
  have := paidDynamics_steps_bounded D path hStep (D.Total (path 0) + 1)
  omega

/-- **`no_step_from_zero_total` — PROVED (§13).** `Total x = 0 ⟹` terminal (no step from `x`). -/
theorem no_step_from_zero_total {State : Type} {Step : State → State → Prop}
    (D : PaidDynamics State Step) {x : State} (hZero : D.Total x = 0) :
    ¬ ∃ y, Step x y := by
  rintro ⟨y, hStep⟩
  have := paidDynamics_strict_drop D hStep; omega

/-! ### §11–12. NoFreeInertia: inertia/credits inside Total ⟹ no free inertia -/

/-- Potential = fuel + inertia + hidden credit (all resources accounted for in `Total`). -/
structure FuelInertiaPotential (State : Type) where
  fuel : State → ℕ
  inertia : State → ℕ
  hiddenCredit : State → ℕ
  Total : State → ℕ
  total_eq : ∀ x, Total x = fuel x + inertia x + hiddenCredit x

/-- No-free-inertia: paid dynamics on the full potential (fuel+inertia+hiddenCredit). -/
structure NoFreeInertiaDynamics (State : Type) (Step : State → State → Prop) where
  P : FuelInertiaPotential State
  Work : State → State → ℕ
  work_pos : ∀ {x y}, Step x y → 0 < Work x y
  paid : ∀ {x y}, Step x y → P.Total y + Work x y ≤ P.Total x

/-- Reduce to paid dynamics. -/
def NoFreeInertiaDynamics.toPaidDynamics {State : Type} {Step : State → State → Prop}
    (D : NoFreeInertiaDynamics State Step) : PaidDynamics State Step where
  Total := D.P.Total
  Work := D.Work
  work_pos := D.work_pos
  paid := D.paid

/-- **`no_infinite_noFreeInertia_run` — PROVED (§12).** One cannot buy inertia and ride for free
    when inertia/credit are accounted for in `Total`. -/
theorem no_infinite_noFreeInertia_run {State : Type} {Step : State → State → Prop}
    (D : NoFreeInertiaDynamics State Step) :
    ¬ ∃ path : ℕ → State, ∀ k, Step (path k) (path (k + 1)) :=
  no_infinite_paid_run D.toPaidDynamics

/-! ### §14–17. PaidJumpDynamics: no acceleration to cofinal levels via paid jumps -/

/-- Paid jump-dynamics: in addition to `paid`, each level jump is paid by work (`level y − level x ≤ Work`). -/
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

/-- Cofinal path by levels. -/
def CofinalPath {State : Type} (level : State → ℕ) (path : ℕ → State) : Prop :=
  ∀ C, ∃ k, C ≤ level (path k)

/--
  **`monotone_nat_telescope_sub_le_sum_sub` — PROVED (§16, brick sorry closed).** Telescope:
  `a n − a 0 ≤ ∑_{k<n} (a(k+1) − a k)` for monotone `a : ℕ → ℕ`. -/
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
  **`paidJump_total_level_gain_bound` — PROVED (§16).** Total level gain is bounded by the initial
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
  -- each telescope term ≤ the corresponding work
  have hStepLe : ∀ k ∈ Finset.range n,
      D.level (path (k + 1)) - D.level (path k) ≤ D.Work (path k) (path (k + 1)) :=
    fun k _ => D.jump_paid (hStep k)
  have hJumpSum : D.level (path n) - D.level (path 0)
      ≤ ∑ k ∈ Finset.range n, D.Work (path k) (path (k + 1)) :=
    le_trans hTele (Finset.sum_le_sum hStepLe)
  omega

/-- **`no_cofinal_paid_jump_path` — PROVED (§17).** No acceleration to cofinal levels: a monotone
    paid jump-path CANNOT be cofinal. -/
theorem no_cofinal_paid_jump_path {State : Type} {Step : State → State → Prop}
    (D : PaidJumpDynamics State Step) (path : ℕ → State)
    (hStep : ∀ k, Step (path k) (path (k + 1)))
    (hLevelMono : ∀ k, D.level (path k) ≤ D.level (path (k + 1))) :
    ¬ CofinalPath D.level path := by
  intro hCofinal
  obtain ⟨k, hk⟩ := hCofinal (D.level (path 0) + D.Total (path 0) + 1)
  have hGain := paidJump_total_level_gain_bound D path hStep hLevelMono k
  omega

/-! ### §21–23. NoFreeCloning: one live unit does not become two live units -/

/-- No free cloning: the sum of children's potentials ≤ parent's potential; live children have
    positive potential. -/
structure NoFreeCloning (State : Type) [DecidableEq State] where
  Live : State → Prop
  Total : State → ℕ
  Split : State → Finset State → Prop
  paid : ∀ {x kids}, Split x kids → (∑ y ∈ kids, Total y) ≤ Total x
  live_positive : ∀ x, Live x → 0 < Total x
  children_live : ∀ {x kids y}, Split x kids → y ∈ kids → Live y

/--
  **`no_two_live_children_from_unit` — PROVED (§23).** A unit with `Total = 1` cannot split into
  two or more live children: each live child has `Total ≥ 1`, so `∑ ≥ 2 > 1 = Total`.
  "One live unit does not become two live units." -/
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

/-! ### §1–5. Hidden engine as carrier-regeneration: abstract assembly

`CloseAt A` = `Step00.EuclideanEngine A ∨ TwinAbove` — treated abstractly here as a disjunction of inputs. -/

/-- Abstract "hidden engine": infinite carrier-regeneration (external scale-engine). -/
structure InfiniteCarrierRegeneration (RegState : Type) where
  state : ℕ → RegState
  scaleOf : RegState → ℕ
  scale_grows : ∀ k, scaleOf (state k) < scaleOf (state (k + 1))
  cofinal : ∀ A, ∃ k, A ≤ scaleOf (state k)

/--
  **`contradiction_from_regeneration` — PROVED (§5, abstract assembly).** Given (1) force theorem
  `NoTwin → NoEngine → InfiniteCarrierRegeneration`, (2) regeneration-to-close
  `InfiniteCarrierRegeneration → EngineFound ∨ TwinFound`, and hypotheses `NoTwin`/`NoEngine` with barriers
  `¬EngineFound from NoEngine`, `¬TwinFound from NoTwin`, we derive `False`. All force lies in (2). -/
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

/-! ### §6, §34, §36. MACHINE DIAGNOSIS OF THE TRAP: regeneration-to-close = SNOL/carrier-density wall

The paid laws above localize the hidden engine but do not eliminate it. The only substantive input is
`regeneration_forces_close` (`InfiniteCarrierRegeneration ⟹ CloseAt`). The brick itself says (§6, §36)
that this is supply clean carrier at scale = `SNOL.SNOLInput`. We fix this machine-formally. -/

/-- Abstract supply theorem (form of `SNOL.SNOLInput`): regeneration ⟹ engine or twin found. This is
    exactly `regeneration_forces_close`. -/
def RegenerationToClose {RegState : Type} (EngineFound TwinFound : Prop) : Prop :=
  InfiniteCarrierRegeneration RegState → EngineFound ∨ TwinFound

/--
  **`regeneration_to_close_is_supply` — PROVED (red-test §6/§36).** `RegenerationToClose`
  UNFOLDS into a pure supply implication "regeneration ⟹ close". The paid laws (proved) do NOT
  provide it: they only bound local/jump/split motion but do NOT supply close from external
  scale-regeneration. Therefore supplying it via `SNOL.SNOLInput`/carrier-density is a wall, not
  a bypass. It is NOT supplied here. -/
theorem regeneration_to_close_is_supply {RegState : Type} (EngineFound TwinFound : Prop) :
    RegenerationToClose (RegState := RegState) EngineFound TwinFound ↔
      (InfiniteCarrierRegeneration RegState → EngineFound ∨ TwinFound) := Iff.rfl

/--
  **`paid_laws_do_not_close_regeneration` — PROVED (diagnostic conclusion).** Formally: `InfiniteCarrierRegeneration`
  requires only `scale_grows` + `cofinal` — it has NO `Total`/`Work` field, so the paid laws
  (`no_infinite_paid_run` etc.) are NOT applicable to it: regeneration is an external scale-engine, not
  a paid local path. We demonstrate this by constructing a non-trivial regeneration (scale k = k) — it
  exists, hence paid laws alone do not forbid it; the only thing that can forbid it is
  `RegenerationToClose` (the supply input). -/
theorem paid_laws_do_not_close_regeneration :
    Nonempty (InfiniteCarrierRegeneration ℕ) := by
  refine ⟨{ state := id, scaleOf := id, scale_grows := ?_, cofinal := ?_ }⟩
  · intro k; simp
  · intro A; exact ⟨A, le_rfl⟩

end EuclidsPath.PaidDynamics
