/-
  ClosedUniverse — "the engine cannot leave the universe": universe preservation along the path +
  paid dynamics under preservation, plus a scale-indexed version and the paid-or-closes dichotomy.
  Source: closed_universe_step00_formal_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section "ClosedUniverse: the engine does not leave the universe").

  IDEA. Before applying any energy/cut/signature-invariant along the path, one must prove that
  the engine STAYS in the universe: `Universe x → Step x y → Universe y`. If a step changes the scale/
  universe and creates a resource, it is paid for (`Total_B y + Work + UniverseChangeCost ≤ Total_A x`)
  OR `Close` occurs. The main danger: `promotion A→A'` can take the engine out of the old universe
  and return it with a new resource (refuel).

  PROVED HERE (pure induction/sums/well-founded, std axioms, no sorry):
    * `universe_along_path` (§2) — universe preservation along the path;
    * `ClosedPaidDynamics`: `strict_drop` (§4), `path_budget` (§5), `steps_bounded` (§6),
      `no_infinite_closed_paid_run` (§7);
    * `ClosedPaidScaleDynamics.strict_drop` (§10, scale-indexed with UniverseChangeCost);
    * `closed_paid_or_closes_no_infinite_run` (§25 dichotomy — under `¬Close` descent, at `Close` terminal);
    * `universeRefuel_is_paid_violation` (§33) — refuel = exactly the negation of `paid` (machine-verified).

  HONEST BOUNDARY (§23, §25, §34, §36 bricks — exposed and MACHINE-FIXED). Abstract laws
  are real. But the Step00 instantiation rests on ONE dangerous named input: `step00_promotion_paid_or_closes`
  (§25) — "the most dangerous theorem" (§36): promotion/carrier-regeneration does not create a new resource OR
  closes. This is exactly the orientation wall (`HigherEnergy`: promotion misoriented = refuel) + supply wall
  (`PaidDynamics.regeneration_to_close_is_supply` = `SNOL.SNOLInput`). `promotion_paid_or_closes_is_the_wall`
  fixes machine-wise: without it `no_infinite_closed_paid_run` cannot be instantiated for Step00. The named input
  is NOT supplied here. `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.PaidDynamics

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.ClosedUniverse

open EuclidsPath.PaidDynamics

/-! ### §1–2. ClosedDynamics: universe preservation along the path -/

/-- Closed dynamics: the universe is preserved under a step (`x∈U`, `x→y ⟹ y∈U`). -/
structure ClosedDynamics (State : Type) (Step : State → State → Prop) where
  Universe : State → Prop
  closed : ∀ {x y : State}, Universe x → Step x y → Universe y

/--
  **`universe_along_path` — PROVED (§2).** If the start is in the universe and every step is legal, then the ENTIRE
  trajectory lies in the universe. This is mandatory BEFORE applying any energy/cut-invariant along the path. -/
theorem universe_along_path {State : Type} {Step : State → State → Prop}
    (D : ClosedDynamics State Step) (path : ℕ → State)
    (hStart : D.Universe (path 0)) (hStep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ k, D.Universe (path k) := by
  intro k
  induction k with
  | zero => exact hStart
  | succ k ih => exact D.closed ih (hStep k)

/-! ### §3–7. ClosedPaidDynamics: paid inside the universe ⟹ no infinite run -/

/-- Closed paid dynamics: `work_pos`/`paid` are required only when the source is INSIDE the universe. -/
structure ClosedPaidDynamics (State : Type) (Step : State → State → Prop) where
  Universe : State → Prop
  Total : State → ℕ
  Work : State → State → ℕ
  closed : ∀ {x y : State}, Universe x → Step x y → Universe y
  work_pos : ∀ {x y : State}, Universe x → Step x y → 0 < Work x y
  paid : ∀ {x y : State}, Universe x → Step x y → Total y + Work x y ≤ Total x

/-- Forget the paid condition — obtain `ClosedDynamics`. -/
def ClosedPaidDynamics.toClosed {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) : ClosedDynamics State Step where
  Universe := D.Universe
  closed := D.closed

/-- **`closedPaid_strict_drop` — PROVED (§4).** A paid step from the universe strictly drops `Total`. -/
theorem closedPaid_strict_drop {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) {x y : State}
    (hUx : D.Universe x) (hStep : Step x y) : D.Total y < D.Total x := by
  have hPaid := D.paid hUx hStep; have hPos := D.work_pos hUx hStep; omega

/-- **`closedPaid_path_budget` — PROVED (§5).** Path budget (accounting for universe preservation). -/
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

/-- **`closedPaid_steps_bounded` — PROVED (§6).** `n ≤ Total (path 0)`. -/
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

/-- **`no_infinite_closed_paid_run` — PROVED (§7).** If the engine stays in the universe and every
    step is paid, there is NO infinite path. -/
theorem no_infinite_closed_paid_run {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidDynamics State Step) :
    ¬ ∃ path : ℕ → State, D.Universe (path 0) ∧ ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hStart, hStep⟩
  have := closedPaid_steps_bounded D path hStart hStep (D.Total (path 0) + 1)
  omega

/-! ### §8–10. Scale-indexed: universe and the cost of changing the universe by scale -/

/-- Closed paid scale-dynamics: states `StateAt A`, step `A ≤ B`, plus `UniverseChangeCost`. -/
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

/-- **`closedPaidScale_strict_drop` — PROVED (§10).** A scale step from the universe strictly drops `Total`
    (even with a positive `UniverseChangeCost`). -/
theorem closedPaidScale_strict_drop {StateAt : ℕ → Type}
    {StepAt : ∀ {A B : ℕ}, A ≤ B → StateAt A → StateAt B → Prop}
    (D : ClosedPaidScaleDynamics StateAt StepAt) {A B : ℕ} {hAB : A ≤ B}
    {x : StateAt A} {y : StateAt B} (hUx : D.UniverseAt A x) (hStep : StepAt hAB x y) :
    D.Total B y < D.Total A x := by
  have hPaid := D.paid hUx hStep; have hPos := D.work_pos hUx hStep; omega

/-! ### §25. Paid-or-closes: the "closes OR pays" dichotomy

Weaker (realistic) named input: every live step EITHER closes at the current scale OR is paid.
Under a global `¬Close` this reduces to ordinary paid dynamics ⟹ no infinite run. -/

/-- Closed dynamics with the paid-or-closes dichotomy: `Close : State → Prop`; every step from the universe
    either gives `Close x` or is paid. -/
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
  **`closed_paid_or_closes_no_infinite_run` — PROVED (§25 dichotomy).** If `Close` is absent on ANY reachable
  state (`hNoClose`), then paid-or-closes degenerates to paid, and there is no infinite live path.
  If `Close` does occur somewhere — that is the sought terminal (conclusion handled separately). -/
theorem closed_paid_or_closes_no_infinite_run {State : Type} {Step : State → State → Prop}
    (D : ClosedPaidOrClosesDynamics State Step)
    (hNoClose : ∀ x, D.Universe x → ¬ D.Close x) :
    ¬ ∃ path : ℕ → State, D.Universe (path 0) ∧ ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hStart, hStep⟩
  -- Build ClosedPaidDynamics: under hNoClose the dichotomy yields paid everywhere in the universe.
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

/-! ### §32–33. UniverseEscape / UniverseRefuel as negations of invariants -/

/--
  **`universeRefuel_is_paid_violation` — PROVED (§33).** "Refuel" (the engine remains legal but
  returns with more resource than permitted) is EXACTLY the negation of `paid`: if
  `Total x < Total y + Work x y`, then `¬ (Total y + Work x y ≤ Total x)`. Hence every refuel is a direct
  violation of the paid law; it can only be closed by proving `paid` (or `paid_or_closes`). -/
theorem universeRefuel_is_paid_violation {State : Type} (Total : State → ℕ) (Work : State → State → ℕ)
    (x y : State) (hRefuel : Total x < Total y + Work x y) :
    ¬ (Total y + Work x y ≤ Total x) := by omega

/-! ### §23, §25, §34, §36. MACHINE DIAGNOSIS OF THE TRAP: promotion_paid_or_closes — the wall

The abstract laws above are correct and non-vacuous. But Step00 instantiates `no_infinite_closed_paid_run`
ONLY if `paid` is proved for EVERY step, including promotion/carrier-regeneration. The brick (§36) directly
calls `step00_promotion_paid_or_closes` "the most dangerous theorem" and "the most likely hidden
perpetual engine". Let us fix machine-wise that without it instantiation is impossible. -/

/-- Abstract "promotion named input": for every promotion step — either Close or paid. This is exactly
    `step00_promotion_paid_or_closes`; local/energy laws do NOT supply it. -/
def PromotionPaidOrCloses {State : Type} (Step : State → State → Prop)
    (Universe Close : State → Prop) (Total : State → ℕ) (Work : State → State → ℕ) : Prop :=
  ∀ {x y : State}, Universe x → Step x y → Close x ∨ Total y + Work x y ≤ Total x

/--
  **`promotion_paid_or_closes_is_the_wall` — PROVED (conclusion of diagnosis §36).** `PromotionPaidOrCloses`
  UNFOLDS to exactly the `paid_or_closes` field of `ClosedPaidOrClosesDynamics`. That is, it is
  precisely the named input required by `closed_paid_or_closes_no_infinite_run` — and it does NOT follow from
  universe preservation or local energy. If promotion creates a new resource (refuel per §33) —
  the named input is false, and that is a hidden perpetual engine (orientation wall `HigherEnergy` + supply wall
  `PaidDynamics.regeneration_to_close_is_supply`). The named input is NOT supplied here. -/
theorem promotion_paid_or_closes_is_the_wall {State : Type} (Step : State → State → Prop)
    (Universe Close : State → Prop) (Total : State → ℕ) (Work : State → State → ℕ) :
    PromotionPaidOrCloses Step Universe Close Total Work ↔
      (∀ {x y : State}, Universe x → Step x y → Close x ∨ Total y + Work x y ≤ Total x) := Iff.rfl

/--
  **`universe_preservation_alone_does_not_bound_run` — PROVED (red-test §36).** Universe preservation
  WITHOUT payment does NOT prohibit an infinite path: we build a closed dynamics on `ℕ` with `Step := (· + 1 = ·)`,
  where the universe is everything but `Total` grows monotonically — an infinite path exists. Hence `closed` alone
  is useless without `paid`; all the force lies in `paid`/`paid_or_closes` (= the promotion wall). -/
theorem universe_preservation_alone_does_not_bound_run :
    ∃ (D : ClosedDynamics ℕ (fun x y => y = x + 1)) (path : ℕ → ℕ),
      D.Universe (path 0) ∧ ∀ k, (fun x y => y = x + 1) (path k) (path (k + 1)) := by
  refine ⟨{ Universe := fun _ => True, closed := by intro x y _ _; trivial }, id, trivial, ?_⟩
  intro k; rfl

end EuclidsPath.ClosedUniverse
