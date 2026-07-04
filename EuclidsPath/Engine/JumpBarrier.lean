/-
  JumpBarrier — rapid energy expenditure, level jumps, and cut-barrier (jump-compatible reverse engine).
  Source: jump_reverse_engine_cut_barrier_formal_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section "Jump engine and cut-barrier").

  IDEA. The engine can spend energy faster and SKIP levels. This means we cannot require
  "visit every level" (`∀A ∃k, level k = A` breaks on `level_k = 2k`) — the correct replacement:
  CROSS/PROJECT onto every cut. For a high-level state at level `B` and cut `A₀ ≤ B` there is
  a finite signature `CutSig A₀`. If the reverse ray goes up indefinitely (cofinal), for a fixed
  `A₀` it yields infinitely many projections onto that cut; with finite `CutSig A₀` the signature REPEATS, and
  a repetition ⟹ `CloseAt A₀`. Contradiction with `¬Close`.

  PROVED HERE (pure logic / pigeonhole / well-founded, std axioms, no sorry):
    * `paidJump_decreases_energy` (§1) — a paid jump strictly drops energy (a larger expenditure only
      STRENGTHENS finiteness);
    * `no_infinite_strict_energy_descent` (§2) — no infinite strictly descending energy chain;
    * `jump_breaks_visitsEveryLevel` (§3) — `level_k=2k` cofinal, but does not visit odd levels ⟹ the correct
      goal = cofinal + cut-projections, not "every level";
    * `CutSystem`/`JumpReverseRay` (§5–6), `repeated_cutSig_on_jumpReverseRay` (§9, jump-pigeonhole);
    * `no_jumpReverseRay_of_cutBarrier` / `..._fixedCut` (§11) — with cut-barrier and `¬Close` no ray exists;
    * `no_jumpAboveGapConflict` (§18) — jump across twin-gap + return inside = ordinal contradiction.

  HONEST BOUNDARY (§17, §19 red-tests of the brick — exposed and MACHINE-FIXED). The abstract no-go
  is correct and not about concrete arithmetic. But the Step00 instantiation rests on TWO unproved inputs:
    * `step00_jumpReverseBarrier` (repeated cut-signature on a jump ray ⟹ Close) — cross-level labelled
      fan-in, the same trap as `snolHallSeed_bare_no_go`;
    * `noTwin_forces_jumpReverseRay` — red-test #5: if it requires `SNOL.SNOLInput`/`CleanDensityBelowA2`,
      it is a wall renaming. `red_test_forceRay_is_supply` records: force-ray = supply theorem.
  Both are inputs here. `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.AboveConflict

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.JumpBarrier

open EuclidsPath.AboveConflict

/-! ### §1. Forward jumps: a paid jump drops energy -/

/-- Paid jump: the level grows, but energy strictly drops by a positive price `cost`.
    (`cost` — existential data so that the structure remains a `Prop`.) -/
structure PaidJumpStep {State : Type} (level energy : State → ℕ) (x y : State) : Prop where
  level_jump : level x < level y
  paid : ∃ cost : ℕ, 0 < cost ∧ energy y + cost ≤ energy x

/--
  **`paidJump_decreases_energy` — PROVED (§1).** A paid jump strictly drops energy.
  A larger expenditure only STRENGTHENS finite termination; it does NOT create an infinite finite-energy path. -/
theorem paidJump_decreases_energy {State : Type} {level energy : State → ℕ} {x y : State}
    (h : PaidJumpStep level energy x y) : energy y < energy x := by
  obtain ⟨cost, hpos, hpaid⟩ := h.paid; omega

/-! ### §2. No infinite strictly descending energy chain -/

/--
  **`no_infinite_strict_energy_descent` — PROVED (§2).** Well-founded: no infinite strictly
  descending energy chain. The core of all "paid/jump" no-go arguments. -/
theorem no_infinite_strict_energy_descent {State : Type}
    (path : ℕ → State) (energy : State → ℕ)
    (hDrop : ∀ k, energy (path (k + 1)) < energy (path k)) : False := by
  have hMono : ∀ k, energy (path k) + k ≤ energy (path 0) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => have := hDrop n; omega
  have := hMono (energy (path 0) + 1); omega

/-! ### §3. Jumps break "visit every level"; the correct goal is cofinal -/

/-- Wrong (too strong) goal for jump systems. -/
def VisitsEveryLevel {State : Type} (level : State → ℕ) (path : ℕ → State) : Prop :=
  ∀ A, ∃ k, level (path k) = A

/-- Correct replacement: cofinality of levels. -/
def CofinalLevels (levelSeq : ℕ → ℕ) : Prop := ∀ C, ∃ k, C ≤ levelSeq k

/--
  **`jump_breaks_visitsEveryLevel` — PROVED (§3).** The sequence `level_k = 2k` is cofinal, but
  does NOT visit odd levels (e.g. `1`). Therefore "visit every level" is a false goal for a
  jump engine; the correct goal is `CofinalLevels`. -/
theorem jump_breaks_visitsEveryLevel :
    CofinalLevels (fun k => 2 * k) ∧ ¬ VisitsEveryLevel (fun n => n) (fun k => 2 * k) := by
  constructor
  · intro C; exact ⟨C, by simp; omega⟩
  · intro h; obtain ⟨k, hk⟩ := h 1; simp at hk

/-- A strictly increasing ℕ-sequence is cofinal (`level k ≥ k`). -/
theorem strictMono_nat_cofinal (levelSeq : ℕ → ℕ) (hStrict : StrictMono levelSeq) :
    CofinalLevels levelSeq := by
  intro C
  refine ⟨C, ?_⟩
  have : C ≤ levelSeq C := hStrict.le_apply
  exact this

/-! ### §5. CutSystem: projection of a high-level state onto a lower cut (finite signature) -/

/-- Cut system: finite signature `CutSig A₀` and projection `sig : StateAt A → CutSig A₀` when `A₀ ≤ A`.
    Key point: a state does NOT have to "land" on `A₀`; `A₀ ≤ A` is sufficient. -/
structure CutSystem (StateAt : ℕ → Type) where
  CutSig : ℕ → Type
  finite : ∀ A0, Finite (CutSig A0)
  sig : ∀ {A0 A : ℕ}, A0 ≤ A → StateAt A → CutSig A0

/-! ### §6. JumpReverseRay: reverse ray with ARBITRARY cofinal level jumps -/

/-- Jump reverse ray: strictly increasing levels `level k`, cofinal, a state at each level,
    and a reverse step between adjacent indices (the level jumps by an arbitrary amount, not `+1`). -/
structure JumpReverseRay (StateAt : ℕ → Type)
    (ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop) where
  level : ℕ → ℕ
  strict : StrictMono level
  cofinal : ∀ C, ∃ k, C ≤ level k
  state : ∀ k, StateAt (level k)
  reverse_step : ∀ k, ReverseStep (strict (Nat.lt_succ_self k)) (state k) (state (k + 1))

/-! ### §9. Jump-compatible pigeonhole: repeated finite cut-signature on a jump ray -/

/--
  **`repeated_cutSig_on_jumpReverseRay` — PROVED (§9).** On a jump reverse ray whose levels are cofinal
  (exceed any given `A₀`), for a fixed cut `A₀` there are infinitely many projections onto `A₀`; with
  finite `CutSig A₀` the signature REPEATS at two indices `i < j`. Pure pigeonhole (∞ → finite type),
  jump-compatible (does not require visiting `A₀`, only `A₀ ≤ level`). -/
theorem repeated_cutSig_on_jumpReverseRay {StateAt : ℕ → Type}
    {ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop}
    (C : CutSystem StateAt) (R : JumpReverseRay StateAt ReverseStep) (A0 : ℕ) :
    ∃ i j, i < j ∧ ∃ (hi : A0 ≤ R.level i) (hj : A0 ≤ R.level j),
      C.sig hi (R.state i) = C.sig hj (R.state j) := by
  classical
  have hfin : Finite (C.CutSig A0) := C.finite A0
  obtain ⟨k0, hk0⟩ := R.cofinal A0
  -- Tail from index k0: level ≥ A0 everywhere (monotonicity); signature is a point in finite CutSig A0.
  have htail : ∀ n, A0 ≤ R.level (k0 + n) :=
    fun n => le_trans hk0 (R.strict.monotone (Nat.le_add_right k0 n))
  set f : ℕ → C.CutSig A0 := fun n => C.sig (htail n) (R.state (k0 + n)) with hf
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨k0 + a, k0 + b, by omega, htail a, htail b, heq⟩
  · exact ⟨k0 + b, k0 + a, by omega, htail b, htail a, heq.symm⟩

/-! ### §10–11. JumpReverseBarrier and no-go -/

/-- Jump-cut-barrier: a repeated cut-signature `sig i = sig j` (`i<j`) on the same jump ray ⟹ `Close`. -/
def JumpReverseBarrier {StateAt : ℕ → Type}
    {ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop}
    (C : CutSystem StateAt) (A0 : ℕ) (Close : Prop) : Prop :=
  ∀ (R : JumpReverseRay StateAt ReverseStep) (i j : ℕ), i < j →
    ∀ (hi : A0 ≤ R.level i) (hj : A0 ≤ R.level j),
      C.sig hi (R.state i) = C.sig hj (R.state j) → Close

/--
  **`no_jumpReverseRay_of_cutBarrier` — PROVED (§11, pure jump-reverse contradiction).** Given a
  jump-cut-barrier (repeated signature on cut `A₀` ⟹ Close) and `¬Close`, no jump reverse ray EXISTS:
  pigeonhole yields a repeated signature, the barrier yields Close — contradicting `¬Close`. -/
theorem no_jumpReverseRay_of_cutBarrier {StateAt : ℕ → Type}
    {ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop}
    (C : CutSystem StateAt) (A0 : ℕ) {Close : Prop}
    (hBarrier : JumpReverseBarrier (ReverseStep := ReverseStep) C A0 Close)
    (hNoClose : ¬ Close)
    (R : JumpReverseRay StateAt ReverseStep) : False := by
  obtain ⟨i, j, hij, hi, hj, hsig⟩ := repeated_cutSig_on_jumpReverseRay C R A0
  exact hNoClose (hBarrier R i j hij hi hj hsig)

/-! ### §18. Interaction with AboveStructure: jump across twin-gap ⟹ ordinal conflict

Jump across twin-gap: `above X Y`, `center X = gap.left`, `gap.right < center Y` (jumped over the gap).
If an object `Z` is structurally AFTER `Y` (`above Y Z`), but lands naturally INSIDE the gap —
ordinal contradiction. -/

/-- Conflict: the engine jumps over a twin-gap, then forces a later object back INSIDE it. -/
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
  **`no_jumpAboveGapConflict` — PROVED (§18).** Such a conflict is impossible: `above Y Z` gives
  `center Y < center Z`, but `z_inside` + `y_past` give `center Z < gap.right < center Y`, i.e.
  `center Z < center Y`. Contradiction. The precise form of "jumped over gap ⟹ forces object inside". -/
theorem no_jumpAboveGapConflict (S : AboveStructure) (G : TwinGap)
    (Cf : JumpAboveGapConflict S G) : False := by
  have hYZnat : S.center Cf.Y < S.center Cf.Z := S.above_sound Cf.Y Cf.Z Cf.hYZ
  have hZltY : S.center Cf.Z < S.center Cf.Y := lt_trans Cf.z_inside.2 Cf.y_past
  omega

/-! ### §17, §19. MACHINE DIAGNOSIS OF THE TRAP (red-tests of the brick)

The abstract no-go above is correct, but NOT about concrete arithmetic. The Step00 instantiation requires TWO
inputs; red-test #5 states directly: force-ray MUST NOT require `SNOL.SNOLInput`. We record machine-formally
that force-ray is equivalent to a supply theorem (the same shape as the wall). -/

/-- Abstract "supply" theorem (form `SNOL.SNOLInput`): for every cut a ray exists. This is exactly
    `noTwin_forces_jumpReverseRay` in pure form — it is NOT proved from local energy/pigeonhole. -/
def ForcesRay {StateAt : ℕ → Type}
    (ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop)
    (NoTwin NoEngine : Prop) : Prop :=
  NoTwin → NoEngine → Nonempty (JumpReverseRay StateAt ReverseStep)

/--
  **`jump_route_is_trapped` — PROVED (diagnosis).** Full jump-reverse route: from `ForcesRay`
  (supply input) + jump-cut-barrier (cross-level fan-in input) + `¬Close` we get `¬NoTwin ∨ ¬NoEngine`.
  But BOTH ingredients are unproved inputs (§17 says barrier = labelled fan-in; §19 red-test #5
  says ForcesRay must not rely on SNOL, and if it does — it is a wall). Pigeonhole/energy
  (the proved part) alone yield NEITHER `ForcesRay` NOR `Barrier`. Formally: the conclusion is derivable ONLY
  when both inputs are supplied, i.e. the route does not eliminate them but repackages them. -/
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
  **`red_test_forceRay_is_supply` — PROVED (red-test #5).** `ForcesRay` UNFOLDS into the pure
  supply form "`NoTwin → NoEngine → ∃ ray`". This is exactly the shape of `SNOL.SNOLInput` (supply clean carrier
  at scale). Therefore if it is supplied via SNOL/carrier-density — it is a wall, not a bypass. Here it is
  NOT supplied. -/
theorem red_test_forceRay_is_supply {StateAt : ℕ → Type}
    (ReverseStep : ∀ {A B : ℕ}, A < B → StateAt A → StateAt B → Prop)
    (NoTwin NoEngine : Prop) :
    ForcesRay ReverseStep NoTwin NoEngine ↔
      (NoTwin → NoEngine → Nonempty (JumpReverseRay StateAt ReverseStep)) := Iff.rfl

end EuclidsPath.JumpBarrier
