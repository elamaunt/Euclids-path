/-
  Euclid's perpetual engine — formal IMPOSSIBILITY (EPMI).

  This file is SELF-CONTAINED: it uses only the Lean 4 kernel (no mathlib),
  so it is checked by the compiler quickly with the command:

      lean EuclidsPath/Engine/EPMI.lean

  Prose: prose/06_EuclideanPerpetualEngine.md, prose/16_MultiRankFanCycle.md
  Source of ideas: euclidean_perpetual_engine_…29 (Def. 11.1, Thm. 10.3);
                 BE_UPDATED §73–77 (Thm. 77.1);
                 twin_prime_new_layers_after_BE_update_… §IV, §XI.

  Substantive essence: the "state" of the engine reduces to its height — the natural
  index of the center m. One successful clean-descent strictly reduces the height by ≥ A times
  (A·m' < m). An infinite chain of such descents is impossible, because
  H(S_t) < H(S_0)/Aᵗ < 1 for large t, and the height is a positive integer.
  This is exactly "no Euclidean perpetual engine" = Fermat's infinite descent.

  (We use `Nat` rather than the notation `ℕ`: in the prelude without mathlib `ℕ` is not available.)
-/
set_option autoImplicit false

namespace EuclidsPath.Engine

/-- One successful clean-descent: the new height `h'` is ≥ `A` times smaller than the old `h`. -/
def DescentStep (A h h' : Nat) : Prop := A * h' < h

/-- With `A ≥ 1` a descent step strictly reduces the height: `A·h' < h ⇒ h' < h`. -/
theorem descent_strict {A h h' : Nat} (hA : 1 ≤ A) (hstep : DescentStep A h h') :
    h' < h := by
  have h1 : h' ≤ A * h' := Nat.le_mul_of_pos_left h' hA
  unfold DescentStep at hstep
  omega

/--
  **EPMI (downward), abstract form.**
  There is no infinite sequence of heights `H : Nat → Nat` in which every step is
  a successful `A`-descent (`A ≥ 1`). That is, the perpetual engine as an infinite clean descent chain
  is impossible.
-/
theorem no_infinite_descent {A : Nat} (hA : 1 ≤ A)
    (H : Nat → Nat) (hchain : ∀ t, DescentStep A (H t) (H (t + 1))) : False := by
  -- for each step: H (t+1) ≤ A * H (t+1)
  have hle : ∀ t, H (t + 1) ≤ A * H (t + 1) := fun t => Nat.le_mul_of_pos_left _ hA
  -- the quantity H t + t is non-increasing, hence bounded by H 0
  have hbound : ∀ t, H t + t ≤ H 0 := by
    intro t
    induction t with
    | zero => omega
    | succ n ih =>
      have hc := hchain n
      unfold DescentStep at hc            -- A * H (n+1) < H n
      have hl := hle n                     -- H (n+1) ≤ A * H (n+1)
      omega
  -- at t = H 0 + 1 we get H(...) + (H 0 + 1) ≤ H 0 — contradiction
  have hbad := hbound (H 0 + 1)
  omega

/-! ### Structured form: state, descent operator, boundary-exit -/

/-- State of the engine. Substantively — the center `m` of the pair `(6m-1, 6m+1)`; height = `m`. -/
structure State where
  height : Nat

/--
  Result of the partial clean descent operator `D_a`:
  * `clean s'` — a successful descent into a clean state of strictly smaller height (`A·s'.height < s.height`);
  * `boundary` — an absorbing exit `⊥` (the descended center left the clean-core).
-/
inductive Step (A : Nat) (s : State) where
  | clean (s' : State) (h : A * s'.height < s.height)
  | boundary

/--
  **EPMI (structured).** There is no infinite trajectory `run : Nat → State` in which every step is
  a successful `clean` descent. (Boundary-exit terminates the branch; see `Step.boundary`.)
-/
theorem no_perpetual_engine {A : Nat} (hA : 1 ≤ A)
    (run : Nat → State)
    (clean_step : ∀ t, A * (run (t + 1)).height < (run t).height) : False :=
  no_infinite_descent hA (fun t => (run t).height) (fun t => clean_step t)

/--
  The boundary leaf is absorbing: every step is either a successful `clean` or a `boundary`.
  Substantively this is the canonical fixation of the dichotomy "the descended center either stays clean
  or exits to the boundary `⊥`" (Lemma 74.1 / §4.2). From `boundary` there is no clean continuation
  of the same branch — that would require a successful `clean` step, which `boundary` is not.
-/
theorem boundary_dichotomy {A : Nat} {s : State} (st : Step A s) :
    (∃ s' h, st = Step.clean s' h) ∨ st = Step.boundary := by
  cases st with
  | clean s' h => exact Or.inl ⟨s', h, rfl⟩
  | boundary => exact Or.inr rfl

end EuclidsPath.Engine
