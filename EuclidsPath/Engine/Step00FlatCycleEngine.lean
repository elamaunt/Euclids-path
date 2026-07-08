import EuclidsPath.Engine.Step00OrnamentCurvatureReservoir

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 flat-cycle engine — the collapse (flat/zero sign) is a perpetual engine (green) + the wall

Sign convention (as in `Step00RelativeCurvatureInstance`): `NoSafeHole → relIndex = 0` is the FLAT /
collapsed state, and `relIndex = -5` is the CURVED / live state.  So the perpetual engine lives at the
FLAT (zero) configuration; the NEGATIVE curvature is exactly what AVOIDS it.  The honest theorem is
therefore "collapse (a flat, cost-free, but paying closed cycle) ⟹ perpetual engine ⟹ ⊥", whence the
negative sign is forced to persist and a survivor (twin) remains.

## Green here (the engine side, machine-explicit)

  * `FlatCostFreeCycle` — a walk that STRICTLY pays rank on every step yet RETURNS to its start after
    a positive period.  It is the perpetual engine in explicit cyclic form: a paying loop is free
    energy.
  * `no_flatCostFreeCycle` — such a cycle is impossible (a budget telescoping in `ℕ`: `rank + period ≤
    rank`, absurd).  This is the flat-sign → engine → `False` step, axiom-free rank exhaustion.
  * `twin_of_engineForcing` / `twinLowersInfinite_of_engineForcingFamily` — if the collapse forces such
    a cycle, then `¬ NoSafeHole`, a safe hole, a twin — CONDITIONAL on the forcing.

## The wall (named, not proved)

`EngineForcing M0 := NoSafeHoleAbove M0 → FlatCostFreeCycle` — the collapse builds the (impossible)
paying loop.  This is the honest, engine-explicit form of `OrnamentEngineBridge`: more concrete than a
bare `relIndex = -5`, but still the parity barrier — proving `NoSafeHole → FlatCostFreeCycle` uniformly
is the twin lower bound.  `twin_prime_conjecture` stays `sorry`.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace GenealogicalOrnament
namespace FlatEngine

open EuclidsPath.Residuals

/-- A flat cost-free cycle: a walk that strictly spends rank on every one of its `period > 0` steps,
    yet returns to its start.  The paying loop of a perpetual engine — free net motion. -/
structure FlatCostFreeCycle where
  State : Type
  walk : ℕ → State
  rank : State → ℕ
  period : ℕ
  period_pos : 0 < period
  returns : walk period = walk 0
  strictDrop : ∀ n : ℕ, n < period → rank (walk (n + 1)) < rank (walk n)

/-- **Green (axiom-free rank exhaustion): a flat cost-free cycle is impossible.**  Telescoping the
    strict per-step payment gives `rank(walk period) + period ≤ rank(walk 0)`; but the walk returns
    (`rank(walk period) = rank(walk 0)`) and `period > 0` — absurd in `ℕ`. -/
theorem no_flatCostFreeCycle (C : FlatCostFreeCycle) : False := by
  have budget : ∀ n : ℕ, n ≤ C.period → C.rank (C.walk n) + n ≤ C.rank (C.walk 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < C.period := by omega
      have hstep := C.strictDrop k hk'
      have := ih (by omega)
      omega
  have h := budget C.period (le_refl _)
  rw [C.returns] at h
  have := C.period_pos
  omega

/-! ### The route: the collapse forces the (impossible) engine — conditional on the wall -/

/-- **The wall (named, not proved): the collapse builds the impossible paying loop.**  The
    engine-explicit form of `OrnamentEngineBridge`.  Proving it uniformly is the parity barrier.
    Not `Prop` because a `FlatCostFreeCycle` carries data (`State`/`walk`/`rank`), so this is a `Type`. -/
def EngineForcing (M0 : ℕ) := NoSafeHoleAbove M0 → FlatCostFreeCycle

/-- **Green:** if the collapse forces a flat cost-free cycle, the collapse is impossible. -/
theorem not_noSafeHole_of_engineForcing {M0 : ℕ} (H : EngineForcing M0) :
    ¬ NoSafeHoleAbove M0 :=
  fun hno => no_flatCostFreeCycle (H hno)

/-- **Green conditional: engine-forcing yields a twin above `M0`.**  `¬ NoSafeHole` gives a surviving
    center, and `safeHole_implies_twin` makes it a twin. -/
theorem twin_of_engineForcing {M0 : ℕ} (H : EngineForcing M0) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  have h := not_noSafeHole_of_engineForcing H
  unfold NoSafeHoleAbove at h
  push_neg at h
  obtain ⟨m, hM0, hm1, hsafe⟩ := h
  exact ⟨m, hM0, safeHole_implies_twin hm1 hsafe⟩

/-- **Green conditional capstone:** engine-forcing at every horizon yields `TwinLowers.Infinite`.
    Conditional ONLY on the forcing family (the parity barrier); the engine impossibility itself is
    axiom-free.  Does NOT close the twin sorry. -/
theorem twinLowersInfinite_of_engineForcingFamily
    (H : ∀ M0 : ℕ, EngineForcing M0) : TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := twin_of_engineForcing (H N)
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end FlatEngine
end GenealogicalOrnament
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
