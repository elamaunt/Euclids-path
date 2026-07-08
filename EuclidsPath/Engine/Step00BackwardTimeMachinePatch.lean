/-
  EuclidsPath.Engine.Step00BackwardTimeMachinePatch

  Companion patch: the "time machine" layer.

  This file formalizes the exact proof logic discussed in the chat:

    * a live time-machine cannot stop;
    * every backward tick strictly decreases a well-founded natural rank;
    * therefore such a machine cannot be perpetual;
    * in the concrete Step00 graph, `ProperRealStep` is a backward tick because
      it strictly decreases `lexRank`;
    * consequently, any live time-pump engine must reach a close event;
    * if close is `TwinClose ∨ TimeStopViolation`, then under `TwinBoundAbove`
      and no stop-violation the engine is impossible.

  The file is intentionally a companion patch.  It does not replace the old
  finite-key Step00 branch.  It provides a precise mathematical layer for the
  slogan:

      "A time machine that must keep moving backward is an impossible
       perpetual engine."
-/

import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.HigherEnergy
import EuclidsPath.Engine.TimePumpBoundary

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace BackwardTimeMachinePatch

open EuclidsPath.HigherEnergy
open EuclidsPath.Residuals

/-!
## 1. Generic backward time machine

A `BackwardTimeMachine` is deliberately minimal:

* `Live x` says that state `x` is still inside live time.
* `Step x y` is one tick of the machine.
* `Rank x : ℕ` is the finite time/fuel rank.
* `start_live` says the machine starts somewhere.
* `time_cannot_stop` says every live state has a next live tick.
* `step_goes_backward` says every tick strictly decreases the rank.

The contradiction is pure well-foundedness of `ℕ`.
-/

structure BackwardTimeMachine
    (σ : Type)
    (Step : σ → σ → Prop) where
  Live : σ → Prop
  Rank : σ → ℕ
  start_live : ∃ x : σ, Live x
  time_cannot_stop :
    ∀ x : σ, Live x → ∃ y : σ, Live y ∧ Step x y
  step_goes_backward :
    ∀ {x y : σ}, Live x → Step x y → Rank y < Rank x

/--
A backward machine has no live state at all, if it has no close event and must
always move to a strictly smaller rank.

This is the core "backward time = impossible perpetual engine" theorem.
-/
theorem BackwardTimeMachine.no_live_state
    {σ : Type}
    {Step : σ → σ → Prop}
    (M : BackwardTimeMachine σ Step) :
    ¬ ∃ x : σ, M.Live x := by
  exact no_live_state_if_closes_or_moves_down
    M.Live
    (fun _ : σ => False)
    (fun x y => M.Live x ∧ Step x y)
    (fun x => (M.Rank x, 0))
    (by
      intro x hx
      rcases M.time_cannot_stop x hx with ⟨y, hyLive, hStep⟩
      exact Or.inr ⟨y, hyLive, hx, hStep⟩)
    (by
      intro x _ hFalse
      exact False.elim hFalse)
    (by
      intro x y hMove
      exact Or.inl (M.step_goes_backward hMove.1 hMove.2))

/--
No `BackwardTimeMachine` can exist.
-/
theorem BackwardTimeMachine.impossible
    {σ : Type}
    {Step : σ → σ → Prop}
    (M : BackwardTimeMachine σ Step) : False := by
  exact M.no_live_state M.start_live

/-!
## 2. Explicit rank exhaustion along a given run

The previous theorem avoids explicitly constructing an infinite run.  This
section records the more concrete fuel-spending statement: if a run exists and
rank strictly decreases at every tick, then after `n` ticks at least `n` units of
rank have been spent.
-/

def BackwardRun
    {σ : Type}
    (Live : σ → Prop)
    (Step : σ → σ → Prop)
    (run : ℕ → σ) : Prop :=
  (∀ n : ℕ, Live (run n)) ∧
  (∀ n : ℕ, Step (run n) (run (n + 1)))

/--
Budget inequality: after `n` backward ticks, rank plus elapsed time is still at
most the initial rank.
-/
theorem backward_run_rank_budget
    {σ : Type}
    {Step : σ → σ → Prop}
    (M : BackwardTimeMachine σ Step)
    (run : ℕ → σ)
    (hRun : BackwardRun M.Live Step run) :
    ∀ n : ℕ, M.Rank (run n) + n ≤ M.Rank (run 0) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hLiveN : M.Live (run n) := hRun.1 n
      have hStepN : Step (run n) (run (n + 1)) := hRun.2 n
      have hDrop : M.Rank (run (n + 1)) < M.Rank (run n) :=
        M.step_goes_backward hLiveN hStepN
      omega

/--
After `n` ticks the machine has spent at least `n` units of rank.
-/
theorem backward_run_spends_at_least_elapsed_time
    {σ : Type}
    {Step : σ → σ → Prop}
    (M : BackwardTimeMachine σ Step)
    (run : ℕ → σ)
    (hRun : BackwardRun M.Live Step run) :
    ∀ n : ℕ, n ≤ M.Rank (run 0) - M.Rank (run n) := by
  intro n
  have hBudget := backward_run_rank_budget M run hRun n
  omega

/--
No infinite run can satisfy the backward machine conditions.
-/
theorem backward_run_impossible
    {σ : Type}
    {Step : σ → σ → Prop}
    (M : BackwardTimeMachine σ Step)
    (run : ℕ → σ)
    (hRun : BackwardRun M.Live Step run) : False := by
  have hBudget := backward_run_rank_budget M run hRun (M.Rank (run 0) + 1)
  omega

/-!
## 3. Time machine with close events

The non-stopping machine is impossible.  The useful Step00 form is therefore a
machine that may close.  If it cannot close, it becomes the impossible backward
perpetual engine above.  Hence any live machine must reach a close event.
-/

structure BackwardTimeMachineWithClose
    (σ : Type)
    (Step : σ → σ → Prop) where
  Live : σ → Prop
  Close : σ → Prop
  Rank : σ → ℕ
  start_live : ∃ x : σ, Live x
  time_moves_or_closes :
    ∀ x : σ, Live x → Close x ∨ ∃ y : σ, Live y ∧ Step x y
  step_goes_backward :
    ∀ {x y : σ}, Live x → Step x y → Rank y < Rank x

/--
A live backward-time machine with close events must close somewhere.
-/
theorem BackwardTimeMachineWithClose.forces_close
    {σ : Type}
    {Step : σ → σ → Prop}
    (M : BackwardTimeMachineWithClose σ Step) :
    ∃ x : σ, M.Live x ∧ M.Close x := by
  by_contra hNoCloseExists
  have hNoClose : ∀ x : σ, M.Live x → ¬ M.Close x := by
    intro x hx hcx
    exact hNoCloseExists ⟨x, hx, hcx⟩

  let N : BackwardTimeMachine σ Step :=
    { Live := M.Live
      Rank := M.Rank
      start_live := M.start_live
      time_cannot_stop := by
        intro x hx
        rcases M.time_moves_or_closes x hx with hClose | hMove
        · exact False.elim ((hNoClose x hx) hClose)
        · exact hMove
      step_goes_backward := M.step_goes_backward }

  exact N.impossible

/-!
## 4. Concrete specialization to `ProperRealStep`

In the Step00 graph, the backward rank is `lexRank`.  A `ProperRealStep` is a
valid backward tick because it is converted to `RealStep`, and every `RealStep`
strictly decreases `lexRank`.
-/

structure ProperBackwardTimeMachine (A M0 : ℕ) where
  Live : State → Prop
  start_live : ∃ U : State, Live U
  time_cannot_stop :
    ∀ U : State, Live U → ∃ V : State, Live V ∧ ProperRealStep A M0 U V

/--
A concrete non-stopping time machine whose ticks are `ProperRealStep`s is
impossible.
-/
def ProperBackwardTimeMachine.toBackwardTimeMachine
    {A M0 : ℕ}
    (M : ProperBackwardTimeMachine A M0) :
    BackwardTimeMachine State (ProperRealStep A M0) where
  Live := M.Live
  Rank := lexRank
  start_live := M.start_live
  time_cannot_stop := M.time_cannot_stop
  step_goes_backward := by
    intro U V _ hStep
    exact lexRank_strict_decrease_on_RealStep
      (properRealStep_to_realStep hStep)

theorem ProperBackwardTimeMachine.impossible
    {A M0 : ℕ}
    (M : ProperBackwardTimeMachine A M0) : False := by
  exact M.toBackwardTimeMachine.impossible

/--
A concrete proper run spends one unit of `lexRank` per tick.
-/
theorem proper_backward_run_lexRank_budget
    {A M0 : ℕ}
    (M : ProperBackwardTimeMachine A M0)
    (run : ℕ → State)
    (hRun : BackwardRun M.Live (ProperRealStep A M0) run) :
    ∀ n : ℕ, lexRank (run n) + n ≤ lexRank (run 0) := by
  exact backward_run_rank_budget M.toBackwardTimeMachine run hRun

/--
There is no infinite concrete proper backward run.
-/
theorem proper_backward_run_impossible
    {A M0 : ℕ}
    (M : ProperBackwardTimeMachine A M0)
    (run : ℕ → State)
    (hRun : BackwardRun M.Live (ProperRealStep A M0) run) : False := by
  exact backward_run_impossible M.toBackwardTimeMachine run hRun

/-!
## 5. Concrete machine with `TwinClose ∨ TimeStopViolation`

This section attaches the generic close theorem to the Step00 time-pump
objects already used in the project.
-/

/--
A `ProperTimePumpEngine` is a backward-time machine with close events.
-/
def ProperTimePumpEngine.toBackwardTimeMachineWithClose
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    BackwardTimeMachineWithClose State (ProperRealStep A M0) where
  Live := E.Live
  Close := TimeClose A M0 E.Live
  Rank := lexRank
  start_live := E.start_live
  time_moves_or_closes := E.step_or_close
  step_goes_backward := by
    intro U V _ hStep
    exact lexRank_strict_decrease_on_RealStep
      (properRealStep_to_realStep hStep)

/--
The time-pump engine must reach either a twin-close or a stop-violation.
This is the precise formal version of: time cannot be a non-stopping backward
perpetual engine.
-/
theorem ProperTimePumpEngine.forces_time_close_by_backward_machine
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    ∃ U : State, E.Live U ∧ TimeClose A M0 E.Live U := by
  exact (ProperTimePumpEngine.toBackwardTimeMachineWithClose E).forces_close

/--
If all stop-violations are forbidden, the engine forces a twin witness.
-/
theorem ProperTimePumpEngine.forces_twin_by_backward_machine
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    (hNoViolation :
      ∀ U : State, E.Live U → ¬ TimeStopViolation A M0 E.Live U) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  obtain ⟨U, hLive, hClose⟩ :=
    ProperTimePumpEngine.forces_time_close_by_backward_machine E
  rcases hClose with hTwin | hViolation
  · cases U with
    | center m =>
        exact ⟨m, hTwin.1, hTwin.2⟩
    | defect n q s =>
        simp [TwinClose] at hTwin
    | absorber n =>
        simp [TwinClose] at hTwin
  · exact False.elim ((hNoViolation U hLive) hViolation)

/--
Under a twin bound and no stop-violation, a live time-pump engine is impossible.
-/
theorem twinBound_and_noViolation_forbid_time_machine
    {A M0 : ℕ}
    (hBound : TwinBoundAbove M0)
    (E : ProperTimePumpEngine A M0)
    (hNoViolation :
      ∀ U : State, E.Live U → ¬ TimeStopViolation A M0 E.Live U) : False := by
  obtain ⟨m, hm, hTwin⟩ :=
    ProperTimePumpEngine.forces_twin_by_backward_machine E hNoViolation
  exact hBound m hm hTwin

/-!
## 6. Step00-level formulation

This is the clean boundary theorem: the temporal Step00 axiom says that for
any horizon there is a live time engine and no illegal stop.  The backward time
machine theorem then turns that into unbounded twin centers.
-/

abbrev TimeCannotStopStep00Obligation : Prop :=
  TimePumpStep00Obligation

/--
The temporal axiom forces unbounded twin centers.
-/
theorem twinCenters_unbounded_of_timeCannotStopStep00
    (H : TimeCannotStopStep00Obligation) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  rcases H M0 with ⟨A, E, hNoViolation⟩
  exact ProperTimePumpEngine.forces_twin_by_backward_machine E hNoViolation

/--
The temporal axiom proves infinitely many twin lower centers.
-/
theorem twinLowersInfinite_of_timeCannotStopStep00
    (H : TimeCannotStopStep00Obligation) :
    TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ :=
    twinCenters_unbounded_of_timeCannotStopStep00 H N
  refine ⟨m, hNm, ?_⟩
  simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ

/--
A compact theorem name for the intended final dependency.
-/
theorem timeCannotStop_generates_twins :
    TimeCannotStopStep00Obligation → TwinLowers.Infinite :=
  twinLowersInfinite_of_timeCannotStopStep00

/-!
## 7. Audit marker

This theorem is meant to be used with `#print axioms`.  If the project declares
an axiom of type `TimeCannotStopStep00Obligation`, final twin theorems should
show that axiom as their only non-standard dependency.
-/

theorem timeCannotStop_dependency_marker
    (H : TimeCannotStopStep00Obligation) :
    TimeCannotStopStep00Obligation :=
  H

end BackwardTimeMachinePatch
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
