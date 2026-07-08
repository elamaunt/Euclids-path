import EuclidsPath.Engine.TimePumpBoundary

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 minimal reachable rank patch

This file records the strict proof logic behind the sentence:

  if time is forced to move from every live non-close state,
  and every move strictly spends one well-founded rank,
  then from any live start a close state is reached after finitely many moves.

For `ProperTimePumpEngine`, `Close` is exactly:

  TwinClose M0 U ∨ TimeStopViolation A M0 Live U.

So, if time-stop violations are forbidden, the close state must be a twin witness.
If a twin bound is also assumed, the engine plus no-violation gives `False`.

No new Step00 principle is introduced here.  This is only the minimal-reachable-rank
proof of the already existing time-pump boundary.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace MinimalReachableRankPatch

open EuclidsPath.Residuals

/-- Finite reachability by repeatedly taking `Step` edges.  This is deliberately
local and independent of any Mathlib relation API, so the patch remains mechanical. -/
inductive Reachable {σ : Type} (Step : σ → σ → Prop) : σ → σ → Prop where
  | refl {x : σ} : Reachable Step x x
  | cons {x y z : σ} : Step x y → Reachable Step y z → Reachable Step x z

namespace Reachable

/-- Compose two finite reachability witnesses. -/
theorem trans {σ : Type} {Step : σ → σ → Prop} {x y z : σ}
    (hxy : Reachable Step x y) (hyz : Reachable Step y z) :
    Reachable Step x z := by
  induction hxy with
  | refl => exact hyz
  | cons hStep hRest ih => exact Reachable.cons hStep (ih hyz)

end Reachable

/--
Minimal-reachable-rank form of the time argument.

From any live state, a `TimeSerialRankEngine` reaches a close state by finitely
many moves.  The proof is strong induction on `Rank x`: if `x` is already close,
we are done; otherwise time supplies a live successor `y`, and `Rank y < Rank x`,
so induction applies to `y`.
-/
theorem timeSerialRankEngine_reaches_close_from_live
    {σ : Type}
    {Step : σ → σ → Prop}
    (E : TimeSerialRankEngine σ Step)
    {x : σ}
    (hx : E.Live x) :
    ∃ z : σ, E.Live z ∧ E.Close z ∧ Reachable Step x z := by
  exact
    (Nat.strongRecOn (E.Rank x)
      (motive := fun n =>
        ∀ x : σ, E.Live x → E.Rank x = n →
          ∃ z : σ, E.Live z ∧ E.Close z ∧ Reachable Step x z)
      (fun n ih x hx hRankEq => by
        rcases E.step_or_close x hx with hClose | hMove
        · exact ⟨x, hx, hClose, Reachable.refl⟩
        · rcases hMove with ⟨y, hyLive, hStep⟩
          have hDrop : E.Rank y < E.Rank x :=
            E.rank_drops hx hStep
          have hyLtN : E.Rank y < n := by
            simpa [hRankEq] using hDrop
          obtain ⟨z, hzLive, hzClose, hyz⟩ :=
            ih (E.Rank y) hyLtN y hyLive rfl
          exact ⟨z, hzLive, hzClose, Reachable.cons hStep hyz⟩))
      x hx rfl

/-- Global close existence, but now obtained through the finite reachable-rank
argument rather than by contradiction with an infinite run. -/
theorem timeSerialRankEngine_forces_close_by_minimalReachableRank
    {σ : Type}
    {Step : σ → σ → Prop}
    (E : TimeSerialRankEngine σ Step)
    (hStart : ∃ x : σ, E.Live x) :
    ∃ z : σ, E.Live z ∧ E.Close z := by
  rcases hStart with ⟨x, hx⟩
  rcases timeSerialRankEngine_reaches_close_from_live E hx with
    ⟨z, hzLive, hzClose, _hzReach⟩
  exact ⟨z, hzLive, hzClose⟩

/-- Same theorem with the reachable path retained. -/
theorem timeSerialRankEngine_reaches_close_from_start
    {σ : Type}
    {Step : σ → σ → Prop}
    (E : TimeSerialRankEngine σ Step)
    (hStart : ∃ x : σ, E.Live x) :
    ∃ x z : σ, E.Live x ∧ E.Live z ∧ E.Close z ∧ Reachable Step x z := by
  rcases hStart with ⟨x, hx⟩
  rcases timeSerialRankEngine_reaches_close_from_live E hx with
    ⟨z, hzLive, hzClose, hxz⟩
  exact ⟨x, z, hx, hzLive, hzClose, hxz⟩

/-- Specialization to the existing proper time-pump engine. -/
theorem properTimePumpEngine_reaches_timeClose_from_live
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    {U : State}
    (hU : E.Live U) :
    ∃ W : State,
      E.Live W ∧
      TimeClose A M0 E.Live W ∧
      Reachable (ProperRealStep A M0) U W := by
  exact timeSerialRankEngine_reaches_close_from_live
    E.toRankEngine hU

/-- From the engine start, a `TimeClose` state is finitely reachable. -/
theorem properTimePumpEngine_reaches_timeClose_from_start
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    ∃ U W : State,
      E.Live U ∧
      E.Live W ∧
      TimeClose A M0 E.Live W ∧
      Reachable (ProperRealStep A M0) U W := by
  rcases E.start_live with ⟨U, hU⟩
  rcases properTimePumpEngine_reaches_timeClose_from_live E hU with
    ⟨W, hWLive, hClose, hReach⟩
  exact ⟨U, W, hU, hWLive, hClose, hReach⟩

/-- Under a twin bound above `M0`, no `TwinClose M0 U` can occur. -/
theorem not_twinClose_of_twinBound
    {M0 : ℕ}
    (hBound : TwinBoundAbove M0)
    (U : State) :
    ¬ TwinClose M0 U := by
  intro hTwin
  cases U with
  | center m =>
      exact hBound m hTwin.1 hTwin.2
  | defect n q s =>
      exact hTwin
  | absorber n =>
      exact hTwin

/-- If a proper time-pump engine runs under a twin bound, then the finite close
reached by minimal-rank descent cannot be a twin close; hence it is a concrete
`TimeStopViolation`. -/
theorem properTimePumpEngine_reaches_violation_under_twinBound
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    (hBound : TwinBoundAbove M0) :
    ∃ U : State, E.Live U ∧ TimeStopViolation A M0 E.Live U := by
  rcases properTimePumpEngine_reaches_timeClose_from_start E with
    ⟨_U0, W, _hU0Live, hWLive, hClose, _hReach⟩
  rcases hClose with hTwin | hViolation
  · exact False.elim ((not_twinClose_of_twinBound hBound W) hTwin)
  · exact ⟨W, hWLive, hViolation⟩

/-- The core contradiction in the user's words:

  assume the engine is obliged to move, assume it is under a twin boundary,
  assume stopping inside that boundary is forbidden; the minimal reachable rank
  argument forces a stop violation anyway.
-/
theorem twinBound_and_noViolation_impossible_by_minimalReachableRank
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    (hBound : TwinBoundAbove M0)
    (hNoViolation :
      ∀ U : State, E.Live U → ¬ TimeStopViolation A M0 E.Live U) :
    False := by
  rcases properTimePumpEngine_reaches_violation_under_twinBound E hBound with
    ⟨U, hULive, hViolation⟩
  exact (hNoViolation U hULive) hViolation

/-- Equivalently: a no-violation proper time-pump engine refutes any twin bound
above `M0`. -/
theorem noViolation_engine_refutes_twinBound_by_minimalReachableRank
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    (hNoViolation :
      ∀ U : State, E.Live U → ¬ TimeStopViolation A M0 E.Live U) :
    ¬ TwinBoundAbove M0 := by
  intro hBound
  exact twinBound_and_noViolation_impossible_by_minimalReachableRank
    E hBound hNoViolation

/-- Direct witness form: a no-violation proper time-pump engine forces a twin
center above the boundary.  This is the finite minimal-rank version of the
existing `properTimePumpEngine_forces_twin`. -/
theorem noViolation_engine_forces_twin_by_minimalReachableRank
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    (hNoViolation :
      ∀ U : State, E.Live U → ¬ TimeStopViolation A M0 E.Live U) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  rcases properTimePumpEngine_reaches_timeClose_from_start E with
    ⟨_U0, W, _hU0Live, hWLive, hClose, _hReach⟩
  rcases hClose with hTwin | hViolation
  · cases W with
    | center m =>
        exact ⟨m, hTwin.1, hTwin.2⟩
    | defect n q s =>
        exact False.elim hTwin
    | absorber n =>
        exact False.elim hTwin
  · exact False.elim ((hNoViolation W hWLive) hViolation)

/-- Step00-level unboundedness from the minimal reachable rank proof. -/
theorem twinCenters_unbounded_of_timePumpStep00_by_minimalReachableRank
    (H : TimePumpStep00Obligation) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  rcases H M0 with ⟨A, E, hNoViolation⟩
  exact noViolation_engine_forces_twin_by_minimalReachableRank
    E hNoViolation

/-- Final twin-lower infinitude from the minimal reachable rank proof. -/
theorem twinLowersInfinite_of_timePumpStep00_by_minimalReachableRank
    (H : TimePumpStep00Obligation) :
    TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ :=
    twinCenters_unbounded_of_timePumpStep00_by_minimalReachableRank H N
  refine ⟨m, hNm, ?_⟩
  simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ

end MinimalReachableRankPatch
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
