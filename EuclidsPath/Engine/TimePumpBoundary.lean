/-
  TimePumpBoundary.lean — the SOUND twin boundary in time-pump form.

  Extracted from Step00CompletePatch (Part IV) and placed UPSTREAM of the first-cause
  axiom, so that `Step00CausalClosureAxiom` can be re-pointed from the refuted
  finite-key obligation `TheStrictLastStep00Obligation` to `TimePumpStep00Obligation`.

  `TimePumpStep00Obligation` is provably EQUIVALENT to "twin centers are unbounded"
  (= the twin-prime conjecture); it implies `TwinLowers.Infinite` unconditionally and
  is NOT refutable by the adic-flow construction that killed the old boundary.
-/
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.HigherEnergy
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

open EuclidsPath.Residuals
open EuclidsPath.HigherEnergy

/-!
## Time pump — "time cannot stop"

A live state must either close or tick.  If close never occurs, well-founded
descent forbids the live state from existing.
-/

structure TimeSerialRankEngine
    (σ : Type)
    (Step : σ → σ → Prop) where
  Live : σ → Prop
  Close : σ → Prop
  Rank : σ → ℕ
  step_or_close :
    ∀ x, Live x → Close x ∨ ∃ y, Live y ∧ Step x y
  rank_drops :
    ∀ {x y : σ}, Live x → Step x y → Rank y < Rank x

theorem timeSerialRankEngine_forces_close
    {σ : Type}
    {Step : σ → σ → Prop}
    (E : TimeSerialRankEngine σ Step)
    (hStart : ∃ x, E.Live x) :
    ∃ x, E.Live x ∧ E.Close x := by
  by_contra hNoCloseExists
  have hNoClose :
      ∀ x, E.Live x → ¬ E.Close x := by
    intro x hx hcx
    exact hNoCloseExists ⟨x, hx, hcx⟩
  have hNoLive :
      ¬ ∃ x, E.Live x := by
    exact no_live_state_if_closes_or_moves_down
      E.Live
      E.Close
      (fun x y => E.Live x ∧ Step x y)
      (fun x => (E.Rank x, 0))
      (by
        intro x hx
        rcases E.step_or_close x hx with hClose | ⟨y, hyLive, hStep⟩
        · exact Or.inl hClose
        · exact Or.inr ⟨y, hyLive, hx, hStep⟩)
      hNoClose
      (by
        intro x y hMove
        exact Or.inl (E.rank_drops hMove.1 hMove.2))
  exact hNoLive hStart

def TwinClose (M0 : ℕ) : State → Prop
  | State.center m => M0 < m ∧ TwinCenterZ m
  | _              => False

structure TimeStopViolation
    (A M0 : ℕ)
    (Live : State → Prop)
    (U : State) : Prop where
  live : Live U
  not_twin : ¬ TwinClose M0 U
  stuck : ¬ ∃ V, Live V ∧ ProperRealStep A M0 U V

def TimeClose
    (A M0 : ℕ)
    (Live : State → Prop)
    (U : State) : Prop :=
  TwinClose M0 U ∨ TimeStopViolation A M0 Live U

structure ProperTimePumpEngine (A M0 : ℕ) where
  Live : State → Prop
  start_live : ∃ U, Live U
  step_or_close :
    ∀ U, Live U →
      TimeClose A M0 Live U ∨
      ∃ V, Live V ∧ ProperRealStep A M0 U V

def ProperTimePumpEngine.toRankEngine
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    TimeSerialRankEngine State (ProperRealStep A M0) where
  Live := E.Live
  Close := TimeClose A M0 E.Live
  Rank := lexRank
  step_or_close := E.step_or_close
  rank_drops := by
    intro U V hLive hStep
    exact lexRank_strict_decrease_on_RealStep
      (properRealStep_to_realStep hStep)

theorem properTimePumpEngine_forces_close
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    ∃ U, E.Live U ∧ TimeClose A M0 E.Live U := by
  exact timeSerialRankEngine_forces_close
    E.toRankEngine
    E.start_live

theorem properTimePumpEngine_forces_twin_or_violation
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    (∃ m : ℕ, M0 < m ∧ TwinCenterZ m) ∨
    (∃ U : State, E.Live U ∧ TimeStopViolation A M0 E.Live U) := by
  obtain ⟨U, hLive, hClose⟩ :=
    properTimePumpEngine_forces_close E
  rcases hClose with hTwin | hViolation
  · cases U with
    | center m =>
        exact Or.inl ⟨m, hTwin.1, hTwin.2⟩
    | defect n q s =>
        simp [TwinClose] at hTwin
    | absorber n =>
        simp [TwinClose] at hTwin
  · exact Or.inr ⟨U, hLive, hViolation⟩

theorem properTimePumpEngine_forces_twin
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    (hNoViolation :
      ∀ U, E.Live U → ¬ TimeStopViolation A M0 E.Live U) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  rcases properTimePumpEngine_forces_twin_or_violation E with hTwin | hBad
  · exact hTwin
  · rcases hBad with ⟨U, hLive, hViolation⟩
    exact False.elim ((hNoViolation U hLive) hViolation)

abbrev TimePumpStep00Obligation : Prop :=
  ∀ M0 : ℕ,
    ∃ A : ℕ,
      ∃ E : ProperTimePumpEngine A M0,
        ∀ U, E.Live U → ¬ TimeStopViolation A M0 E.Live U

theorem twinCenters_unbounded_of_timePumpStep00
    (H : TimePumpStep00Obligation) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  rcases H M0 with ⟨A, E, hNoViolation⟩
  exact properTimePumpEngine_forces_twin E hNoViolation

theorem twinLowersInfinite_of_timePumpStep00
    (H : TimePumpStep00Obligation) :
    TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ :=
    twinCenters_unbounded_of_timePumpStep00 H N
  refine ⟨m, hNm, ?_⟩
  simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ

theorem timePumpStep00_generates_twins :
    TimePumpStep00Obligation → TwinLowers.Infinite :=
  twinLowersInfinite_of_timePumpStep00

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
