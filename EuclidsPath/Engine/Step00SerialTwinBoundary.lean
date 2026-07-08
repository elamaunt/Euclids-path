import EuclidsPath.Engine.TimePumpBoundary

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 twin boundary in seriality form

The transparent, minimal Step00 first-cause boundary:

  "live time cannot stall inside the twin boundary without a witness."

Formally, for every horizon `M0` there is a scale `A` and a live region on which
every non-twin live state has a live proper successor:

  Live U ∧ ¬ TwinClose M0 U → ∃ V, Live V ∧ ProperRealStep A M0 U V.

This file proves that this boundary is EXACTLY the unbounded-twin-centre statement
(and a drop-in for `TimePumpStep00Obligation`).  So adopting it as the accepted
first cause assumes precisely the twin conjecture — no more, no less.  It is a
reduction to a twin-equivalent boundary, NOT a proof of the twin conjecture.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace SerialTwinBoundary

open EuclidsPath.Residuals

/-- The seriality boundary: live time cannot stall inside the twin boundary. -/
def SerialTwinBoundaryObligation : Prop :=
  ∀ M0 : ℕ, ∃ A : ℕ, ∃ Live : State → Prop,
    (∃ U, Live U) ∧
    (∀ U, Live U → ¬ TwinClose M0 U → ∃ V, Live V ∧ ProperRealStep A M0 U V)

/-- Forward: seriality forces a twin above every horizon (rank exhaustion: the live
    run cannot descend forever, so it must close, and the only non-violating close
    is a twin). -/
theorem twinCenters_unbounded_of_serialTwinBoundary
    (H : SerialTwinBoundaryObligation) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  obtain ⟨A, Live, ⟨U0, hU0⟩, hSerial⟩ := H M0
  let E : ProperTimePumpEngine A M0 :=
    { Live := Live
      start_live := ⟨U0, hU0⟩
      step_or_close := by
        intro U hU
        by_cases hTwin : TwinClose M0 U
        · exact Or.inl (Or.inl hTwin)
        · exact Or.inr (hSerial U hU hTwin) }
  have hNoViol : ∀ U, E.Live U → ¬ TimeStopViolation A M0 E.Live U := by
    intro U hU hViol
    exact hViol.stuck (hSerial U hU hViol.not_twin)
  exact properTimePumpEngine_forces_twin E hNoViol

/-- Reverse: a twin above every horizon realizes seriality, via the singleton live
    engine (the live state is the twin itself — already a `TwinClose`, so the
    seriality premise `¬ TwinClose` is never met). -/
theorem serialTwinBoundary_of_unboundedTwinCenters
    (H : ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) :
    SerialTwinBoundaryObligation := by
  intro M0
  obtain ⟨m, hm, htwin⟩ := H M0
  refine ⟨0, fun U => U = State.center m, ⟨State.center m, rfl⟩, ?_⟩
  intro U hU hNotTwin
  subst hU
  exact absurd (show TwinClose M0 (State.center m) from ⟨hm, htwin⟩) hNotTwin

/-- **THE EQUIVALENCE: the seriality boundary ⟺ unbounded twin centers.**  Adopting
    it as the accepted first cause assumes EXACTLY the twin conjecture. -/
theorem serialTwinBoundary_iff_unboundedTwinCenters :
    SerialTwinBoundaryObligation ↔ (∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) :=
  ⟨twinCenters_unbounded_of_serialTwinBoundary,
   serialTwinBoundary_of_unboundedTwinCenters⟩

/-- Drop-in: the seriality boundary ⟺ the current `TimePumpStep00Obligation`. -/
theorem serialTwinBoundary_iff_timePumpStep00 :
    SerialTwinBoundaryObligation ↔ TimePumpStep00Obligation := by
  constructor
  · intro H M0
    obtain ⟨m, hm, htwin⟩ := twinCenters_unbounded_of_serialTwinBoundary H M0
    refine ⟨0,
      { Live := fun U => U = State.center m
        start_live := ⟨State.center m, rfl⟩
        step_or_close := by
          intro U hU; subst hU
          exact Or.inl (Or.inl ⟨hm, htwin⟩) },
      ?_⟩
    intro U hU hViol; subst hU
    exact hViol.not_twin ⟨hm, htwin⟩
  · intro H
    exact serialTwinBoundary_of_unboundedTwinCenters
      (twinCenters_unbounded_of_timePumpStep00 H)

/-- The seriality boundary yields twin-lower infinitude (the goal form). -/
theorem twinLowersInfinite_of_serialTwinBoundary
    (H : SerialTwinBoundaryObligation) : TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := twinCenters_unbounded_of_serialTwinBoundary H N
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end SerialTwinBoundary
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
