import EuclidsPath.Engine.Step00CompletePatch

open EuclidsPath.ConcreteStep00Graph EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Step00CompletePatch

namespace Step00PatchAudit

/-- The honest twin boundary, in center form: twin centers are unbounded. -/
def UnboundedTwinCenters : Prop := ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m

/-- REVERSE direction: a single twin above `M0` already builds a violation-free
    time-pump engine (Live = that one twin; it closes immediately, never gets stuck). -/
theorem timePumpStep00_of_unboundedTwinCenters
    (h : UnboundedTwinCenters) : TimePumpStep00Obligation := by
  intro M0
  obtain ⟨m, hM0m, hTwin⟩ := h M0
  let E : ProperTimePumpEngine M0 M0 :=
    { Live := fun U => U = State.center m
      start_live := ⟨State.center m, rfl⟩
      step_or_close := fun U hU => by
        have hEq : U = State.center m := hU
        subst hEq
        exact Or.inl (Or.inl ⟨hM0m, hTwin⟩) }
  refine ⟨M0, E, ?_⟩
  intro U hU hViol
  have hEq : U = State.center m := hU
  subst hEq
  exact hViol.not_twin ⟨hM0m, hTwin⟩

/-- The new boundary is EXACTLY "twin centers unbounded" (both directions green). -/
theorem timePumpStep00_iff_unboundedTwinCenters :
    TimePumpStep00Obligation ↔ UnboundedTwinCenters :=
  ⟨fun H => twinCenters_unbounded_of_timePumpStep00 H,
   timePumpStep00_of_unboundedTwinCenters⟩

/-- …and unbounded twin centers is the canonical `TwinLowers.Infinite`. -/
theorem unboundedTwinCenters_imp_infinite
    (h : UnboundedTwinCenters) : EuclidsPath.TwinLowers.Infinite :=
  EuclidsPath.infinite_of_unbounded_centers
    (fun N => by
      obtain ⟨m, hN, hT⟩ := h N
      refine ⟨m, hN, ?_⟩
      simpa [EuclidsPath.IsTwinCenter, EuclidsPath.Residuals.TwinCenterZ] using hT)

#print axioms timePumpStep00_of_unboundedTwinCenters
#print axioms timePumpStep00_iff_unboundedTwinCenters
#print axioms unboundedTwinCenters_imp_infinite

end Step00PatchAudit
