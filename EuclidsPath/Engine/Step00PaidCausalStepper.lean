import EuclidsPath.Engine.TimePumpBoundary
import EuclidsPath.Engine.Step00SerialTwinBoundary

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 paid causal stepper — "pay the present to know the future"

A `PaidCausalStepper` is the honest, LOCAL replacement for the global "time cannot
stop" obligation.  In each live state the machine returns one of three things,
using only the present (no oracle for a future twin):

  * a twin witness (`TwinClose`), or
  * an explicit violation (`TimeStopViolation`), or
  * a next live state together with a PAYMENT: `Fuel` strictly decreases.

Rank exhaustion then forces a close: since every paid step spends one unit of a
finite `ℕ` fuel, the run cannot pay forever, so a close (twin or violation) is
reached.  Forbidding illegal stops (`no violation`) leaves a twin witness.

## What this file proves (all green, conditional)

  * `PaidCausalStepper.forces_close_or_violation` — the machine reaches a close;
  * `PaidCausalStepper.forces_twin` — with no violation, a twin above `M0`;
  * `paidStepper_iff_unboundedTwinCenters` — **the wall, machine-checked:** the
    paid-stepper obligation is EXACTLY the twin conjecture.

## What this file does NOT do (the honest wall)

It does NOT construct an ARITHMETIC stepper unconditionally.  Building the local
`next` from the Euclid old-peel is real arithmetic (a paid step = peel a divisor,
`lexRank` drops), but the crucial `no_time_stop_violation` — "the paid descent
never falls below `M0` without landing on an above-`M0` twin" — is EXACTLY the twin
conjecture.  This is the same wall as `TimePumpStep00Obligation` /
`SerialTwinBoundaryObligation`, and the same wall the repo already certifies for the
descent/window routes (`descent_reduction_is_circular`, `smallCleanSupply_iff_goal`):
`no violation ⟺ SmallCleanSupply ⟺ the goal`.  Paying the present spends a finite
budget, so it can only reach a twin within that budget — an effective twin-gap bound,
i.e. the conjecture (indeed stronger).  This is a reduction, NOT a proof.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace PaidCausalStepper

open EuclidsPath.Residuals

/-- A local, causal, paid stepper: at each live state it exhibits a twin witness, a
    violation, or a next live state paid for by a strict drop of `Fuel`. -/
structure PaidCausalStepper (A M0 : ℕ) where
  Live : State → Prop
  Fuel : State → ℕ
  start : ∃ U : State, Live U
  next :
    ∀ U : State, Live U →
      TwinClose M0 U ∨
      TimeStopViolation A M0 Live U ∨
      ∃ V : State, Live V ∧ ProperRealStep A M0 U V ∧ Fuel V < Fuel U

/-- **Rank exhaustion for the paid stepper.**  A live paid stepper reaches a close
    event (twin or violation): every paid step spends one unit of finite fuel, so the
    run cannot pay forever.  Strong induction on `Fuel`. -/
theorem PaidCausalStepper.forces_close_or_violation
    {A M0 : ℕ} (S : PaidCausalStepper A M0) :
    ∃ U : State, S.Live U ∧
      (TwinClose M0 U ∨ TimeStopViolation A M0 S.Live U) := by
  obtain ⟨U0, hU0⟩ := S.start
  exact
    (Nat.strongRecOn (S.Fuel U0)
      (motive := fun n =>
        ∀ U : State, S.Live U → S.Fuel U = n →
          ∃ W : State, S.Live W ∧
            (TwinClose M0 W ∨ TimeStopViolation A M0 S.Live W))
      (fun n ih U hU hFuel => by
        rcases S.next U hU with hTwin | hViol | ⟨V, hVLive, _hStep, hFuelLt⟩
        · exact ⟨U, hU, Or.inl hTwin⟩
        · exact ⟨U, hU, Or.inr hViol⟩
        · have hlt : S.Fuel V < n := by omega
          exact ih (S.Fuel V) hlt V hVLive rfl)
      U0 hU0 rfl)

/-- If illegal stops are forbidden, the paid stepper forces a twin above `M0`. -/
theorem PaidCausalStepper.forces_twin
    {A M0 : ℕ} (S : PaidCausalStepper A M0)
    (hNoViolation : ∀ U : State, S.Live U → ¬ TimeStopViolation A M0 S.Live U) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  obtain ⟨U, hU, hClose⟩ := S.forces_close_or_violation
  rcases hClose with hTwin | hViol
  · cases U with
    | center m => exact ⟨m, hTwin.1, hTwin.2⟩
    | defect n q s => exact False.elim hTwin
    | absorber n => exact False.elim hTwin
  · exact absurd hViol (hNoViolation U hU)

/-- The Step00 obligation in paid-stepper form: for every horizon there is a scale and
    a violation-free paid causal stepper. -/
def PaidStepperStep00Obligation : Prop :=
  ∀ M0 : ℕ, ∃ A : ℕ, ∃ S : PaidCausalStepper A M0,
    ∀ U : State, S.Live U → ¬ TimeStopViolation A M0 S.Live U

/-- Forward: the paid-stepper obligation forces unbounded twin centers. -/
theorem twinCenters_unbounded_of_paidStepper
    (H : PaidStepperStep00Obligation) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  obtain ⟨A, S, hNoViol⟩ := H M0
  exact S.forces_twin hNoViol

/-- Reverse: a twin above every horizon realizes the obligation, via the singleton paid
    stepper (the live state is the twin itself — an immediate `TwinClose`, so the paid
    branch is never needed and there is no violation). -/
theorem paidStepper_of_unboundedTwinCenters
    (H : ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) :
    PaidStepperStep00Obligation := by
  intro M0
  obtain ⟨m, hm, htwin⟩ := H M0
  refine ⟨0,
    { Live := fun U => U = State.center m
      Fuel := fun _ => 0
      start := ⟨State.center m, rfl⟩
      next := by
        intro U hU
        subst hU
        exact Or.inl ⟨hm, htwin⟩ },
    ?_⟩
  intro U hU hViol
  subst hU
  exact hViol.not_twin ⟨hm, htwin⟩

/-- **THE WALL, machine-checked: the paid-stepper obligation is EXACTLY the twin
    conjecture.**  So it is a reduction to a twin-equivalent boundary, not a proof —
    the same wall as `TimePumpStep00Obligation` / `SerialTwinBoundaryObligation`. -/
theorem paidStepper_iff_unboundedTwinCenters :
    PaidStepperStep00Obligation ↔ (∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) :=
  ⟨twinCenters_unbounded_of_paidStepper, paidStepper_of_unboundedTwinCenters⟩

/-- Drop-in: the paid-stepper obligation ⟺ the seriality boundary ⟺ TimePump. -/
theorem paidStepper_iff_serialTwinBoundary :
    PaidStepperStep00Obligation ↔ SerialTwinBoundary.SerialTwinBoundaryObligation :=
  paidStepper_iff_unboundedTwinCenters.trans
    SerialTwinBoundary.serialTwinBoundary_iff_unboundedTwinCenters.symm

/-- The paid-stepper obligation yields twin-lower infinitude (the goal form). -/
theorem twinLowersInfinite_of_paidStepper
    (H : PaidStepperStep00Obligation) : TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := twinCenters_unbounded_of_paidStepper H N
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end PaidCausalStepper
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
