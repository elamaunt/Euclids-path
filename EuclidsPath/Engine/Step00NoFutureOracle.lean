import EuclidsPath.Engine.Step00PaidCausalStepper

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 no-future-oracle audit — "the future may exist, but is not a local input"

An honesty audit that separates a genuine causal proof from a circular one.

The bad (teleological) scheme: pick the next twin `T` above `M0`, build steps leading
to `T`, pay for each step "because we know the goal `T`".  This is circular — the whole
strength sits in the choice of `T`.  Formally the object

  FutureOracle M0 := (T, above : M0 < T, twin : TwinCenterZ T)

IS the goal itself.  So any construction that uses a `FutureOracle` as an input to the
current step or to the payment certificate is NOT a proof of existence of a twin — it
only uses an already-known twin.

This file makes that precise and machine-checked:

  * `nonempty_futureOracle_iff_twinAbove` — the oracle EXISTS iff a twin exists above M0
    (the oracle is the goal);
  * `allFutureOracle_iff_unboundedTwinCenters` — oracle-for-every-horizon ⟺ the twin
    conjecture;
  * `oracleStepper` / `paidStepperObligation_of_allFutureOracle` — the FORBIDDEN pattern
    exhibited: a `FutureOracle` builds a violation-free `PaidCausalStepper` trivially (the
    live state IS the oracle's twin), so the reverse `⟸` half of every "X ⟺ twins"
    equivalence (e.g. `paidStepper_of_unboundedTwinCenters`) is an ORACLE construction —
    the circular half.

## The honest principle (No Future Oracle)

A valid causal proof may use that a next local state EXISTS (`FutureExists`), but may NOT
use a future twin witness as an input to the current transition or payment
(`FutureOracle` forbidden).  Building a `PaidCausalStepper` whose `next`/payment depend
ONLY on the present local view (arithmetic obstruction/residue data), WITHOUT a
`FutureOracle`, is the genuine open node.  Rank exhaustion then does the rest.  This file
does NOT build such a causal stepper (that is the twin conjecture); it certifies where the
circularity lives so a circular proof cannot be accepted as a causal one.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace NoFutureOracle

open EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.PaidCausalStepper

/-- A future oracle for horizon `M0`: a twin above `M0`, packaged as data.  It IS the
    goal — having it is having the answer. -/
structure FutureOracle (M0 : ℕ) where
  T : ℕ
  above : M0 < T
  twin : TwinCenterZ T

/-- Having the oracle is having the twin (trivial: the oracle is the answer). -/
theorem twinAbove_of_futureOracle {M0 : ℕ} (O : FutureOracle M0) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m :=
  ⟨O.T, O.above, O.twin⟩

/-- Conversely a twin above `M0` gives the oracle. -/
noncomputable def futureOracle_of_twinAbove {M0 : ℕ}
    (h : ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) : FutureOracle M0 :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

/-- **The oracle EXISTS iff a twin exists above `M0`.**  So the "future oracle" is
    definitionally the goal; a proof that consumes it is circular. -/
theorem nonempty_futureOracle_iff_twinAbove {M0 : ℕ} :
    Nonempty (FutureOracle M0) ↔ ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  constructor
  · rintro ⟨O⟩; exact twinAbove_of_futureOracle O
  · intro h; exact ⟨futureOracle_of_twinAbove h⟩

/-- Oracle-for-every-horizon is exactly the twin conjecture. -/
theorem allFutureOracle_iff_unboundedTwinCenters :
    (∀ M0 : ℕ, Nonempty (FutureOracle M0)) ↔
      (∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) := by
  constructor
  · intro H M0; exact nonempty_futureOracle_iff_twinAbove.mp (H M0)
  · intro H M0; exact nonempty_futureOracle_iff_twinAbove.mpr (H M0)

/-- **The FORBIDDEN (circular) construction, exhibited.**  From a `FutureOracle` a paid
    causal stepper is built trivially: the singleton live state is the oracle's twin `T`,
    an immediate `TwinClose`.  Its very existence is powered by the future twin — this is
    the oracle pattern, NOT a causal proof. -/
def oracleStepper {M0 : ℕ} (O : FutureOracle M0) :
    PaidCausalStepper 0 M0 where
  Live := fun U => U = State.center O.T
  Fuel := fun _ => 0
  start := ⟨State.center O.T, rfl⟩
  next := by
    intro U hU
    subst hU
    exact Or.inl ⟨O.above, O.twin⟩

/-- The oracle stepper never violates (its only live state is the twin itself). -/
theorem oracleStepper_noViolation {M0 : ℕ} (O : FutureOracle M0) :
    ∀ U : State, (oracleStepper O).Live U →
      ¬ TimeStopViolation 0 M0 (oracleStepper O).Live U := by
  intro U hU hViol
  have hEq : U = State.center O.T := hU
  subst hEq
  exact hViol.not_twin ⟨O.above, O.twin⟩

/-- **The circle, closed and named.**  An oracle for every horizon builds the paid-stepper
    obligation — but only because each stepper is powered by an already-known twin.  So
    the `⟸` direction of `paidStepper_iff_unboundedTwinCenters` (and of every "X ⟺ twins")
    is an oracle construction: the circular half.  A CAUSAL (oracle-free, arithmetic)
    stepper is the genuine open node. -/
theorem paidStepperObligation_of_allFutureOracle
    (H : ∀ M0 : ℕ, Nonempty (FutureOracle M0)) :
    PaidStepperStep00Obligation := by
  intro M0
  obtain ⟨O⟩ := H M0
  exact ⟨0, oracleStepper O, oracleStepper_noViolation O⟩

end NoFutureOracle
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
