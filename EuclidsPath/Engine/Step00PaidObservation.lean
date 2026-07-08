import EuclidsPath.Engine.Step00NoFutureOracle

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 paid observation & causality audit — "the future cannot pay for the present"

Two honesty guardrails that separate a genuine causal proof from a circular one.  Neither
proves the twin conjecture; both certify *where* a would-be proof may cheat, so a circular
proof cannot pass as a causal one.  Companion to `Step00NoFutureOracle` (the oracle IS the
goal) and `Step00PaidCausalStepper` (the paid rank-exhaustion wall).

## Part A — causality by indistinguishable worlds (No Future Oracle, §5)

A decision procedure is **causal through a local view** when it factors through that view:
worlds sharing the same local view get the same action.  This is the *informational* form
of "cannot use the future": the action depends only on what is locally visible, never on a
future witness beyond the horizon.

  * `not_causal_of_usesFuture` — **the audit theorem:** if a decision distinguishes two
    locally-indistinguishable worlds (same view, different action) then it is NOT causal.
    Only a non-local input (a future oracle) can do that.
  * `not_usesFuture_of_causal` — contrapositive guardrail: a causal decision is constant on
    each view-fibre, so it never smuggles in the future.
  * `oracleBit_not_causal` — concrete witness: reading "is there a twin far above `M0`" is
    not causal through the local boundary view.

## Part B — paid observation budget (Paid Observation Principle, §7/§8/§12)

A `PaidObserver` carries a finite global resource `rank` that never rises, a visibility
`horizon` that never falls, and a per-step `cost`; every step pays for itself out of the
resource.  Then:

  * `PaidObserver.budget` — resource + total cost paid so far ≤ initial resource;
  * `PaidObserver.cost_bounded` — total observation cost is forever bounded by the initial
    finite resource (**no free global observation**);
  * `PaidObserver.horizon_bounded` — if each unit of new visibility costs a unit of
    resource, the horizon a finite observer can EVER reach is bounded (`horizon 0 + rank 0`):
    a finite observer never attains an infinite horizon for free (the closed-system /
    second-law form).

## Part C — the forbidden move, named (§8)

`FreeGlobalObservation` — obtaining a future oracle for every horizon at no cost — is
exactly the twin conjecture (`freeGlobalObservation_iff_unboundedTwinCenters`).  So the
"free" global observation is precisely the goal: it may be an OUTPUT of the whole proof,
never an INPUT to a local step.  The honest route pays a finite budget, which (Part B)
bounds the reachable horizon — and reaching a twin within a finite budget is an effective
twin-gap bound, i.e. the conjecture.  A reduction, not a proof.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace PaidObservation

open EuclidsPath.Residuals

/-! ### Part A — causality by indistinguishable worlds -/

variable {World View Decision : Type}

/-- A decision is **causal through a local view** when it factors through that view:
    worlds with the same local view produce the same action.  The informational form of
    "the action uses only the present, not the future". -/
def CausalThroughView (view : World → View) (decide : World → Decision) : Prop :=
  ∀ w w' : World, view w = view w' → decide w = decide w'

/-- A decision **uses the future** when it distinguishes two locally-indistinguishable
    worlds (same view, different action).  Only a non-local input — a future oracle — can
    make that difference. -/
def UsesFuture (view : World → View) (decide : World → Decision) : Prop :=
  ∃ w w' : World, view w = view w' ∧ decide w ≠ decide w'

/-- **The causality audit theorem (§5): using the future ⇒ not causal.**  A guardrail, not
    a proof of twins: any stepper whose action depends on a future witness invisible to the
    local view fails to be causal. -/
theorem not_causal_of_usesFuture {view : World → View} {decide : World → Decision}
    (h : UsesFuture view decide) : ¬ CausalThroughView view decide := by
  rintro hCausal
  obtain ⟨w, w', hview, hne⟩ := h
  exact hne (hCausal w w' hview)

/-- Contrapositive guardrail: a causal decision never uses the future — it is constant on
    each local-view fibre. -/
theorem not_usesFuture_of_causal {view : World → View} {decide : World → Decision}
    (h : CausalThroughView view decide) : ¬ UsesFuture view decide :=
  fun hu => not_causal_of_usesFuture hu h

/-- Concrete witness.  A world is `(boundary M0, far twin bit)`; the local view is the
    boundary, the oracle reads the far bit.  Two worlds with the same boundary but a
    different far bit are locally indistinguishable, yet the oracle acts differently — so
    reading a future twin is not causal. -/
theorem oracleBit_not_causal :
    ¬ CausalThroughView (fun w : ℕ × Bool => w.1) (fun w : ℕ × Bool => w.2) :=
  not_causal_of_usesFuture ⟨(0, true), (0, false), rfl, by decide⟩

/-! ### Part B — paid observation budget -/

/-- A **paid observer**: a finite global resource `rank` that never rises, a visibility
    `horizon` that never falls, and a per-step `cost`; every step pays for its expansion out
    of the resource (`rank (n+1) + cost n ≤ rank n`). -/
structure PaidObserver where
  rank : ℕ → ℕ
  horizon : ℕ → ℕ
  cost : ℕ → ℕ
  expands : ∀ n, horizon n ≤ horizon (n + 1)
  paid : ∀ n, rank (n + 1) + cost n ≤ rank n

/-- **The budget identity:** remaining resource plus total cost paid through `n` steps is
    within the initial resource (`rank n + ∑_{i<n} cost i ≤ rank 0`).  Closed-system form. -/
theorem PaidObserver.budget (O : PaidObserver) :
    ∀ n, O.rank n + ∑ i ∈ Finset.range n, O.cost i ≤ O.rank 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep := O.paid k
    rw [Finset.sum_range_succ]
    omega

/-- **No free global observation:** total observation cost is forever bounded by the
    initial finite resource. -/
theorem PaidObserver.cost_bounded (O : PaidObserver) :
    ∀ n, ∑ i ∈ Finset.range n, O.cost i ≤ O.rank 0 := by
  intro n
  have := O.budget n
  omega

/-- Horizon growth is bounded by the cost paid: if each unit of new visibility costs a unit
    of resource, `horizon n ≤ horizon 0 + ∑_{i<n} cost i`. -/
theorem PaidObserver.horizon_le_cost (O : PaidObserver)
    (hcost : ∀ n, O.horizon (n + 1) ≤ O.horizon n + O.cost n) :
    ∀ n, O.horizon n ≤ O.horizon 0 + ∑ i ∈ Finset.range n, O.cost i := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have h := hcost k
    rw [Finset.sum_range_succ]
    omega

/-- **A finite observer's horizon is bounded (`horizon 0 + rank 0`).**  If each unit of new
    visibility must be paid for, no finite observer ever attains an infinite horizon for
    free — the second-law / closed-system form of "global knowledge is not free". -/
theorem PaidObserver.horizon_bounded (O : PaidObserver)
    (hcost : ∀ n, O.horizon (n + 1) ≤ O.horizon n + O.cost n) :
    ∀ n, O.horizon n ≤ O.horizon 0 + O.rank 0 := by
  intro n
  have h1 := O.horizon_le_cost hcost n
  have h2 := O.cost_bounded n
  omega

/-! ### Part C — the forbidden move, named -/

/-- The forbidden move (§8): a future oracle for EVERY horizon, obtained for free.  Naming
    it as a proposition makes the guardrail explicit. -/
def FreeGlobalObservation : Prop :=
  ∀ M0 : ℕ, Nonempty (NoFutureOracle.FutureOracle M0)

/-- **The free global observation IS the twin conjecture.**  So it may be an OUTPUT of the
    whole proof, never an INPUT to a local step; the honest route pays (Part B bounds the
    reachable horizon) and thereby hits the same wall as `paidStepper_iff_unboundedTwinCenters`. -/
theorem freeGlobalObservation_iff_unboundedTwinCenters :
    FreeGlobalObservation ↔ (∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) :=
  NoFutureOracle.allFutureOracle_iff_unboundedTwinCenters

end PaidObservation
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
