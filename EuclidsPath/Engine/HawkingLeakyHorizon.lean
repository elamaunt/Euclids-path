/-
  HawkingLeakyHorizon — 🟢 a leaky horizon relocates the epistemic barrier by ZERO.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ANSWERING THE HAWKING-RADIATION HYPOTHESIS IN THE PROJECT'S OWN TERMS.      │
  └───────────────────────────────────────────────────────────────────────────┘

  THE HYPOTHESIS. Could a Hawking-radiation-like "leak" across the first-cause
  horizon let one DERIVE the first cause / resolve the twins FROM INSIDE — an
  attack on `no_internalisedHorizonBoundary`?

  THE ANSWER (machine-checked here). No. A Hawking-style leak reconstructs the
  boundary from OUTSIDE the horizon — physically, "no operation on the Hawking
  radiation can affect the infalling observer"; the reconstruction is performed
  by an asymptotic (outside) observer on exterior data. In this repository's
  dictionary that is an `ExternalUniverseCause` (`Step00CausalClosureBeyondHorizon`),
  the route the architecture ALREADY permits, NOT an `InternalUniverseCause`
  (`InternalisedStep00HorizonBoundary`), the route it forbids. So the leak lands
  on the side already open; it relocates the barrier by exactly zero.

  `hawking_leaky_horizon` states both halves at once, GREEN (pure composition of
  existing theorems, no new axiom, taint unchanged):
    • the OUTSIDE route works — a beyond-horizon acceptance yields the twins
      conclusion (`causalClosureBeyondHorizon_generates_twins`, CONDITIONAL: the
      leak is a hypothesis, not the axiom, so this conjunct is axiom-free);
    • the INSIDE route stays impossible — `¬ InternalisedStep00HorizonBoundary`
      (`no_internalisedHorizonBoundary`): any internalisation builds the forbidden
      engine.
  A leak that only reaches outside therefore changes nothing: the barrier it
  "crosses" (accept from outside) was already open; the barrier it does NOT cross
  (derive from inside) stays shut. This CORROBORATES `no_internalisedHorizonBoundary`
  under a new stress test — it is not a new impossibility.

  WHAT THIS IS NOT (RED LINES — LOUD).
    • NOT physics. There is no metric, temperature, entropy or black hole in Lean;
      this formalises only the EPISTEMIC relocation, not any Hawking computation.
    • The physics itself is NOT theorem-grade: information escape (Page curve,
      islands, replica wormholes) is a MODEL-LEVEL result in 2D/AdS gravity with
      debated foundations; and even granting escape, decoding is CONJECTURED
      exponentially hard (Python's Lunch). Importing it as settled would be
      overclaiming. This lemma leans on NONE of that — only on the project's own
      inside/outside split.
    • NO new boundary of `step00FirstCause` is introduced (that would be
      conjectural physics dressed as an axiom, and structurally redundant per
      `step00FirstCause_iff_causalClosure`).
-/
import Mathlib
import EuclidsPath.Engine.CausalClosureAxiom

set_option autoImplicit false

namespace EuclidsPath.HawkingLeakyHorizon

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-- **`hawking_leaky_horizon` — 🟢 a leak relocates the barrier by zero.**

Both hold at once, axiom-free:
  (i)  `Step00CausalClosureBeyondHorizon → TwinLowers.Infinite` — an OUTSIDE leak
       (a beyond-horizon acceptance) already yields the twins conclusion;
  (ii) `¬ InternalisedStep00HorizonBoundary` — the INSIDE route stays impossible.

So a Hawking-style leak, which is an outside reconstruction, gives only the route
already permitted and never an inside derivation: the epistemic barrier moves by
zero. Green: `⟨causalClosureBeyondHorizon_generates_twins, no_internalisedHorizonBoundary⟩`. -/
theorem hawking_leaky_horizon :
    (Step00CausalClosureBeyondHorizon → TwinLowers.Infinite) ∧
      ¬ InternalisedStep00HorizonBoundary :=
  ⟨causalClosureBeyondHorizon_generates_twins, no_internalisedHorizonBoundary⟩

-- 🟢 CONTROL: must NOT show step00FirstCause (only the standard triple).
#print axioms hawking_leaky_horizon

end EuclidsPath.HawkingLeakyHorizon
