import EuclidsPath.Engine.Step00SignInvariance

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 sign-invariance base — the start sign is green; the barrier collapses to one field

"What about the start sign?"  With the natural sign — the twin indicator `sign k = -1` if a twin exists
above the horizon `5 + k`, else `0` — the base sign is settled GREEN (a twin exists above the base:
`m = 7` gives `(41, 43)`).  Moreover the indicator is bounded in `{-1, 0}`, so `base`, `step_up` AND
`neg_forces_twin` are ALL discharged green at once, and the ENTIRE remaining barrier of the
sign-invariance route collapses into the single field

  `zero_forces_engine : ∀ k, sign k = 0 → FlatCostFreeCycle`

i.e. "no twin above the horizon builds a flat cost-free cycle" — the engine-forcing wall (the parity
barrier), the same node as `EngineForcing` / `TwinSurvivorNode`.

So the start sign is not where the difficulty lives.  This is honest: `zero_forces_engine` is the one
unproven field; `twin_prime_conjecture` stays `sorry`.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace GenealogicalOrnament
namespace SignInvariance
namespace Concrete

open EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament.FlatEngine
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament.Reservoir
open Classical

/-- The natural sign: `-1` when a twin exists above the horizon `5 + k`, else `0`. -/
noncomputable def twinIndicator (k : ℕ) : ℤ :=
  if (∃ m : ℕ, 5 + k < m ∧ TwinCenterZ m) then -1 else 0

/-- **Green base:** the start sign is negative — a twin exists above the base (`m = 7`, giving `41,43`). -/
theorem twinIndicator_base : twinIndicator 0 < 0 := by
  have h : ∃ m : ℕ, 5 + 0 < m ∧ TwinCenterZ m := ⟨7, by norm_num, twinCenterZ_seven⟩
  unfold twinIndicator
  rw [if_pos h]
  decide

/-- **Green step-up:** the indicator lives in `{-1, 0}`, so it moves up by at most `1` per layer. -/
theorem twinIndicator_step_up (k : ℕ) : twinIndicator (k + 1) ≤ twinIndicator k + 1 := by
  unfold twinIndicator
  split_ifs <;> omega

/-- **Green connection:** a negative indicator IS a twin above the horizon (definitional). -/
theorem twinIndicator_neg_forces_twin (k : ℕ) (h : twinIndicator k < 0) :
    ∃ m : ℕ, 5 + k < m ∧ TwinCenterZ m := by
  unfold twinIndicator at h
  split_ifs at h with hc
  · exact hc
  · omega

/-- **All three easy fields discharged; only `zero_forces_engine` remains.**  From the single
    engine-forcing hypothesis (`no twin above the horizon → a flat cost-free cycle`), the concrete
    sign-invariance certificate is built with `base`, `step_up`, `neg_forces_twin` all green. -/
noncomputable def certificate_of_engineForcing
    (H : ∀ k : ℕ, twinIndicator k = 0 → FlatCostFreeCycle) : SignInvarianceCertificate :=
  { sign := twinIndicator
    base := twinIndicator_base
    step_up := twinIndicator_step_up
    zero_forces_engine := H
    neg_forces_twin := twinIndicator_neg_forces_twin }

/-- **The whole sign-invariance route now rests on ONE field.**  Twin infinitude follows from the
    single engine-forcing hypothesis; `base`/`step_up`/`neg_forces_twin` are green.  Does NOT close the
    twin sorry — `H` is the parity barrier (`no twin above → flat cycle`). -/
theorem twinLowersInfinite_of_engineForcing
    (H : ∀ k : ℕ, twinIndicator k = 0 → FlatCostFreeCycle) : TwinLowers.Infinite :=
  twinLowersInfinite_of_signInvarianceCertificate (certificate_of_engineForcing H)

/-- **The honest audit (backward, VACUOUS): twins make the engine-forcing field trivially inhabited.**
    If a twin exists above every horizon, then `twinIndicator k = 0` never holds, so the implication
    is empty (`absurd`).  Together with the forward `twinLowersInfinite_of_engineForcing`, this shows
    the field `∀ k, twinIndicator k = 0 → FlatCostFreeCycle` is inhabited **iff** the twin conjecture
    holds.  So "the sign is stable" is a REDUCTION to this field, and the field IS the conjecture —
    nothing here discharges it, and the sign was proved stable only RELATIVE to it. -/
noncomputable def engineForcing_of_unboundedTwinCenters
    (H : ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) :
    ∀ k : ℕ, twinIndicator k = 0 → FlatCostFreeCycle := by
  intro k hzero
  have hex : ∃ m : ℕ, 5 + k < m ∧ TwinCenterZ m := H (5 + k)
  unfold twinIndicator at hzero
  rw [if_pos hex] at hzero
  exact absurd hzero (by decide)

end Concrete
end SignInvariance
end GenealogicalOrnament
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
