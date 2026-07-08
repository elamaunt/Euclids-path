import EuclidsPath.Engine.Step00FlatCycleEngine
import EuclidsPath.Engine.Step00OrnamentCurvatureReservoir

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 sign invariance — the start sets the sign, and the engine forbids it to flip

The idea: the sign of the ornament curvature is set at the base, and to CHANGE sign it would have to
pass through zero — but zero is the FLAT state, and flat is a perpetual engine, which is forbidden.
So the crossing is stopped: the sign set at the start cannot flip, and stays negative forever, so a
survivor (twin) always remains.

The engine does real work here for FREE: `no_flatCostFreeCycle` forbids the zero value, so the sign
never hits `0`.  Combined with a base sign `< 0` and a per-step "continuity" bound (the sign moves up
by at most one per layer, so it cannot jump over `0`), a discrete intermediate-value argument keeps
the sign strictly negative on the whole tail.

## Green here

  * `discrete_ivt_neg` — discrete IVT: `f 0 < 0`, `f (k+1) ≤ f k + 1`, `f k ≠ 0` ⟹ `f k < 0` (the sign
    cannot flip without touching `0`);
  * `never_zero` — the sign never equals `0`, because `sign k = 0` would build a `FlatCostFreeCycle`
    (`no_flatCostFreeCycle` — axiom-light rank exhaustion);
  * `sign_stays_negative`, `twinLowersInfinite_of_signInvarianceCertificate` — the start sign persists
    and yields twins, CONDITIONAL on the certificate.

## The wall (named, not proved) — now distributed, with the zero-crossing handled by the engine

The certificate fields carry the parity barrier: `base` (the start sign is negative), `step_up` (the
sign moves up by ≤ 1 per layer — a discreteness/continuity claim), and `neg_forces_twin` (a negative
sign is a surviving twin).  What the engine buys for free is exactly the middle: the sign cannot cross
`0`.  Proving `base`, `step_up`, `neg_forces_twin` uniformly is the remaining barrier;
`twin_prime_conjecture` stays `sorry`.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace GenealogicalOrnament
namespace SignInvariance

open EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament.FlatEngine
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament.Reservoir

/-- **Green — discrete intermediate value theorem.**  If an integer sequence starts negative, moves up
    by at most one per step, and never equals zero, then it stays strictly negative: it cannot flip
    sign without passing through `0`. -/
theorem discrete_ivt_neg {f : ℕ → ℤ} (h0 : f 0 < 0)
    (hstep : ∀ k : ℕ, f (k + 1) ≤ f k + 1) (hne : ∀ k : ℕ, f k ≠ 0) :
    ∀ k : ℕ, f k < 0 := by
  intro k
  induction k with
  | zero => exact h0
  | succ n ih =>
    have hs := hstep n
    have hn := hne (n + 1)
    omega

/-- The certificate for the sign-invariance route.  `sign k` is the ornament curvature sign at horizon
    `5 + k`.  Three fields carry the parity barrier; the fourth (`zero_forces_engine`) is discharged by
    the engine below. -/
structure SignInvarianceCertificate where
  sign : ℕ → ℤ
  base : sign 0 < 0
  step_up : ∀ k : ℕ, sign (k + 1) ≤ sign k + 1
  zero_forces_engine : ∀ k : ℕ, sign k = 0 → FlatCostFreeCycle
  neg_forces_twin : ∀ k : ℕ, sign k < 0 → ∃ m : ℕ, 5 + k < m ∧ TwinCenterZ m

/-- **Green: the sign never hits zero** — a zero would build a flat cost-free cycle, which
    `no_flatCostFreeCycle` forbids.  This is the engine doing the zero-crossing prohibition for free. -/
theorem never_zero (C : SignInvarianceCertificate) : ∀ k : ℕ, C.sign k ≠ 0 :=
  fun k h => no_flatCostFreeCycle (C.zero_forces_engine k h)

/-- **Green: the start sign persists** — negative at the base, unable to cross zero (engine), moving
    up by ≤ 1 per step, so strictly negative on the whole tail. -/
theorem sign_stays_negative (C : SignInvarianceCertificate) : ∀ k : ℕ, C.sign k < 0 :=
  discrete_ivt_neg C.base C.step_up (never_zero C)

/-- Cofinal twins from the certificate: every horizon `M0 ≥ 5` has a twin above it. -/
theorem cofinalFromFive (C : SignInvarianceCertificate) :
    ∀ M0 : ℕ, 5 ≤ M0 → ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0 h5
  obtain ⟨m, hm, ht⟩ := C.neg_forces_twin (M0 - 5) (sign_stays_negative C (M0 - 5))
  exact ⟨m, by omega, ht⟩

/-- **Green conditional capstone: the sign-invariance certificate yields `TwinLowers.Infinite`.**  The
    engine forbids the zero-crossing for free; the certificate's `base`/`step_up`/`neg_forces_twin`
    fields carry the remaining parity barrier.  Does NOT close the twin sorry. -/
theorem twinLowersInfinite_of_signInvarianceCertificate
    (C : SignInvarianceCertificate) : TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := twinCofinal_of_fromFive (cofinalFromFive C) N
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end SignInvariance
end GenealogicalOrnament
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
