import EuclidsPath.Engine.Residuals
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 genealogical ornament — the curvature route, green scaffold + the named wall

A second proof route for the twins, structurally different from the seriality boundary.  The
seriality route `TimeCannotStop → Twin` is (honestly) close to a restatement of the goal.  This
route instead tries to make the ABSENCE of twins produce a concrete geometric pathology:

  NoTwinAbove M0
    → no safe holes in the genealogical sieve ornament            (HL3, green here)
    → a flat, zero-curvature, cost-free closed cycle              (HL5, THE WALL)
    → a perpetual engine                                          (HL17)
    → ⊥  (no perpetual engine on well-founded ℕ)                  (HL18, green here)
    → ∃ m > M0, TwinCenterZ m.

## What this file proves (all green, no sorry, no new axiom)

  * `safeHole_implies_twin` — HL2, a genuine sieve lemma: a center whose both sides survive every
    obstruction clock up to `√(6m+1)` is a twin (`Nat.prime_def_le_sqrt`);
  * `twinBound_forces_noSafeHole` — HL3, the contrapositive: no twins above `M0` ⟹ no safe holes;
  * `no_perpetualEngine` — HL18: a strictly ℕ-rank-spending step cannot exist (well-foundedness —
    the same prohibition as EPMI); this is the machine-form of "flat cost-free cycle is impossible";
  * `not_twinBoundAbove_of_bridge`, `twin_exists_above_of_bridge`,
    `twinLowersInfinite_of_allBridges` — §19: the route reaches the twin goal, CONDITIONAL on the
    one wall below.

## The one wall — named, NOT decreed

`OrnamentEngineBridge M0 : NoSafeHoleAbove M0 → PerpetualEngine` bundles HL5 (no safe holes forces a
flat ornament) and HL17 (flat forces a perpetual engine).  It is a HYPOTHESIS, never an axiom.
Proving it IS the twin conjecture: arithmetically it says the sifted set above `M0` cannot be empty
without its curvature closing into a flat, cost-free cycle — i.e. the sieve's curvature cannot all
dissipate harmlessly through boundaries.  That is exactly the parity barrier of sieve theory, and it
is not provable from the accounting identity alone (the identity is true, but forcing flatness needs a
bound on the boundary/dissipation term — the genuinely hard, unformalised input).  So this route does
NOT prove the twins; it relocates the single open node from the near-tautological seriality boundary
to a more concrete curvature/sieve statement.  `twin_prime_conjecture` stays `sorry`.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace GenealogicalOrnament

open EuclidsPath.Residuals

/-! ### The arithmetic sieve layer (green) -/

/-- The "safe hole" at center `m` (§11, §21): no obstruction clock `2 ≤ k ≤ √(6m+1)` divides either
    side `6m ± 1`.  This is the active-horizon triangular sieve condition. -/
def ActiveSieveSafe (m : ℕ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → k ≤ Nat.sqrt (6 * m + 1) →
    ¬ k ∣ (6 * m - 1) ∧ ¬ k ∣ (6 * m + 1)

/-- **HL2 (green sieve lemma): a safe hole is a twin.**  If no `k ∈ [2, √(6m+1)]` divides either
    side, both `6m − 1` and `6m + 1` are prime, i.e. `m` is a twin center. -/
theorem safeHole_implies_twin {m : ℕ} (hm : 1 ≤ m) (hsafe : ActiveSieveSafe m) :
    TwinCenterZ m := by
  have hsqrt_le : Nat.sqrt (6 * m - 1) ≤ Nat.sqrt (6 * m + 1) :=
    Nat.sqrt_le_sqrt (by omega)
  refine ⟨?_, ?_⟩
  · rw [Nat.prime_def_le_sqrt]
    refine ⟨by omega, ?_⟩
    intro k hk2 hkle
    exact (hsafe k hk2 (le_trans hkle hsqrt_le)).1
  · rw [Nat.prime_def_le_sqrt]
    refine ⟨by omega, ?_⟩
    intro k hk2 hkle
    exact (hsafe k hk2 hkle).2

/-- Twin absence above a horizon (§1). -/
def TwinBoundAbove (M0 : ℕ) : Prop :=
  ∀ m : ℕ, M0 < m → ¬ TwinCenterZ m

/-- No safe hole above `M0` (§12): every center above `M0` fails the sieve. -/
def NoSafeHoleAbove (M0 : ℕ) : Prop :=
  ∀ m : ℕ, M0 < m → 1 ≤ m → ¬ ActiveSieveSafe m

/-- **HL3 (green): twin absence forces no safe holes.**  The contrapositive of HL2 — if there is no
    twin above `M0`, then no center above `M0` can be a safe hole. -/
theorem twinBound_forces_noSafeHole {M0 : ℕ} (h : TwinBoundAbove M0) :
    NoSafeHoleAbove M0 := by
  intro m hM0 hm hsafe
  exact h m hM0 (safeHole_implies_twin hm hsafe)

/-! ### The perpetual-engine layer (green) -/

/-- A perpetual engine (§17): a state space with a step that strictly spends a finite ℕ rank from a
    start state — the machine-form of a flat, zero-fuel-drop, endlessly repeatable cycle. -/
structure PerpetualEngine where
  State : Type
  step : State → State
  rank : State → ℕ
  start : State
  spends : ∀ s : State, rank (step s) < rank s

/-- **HL18 (green): no perpetual engine.**  A strictly ℕ-rank-spending step cannot exist — its orbit
    would descend forever in ℕ.  Well-foundedness of `<` on ℕ; the same prohibition as EPMI. -/
theorem no_perpetualEngine (E : PerpetualEngine) : False :=
  Nat.strongRecOn (E.rank E.start)
    (motive := fun n => ∀ s : E.State, E.rank s = n → False)
    (fun n ih s hs => ih (E.rank (E.step s)) (hs ▸ E.spends s) (E.step s) rfl)
    E.start rfl

/-- The Prop "a perpetual engine exists" (so the wall below can live in `Prop`). -/
def PerpetualEngineExists : Prop := Nonempty PerpetualEngine

/-- No perpetual engine exists (green). -/
theorem no_perpetualEngineExists : ¬ PerpetualEngineExists :=
  fun ⟨E⟩ => no_perpetualEngine E

/-! ### The route — §19, conditional on the one named wall -/

/-- **The single open node (HL5 + HL17): no safe holes build a perpetual engine.**  A HYPOTHESIS,
    never an axiom.  Proving it is the twin conjecture (the sieve parity barrier); we name it, we do
    not decree it. -/
def OrnamentEngineBridge (M0 : ℕ) : Prop :=
  NoSafeHoleAbove M0 → PerpetualEngineExists

/-- **§19 (green conditional): the ornament route refutes twin absence, GIVEN the wall.** -/
theorem not_twinBoundAbove_of_bridge {M0 : ℕ}
    (bridge : OrnamentEngineBridge M0) : ¬ TwinBoundAbove M0 :=
  fun hBound => no_perpetualEngineExists (bridge (twinBound_forces_noSafeHole hBound))

/-- A twin above `M0`, GIVEN the wall (green conditional). -/
theorem twin_exists_above_of_bridge {M0 : ℕ}
    (bridge : OrnamentEngineBridge M0) : ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  by_contra hNone
  exact not_twinBoundAbove_of_bridge bridge (fun m hm htwin => hNone ⟨m, hm, htwin⟩)

/-- The route reaches the twin goal at every horizon, GIVEN the wall at every horizon. -/
theorem unboundedTwinCenters_of_allBridges
    (H : ∀ M0 : ℕ, OrnamentEngineBridge M0) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m :=
  fun M0 => twin_exists_above_of_bridge (H M0)

/-- **The route reaches `TwinLowers.Infinite` — CONDITIONAL on the wall, and only on it.**  This does
    NOT close the twin sorry: `OrnamentEngineBridge` is an unproven hypothesis (the parity barrier),
    not a theorem and not an axiom. -/
theorem twinLowersInfinite_of_allBridges
    (H : ∀ M0 : ℕ, OrnamentEngineBridge M0) : TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := unboundedTwinCenters_of_allBridges H N
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end GenealogicalOrnament
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
