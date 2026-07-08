import EuclidsPath.Engine.Step00TwinFractalArithmetic
import EuclidsPath.Engine.Step00OrnamentCurvatureReservoir

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 sign/parity twin node — the one barrier, named and certified as EXACTLY the twins

Every honest route in this project (the relative-curvature realization, the four-corner balance
`B₅ = N₀₀ − N₃₃ > 0`, the fractal short-survivor) converges to a single distributional node: for
every horizon there is a surviving center in the active window.  This is the **sign / parity barrier**
of sieve theory — the four-corner negative rank correlation (`R_fc < 1`) is a sign statement, kin to
the Liouville `λ`-sum (prose ch. 32, ch. 12/14; the `N = 2^k` data up to `k = 27` in ch. 51 shows
`B₅ > 0` with a margin `1 − R_fc → 0⁺`).  It is why bounded-gap results (Zhang/Maynard) do not reach
gap 2.

This file makes that node first-class and machine-certifies it is **EXACTLY** the twin conjecture —
provably equivalent in BOTH directions, so it is neither a shortcut nor a weakening, and it does not
multiply open problems: it is the one wall, named.

  * `TwinSurvivorNode` — for every `M0`, some active window has a short survivor;
  * `shortSurvivor_of_twinAbove` — conversely a twin center IS a short survivor (green arithmetic);
  * `twinSurvivorNode_iff_unboundedTwinCenters` — the node ⟺ the twin conjecture (both directions,
    green);
  * `twinLowersInfinite_of_twinSurvivorNode` — the node yields `TwinLowers.Infinite`.

Nothing here proves the node.  Proving it (uniformly for all `M0 ≥ 5`) is the parity barrier;
`twin_prime_conjecture` stays `sorry`.
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace GenealogicalOrnament
namespace Fractal

open EuclidsPath.Residuals

/-- **The sign/parity twin node.**  For every horizon `M0` there is a clock scale `z` whose active
    window `(M0, (z²-1)/6]` contains a survivor of every prime clock `≤ z` — i.e. a twin.  This is
    the four-corner `N₀₀ > 0`-in-every-tail statement, the distributional parity node. -/
def TwinSurvivorNode : Prop := ∀ M0 : ℕ, ∃ z : ℕ, ShortSurvivor z M0

/-- **Green:** a twin center above `M0` IS a short survivor (take the clock scale `z = 6m - 2`: it is
    below both prime sides `6m ± 1`, so no prime `≤ z` divides them, and above `√(6m+1)`). -/
theorem shortSurvivor_of_twinAbove {M0 m : ℕ} (hM0 : M0 < m) (htwin : TwinCenterZ m) :
    ShortSurvivor (6 * m - 2) M0 := by
  have hm : 1 ≤ m := by omega
  refine ⟨m, ⟨hM0, ?_⟩, ?_⟩
  · -- 6m + 1 ≤ (6m - 2)²
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hz : 6 * (k + 1) - 2 = 6 * k + 4 := by omega
    rw [hz]
    nlinarith [Nat.zero_le k]
  · -- SurvivesUpTo (6m - 2) m: no prime 5 ≤ p ≤ 6m-2 divides either (prime) side
    intro p hp h5 hpz hforbidden
    rcases hforbidden with hd | hd
    · have hpe : p = 6 * m - 1 :=
        (htwin.1.eq_one_or_self_of_dvd p hd).resolve_left hp.ne_one
      omega
    · have hpe : p = 6 * m + 1 :=
        (htwin.2.eq_one_or_self_of_dvd p hd).resolve_left hp.ne_one
      omega

/-- **The node is EXACTLY the twin conjecture** (both directions, green): forward by
    `shortSurvivor_implies_twin`, backward by `shortSurvivor_of_twinAbove`.  So it is the one barrier,
    not a shortcut and not a weakening. -/
theorem twinSurvivorNode_iff_unboundedTwinCenters :
    TwinSurvivorNode ↔ (∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) := by
  constructor
  · intro H M0
    obtain ⟨z, hs⟩ := H M0
    exact shortSurvivor_implies_twin hs
  · intro H M0
    obtain ⟨m, hM0, ht⟩ := H M0
    exact ⟨6 * m - 2, shortSurvivor_of_twinAbove hM0 ht⟩

/-- **The sign/parity node yields twin infinitude** — conditional on the node (the parity barrier),
    which this file does NOT prove. -/
theorem twinLowersInfinite_of_twinSurvivorNode (H : TwinSurvivorNode) : TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ := twinSurvivorNode_iff_unboundedTwinCenters.mp H N
  exact ⟨m, hNm, by
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ⟩

end Fractal
end GenealogicalOrnament
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
