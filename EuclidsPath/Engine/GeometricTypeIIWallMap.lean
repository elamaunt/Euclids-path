/-
  GeometricTypeIIWallMap — the capstone honest map: corrections, open residuals, final package.

  ORIGIN (parity_wall Prime-Chaos session dossier §56–68).  After all resummations the parity wall
  is no longer in local compatibility, `Zrow_mean_zero`, arbitrary forest backgrounds, the
  high-conductor divisor tail, principal-character extensions, prime exact conductors, determinant
  counting alone, or the passage to `S₆,S₈,…` (§66).  It is concentrated in TWO explicit objects:
  the degree-two exact-conductor short restriction (`c = pq`) and the signed low-frequency CRT-root
  remainder, together with a negative one-wing Liouville bias.  Several routes are CLOSED (§56–62):
  divisor switching returns the survivor (§60), the `√M` loss is not part of the wall (§61), higher
  moments reproduce the fixed point (§59).

  STATUS REGISTRY.
    * §63 (24 blocks) — fully closed algebra/local: CRT margin, Möbius–CRT residual, Gram/isometry,
      spectrum, prime-chaos + S₂/S₄ threshold, one-defect fixed point, forest recursion + nonlocal
      closure, exact-conductor resummation, degree-two masses, root moments, Kloosterman geometry.
    * §64 — closed under standard inputs (large sieve, low conductors, vector-valued leaf).
    * §65 — open residuals A–E as named `Prop`s (not `sorry`): A+B bundled in `OneWingTarget`
      (one-wing route), C = `SemiprimeShortRestriction`, D = `HigherConductorDispersion`,
      E = `LowFreqRootCoherence` (root module).
    * §66 — the two wall centers: degree-two `c = pq` and the low-frequency CRT-root remainder.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `divisor_switch_returns_survivor` — `Σ_{d|M,d>D} μ(d) = (Σ_{d|M} μ) − Σ_{d|M,d≤D} μ(d)` (§60);
    * `twins_of_final_package` — closing the one-wing route (`OneWingTarget`) yields infinitely many
      twin centers: the final logical route without hidden `Bridge` (§68).

  DISCLOSURE. This is NOT a proof of the twin prime conjecture — the dossier proves it isn't: the
  wall is localized to two explicit objects, not defeated.  twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIILiouville

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ## Corrections and withdrawn overclaims (§56–62) -/

/-- **Divisor switching returns the survivor (§60).** The high-divisor Möbius tail equals the full
    Möbius sum minus the truncated head — switching alone does not close the tail; it returns the
    hard survivor. -/
theorem divisor_switch_returns_survivor (M D : ℕ) :
    (∑ d ∈ M.divisors.filter (fun d => D < d), (ArithmeticFunction.moebius d : ℤ))
      = (∑ d ∈ M.divisors, (ArithmeticFunction.moebius d : ℤ))
        - ∑ d ∈ M.divisors.filter (fun d => d ≤ D), (ArithmeticFunction.moebius d : ℤ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not M.divisors (fun d => D < d)
    (fun d => (ArithmeticFunction.moebius d : ℤ))
  have hfeq : M.divisors.filter (fun d => ¬ (D < d)) = M.divisors.filter (fun d => d ≤ D) := by
    apply Finset.filter_congr
    intro d _
    exact Nat.not_lt
  rw [hfeq] at hsplit
  linarith [hsplit]

/-! ## The open residuals (§65) -/

-- Residuals A (pair-rough positivity) and B (negative one-wing Liouville bias) are bundled,
-- non-trivially and tied to the actual prime counts, in `OneWingTarget` (the one-wing route,
-- `GeometricTypeIILiouville`).  Residual E (low-frequency root coherence) is `LowFreqRootCoherence`
-- (`GeometricTypeIIRoots`).  Residuals C and D are the CRE-shape targets below.

/-- **Residual C (§65): exact semiprime-conductor short restriction.** The degree-two connected core
    `R^{[2]}` obeys the cross-modulus energy bound (CRE shape). -/
def SemiprimeShortRestriction (𝔈 : ℝ → ℝ) : Prop :=
  ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → 𝔈 x ≤ C * x ^ 2 / (Real.log x) ^ B

/-- **Residual D (§65): higher exact-conductor dispersion.** Conductors `ω(c) ≥ 3` need a short
    multilinear dispersion bound (CRE shape). -/
def HigherConductorDispersion (𝔈 : ℝ → ℝ) : Prop :=
  ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → 𝔈 x ≤ C * x ^ 2 / (Real.log x) ^ B

/-! ## The final package (§68) -/

/-- **The final package (§68).** Closing the one-wing route (`OneWingTarget` — pair-rough positivity
    together with a negative one-wing Liouville bias) yields infinitely many twin centers.  This is
    the final logical route to twins, without any hidden `Bridge`. -/
theorem twins_of_final_package (H : OneWingTarget) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsTwinCenter m :=
  twinCenters_cofinal_of_oneWing H

end TypeII
end Geometric
end EuclidsPath
