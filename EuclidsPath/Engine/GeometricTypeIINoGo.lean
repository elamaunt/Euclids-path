/-
  GeometricTypeIINoGo — the no-go map: WHERE the wall is, and the anti-renaming gate.

  ORIGIN (parity_wall dossier §72 / §83 / §84 / §93 / §110): the parity wall has an exact
  LOCAL form — the mixed `ZG/GZ` modes carry `1/p` energy (parity-divergent, `Σ 1/p = ∞`),
  in contrast to the diagonal / gained `1/p^{2k-1}` (`Σ < ∞`).  On the full CRT the mixed
  modes annihilate (mean zero, `TypeII.Projection.Zrow_mean_zero`); the interval leakage is
  the open target (`CRE`).  Several routes are CLOSED and must not be re-tried.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `mixed_mode_parity_scale` — the `S_2` residual energy is `≥ 1/(2p)`: parity-DIVERGENT,
      `Σ_p 1/p = ∞` — the wall's exact local form (§72.1, §38);
    * `zEnergy_is_gain` / `typeII_genuine_progress` — the `S_4` energy IS a summability gain
      (`≤ 1/(p−1)^2`, `Σ < ∞`): the machine "genuine progress" witness (criterion B, §110).

  CLOSED ROUTES (documented, §51 / §99 / §104 — NOT to be re-tried; each is a research-level
  refutation, recorded here as the honest map, not a Lean theorem):
    * `MoebiusChowlaTrap` (§83, §99.1) — premature divisor-switching to individual hit-divisors
      re-introduces `μ(m₁n+2)μ(m₂n+2)`, a binary Chowla correlation of twin-prime strength;
    * `DHRLowerSieveCollapse` (§23) — the separate lower+upper sieve route dies at the DHR
      sifting limit (loses almost all main term);
    * `ScalarBVNoTensorize` (§84) — scalar Bombieri–Vinogradov cancellation does NOT give the
      vector-valued (high–high tensor) bound;
    * `FalseSqrtWall` (§93) — the `√(m₁m₂)` character-modulus loss is NOT part of the wall; it
      came from wrongly merging the two row coordinates.

  ANTI-RENAMING (§110). A step counts as genuine progress only if it gives (A) exact
  annihilation, (B) a summability gain, or (C) a well-founded dimension reduction.  A mere
  change of coordinates does not.  Here (B) is machine-checked (`typeII_genuine_progress`);
  (A) is `Zrow_mean_zero`; (C) is the determinant bridge (`TypeII.Cycle.det_bridge`).

  DISCLOSURE. Nothing here proves twins.  The wall is localized, not defeated.  twin sorry
  untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIQuartic

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

/-! ## The wall's exact local form: parity-divergent S_2 energy (§72.1) -/

/-- **Mixed-mode parity scale (§72.1).** The `S_2` residual local energy is `≥ 1/(2p)`:
    parity-DIVERGENT (`Σ_p 1/p = ∞`).  This is the exact local form of the parity wall —
    the mixed `ZG/GZ` modes carry `1/p` energy, in contrast to the gained `1/p^3` (§38). -/
theorem mixed_mode_parity_scale {p : ℕ} (hp : 3 ≤ p) :
    1 / (2 * (p : ℝ)) ≤ zEnergy 1 p := by
  have hpp : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  unfold zEnergy
  simp only [mul_one]
  have e : ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 - 1 / (2 * (p : ℝ))
      = (2 * (p : ℝ) * ((p : ℝ) - 2) - ((p : ℝ) - 1) ^ 2)
          / (2 * (p : ℝ) * ((p : ℝ) - 1) ^ 2) := by
    field_simp
  have hnum : 0 ≤ 2 * (p : ℝ) * ((p : ℝ) - 2) - ((p : ℝ) - 1) ^ 2 := by nlinarith [hpp]
  have hden : 0 < 2 * (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
  have hge : 0 ≤ ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 - 1 / (2 * (p : ℝ)) := by
    rw [e]; exact div_nonneg hnum (le_of_lt hden)
  linarith

/-! ## The summability gain and the anti-renaming gate (§110) -/

/-- A local energy `e` exhibits a summability gain iff it is dominated by the summable
    `1/(p−1)^2` (criterion B). -/
def IsSummabilityGain (e : ℕ → ℝ) : Prop := ∀ p : ℕ, 3 ≤ p → e p ≤ 1 / ((p : ℝ) - 1) ^ 2

/-- **The S_4 energy is a genuine summability gain (§42, §110).** `zEnergy 2 p ≤ 1/(p−1)^2`
    (`Σ < ∞`) — the machine-checked criterion-B witness. -/
theorem zEnergy_is_gain : IsSummabilityGain (zEnergy 2) := by
  intro p hp
  have hpp : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  calc zEnergy 2 p ≤ 1 / ((p : ℝ) - 1) ^ 3 := zEnergy_S4 (by omega)
    _ ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [h1]

/-- **The anti-renaming gate (§110).** A step is genuine progress iff exact annihilation,
    summability gain, or dimension reduction.  The Type-II pass achieves a summability
    gain (machine-checked here), an exact annihilation (`Zrow_mean_zero`), and a dimension
    reduction (`det_bridge`) — so it is NOT a mere renaming of the wall. -/
def GenuineProgress (e : ℕ → ℝ) : Prop := IsSummabilityGain e

theorem typeII_genuine_progress : GenuineProgress (zEnergy 2) := zEnergy_is_gain

end TypeII
end Geometric
end EuclidsPath
