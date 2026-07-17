/-
  GeometricTypeIIBrunTwinRate — BRUN STAGE 4a: the QUANTITATIVE RATE, one named
  analytic input away.  The parametric bound

      twins(N) ≤ B·N + 3^z + z/6 + 1        (for ANY product bound B at level z)

  is unconditional glue over stages 1–3; feeding it the classical Mertens
  product bound `∏_{5≤p≤z}(1 − 2/p) ≤ C/log²z` — stated as a NAMED HYPOTHESIS,
  the house conditional-theorem pattern — yields the machine-checked rate

      twins(N) ≤ C·N/log²z + 3^z + z/6 + 1        (all N, all z ≥ 2).

  ORIGIN.  Idea-generation session continuation (the Brun track's formal
  closure).  Stages 1–3 are unconditional (Bonferroni key, sieve instance,
  density zero); the QUANTITATIVE stage needs exactly one input the mathlib pin
  does not carry: a Mertens-type bound.  Rather than leaving stage 4 as prose,
  this module reduces it to that ONE input — everything else is machine-checked.
  This is the same honest architecture as the repo's `twins_of_typeII` (CRE as
  the named input) and `twins_of_oneWing` (the bias premise): a green
  conditional theorem whose condition is a classical named statement.

  THE ASYMPTOTIC READING (prose only — the theorems are the finite
  inequalities): choosing `z ≈ ½·log N` makes `3^z ≈ N^{0.55} = o(N/log²log N)`
  and gives `twins(N) = O(N/(log log N)²)` — the crude Brun rate.  The TRUE
  Brun rate `O(N·(log log N)²/log²N)` requires the truncated sieve with the
  stage-2 tail tool (`esymmOn_le_pow_div_factorial`, dormant since stage 2) and
  level `z = N^{1/(c·t)}` — that is stage 4b, named here and NOT claimed.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `sievePrimes_card_le` — `k = #sievePrimes z ≤ z`;
    * `twin_errSum_le_pow` — the error budget in level form: `errSum ≤ 3^z`;
    * `twin_count_of_prod_le` — **THE PARAMETRIC RATE** (unconditional): any
      bound `B` on the Legendre product yields `twins(N) ≤ B·N + 3^z + z/6 + 1`;
    * `twin_count_log_rate` — **THE CONDITIONAL RATE**: under the named Mertens
      hypothesis `hM : ∀ z ≥ 2, ∏_{5≤p≤z}(1 − 2/p) ≤ C/log²z`, for ALL `N, z ≥ 2`:
      `twins(N) ≤ C·N/log²z + 3^z + z/6 + 1`.

  DISCLOSURES (mandatory reading before quoting):
    * THE MERTENS HYPOTHESIS IS NOT PROVED HERE — it is classical (a weak form
      of Mertens' third theorem, true with room to spare) but ABSENT from the
      pin; it enters as an explicit hypothesis of `twin_count_log_rate`, never
      silently.  Discharging it (or importing a future mathlib Mertens) is the
      named remaining step of stage 4a.
    * STAGE 4b (the true Brun rate via truncation + the esymm tail) is NOT
      claimed; the stage-2 tail tool stays dormant.
    * STILL NOT THE TWIN CONJECTURE — upper bounds only; Brun's method is
      structurally blind to the parity wall.  No registered target (CRE,
      SemiprimeShortRestriction, HigherConductorDispersion, LowFreqRootCoherence,
      OneWingTarget) is touched: NOT a §110 event.
    * ZERO NEW OPEN PROPS (the Mertens input is a HYPOTHESIS of a theorem, not
      a named open Prop).  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIBrunTwinDensity

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### The level-form error budget -/

/-- The sieve-prime count is at most the level: `k ≤ z`. -/
theorem sievePrimes_card_le (z : ℕ) : (sievePrimes z).card ≤ z := by
  calc (sievePrimes z).card ≤ (Finset.Icc 5 z).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = z + 1 - 5 := Nat.card_Icc 5 z
    _ ≤ z := by omega

/-- The error budget in LEVEL form: `errSum ≤ 3^z` (from the stage-3 `3^k` and
    `k ≤ z`). -/
theorem twin_errSum_le_pow (N z t : ℕ) :
    (twinSieve N z).errSum (bonferroniWeight t) ≤ (3 : ℝ) ^ z := by
  refine (twin_errSum_le_const N z t).trans ?_
  exact pow_le_pow_right₀ (by norm_num) (sievePrimes_card_le z)

/-! ### The parametric rate -/

/-- **THE PARAMETRIC RATE** (unconditional): any bound `B ≥ 0` on the Legendre
    product at level `z` bounds the twin count by `B·N + 3^z + z/6 + 1` —
    stages 1–3 glued into a single consumable inequality. -/
theorem twin_count_of_prod_le (N z : ℕ) {B : ℝ}
    (hB : ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)) ≤ B) :
    (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      ≤ B * N + (3 : ℝ) ^ z + ((z : ℝ) / 6 + 1) := by
  set k := (sievePrimes z).card with hk
  have hupper := brun_twin_upper N z (2 * k) (even_two_mul k)
  rw [twin_mainSum_eq N z (2 * k) (by omega)] at hupper
  have herr := twin_errSum_le_pow N z (2 * k)
  have hprodN : (N : ℝ) * ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ))
      ≤ (N : ℝ) * B :=
    mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg N)
  calc (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      ≤ (N : ℝ) * ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ))
          + (twinSieve N z).errSum (bonferroniWeight (2 * k))
          + ((z : ℝ) / 6 + 1) := hupper
    _ ≤ (N : ℝ) * B + (3 : ℝ) ^ z + ((z : ℝ) / 6 + 1) := by linarith
    _ = B * N + (3 : ℝ) ^ z + ((z : ℝ) / 6 + 1) := by ring

/-! ### The conditional rate (the named Mertens input) -/

/-- **THE CONDITIONAL RATE — BRUN STAGE 4a**: under the NAMED Mertens-type
    hypothesis `∏_{5≤p≤z}(1 − 2/p) ≤ C/log²z` (classical, NOT in the pin,
    entering explicitly), the twin count obeys

        `twins(N) ≤ C·N/log²z + 3^z + z/6 + 1`   for ALL `N` and ALL `z ≥ 2`.

    Prose reading (not Lean-stated): `z ≈ ½·log N` gives the crude Brun rate
    `O(N/(log log N)²)`; the true Brun rate is stage 4b (truncation + esymm,
    not claimed). -/
theorem twin_count_log_rate {C : ℝ}
    (hM : ∀ z : ℕ, 2 ≤ z →
      ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)) ≤ C / (Real.log z) ^ 2)
    (N z : ℕ) (hz : 2 ≤ z) :
    (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      ≤ C / (Real.log z) ^ 2 * N + (3 : ℝ) ^ z + ((z : ℝ) / 6 + 1) :=
  twin_count_of_prod_le N z (hM z hz)

/-! ### Axiom audit -/

#print axioms sievePrimes_card_le
#print axioms twin_errSum_le_pow
#print axioms twin_count_of_prod_le
#print axioms twin_count_log_rate

end TypeII
end Geometric
end EuclidsPath
