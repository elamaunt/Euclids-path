/-
  Engine/GeometricTwinClassFactorPlus — wave-5 W5-1 brick of the
  binary-cancellation program: the PLUS-WINDOW instantiation of the Arm-A
  per-class factorization identity.

  ORIGIN.  Wave 4 (W4-2, `GeometricTwinClassFactor`) proved the general
  per-class factorization identity `liouville_sum_classFactor_map` — for any
  finite index set, any wing map with the pointwise prime/semiprime dichotomy,
  any modulus and any class weight, the weighted Liouville sum factors EXACTLY
  through per-class (rough count, prime count) pairs — and instantiated it on
  the MINUS rough window (`6m−1`).  This module closes the mirror: the same
  two spellings on the PLUS rough window (`6m+1`), with the dichotomy
  discharged by `plusRoughWindow_omega` (`GeometricTypeIIPlusWing`), in the
  same regime `1 ≤ z`, `X < z³`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `plusWindow_liouville_classFactor` — for `z ≥ 1` and `X < z³`, the
      plus-window Liouville sum against ANY mod-`q` weight `g : ZMod q → ℤ`
      factors through per-class (rough, prime) counts:
        `Σ_{m∈W⁺} λ(6m+1)·g(6m+1 mod q)
           = Σ_{c : ZMod q} g(c)·(#{fiber c} − 2·#{prime fiber c})`;
    * `plusWindow_pow_classFactor` — the same identity in the repo's explicit
      `(−1)^{Ω(6m+1)}` vocabulary (matching `plusWindow_liouville_eq`).

  DISCLOSURES.
    * Unconditional identities; NOTHING is estimated.  The general lemma is
      window-agnostic; only the instantiation and the Ω-dichotomy discharge
      differ from the minus brick.
    * The parity wall is UNTOUCHED: the wall remains the single arrow
      `Chowla2LogHypothesis → Chowla2Hypothesis` (un-averaging), and nothing
      here bears on it.  No §110 event is claimed.
    * The two windows are per-wing objects over DIFFERENT `m`-sets; no
      per-wing→pair-rough bridge is claimed (three such bridges were refuted).
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Engine.GeometricTwinClassFactor
import EuclidsPath.Engine.GeometricTypeIIPlusWing

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### Instantiation on the repo's z-rough plus window -/

/-- **Per-class factorization on the plus rough window.**  For `z ≥ 1` and
    `X < z³` (the regime where `plusRoughWindow_omega` discharges the
    dichotomy from real arithmetic), the plus-window Liouville sum against
    ANY mod-`q` weight factors through per-class (rough, prime) counts —
    the `6m+1` mirror of `minusWindow_liouville_classFactor`. -/
theorem plusWindow_liouville_classFactor {X z q : ℕ} [NeZero q]
    (hz : 1 ≤ z) (hXz : X < z ^ 3) (g : ZMod q → ℤ) :
    ∑ m ∈ plusRoughWindow X z,
        liouville (6 * m + 1) * g (((6 * m + 1 : ℕ) : ZMod q))
      = ∑ c : ZMod q, g c *
          ((((plusRoughWindow X z).filter
              fun m => (((6 * m + 1 : ℕ) : ZMod q)) = c).card : ℤ)
            - 2 * (((plusRoughWindow X z).filter
              fun m => (((6 * m + 1 : ℕ) : ZMod q)) = c
                ∧ (6 * m + 1).Prime).card : ℤ)) :=
  liouville_sum_classFactor_map (plusRoughWindow X z) (fun m => 6 * m + 1)
    (plusRoughWindow_omega hz hXz) g

/-- **The `(−1)^Ω` spelling.**  The same identity in the repo's explicit
    `(−1)^{Ω(6m+1)}` vocabulary (matching `plusWindow_liouville_eq`). -/
theorem plusWindow_pow_classFactor {X z q : ℕ} [NeZero q]
    (hz : 1 ≤ z) (hXz : X < z ^ 3) (g : ZMod q → ℤ) :
    ∑ m ∈ plusRoughWindow X z,
        ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) * g (((6 * m + 1 : ℕ) : ZMod q))
      = ∑ c : ZMod q, g c *
          ((((plusRoughWindow X z).filter
              fun m => (((6 * m + 1 : ℕ) : ZMod q)) = c).card : ℤ)
            - 2 * (((plusRoughWindow X z).filter
              fun m => (((6 * m + 1 : ℕ) : ZMod q)) = c
                ∧ (6 * m + 1).Prime).card : ℤ)) := by
  have hcongr : ∀ m ∈ plusRoughWindow X z,
      ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) * g (((6 * m + 1 : ℕ) : ZMod q))
        = liouville (6 * m + 1) * g (((6 * m + 1 : ℕ) : ZMod q)) := by
    intro m _
    rw [ArithmeticFunction.liouville_apply (by omega : 6 * m + 1 ≠ 0)]
  rw [Finset.sum_congr rfl hcongr]
  exact plusWindow_liouville_classFactor hz hXz g

end TypeII
end Geometric
end EuclidsPath
