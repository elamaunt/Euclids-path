/-
  Engine/GeometricTwinClassFactor — wave-4 W4-2 brick of the binary-cancellation
  program: the Arm-A PER-CLASS FACTORIZATION IDENTITY, machine-proved.

  ORIGIN (tools/RESEARCH_binary_cancellation.md, wave 3, probe W3-2).  The LFU
  SP-subtraction probe discovered empirically-then-algebraically that on any
  Omega <= 2 window (the prime/semiprime dichotomy), the residual of the
  per-class S-P model at EXACT rational frequencies is identically zero: at
  rational points, ALL structure of the Liouville function on dichotomy windows
  is per-class (rough count, prime count) bookkeeping.  This module upgrades
  that "residual identically zero" discovery to an unconditional Lean identity.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `liouville_eq_on_dichotomy` — on `Omega(n) ∈ {1,2}`,
      `λ(n) = 1 − 2·1_ℙ(n)` (the ℤ-valued form of `prime_liouville_form`);
    * `liouville_sum_classFactor_map` — for ANY finite index set `R`, ANY wing
      map `w` with the pointwise dichotomy, ANY modulus `q ≠ 0` and ANY weight
      `g : ZMod q → ℤ`:
        `Σ_{n∈R} λ(w n)·g(w n mod q)
           = Σ_{c : ZMod q} g(c)·(#{fiber c} − 2·#{prime fiber c})` —
      the weighted Liouville sum factors EXACTLY through per-class
      (rough count, prime count) pairs;
    * `liouville_sum_classFactor` — the `w = id` special case (the probe's
      literal Arm-A statement);
    * `minusWindow_liouville_classFactor` — instantiation on the repo's
      z-rough minus window (`z ≥ 1`, `X < z³`; dichotomy discharged by
      `minusRoughWindow_omega`), plus the `(−1)^Ω` spelling
      `minusWindow_pow_classFactor` matching `minusWindow_liouville_eq`.

  DISCLOSURES.
    * Unconditional identities; NOTHING is estimated.  This is the
      Fourier-side companion of the proven wing-sign theorems: it certifies
      that at rational frequencies the only structure available to λ on
      dichotomy windows is per-class prime/semiprime counting.
    * The parity wall is UNTOUCHED: the wall remains the single arrow
      `Chowla2LogHypothesis → Chowla2Hypothesis` (un-averaging), and nothing
      here bears on it.  No §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Engine.GeometricTypeIIWingWindow

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### (1) The ℤ-valued Liouville dichotomy -/

/-- **Liouville normal form on the dichotomy (ℤ-valued).**  On `Ω(n) ∈ {1,2}`
    (primes and semiprimes), `λ(n) = 1 − 2·1_ℙ(n)`: the sign of λ carries
    EXACTLY the prime indicator and nothing else. -/
theorem liouville_eq_on_dichotomy {n : ℕ}
    (hn : cardFactors n = 1 ∨ cardFactors n = 2) :
    liouville n = 1 - 2 * (if n.Prime then (1 : ℤ) else 0) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [ArithmeticFunction.map_zero] at hn
    rcases hn with h | h <;> omega
  rw [ArithmeticFunction.liouville_apply hn0]
  rcases hn with h | h
  · rw [h, if_pos (cardFactors_eq_one_iff_prime.mp h)]; norm_num
  · have hnp : ¬ n.Prime := by
      intro hp
      rw [cardFactors_eq_one_iff_prime.mpr hp] at h
      omega
    rw [h, if_neg hnp]; norm_num

/-! ### (2) The per-class factorization identity -/

/-- **The Arm-A per-class factorization identity (mapped form).**  For any
    finite index set `R`, any wing map `w` whose values satisfy the
    prime/semiprime dichotomy pointwise, any modulus `q ≠ 0` and any
    class-function weight `g : ZMod q → ℤ`, the weighted Liouville sum
    factors EXACTLY through the per-class (rough count, prime count) pairs. -/
theorem liouville_sum_classFactor_map {q : ℕ} [NeZero q] (R : Finset ℕ)
    (w : ℕ → ℕ) (hR : ∀ n ∈ R, cardFactors (w n) = 1 ∨ cardFactors (w n) = 2)
    (g : ZMod q → ℤ) :
    ∑ n ∈ R, liouville (w n) * g ((w n : ZMod q))
      = ∑ c : ZMod q, g c *
          (((R.filter fun n => ((w n : ZMod q)) = c).card : ℤ)
            - 2 * ((R.filter fun n =>
                ((w n : ZMod q)) = c ∧ (w n).Prime).card : ℤ)) := by
  refine ((Finset.sum_fiberwise R (fun n => ((w n : ZMod q)))
      (fun n => liouville (w n) * g ((w n : ZMod q)))).symm).trans
    (Finset.sum_congr rfl fun c _ => ?_)
  calc ∑ n ∈ R.filter (fun n => ((w n : ZMod q)) = c),
          liouville (w n) * g ((w n : ZMod q))
      = ∑ n ∈ R.filter (fun n => ((w n : ZMod q)) = c),
          (1 - 2 * (if (w n).Prime then (1 : ℤ) else 0)) * g c := by
        refine Finset.sum_congr rfl fun n hn => ?_
        obtain ⟨hnR, hnc⟩ := Finset.mem_filter.mp hn
        rw [hnc, liouville_eq_on_dichotomy (hR n hnR)]
    _ = (∑ n ∈ R.filter (fun n => ((w n : ZMod q)) = c),
          (1 - 2 * (if (w n).Prime then (1 : ℤ) else 0))) * g c := by
        rw [Finset.sum_mul]
    _ = (((R.filter fun n => ((w n : ZMod q)) = c).card : ℤ)
          - 2 * ((R.filter fun n =>
              ((w n : ZMod q)) = c ∧ (w n).Prime).card : ℤ)) * g c := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
          Finset.filter_filter]
        simp
    _ = g c * (((R.filter fun n => ((w n : ZMod q)) = c).card : ℤ)
          - 2 * ((R.filter fun n =>
              ((w n : ZMod q)) = c ∧ (w n).Prime).card : ℤ)) := mul_comm _ _

/-- **The Arm-A per-class factorization identity.**  On a finite set with the
    pointwise prime/semiprime dichotomy, ANY class-function-weighted Liouville
    sum equals the per-class combination
    `Σ_c g(c)·(#{class c} − 2·#{primes in class c})`. -/
theorem liouville_sum_classFactor {q : ℕ} [NeZero q] (R : Finset ℕ)
    (hR : ∀ n ∈ R, cardFactors n = 1 ∨ cardFactors n = 2) (g : ZMod q → ℤ) :
    ∑ n ∈ R, liouville n * g ((n : ZMod q))
      = ∑ c : ZMod q, g c *
          (((R.filter fun n : ℕ => ((n : ZMod q)) = c).card : ℤ)
            - 2 * ((R.filter fun n : ℕ =>
                ((n : ZMod q)) = c ∧ n.Prime).card : ℤ)) :=
  liouville_sum_classFactor_map R (fun n => n) hR g

/-! ### (3) Instantiation on the repo's z-rough minus window -/

/-- **Per-class factorization on the minus rough window.**  For `z ≥ 1` and
    `X < z³` (the regime where `minusRoughWindow_omega` discharges the
    dichotomy from real arithmetic), the minus-window Liouville sum against
    ANY mod-`q` weight factors through per-class (rough, prime) counts —
    the exact statement wave-3 probe W3-2 measured as "residual identically
    zero" at rational frequencies. -/
theorem minusWindow_liouville_classFactor {X z q : ℕ} [NeZero q]
    (hz : 1 ≤ z) (hXz : X < z ^ 3) (g : ZMod q → ℤ) :
    ∑ m ∈ minusRoughWindow X z,
        liouville (6 * m - 1) * g (((6 * m - 1 : ℕ) : ZMod q))
      = ∑ c : ZMod q, g c *
          ((((minusRoughWindow X z).filter
              fun m => (((6 * m - 1 : ℕ) : ZMod q)) = c).card : ℤ)
            - 2 * (((minusRoughWindow X z).filter
              fun m => (((6 * m - 1 : ℕ) : ZMod q)) = c
                ∧ (6 * m - 1).Prime).card : ℤ)) :=
  liouville_sum_classFactor_map (minusRoughWindow X z) (fun m => 6 * m - 1)
    (minusRoughWindow_omega hz hXz) g

/-- **The `(−1)^Ω` spelling.**  The same identity in the repo's explicit
    `(−1)^{Ω(6m−1)}` vocabulary (matching `minusWindow_liouville_eq`). -/
theorem minusWindow_pow_classFactor {X z q : ℕ} [NeZero q]
    (hz : 1 ≤ z) (hXz : X < z ^ 3) (g : ZMod q → ℤ) :
    ∑ m ∈ minusRoughWindow X z,
        ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) * g (((6 * m - 1 : ℕ) : ZMod q))
      = ∑ c : ZMod q, g c *
          ((((minusRoughWindow X z).filter
              fun m => (((6 * m - 1 : ℕ) : ZMod q)) = c).card : ℤ)
            - 2 * (((minusRoughWindow X z).filter
              fun m => (((6 * m - 1 : ℕ) : ZMod q)) = c
                ∧ (6 * m - 1).Prime).card : ℤ)) := by
  have hcongr : ∀ m ∈ minusRoughWindow X z,
      ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) * g (((6 * m - 1 : ℕ) : ZMod q))
        = liouville (6 * m - 1) * g (((6 * m - 1 : ℕ) : ZMod q)) := by
    intro m hm
    obtain ⟨hmI, -⟩ := Finset.mem_filter.mp hm
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hmI
    rw [ArithmeticFunction.liouville_apply (by omega : 6 * m - 1 ≠ 0)]
  rw [Finset.sum_congr rfl hcongr]
  exact minusWindow_liouville_classFactor hz hXz g

end TypeII
end Geometric
end EuclidsPath
