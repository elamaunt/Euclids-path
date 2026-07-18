/-
  GeometricTwinJacobsthal — THE COMPLETE JACOBSTHAL CROSS-SUM, MACHINE-CHECKED:
  for every prime p ∉ {2, 3}, with χ the quadratic character of ZMod p,

      Σ_{m : ZMod p} χ(36·m² − 1) = −1.

  This is the algebraic kernel of the Siegel-dichotomy exploration: the split
  form (6m−1)(6m+1) = 36m²−1 exhibits SQUARE-ROOT-STRENGTH cancellation at the
  complete-sum level — the complete sum is O(1), not main-term sized — so the
  SPLIT FORM ITSELF DOES NOT OBSTRUCT cancellation at any single prime modulus.

  PROOF (classical, Jacobsthal 1907 style).  Substitute u = 6m (a bijection of
  ZMod p since 6 is a unit for p ∤ 6); factor χ(u²−1) = χ(u−1)·χ(u+1); shift
  v = u − 1 to get Σ_v χ(v)·χ(v+2); for v ≠ 0 pull out χ(v)² = 1 to rewrite
  the term as χ(1 + 2·v⁻¹), whose argument sweeps ZMod p \ {1} bijectively as
  v sweeps the nonzero elements; the completed sum of χ vanishes, leaving
  −χ(1) = −1.

  DISCLOSURES.
    * COMPLETE-SUM LEVEL ONLY.  This brick evaluates the full sum over a
      residue ring.  It makes NO claim about incomplete sums, about sums
      restricted to pair-rough (sieved) windows, or about the integer-side
      Liouville sum Σ λ(36m²−1) — the empirical sign-flip of that sum under
      sieve restriction is precisely the phenomenon this kernel does NOT
      touch.  The parity wall is UNTOUCHED.
    * No new axioms, no sorry.  The twin sorry (`twin_prime_conjecture`)
      is untouched.  This file is self-contained modulo mathlib and is NOT
      registered in `EuclidsPath.lean` by itself.
-/
import Mathlib

set_option maxHeartbeats 800000

namespace EuclidsPath
namespace Geometric
namespace Jacobsthal

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- `2` is a nonzero element of `ZMod p` when `p ≠ 2`. -/
theorem two_ne_zero' (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)

/-- `3` is a nonzero element of `ZMod p` when `p ≠ 3`. -/
theorem three_ne_zero' (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h'
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hdvd)

/-- `6` is a nonzero element of `ZMod p` when `p ∉ {2, 3}`. -/
theorem six_ne_zero' (hp2 : p ≠ 2) (hp3 : p ≠ 3) : (6 : ZMod p) ≠ 0 := by
  have h : (6 : ZMod p) = 2 * 3 := by norm_num
  rw [h]
  exact mul_ne_zero (two_ne_zero' hp2) (three_ne_zero' hp3)

/-- The ring characteristic of `ZMod p` is odd (as `≠ 2`) when `p ≠ 2`. -/
theorem ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

/-- **Term identity off `v = 0`**: for `v ≠ 0`,
`χ(v)·χ(v+2) = χ(1 + 2·v⁻¹)` — pull out `χ(v)² = 1`. -/
theorem term_eq_off_zero {v : ZMod p} (hv : v ≠ 0) :
    quadraticChar (ZMod p) v * quadraticChar (ZMod p) (v + 2)
      = quadraticChar (ZMod p) (1 + 2 * v⁻¹) := by
  have hrw : v * (1 + 2 * v⁻¹) = v + 2 := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm v 2, mul_assoc,
      mul_inv_cancel₀ hv, mul_one]
  rw [← hrw, map_mul, ← mul_assoc, ← pow_two, quadraticChar_sq_one hv, one_mul]

/-- **Bijectivity of the Jacobsthal fractional substitution** `v ↦ 1 + 2·v⁻¹`
on `ZMod p` (with the field convention `0⁻¹ = 0`), for `p ≠ 2`. -/
theorem frac_subst_bijective (hp2 : p ≠ 2) :
    Function.Bijective (fun v : ZMod p => 1 + 2 * v⁻¹) := by
  refine Finite.injective_iff_bijective.mp (fun a b hab => ?_)
  exact inv_injective (mul_left_cancel₀ (two_ne_zero' hp2) (add_left_cancel hab))

/-- **The bilinear Jacobsthal sum**: `Σ_v χ(v)·χ(v+2) = −1` for `p ≠ 2`. -/
theorem sum_bilinear (hp2 : p ≠ 2) :
    ∑ v : ZMod p, quadraticChar (ZMod p) v * quadraticChar (ZMod p) (v + 2)
      = -1 := by
  set χ := quadraticChar (ZMod p) with hχ
  -- the completed fractional sum vanishes (complete character sum)
  have hsum0 : ∑ v : ZMod p, χ (1 + 2 * v⁻¹) = 0 := by
    rw [Fintype.sum_bijective (fun v : ZMod p => 1 + 2 * v⁻¹)
      (frac_subst_bijective hp2) _ χ (fun v => rfl)]
    exact quadraticChar_sum_zero (ringChar_ne_two hp2)
  -- drop the vanishing v = 0 term on the left
  have hL : ∑ v : ZMod p, χ v * χ (v + 2)
      = ∑ v ∈ Finset.univ.erase (0 : ZMod p), χ v * χ (v + 2) :=
    (Finset.sum_erase _ (by rw [hχ, quadraticChar_zero, zero_mul])).symm
  -- split off the v = 0 term (value χ(1) = 1) on the right
  have hR : ∑ v : ZMod p, χ (1 + 2 * v⁻¹)
      = 1 + ∑ v ∈ Finset.univ.erase (0 : ZMod p), χ (1 + 2 * v⁻¹) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    congr 1
    rw [inv_zero, mul_zero, add_zero, hχ]
    exact map_one _
  -- the two erased sums agree termwise
  have hE : ∑ v ∈ Finset.univ.erase (0 : ZMod p), χ v * χ (v + 2)
      = ∑ v ∈ Finset.univ.erase (0 : ZMod p), χ (1 + 2 * v⁻¹) :=
    Finset.sum_congr rfl (fun v hv => term_eq_off_zero (Finset.ne_of_mem_erase hv))
  have h0 : 1 + ∑ v ∈ Finset.univ.erase (0 : ZMod p), χ (1 + 2 * v⁻¹) = 0 := by
    rw [← hR]; exact hsum0
  rw [hL, hE]
  linarith

/-- **THE COMPLETE JACOBSTHAL CROSS-SUM** (the headline): for a prime
`p ∉ {2, 3}`, `Σ_{m : ZMod p} χ(36·m² − 1) = −1` — square-root-strength
(indeed `O(1)`) cancellation of the split form at the complete-sum level. -/
theorem jacobsthal_cross_sum (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∑ m : ZMod p, quadraticChar (ZMod p) (36 * m ^ 2 - 1) = -1 := by
  set χ := quadraticChar (ZMod p) with hχ
  -- Step 1: u = 6m is a bijection of ZMod p
  have step1 : ∑ m : ZMod p, χ (36 * m ^ 2 - 1) = ∑ u : ZMod p, χ (u ^ 2 - 1) :=
    Fintype.sum_bijective (fun m : ZMod p => 6 * m)
      (mulLeft_bijective₀ 6 (six_ne_zero' hp2 hp3)) _ _
      (fun m => congrArg χ (by ring))
  -- Step 2: factor the character; Step 3: shift v = u − 1
  have step23 : ∑ u : ZMod p, χ (u ^ 2 - 1)
      = ∑ v : ZMod p, χ v * χ (v + 2) := by
    have hfac : ∀ u : ZMod p, χ (u ^ 2 - 1) = χ (u - 1) * χ (u + 1) := fun u => by
      rw [hχ, ← map_mul]
      exact congrArg _ (by ring)
    have hshift : Function.Bijective (fun v : ZMod p => v + 1) :=
      Finite.injective_iff_bijective.mp (add_left_injective 1)
    calc ∑ u : ZMod p, χ (u ^ 2 - 1)
        = ∑ u : ZMod p, χ (u - 1) * χ (u + 1) :=
          Finset.sum_congr rfl (fun u _ => hfac u)
      _ = ∑ v : ZMod p, χ v * χ (v + 2) :=
          (Fintype.sum_bijective (fun v : ZMod p => v + 1) hshift _ _
            (fun v => by
              have e1 : v + 1 - 1 = v := add_sub_cancel_right v 1
              have e2 : v + 1 + 1 = v + 2 := by ring
              rw [e1, e2])).symm
  -- Steps 4–5: the bilinear Jacobsthal evaluation
  rw [step1, step23]
  exact sum_bilinear hp2

/-- **Corollary in split (twin) form**: for a prime `p ∉ {2, 3}`,
`Σ_{m : ZMod p} χ((6m−1)·(6m+1)) = −1` — the exact character-side analogue of
the Liouville product `λ(6m−1)·λ(6m+1) = λ(36m²−1)`, at the complete-sum
level ONLY. -/
theorem jacobsthal_cross_sum_split (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∑ m : ZMod p, quadraticChar (ZMod p) ((6 * m - 1) * (6 * m + 1)) = -1 := by
  calc ∑ m : ZMod p, quadraticChar (ZMod p) ((6 * m - 1) * (6 * m + 1))
      = ∑ m : ZMod p, quadraticChar (ZMod p) (36 * m ^ 2 - 1) :=
        Finset.sum_congr rfl (fun m _ => congrArg _ (by ring))
    _ = -1 := jacobsthal_cross_sum hp2 hp3

end Jacobsthal
end Geometric
end EuclidsPath
