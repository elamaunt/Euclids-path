/-
  GeometricTwinJacobsthalSqfree — THE COMPLETE JACOBSTHAL CROSS-SUM AT SQUAREFREE
  MODULI EQUALS THE MOEBIUS FUNCTION, MACHINE-CHECKED:
  for every squarefree d coprime to 6,

      Σ_{m = 0}^{d−1} J(36·m² − 1 | d) = μ(d),

  where J(· | ·) is the Jacobi symbol and μ is the Moebius function.

  This is the multiplicative extension of the wave-1 prime brick
  (`GeometricTwinJacobsthal.lean`: Σ_{m : ZMod p} χ(36m²−1) = −1 for p ∉ {2,3}).

  PROOF.  Induction on the least prime factor: write d = p·n with p = minFac d
  (coprime to n by squarefreeness).  The Jacobi symbol splits along the modulus
  (`jacobiSym.mul_right'`), the summation index splits by the CRT ring
  equivalence `ZMod.chineseRemainder`, and the double sum factors as a product
  of the two complete sums.  The prime factor evaluates to −1 by the wave-1
  quadraticChar brick, bridged through `legendreSym.to_jacobiSym`; the cofactor
  is the induction hypothesis.  Base d = 1: J(· | 1) = 1 = μ(1).

  DISCLOSURES.
    * COMPLETE-SUM LEVEL ONLY.  This brick evaluates full sums over residue
      rings.  It makes NO claim about incomplete sums, about sums restricted
      to pair-rough (sieved) windows, or about the integer-side Liouville sum
      Σ λ(36m²−1).  The parity wall is UNTOUCHED.
    * No new axioms, no sorry.  The twin sorry (`twin_prime_conjecture`) is
      untouched.  This file is self-contained modulo mathlib and the wave-1
      brick, and is NOT registered in `EuclidsPath.lean` by itself.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTwinJacobsthal

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace JacobsthalSqfree

open Finset

/-- **Periodicity of the summand**: the Jacobi symbol `J(36·x² − 1 | d)`
depends on the integer `x` only through `x mod d`. -/
theorem jacobi_arg_congr {d : ℕ} {x y : ℤ} (h : (x : ZMod d) = (y : ZMod d)) :
    jacobiSym (36 * x ^ 2 - 1) d = jacobiSym (36 * y ^ 2 - 1) d := by
  have hmod : x ≡ y [ZMOD (d : ℤ)] := (ZMod.intCast_eq_intCast_iff' x y d).mp h
  exact jacobiSym.mod_left' (((hmod.pow 2).mul_left 36).sub_right 1)

/-- **The prime factor**, bridged from the wave-1 quadraticChar brick:
`Σ_{m : ZMod p} J(36·m² − 1 | p) = −1` for a prime `p ∉ {2, 3}`. -/
theorem sum_zmod_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∑ m : ZMod p, jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) p = -1 := by
  have key : ∀ m : ZMod p,
      jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) p
        = quadraticChar (ZMod p) (36 * m ^ 2 - 1) := by
    intro m
    rw [← jacobiSym.legendreSym.to_jacobiSym p (36 * (m.val : ℤ) ^ 2 - 1)]
    show quadraticChar (ZMod p) ((36 * (m.val : ℤ) ^ 2 - 1 : ℤ) : ZMod p) = _
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val m]
  rw [Finset.sum_congr rfl (fun m _ => key m)]
  exact Jacobsthal.jacobsthal_cross_sum hp2 hp3

/-- **CRT factorization of the complete sum**: for coprime moduli `a, b`,
the complete Jacobsthal–Jacobi sum at `a·b` is the product of the complete
sums at `a` and at `b`.  The Jacobi symbol splits along the modulus and the
index splits by the Chinese-remainder ring equivalence. -/
theorem sum_zmod_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    ∑ m : ZMod (a * b), jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) (a * b)
      = (∑ m : ZMod a, jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) a)
        * ∑ m : ZMod b, jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) b := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  -- split each Jacobi symbol along the factorization of the modulus
  have hsplit : ∀ m : ZMod (a * b),
      jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) (a * b)
        = jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) a
          * jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) b := fun _ =>
    jacobiSym.mul_right' _ (NeZero.ne a) (NeZero.ne b)
  rw [Finset.sum_congr rfl (fun m _ => hsplit m)]
  -- reindex by the CRT ring equivalence
  let φ := ZMod.chineseRemainder hab
  have hre : ∑ m : ZMod (a * b),
      jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) a * jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) b
      = ∑ x : ZMod a × ZMod b,
          jacobiSym (36 * (x.1.val : ℤ) ^ 2 - 1) a
            * jacobiSym (36 * (x.2.val : ℤ) ^ 2 - 1) b := by
    refine Fintype.sum_equiv φ.toEquiv _ _ (fun m => ?_)
    have hφm : φ.toEquiv m = (ZMod.cast m : ZMod a × ZMod b) := rfl
    have hm1 : (φ.toEquiv m).1 = (ZMod.cast m : ZMod a) := by
      rw [hφm, Prod.fst_zmod_cast]
    have hm2 : (φ.toEquiv m).2 = (ZMod.cast m : ZMod b) := by
      rw [hφm, Prod.snd_zmod_cast]
    congr 1
    · exact jacobi_arg_congr (by
        push_cast
        rw [ZMod.natCast_zmod_val, hm1, ZMod.natCast_val m])
    · exact jacobi_arg_congr (by
        push_cast
        rw [ZMod.natCast_zmod_val, hm2, ZMod.natCast_val m])
  rw [hre, Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- **Range-to-`ZMod` bridge**: the sum over `Finset.range d` and the sum over
`ZMod d` of the Jacobsthal–Jacobi summand agree (`d ≠ 0`), since the summand
only depends on the index mod `d`. -/
theorem sum_range_eq_sum_zmod (d : ℕ) [NeZero d] :
    ∑ m ∈ Finset.range d, jacobiSym (36 * (m : ℤ) ^ 2 - 1) d
      = ∑ m : ZMod d, jacobiSym (36 * (m.val : ℤ) ^ 2 - 1) d := by
  refine Finset.sum_nbij' (i := fun m : ℕ => (m : ZMod d))
    (j := fun m : ZMod d => m.val) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro b _
    exact Finset.mem_range.mpr (ZMod.val_lt b)
  · intro a ha
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro b _
    exact ZMod.natCast_zmod_val b
  · intro a _
    exact jacobi_arg_congr (by
      push_cast
      rw [ZMod.natCast_zmod_val])

/-- **THE HEADLINE: the complete Jacobsthal cross-sum at a squarefree modulus
is the Moebius function.**  For every squarefree `d` coprime to `6`,

    `Σ_{m = 0}^{d−1} J(36·m² − 1 | d) = μ(d)`.

The wave-1 prime brick (complete sum = −1 at every good prime) extends
multiplicatively through CRT: square-root-strength (indeed `O(1)`) cancellation
of the split twin form at EVERY squarefree modulus, with the exact sign carried
by the Moebius function.  Complete-sum level only — see the disclosures. -/
theorem jacobsthal_jacobi_sum {d : ℕ} (hd : Squarefree d) (h6 : Nat.Coprime d 6) :
    ∑ m ∈ Finset.range d, jacobiSym (36 * (m : ℤ) ^ 2 - 1) d
      = ArithmeticFunction.moebius d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases eq_or_ne d 1 with h1 | h1
    · subst h1
      simp
    · -- d > 1: peel off the least prime factor p, d = p * n
      have hd0 : d ≠ 0 := hd.ne_zero
      have hp : d.minFac.Prime := Nat.minFac_prime h1
      set p := d.minFac with hpdef
      obtain ⟨n, hn⟩ : p ∣ d := d.minFac_dvd
      have hn0 : n ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hn
        exact hd0 hn
      have hndvd : n ∣ d := ⟨p, by rw [hn]; ring⟩
      have hpcop6 : p.Coprime 6 := Nat.Coprime.coprime_dvd_left d.minFac_dvd h6
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hpcop6
        exact absurd hpcop6 (by decide)
      have hp3 : p ≠ 3 := by
        intro h3
        rw [h3] at hpcop6
        exact absurd hpcop6 (by decide)
      have hcop : p.Coprime n := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hpn
        obtain ⟨k, hk⟩ := hpn
        exact hp.prime.not_unit (hd p ⟨k, by rw [hn, hk]; ring⟩)
      have hsqn : Squarefree n := Squarefree.squarefree_of_dvd hndvd hd
      have h6n : n.Coprime 6 := Nat.Coprime.coprime_dvd_left hndvd h6
      have hlt : n < d := by
        have h1n : n < 2 * n := by omega
        have h2n : 2 * n ≤ p * n := Nat.mul_le_mul_right n hp.two_le
        rw [hn]
        exact lt_of_lt_of_le h1n h2n
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero p := ⟨hp.ne_zero⟩
      haveI : NeZero n := ⟨hn0⟩
      haveI : NeZero (p * n) := ⟨Nat.mul_ne_zero hp.ne_zero hn0⟩
      have IH := ih n hlt hsqn h6n
      rw [hn, sum_range_eq_sum_zmod (p * n), sum_zmod_mul hcop,
        sum_zmod_prime p hp2 hp3, ← sum_range_eq_sum_zmod n, IH,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp]

/-- **Corollary in split (twin) form**: for squarefree `d` coprime to `6`,
`Σ_{m = 0}^{d−1} J((6m−1)·(6m+1) | d) = μ(d)` — the Jacobi-symbol analogue of
the Liouville product `λ(6m−1)·λ(6m+1)`, at the complete-sum level ONLY. -/
theorem jacobsthal_jacobi_sum_split {d : ℕ} (hd : Squarefree d)
    (h6 : Nat.Coprime d 6) :
    ∑ m ∈ Finset.range d, jacobiSym ((6 * (m : ℤ) - 1) * (6 * (m : ℤ) + 1)) d
      = ArithmeticFunction.moebius d := by
  calc ∑ m ∈ Finset.range d, jacobiSym ((6 * (m : ℤ) - 1) * (6 * (m : ℤ) + 1)) d
      = ∑ m ∈ Finset.range d, jacobiSym (36 * (m : ℤ) ^ 2 - 1) d :=
        Finset.sum_congr rfl (fun m _ => by
          have h : (6 * (m : ℤ) - 1) * (6 * (m : ℤ) + 1)
              = 36 * (m : ℤ) ^ 2 - 1 := by ring
          rw [h])
    _ = ArithmeticFunction.moebius d := jacobsthal_jacobi_sum hd h6

end JacobsthalSqfree
end Geometric
end EuclidsPath
