/-
  GeometricTwinOpenedSieveRoots — THE ROOT-CLASS FORM OF THE OPENED SIEVE:
  wave-5 W5-3 brick of the binary-cancellation program, connecting the finite
  opened-pair-sieve unroll (`GeometricTwinOpenedSieve`) to the CRT machinery
  of the squarefree Jacobsthal brick (`GeometricTwinJacobsthalSqfree`).

  Each opened term of the sieve unroll at modulus `d` is a divisibility-
  restricted window sum `Σ_{m ∈ I, d | (6m−1)(6m+1)} F m`.  This brick shows
  that the divisibility condition is EXACTLY root membership for the split
  twin form, and decomposes each opened term into congruence-class sums over
  the root set `R_d = {a : ZMod d | 36·a² − 1 = 0}`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * (1) `dvd_iff_root` — for ANY modulus `d` and any `m ≥ 1`,
          `d | (6m−1)(6m+1)  ↔  36·m̄² − 1 = 0 in ZMod d`.
      (Pure Int-cast arithmetic: `(6m−1)(6m+1) = 36m² − 1` over ℤ, then
      `ZMod.intCast_zmod_eq_zero_iff_dvd`.  No coprimality to 6 is needed at
      this level; coprimality governs only the SIZE of the root set.)
    * (2) `opened_term_eq_root_classes` — the fiberwise decomposition: for
      any window `I` of positive integers and any weight `F : ℕ → ℤ`,
          `Σ_{m ∈ I, d | (6m−1)(6m+1)} F m
             = Σ_{a ∈ R_d} Σ_{m ∈ I, m ≡ a (mod d)} F m`,
      where `R_d = rootSet d` is the finset of roots of `36·a² = 1` in
      `ZMod d`: every opened term splits into progression sums over roots.
      `openedTerm_eq_root_classes` instantiates this on the repo's
      `OpenedSieve.openedTerm` at modulus `d = Π S` (a subset of sieve
      primes; `neZero_prod_of_subset_sievePrimes` supplies `d ≠ 0`).
    * (3) BONUS (the root count): `card_rootSet_prime` — exactly TWO roots
      `±6⁻¹` at every prime `p ∉ {2,3}`; `card_rootSet_mul` — CRT
      multiplicativity of the root count; `card_rootSet` — for squarefree
      `d` coprime to 6, `|R_d| = 2^{ω(d)}`; and
      `card_rootSet_of_subset_sievePrimes` — for `S ⊆ sievePrimes z`,
      `|R_{Π S}| = 2^{|S|}`: each opened term splits into exactly `2^{|S|}`
      progression sums, the finite skeleton of the `Π (1 − 2/p)` sieve
      density and the class-count twin of `J(d) = μ(d)`.

  DISCLOSURES (mandatory reading before quoting).
    * FINITE IDENTITY ONLY.  Exact bookkeeping over finite windows and
      residue rings: no estimate, no limit, no asymptotic claim.  Nothing
      here controls the size of any progression sum.
    * NOTHING MOVES THE PARITY WALL.  The wall remains the single arrow
      `Chowla2LogHypothesis → Chowla2Hypothesis` (un-averaging); no finite
      identity touches it, and this one does not either.
    * No new axioms, no sorry.  This file is NOT registered in
      `EuclidsPath.lean`.  The twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTwinOpenedSieve
import EuclidsPath.Engine.GeometricTwinJacobsthalSqfree

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace OpenedSieveRoots

open Finset ArithmeticFunction

/-! ### The root set of the split twin form -/

/-- **The root set** `R_d = {a : ZMod d | 36·a² − 1 = 0}`: the residue
classes solving `36·a² = 1 (mod d)`, i.e. the congruence classes through
which the opened sieve terms at modulus `d` factor. -/
def rootSet (d : ℕ) [NeZero d] : Finset (ZMod d) :=
  Finset.univ.filter (fun a => 36 * a ^ 2 - 1 = 0)

theorem mem_rootSet {d : ℕ} [NeZero d] {a : ZMod d} :
    a ∈ rootSet d ↔ 36 * a ^ 2 - 1 = 0 := by
  simp [rootSet]

/-! ### (1) Divisibility is root membership -/

/-- **Divisibility = root membership**: for any modulus `d` and any `m ≥ 1`,
`d | (6m−1)(6m+1)` in ℕ iff `36·m̄² − 1 = 0` in `ZMod d`.  The ℕ-side
product expands to `36m² − 1` after the Int cast (where the truncated
subtraction `6m − 1` is genuine, since `6m ≥ 1`), and Int-divisibility by
`d` is vanishing of the `ZMod d` cast. -/
theorem dvd_iff_root (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    d ∣ (6 * m - 1) * (6 * m + 1)
      ↔ (36 * (m : ZMod d) ^ 2 - 1 : ZMod d) = 0 := by
  have h6 : (1 : ℕ) ≤ 6 * m := by omega
  have hcast : (((6 * m - 1) * (6 * m + 1) : ℕ) : ℤ) = 36 * (m : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_mul, Nat.cast_sub h6]
    push_cast
    ring
  have hzmod : ((36 * (m : ℤ) ^ 2 - 1 : ℤ) : ZMod d)
      = 36 * (m : ZMod d) ^ 2 - 1 := by
    push_cast
    ring
  rw [← Int.natCast_dvd_natCast, hcast, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    hzmod]

/-! ### (2) The fiberwise root-class decomposition of an opened term -/

/-- **THE ROOT-CLASS DECOMPOSITION OF AN OPENED TERM** (unconditional,
finite): for any window `I` of positive integers, any weight `F : ℕ → ℤ`,
and any modulus `d ≠ 0`,

`Σ_{m ∈ I, d | (6m−1)(6m+1)} F m
   = Σ_{a ∈ R_d} Σ_{m ∈ I, m ≡ a (mod d)} F m`.

Route: by `dvd_iff_root` the divisibility filter maps into the root set
under `m ↦ m mod d`, so the sum splits fiberwise
(`Finset.sum_fiberwise_of_maps_to`); within the fiber of a root `a`, the
congruence `m ≡ a` already IMPLIES the divisibility, so the double filter
collapses to the plain progression filter. -/
theorem opened_term_eq_root_classes (d : ℕ) [NeZero d] (I : Finset ℕ)
    (hI : ∀ m ∈ I, 1 ≤ m) (F : ℕ → ℤ) :
    ∑ m ∈ I.filter (fun m => d ∣ (6 * m - 1) * (6 * m + 1)), F m
      = ∑ a ∈ rootSet d,
          ∑ m ∈ I.filter (fun m : ℕ => (m : ZMod d) = a), F m := by
  have hmaps : ∀ m ∈ I.filter (fun m => d ∣ (6 * m - 1) * (6 * m + 1)),
      ((m : ZMod d)) ∈ rootSet d := by
    intro m hm
    obtain ⟨hmI, hdvd⟩ := Finset.mem_filter.mp hm
    exact mem_rootSet.mpr ((dvd_iff_root d (hI m hmI)).mp hdvd)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  refine Finset.sum_congr rfl fun a ha => ?_
  congr 1
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun m hmI => ?_
  have hroot : (36 * a ^ 2 - 1 : ZMod d) = 0 := mem_rootSet.mp ha
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(dvd_iff_root d (hI m hmI)).mpr ?_, h⟩
    rw [h]
    exact hroot

/-! ### The repo specialization: opened terms of the opened cross sum -/

/-- A subset of the sieve primes has nonzero (indeed positive) product:
the `NeZero` instance feeding `openedTerm_eq_root_classes`. -/
theorem neZero_prod_of_subset_sievePrimes {z : ℕ} {S : Finset ℕ}
    (hS : S ⊆ OpenedSieve.sievePrimes z) : NeZero (S.prod id) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun p hp => ?_⟩
  exact ((Finset.mem_filter.mp (hS hp)).2).ne_zero

/-- **Root-class form of the repo's opened term**: for the modulus
`d = Π S` of an opened term of `opened_cross_sum`,

`openedTerm X S = Σ_{a ∈ R_{Π S}} Σ_{m ≤ X, m ≡ a (mod Π S)} λ(6m−1)·λ(6m+1)`

— each opened term of the sieve unroll is a sum of `|R_{Π S}|` progression
sums of the cross weight. -/
theorem openedTerm_eq_root_classes (X : ℕ) (S : Finset ℕ)
    [NeZero (S.prod id)] :
    OpenedSieve.openedTerm X S
      = ∑ a ∈ rootSet (S.prod id),
          ∑ m ∈ (Finset.Icc 1 X).filter
              (fun m : ℕ => (m : ZMod (S.prod id)) = a),
            liouville (6 * m - 1) * liouville (6 * m + 1) := by
  unfold OpenedSieve.openedTerm
  exact opened_term_eq_root_classes (S.prod id) (Finset.Icc 1 X)
    (fun m hm => (Finset.mem_Icc.mp hm).1) _

/-! ### (3) BONUS: the root count `|R_d| = 2^(omega d)` -/

/-- **Two roots at every good prime**: for a prime `p ∉ {2, 3}`, the root set
of `36·a² = 1` in the field `ZMod p` is exactly `{6⁻¹, −6⁻¹}`, of size 2. -/
theorem card_rootSet_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (rootSet p).card = 2 := by
  have h6 : (6 : ZMod p) ≠ 0 := Jacobsthal.six_ne_zero' hp2 hp3
  have h2 : (2 : ZMod p) ≠ 0 := Jacobsthal.two_ne_zero' hp2
  have hukey : (6 : ZMod p) * (6 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h6
  have key : rootSet p = {(6 : ZMod p)⁻¹, -(6 : ZMod p)⁻¹} := by
    ext a
    rw [mem_rootSet]
    constructor
    · intro h
      have h' : ((6 : ZMod p) * a - 1) * ((6 : ZMod p) * a + 1) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h' with h1 | h1
      · have h6a : (6 : ZMod p) * a = 1 := by linear_combination h1
        have hinv : (6 : ZMod p)⁻¹ = a := inv_eq_of_mul_eq_one_right h6a
        rw [← hinv]
        exact Finset.mem_insert_self _ _
      · have h6a : (6 : ZMod p) * (-a) = 1 := by linear_combination -h1
        have hinv : (6 : ZMod p)⁻¹ = -a := inv_eq_of_mul_eq_one_right h6a
        have ha : a = -(6 : ZMod p)⁻¹ := by rw [hinv]; ring
        rw [ha]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    · intro h
      rcases Finset.mem_insert.mp h with rfl | h
      · linear_combination ((6 : ZMod p) * (6 : ZMod p)⁻¹ + 1) * hukey
      · rw [Finset.mem_singleton.mp h]
        linear_combination ((6 : ZMod p) * (6 : ZMod p)⁻¹ + 1) * hukey
  have hu0 : (6 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h6
  have hne : (6 : ZMod p)⁻¹ ≠ -(6 : ZMod p)⁻¹ := by
    intro h
    have h2u : (2 : ZMod p) * (6 : ZMod p)⁻¹ = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2u with h' | h'
    · exact h2 h'
    · exact hu0 h'
  rw [key]
  exact Finset.card_pair hne

/-- **CRT multiplicativity of the root count**: for coprime moduli `a, b`,
the CRT ring equivalence restricts to a bijection between `R_{ab}` and
`R_a × R_b` (a ring isomorphism preserves the polynomial condition
componentwise), so `|R_{ab}| = |R_a| · |R_b|` — the root-set companion of
`JacobsthalSqfree.sum_zmod_mul`. -/
theorem card_rootSet_mul {a b : ℕ} [NeZero a] [NeZero b]
    (hab : Nat.Coprime a b) :
    haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    (rootSet (a * b)).card = (rootSet a).card * (rootSet b).card := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  set φ := ZMod.chineseRemainder hab with hφdef
  set ψ₁ : ZMod (a * b) →+* ZMod a :=
    (RingHom.fst (ZMod a) (ZMod b)).comp φ.toRingHom with hψ₁def
  set ψ₂ : ZMod (a * b) →+* ZMod b :=
    (RingHom.snd (ZMod a) (ZMod b)).comp φ.toRingHom with hψ₂def
  have h1 : ∀ x : ZMod (a * b), (φ x).1 = ψ₁ x := fun _ => rfl
  have h2 : ∀ x : ZMod (a * b), (φ x).2 = ψ₂ x := fun _ => rfl
  have hpsi1 : ∀ x : ZMod (a * b),
      ψ₁ (36 * x ^ 2 - 1) = 36 * (ψ₁ x) ^ 2 - 1 := by
    intro x
    rw [map_sub, map_mul, map_pow, map_one, map_ofNat]
  have hpsi2 : ∀ x : ZMod (a * b),
      ψ₂ (36 * x ^ 2 - 1) = 36 * (ψ₂ x) ^ 2 - 1 := by
    intro x
    rw [map_sub, map_mul, map_pow, map_one, map_ofNat]
  have hmem : ∀ x : ZMod (a * b),
      x ∈ rootSet (a * b) ↔ (φ x).1 ∈ rootSet a ∧ (φ x).2 ∈ rootSet b := by
    intro x
    simp only [mem_rootSet, h1, h2]
    constructor
    · intro h
      constructor
      · rw [← hpsi1 x, h, _root_.map_zero]
      · rw [← hpsi2 x, h, _root_.map_zero]
    · rintro ⟨hra, hrb⟩
      apply φ.injective
      rw [_root_.map_zero]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_zero, h1, hpsi1]
        exact hra
      · rw [Prod.snd_zero, h2, hpsi2]
        exact hrb
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun x => φ x) (fun y => φ.symm y) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' := (hmem x).mp (Finset.mem_coe.mp hx)
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hx'.1, hx'.2⟩)
  · intro y hy
    have hy' := Finset.mem_product.mp (Finset.mem_coe.mp hy)
    refine Finset.mem_coe.mpr ((hmem (φ.symm y)).mpr ?_)
    rw [RingEquiv.apply_symm_apply]
    exact ⟨hy'.1, hy'.2⟩
  · intro x _
    exact φ.symm_apply_apply x
  · intro y _
    exact φ.apply_symm_apply y

/-- Transport of the root count along an equality of moduli (the `NeZero`
instances are propositional, so the two root sets agree definitionally). -/
theorem card_rootSet_congr {d e : ℕ} [NeZero d] [NeZero e] (h : d = e) :
    (rootSet d).card = (rootSet e).card := by
  subst h
  rfl

/-- **THE ROOT COUNT AT SQUAREFREE MODULI**: for squarefree `d` coprime
to 6, `|R_d| = 2^{ω(d)}` — two roots per prime factor, multiplied along
CRT.  This is the class-count twin of `jacobsthal_jacobi_sum`
(`J(d) = μ(d)`): the SAME strong induction on the least prime factor,
counting roots instead of summing characters. -/
theorem card_rootSet {d : ℕ} [NeZero d] (hd : Squarefree d)
    (h6 : Nat.Coprime d 6) :
    (rootSet d).card = 2 ^ d.primeFactors.card := by
  rcases eq_or_ne d 1 with h1 | h1
  · subst h1
    have huniv : rootSet 1 = (Finset.univ : Finset (ZMod 1)) := by
      unfold rootSet
      exact Finset.filter_true_of_mem fun a _ => Subsingleton.elim _ _
    rw [huniv, Finset.card_univ, ZMod.card, Nat.primeFactors_one,
      Finset.card_empty, pow_zero]
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
    have IH : (rootSet n).card = 2 ^ n.primeFactors.card :=
      card_rootSet hsqn h6n
    have hpn : p ∉ n.primeFactors := by
      intro hmem
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop)
        (Nat.dvd_of_mem_primeFactors hmem)
    simp only [hn]
    rw [card_rootSet_congr hn, card_rootSet_mul hcop,
      card_rootSet_prime p hp2 hp3, IH,
      Nat.Coprime.primeFactors_mul hcop, Nat.Prime.primeFactors hp,
      Finset.singleton_union, Finset.card_insert_of_notMem hpn, pow_succ]
    ring
termination_by d
decreasing_by exact hlt

/-! ### The sieve-prime application: `2^{|S|}` classes per opened term -/

/-- A subset of the sieve primes has squarefree product. -/
theorem squarefree_prod_of_primes :
    ∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → Squarefree (S.prod id) := by
  intro S
  induction S using Finset.cons_induction with
  | empty => intro _; exact squarefree_one
  | cons a s ha ih =>
    intro h
    have hap : a.Prime := h a (Finset.mem_cons_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp =>
      h p (Finset.mem_cons.mpr (Or.inr hp))
    have hcop : Nat.Coprime a (s.prod id) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hap (hs p hp)).mpr (fun he => ha (he ▸ hp))
    rw [Finset.prod_cons]
    exact (Nat.squarefree_mul hcop).mpr ⟨hap.squarefree, ih hs⟩

/-- The product of a subset of the sieve primes is coprime to 6
(all sieve primes exceed 3). -/
theorem coprime_six_prod_of_subset_sievePrimes {z : ℕ} {S : Finset ℕ}
    (hS : S ⊆ OpenedSieve.sievePrimes z) : Nat.Coprime (S.prod id) 6 := by
  refine Nat.Coprime.prod_left fun p hp => ?_
  have hmem := Finset.mem_filter.mp (hS hp)
  have hpp : p.Prime := hmem.2
  have h3 : 3 < p := (Finset.mem_Ioc.mp hmem.1).1
  have hc2 : Nat.Coprime p 2 :=
    (Nat.coprime_primes hpp Nat.prime_two).mpr (by omega)
  have hc3 : Nat.Coprime p 3 :=
    (Nat.coprime_primes hpp Nat.prime_three).mpr (by omega)
  exact Nat.Coprime.mul_right hc2 hc3

/-- **`2^{|S|}` root classes per opened term**: for any subset `S` of the
sieve primes, the opened term at modulus `Π S` splits into exactly
`2^{|S|}` progression sums — the finite skeleton of the `Π (1 − 2/p)`
sieve density. -/
theorem card_rootSet_of_subset_sievePrimes {z : ℕ} {S : Finset ℕ}
    [NeZero (S.prod id)] (hS : S ⊆ OpenedSieve.sievePrimes z) :
    (rootSet (S.prod id)).card = 2 ^ S.card := by
  have hprimes : ∀ p ∈ S, p.Prime := fun p hp =>
    (Finset.mem_filter.mp (hS hp)).2
  have hsq : Squarefree (S.prod id) := squarefree_prod_of_primes hprimes
  have h6 : Nat.Coprime (S.prod id) 6 :=
    coprime_six_prod_of_subset_sievePrimes hS
  have hpf : (S.prod id).primeFactors = S := Nat.primeFactors_prod hprimes
  rw [card_rootSet hsq h6, hpf]

end OpenedSieveRoots
end Geometric
end EuclidsPath
