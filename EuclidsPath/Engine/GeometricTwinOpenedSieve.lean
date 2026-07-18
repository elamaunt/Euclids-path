/-
  GeometricTwinOpenedSieve — THE FINITE OPENED-PAIR-SIEVE UNROLL,
  unconditional and finite: the inclusion-exclusion identity behind the
  wave-3 integer-exact verification (tools/probe3_opened_sieve.py, X = 10^8)
  of Lx(z) = Σ_{d | P(z)} μ(d)·S_roots(d), proved here at the divisibility
  level (no root classes needed).

  (1) GENERAL IDENTITY (`opened_pair_sieve`).  For any finite window
      `I : Finset ℕ`, any integer weight `F : ℕ → ℤ`, any modulus map
      `w : ℕ → ℕ`, and any finite sieve set `Q : Finset ℕ` of PAIRWISE
      COPRIME elements (primes in the application):

          Σ_{m ∈ I, ∀ p ∈ Q, p ∤ w m} F m
            = Σ_{S ⊆ Q} (−1)^{|S|} · Σ_{m ∈ I, (Π S) | w m} F m.

      Route: the rough indicator factors as the Int-valued product
      `Π_{p ∈ Q} (1 − 1_{p | w m})`; `Finset.prod_add` expands the product
      over the powerset; the S-divisibility conjunction collapses via
      `(Π S) | n ↔ ∀ p ∈ S, p | n`, valid for pairwise-coprime `S`
      (`coprime_prod_dvd_iff`, by cons-induction from
      `Nat.Coprime.mul_dvd_of_dvd_of_dvd` and `Nat.Coprime.prod_right`);
      then swap the two finite sums.

  (2) REPO SPECIALIZATION (`opened_cross_sum`).  Take `I = Icc 1 X`,
      `w m = (6m−1)(6m+1)`, `F m = λ(6m−1)·λ(6m+1)`, and
      `Q = (Finset.Ioc 3 z).filter Nat.Prime` — the sieve primes in
      `(3, z]`, pairwise coprime because distinct primes are coprime
      (`sievePrimes_pairwise_coprime`).  The LHS is the pair-rough cross
      sum `Lx(X, z)` (`pairRoughCrossSum`), the RHS the opened sieve
      (`openedTerm` summed over the powerset with sign `(−1)^{|S|}`).
      `pairRoughCrossSum_eq_wings` records that the product-divisibility
      roughness condition is literally per-wing pair-roughness (each sieve
      prime divides neither `6m−1` nor `6m+1`), via `Nat.Prime.dvd_mul`.

  DISCLOSURES (mandatory reading before quoting).
    * FINITE IDENTITY ONLY.  No estimate, no limit, no asymptotic claim:
      this is exact bookkeeping over a finite window, the Lean twin of the
      integer-exact numerical check of wave 3.  The powerset sum has 2^{|Q|}
      terms; nothing here controls any of them.
    * NOTHING MOVES THE PARITY WALL.  The wall remains the single arrow
      Chowla2LogHypothesis → Chowla2Hypothesis (un-averaging); this file
      does not touch it.  The twin sorry (`twin_prime_conjecture`) is
      untouched.
    * No new axioms, no sorry.  This file is NOT registered in
      `EuclidsPath.lean`.
-/
import Mathlib

set_option maxHeartbeats 800000

namespace EuclidsPath
namespace Geometric
namespace OpenedSieve

open Finset ArithmeticFunction

/-! ### The coprime product-divisibility collapse -/

/-- **Pairwise-coprime divisibility collapse**: for a finset `S` of pairwise
coprime naturals, `(Π S) | n ↔ ∀ p ∈ S, p | n`.  (Applied to sets of
distinct primes.)  Cons-induction: the head is coprime to the product of
the tail (`Nat.Coprime.prod_right`), so divisibilities combine by
`Nat.Coprime.mul_dvd_of_dvd_of_dvd`. -/
theorem coprime_prod_dvd_iff {n : ℕ} :
    ∀ {S : Finset ℕ}, (S : Set ℕ).Pairwise Nat.Coprime →
      (S.prod id ∣ n ↔ ∀ p ∈ S, p ∣ n) := by
  intro S
  induction S using Finset.cons_induction with
  | empty => intro _; simp
  | cons a s ha ih =>
    intro hS
    have hs : (s : Set ℕ).Pairwise Nat.Coprime := by
      refine hS.mono ?_
      rw [Finset.coe_cons]
      exact Set.subset_insert a (s : Set ℕ)
    have hcop : Nat.Coprime a (s.prod id) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact hS (Finset.mem_coe.mpr (Finset.mem_cons_self a s))
        (Finset.mem_coe.mpr (Finset.mem_cons.mpr (Or.inr hp)))
        (fun h => ha (h ▸ hp))
    rw [Finset.prod_cons]
    constructor
    · intro h p hp
      rcases Finset.mem_cons.mp hp with rfl | hps
      · exact (dvd_mul_right (id p) (s.prod id)).trans h
      · exact (ih hs).mp ((dvd_mul_left (s.prod id) (id a)).trans h) p hps
    · intro h
      exact hcop.mul_dvd_of_dvd_of_dvd (h a (Finset.mem_cons_self a s))
        ((ih hs).mpr fun p hp => h p (Finset.mem_cons.mpr (Or.inr hp)))

/-! ### The opened rough indicator -/

/-- **The opened rough indicator**: for pairwise-coprime `Q`, the Int-valued
indicator of `∀ p ∈ Q, p ∤ n` unrolls over the powerset,

`1_{∀ p ∈ Q, p ∤ n} = Σ_{S ⊆ Q} (−1)^{|S|} · 1_{(Π S) | n}`.

Proof: the indicator is the product `Π_{p ∈ Q} (1 − 1_{p | n})`
(`Finset.prod_boole`), which `Finset.prod_add` expands over subsets; the
subset conjunction of divisibilities collapses through
`coprime_prod_dvd_iff`. -/
theorem opened_indicator (Q : Finset ℕ) (hQ : (Q : Set ℕ).Pairwise Nat.Coprime)
    (n : ℕ) :
    (if ∀ p ∈ Q, ¬ p ∣ n then (1 : ℤ) else 0)
      = ∑ S ∈ Q.powerset, (-1 : ℤ) ^ S.card *
          (if S.prod id ∣ n then (1 : ℤ) else 0) := by
  calc (if ∀ p ∈ Q, ¬ p ∣ n then (1 : ℤ) else 0)
      = ∏ p ∈ Q, (if ¬ p ∣ n then (1 : ℤ) else 0) := Finset.prod_boole.symm
    _ = ∏ p ∈ Q, ((-(if p ∣ n then (1 : ℤ) else 0)) + 1) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        by_cases h : p ∣ n <;> simp [h]
    _ = ∑ S ∈ Q.powerset,
          (∏ p ∈ S, -(if p ∣ n then (1 : ℤ) else 0)) * ∏ _p ∈ Q \ S, (1 : ℤ) :=
        Finset.prod_add _ _ Q
    _ = ∑ S ∈ Q.powerset, (-1 : ℤ) ^ S.card *
          (if S.prod id ∣ n then (1 : ℤ) else 0) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        have hSp : (S : Set ℕ).Pairwise Nat.Coprime :=
          hQ.mono (Finset.coe_subset.mpr (Finset.mem_powerset.mp hS))
        have hneg : ∏ p ∈ S, -(if p ∣ n then (1 : ℤ) else 0)
            = (-1 : ℤ) ^ S.card * ∏ p ∈ S, (if p ∣ n then (1 : ℤ) else 0) := by
          calc ∏ p ∈ S, -(if p ∣ n then (1 : ℤ) else 0)
              = ∏ p ∈ S, ((-1) * (if p ∣ n then (1 : ℤ) else 0)) :=
                Finset.prod_congr rfl fun p _ => by ring
            _ = (∏ _p ∈ S, (-1 : ℤ)) * ∏ p ∈ S, (if p ∣ n then (1 : ℤ) else 0) :=
                Finset.prod_mul_distrib
            _ = (-1 : ℤ) ^ S.card * ∏ p ∈ S, (if p ∣ n then (1 : ℤ) else 0) := by
                rw [Finset.prod_const]
        rw [Finset.prod_const_one, mul_one, hneg, Finset.prod_boole]
        congr 1
        exact if_congr (Iff.symm (coprime_prod_dvd_iff hSp)) rfl rfl

/-! ### (1) The general finite opened-pair-sieve identity -/

/-- **THE FINITE OPENED-PAIR-SIEVE IDENTITY** (unconditional, finite): for
any window `I`, integer weight `F`, modulus map `w`, and pairwise-coprime
sieve set `Q`,

`Σ_{m ∈ I : ∀ p ∈ Q, p ∤ w m} F m
   = Σ_{S ⊆ Q} (−1)^{|S|} · Σ_{m ∈ I : (Π S) | w m} F m`.

This is the exact inclusion-exclusion unroll verified integer-exactly at
`X = 10^8` in wave 3 — no estimate, no limit. -/
theorem opened_pair_sieve (I : Finset ℕ) (F : ℕ → ℤ) (Q : Finset ℕ)
    (w : ℕ → ℕ) (hQ : (Q : Set ℕ).Pairwise Nat.Coprime) :
    ∑ m ∈ I.filter (fun m => ∀ p ∈ Q, ¬ p ∣ w m), F m
      = ∑ S ∈ Q.powerset, (-1 : ℤ) ^ S.card *
          ∑ m ∈ I.filter (fun m => S.prod id ∣ w m), F m := by
  calc ∑ m ∈ I.filter (fun m => ∀ p ∈ Q, ¬ p ∣ w m), F m
      = ∑ m ∈ I, (if ∀ p ∈ Q, ¬ p ∣ w m then (1 : ℤ) else 0) * F m := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> ring
    _ = ∑ m ∈ I, ∑ S ∈ Q.powerset, (-1 : ℤ) ^ S.card *
          ((if S.prod id ∣ w m then (1 : ℤ) else 0) * F m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [opened_indicator Q hQ (w m), Finset.sum_mul]
        exact Finset.sum_congr rfl fun S _ => by ring
    _ = ∑ S ∈ Q.powerset, ∑ m ∈ I, (-1 : ℤ) ^ S.card *
          ((if S.prod id ∣ w m then (1 : ℤ) else 0) * F m) := Finset.sum_comm
    _ = ∑ S ∈ Q.powerset, (-1 : ℤ) ^ S.card *
          ∑ m ∈ I.filter (fun m => S.prod id ∣ w m), F m := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.mul_sum, Finset.sum_filter]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> ring

/-! ### (2) The repo specialization: the opened pair-rough cross sum -/

/-- The sieve-prime set `Q = {p prime : 3 < p ≤ z}`. -/
def sievePrimes (z : ℕ) : Finset ℕ := (Finset.Ioc 3 z).filter Nat.Prime

/-- Distinct primes are coprime, so `sievePrimes z` is pairwise coprime. -/
theorem sievePrimes_pairwise_coprime (z : ℕ) :
    ((sievePrimes z : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
  intro p hp q hq hpq
  have hpp : Nat.Prime p := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
  have hqq : Nat.Prime q := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  exact (Nat.coprime_primes hpp hqq).mpr hpq

/-- The pair-rough cross sum `Lx(X, z)`: the cross sum
`Σ λ(6m−1)·λ(6m+1)` restricted to `m ≤ X` with `(6m−1)(6m+1)` free of all
sieve primes in `(3, z]`. -/
def pairRoughCrossSum (X z : ℕ) : ℤ :=
  ∑ m ∈ (Finset.Icc 1 X).filter
      (fun m => ∀ p ∈ sievePrimes z, ¬ p ∣ (6 * m - 1) * (6 * m + 1)),
    liouville (6 * m - 1) * liouville (6 * m + 1)

/-- One opened term: the cross sum over the sub-window where the (squarefree)
product `Π S` of a subset `S` of sieve primes divides `(6m−1)(6m+1)`. -/
def openedTerm (X : ℕ) (S : Finset ℕ) : ℤ :=
  ∑ m ∈ (Finset.Icc 1 X).filter (fun m => S.prod id ∣ (6 * m - 1) * (6 * m + 1)),
    liouville (6 * m - 1) * liouville (6 * m + 1)

/-- **THE OPENED CROSS SUM** (unconditional, finite): the pair-rough cross
sum unrolls exactly into signed opened terms over subsets of sieve primes,

`Lx(X, z) = Σ_{S ⊆ sievePrimes z} (−1)^{|S|} · openedTerm X S`.

This is the Lean twin of the wave-3 integer-exact verification. -/
theorem opened_cross_sum (X z : ℕ) :
    pairRoughCrossSum X z
      = ∑ S ∈ (sievePrimes z).powerset, (-1 : ℤ) ^ S.card * openedTerm X S :=
  opened_pair_sieve (Finset.Icc 1 X)
    (fun m => liouville (6 * m - 1) * liouville (6 * m + 1))
    (sievePrimes z) (fun m => (6 * m - 1) * (6 * m + 1))
    (sievePrimes_pairwise_coprime z)

/-- **Per-wing reading of pair-roughness**: since sieve elements are prime,
`p ∤ (6m−1)(6m+1)` for all sieve `p` is literally `p ∤ 6m−1 AND p ∤ 6m+1`
for all sieve `p` (`Nat.Prime.dvd_mul`) — the roughness condition of
`pairRoughCrossSum` is per-wing pair-roughness. -/
theorem pairRoughCrossSum_eq_wings (X z : ℕ) :
    pairRoughCrossSum X z
      = ∑ m ∈ (Finset.Icc 1 X).filter
          (fun m => ∀ p ∈ sievePrimes z, ¬ p ∣ (6 * m - 1) ∧ ¬ p ∣ (6 * m + 1)),
        liouville (6 * m - 1) * liouville (6 * m + 1) := by
  unfold pairRoughCrossSum
  congr 1
  refine Finset.filter_congr fun m _ => ?_
  constructor
  · intro h p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hnot := h p hp
    rw [hpp.dvd_mul] at hnot
    exact ⟨fun ha => hnot (Or.inl ha), fun hb => hnot (Or.inr hb)⟩
  · intro h p hp hdvd
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    rcases hpp.dvd_mul.mp hdvd with ha | hb
    · exact (h p hp).1 ha
    · exact (h p hp).2 hb

end OpenedSieve
end Geometric
end EuclidsPath
