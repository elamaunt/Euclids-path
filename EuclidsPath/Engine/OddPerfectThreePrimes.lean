/-
  OddPerfectThreePrimes — three prime factors of an odd perfect witness.
  Report section: "Perfect numbers (odd witness)", candidate 2 [medium].
  Witness type and decide-boundary: Engine/PerfectNumberBranch.lean (oddPerfect_ge_101).

  GREEN MODULE (everything proved, no sorry/axiom, quarantine NOT imported):
    * pred_mul_geomSum_add_one — geometric sum in unsigned form:
      (p−1)·(1 + p + … + p^a) + 1 = p^(a+1);
    * pred_mul_sigma_prime_pow_add_one — the same form for σ₁(p^a): instead of the fraction
      (p^(a+1)−1)/(p−1) — an exact integer identity without subtraction;
    * not_perfect_prime_pow / not_perfect_prime — NO prime power is perfect
      (including even 2^k!): σ₁(p^k) ≡ 1 (mod p), while perfection requires σ₁(p^k) = 2·p^k ≡ 0
      (mod p); hence p ∣ 1 — contradiction;
    * perfect_two_mul_prod_pred_le_prod — abundance bound for ANY perfect
      n ≠ 0: 2·∏(p−1) ≤ ∏p over all prime factors of n (multiplicativity of σ₁
      over the factorization + geometric identity for each prime);
    * odd_perfect_three_le_card_primeFactors — an odd perfect number has
      at least three distinct prime factors (classical);
    * oddPerfect_not_prime / oddPerfect_not_primePow /
      oddPerfect_min_three_prime_factors — the same facts in the language of the witness
      OddPerfectNumber.

  MATHEMATICS (classical, known since Euler). For a perfect n
  we have σ(n) = 2n. By multiplicativity σ(n) = ∏_p σ(p^{a_p}), and for
  each prime p:  (p−1)·σ(p^{a_p}) = p^{a_p+1} − 1 < p·p^{a_p}.
  Multiplying: (∏(p−1))·σ(n) ≤ (∏p)·n, whence 2·∏(p−1) ≤ ∏p. If an odd n has
  one prime factor p ≥ 3, we get 2(p−1) ≤ p, i.e. p ≤ 2 — contradiction;
  if there are two distinct odd p, q ≥ 3 (one of them ≥ 5), then 2(p−1)(q−1) ≤ pq
  contradicts (p−2)(q−2) ≥ 3. In the familiar notation this is σ(n)/n < p/(p−1) · q/(q−1)
  ≤ (3/2)·(5/4) = 15/8 < 2. Hence there are at least three prime factors.

  HONESTY: this is NOT a solution to the odd perfect number problem — it has been open
  since antiquity, and here NEITHER existence NOR non-existence of a witness is claimed.
  This is a QUALITATIVE green narrowing of the domain of type OddPerfectNumber —
  the first non-numeric narrowing (in addition to the decide-cutoff oddPerfect_ge_101): every
  hypothetical witness must have ≥ 3 distinct prime factors.
  There are no formal decree links in the module: all theorems are unconditional
  arithmetic, paid for by mathlib multiplicativity of σ and kernel verification.
  The taint ledger of the repository does not change.
-/
import Mathlib
import EuclidsPath.Engine.PerfectNumberBranch

set_option autoImplicit false

namespace EuclidsPath.PerfectNumberBranch

/-! ### Geometric identity without subtraction -/

/-- Geometric sum in unsigned form: `(p − 1)·(1 + p + … + p^a) + 1 = p^(a+1)`.
    The usual expression `∑ p^i = (p^(a+1) − 1)/(p − 1)` in ℕ is inconvenient (truncated subtraction
    and division); this form is an exact integer identity. -/
theorem pred_mul_geomSum_add_one {p : ℕ} (hp : 1 ≤ p) (a : ℕ) :
    (p - 1) * (∑ i ∈ Finset.range (a + 1), p ^ i) + 1 = p ^ (a + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ, ← ih]
    ring

/-- Sum of divisors of a prime power, unsigned form:
    `(p − 1)·σ₁(p^a) + 1 = p^(a+1)` — this is exactly `σ(p^a) = (p^(a+1)−1)/(p−1)`
    without a fraction. The key brick of the abundance bound. -/
theorem pred_mul_sigma_prime_pow_add_one {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * (ArithmeticFunction.sigma 1 (p ^ a)) + 1 = p ^ (a + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  exact pred_mul_geomSum_add_one hp.one_lt.le a

/-! ### No prime power is perfect (mod p) -/

/-- **Classical (proved): no prime power is perfect** — including
    even `2^k`. Argument: σ₁(p^k) = 1 + p·(1 + … + p^(k−1)) ≡ 1 (mod p),
    whereas perfection requires σ₁(p^k) = 2·p^k ≡ 0 (mod p); hence p ∣ 1. -/
theorem not_perfect_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ¬ Nat.Perfect (p ^ k) := by
  intro hperf
  have hσ : ArithmeticFunction.sigma 1 (p ^ k) = 2 * p ^ k := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (pow_pos hp.pos k)).mp hperf
  have hgeom : ArithmeticFunction.sigma 1 (p ^ k)
      = p * (∑ i ∈ Finset.range k, p ^ i) + 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
      Finset.mul_sum]
    simp [pow_succ']
  have hkey : p * (∑ i ∈ Finset.range k, p ^ i) + 1 = 2 * p ^ k := by
    rw [← hgeom]; exact hσ
  have hp_dvd : p ∣ 1 := by
    have h1 : p ∣ 2 * p ^ k := (dvd_pow_self p hk).mul_left 2
    have h2 : p ∣ p * (∑ i ∈ Finset.range k, p ^ i) := dvd_mul_right p _
    have h3 := Nat.dvd_sub h1 h2
    rwa [← hkey, Nat.add_sub_cancel_left] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp hp_dvd)

/-- A prime is not perfect: σ₁(p) = p + 1 ≠ 2p. Special case `k = 1`. -/
theorem not_perfect_prime {p : ℕ} (hp : p.Prime) : ¬ Nat.Perfect p := by
  intro h
  exact not_perfect_prime_pow hp one_ne_zero (by rwa [pow_one])

/-! ### Abundance bound: 2·∏(p−1) ≤ ∏p for a perfect n -/

/-- **Abundance bound (proved):** for any perfect `n ≠ 0`
    `2·∏(p−1) ≤ ∏p` over all prime factors of `n`. This is the integer form
    of the classical `2 = σ(n)/n < ∏ p/(p−1)`: multiplicativity of σ₁ over
    the factorization + geometric identity for each prime. -/
theorem perfect_two_mul_prod_pred_le_prod {n : ℕ} (hn : n ≠ 0) (hperf : Nat.Perfect n) :
    2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
  have hσ : ArithmeticFunction.sigma 1 n = 2 * n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero hn)).mp hperf
  have hfac : ArithmeticFunction.sigma 1 n
      = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    simpa using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) hn
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.prod_factorization_pow_eq_self hn
  have hchain :
      (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) ≤ (∏ p ∈ n.primeFactors, p) * n := by
    calc (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n)
        = (∏ p ∈ n.primeFactors, (p - 1)) * ArithmeticFunction.sigma 1 n := by rw [hσ]
      _ = ∏ p ∈ n.primeFactors,
            ((p - 1) * ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) := by
          rw [hfac, Finset.prod_mul_distrib]
      _ ≤ ∏ p ∈ n.primeFactors, p ^ (n.factorization p + 1) :=
          Finset.prod_le_prod' fun p hp =>
            Nat.le.intro
              (pred_mul_geomSum_add_one
                (Nat.prime_of_mem_primeFactors hp).one_lt.le _)
      _ = ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) :=
          Finset.prod_congr rfl fun p _ => pow_succ p _
      _ = (∏ p ∈ n.primeFactors, p ^ n.factorization p) * ∏ p ∈ n.primeFactors, p :=
          Finset.prod_mul_distrib
      _ = n * ∏ p ∈ n.primeFactors, p := by rw [hself]
      _ = (∏ p ∈ n.primeFactors, p) * n := Nat.mul_comm _ _
  have hfin :
      (2 * ∏ p ∈ n.primeFactors, (p - 1)) * n ≤ (∏ p ∈ n.primeFactors, p) * n := by
    have hre : (2 * ∏ p ∈ n.primeFactors, (p - 1)) * n
        = (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by ring
    rw [hre]; exact hchain
  exact Nat.le_of_mul_le_mul_right hfin (Nat.pos_of_ne_zero hn)

/-! ### Counting part: two odd primes do not pay for abundance -/

/-- Arithmetic fact: for distinct odd `p, q ≥ 3` (one of them is then ≥ 5)
    we have `pq < 2(p−1)(q−1)` — equivalent to `(p−2)(q−2) ≥ 3 > 2`. -/
private theorem two_mul_pred_mul_pred_gt {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hne : p ≠ q) (hpo : p % 2 = 1) (hqo : q % 2 = 1) :
    p * q < 2 * ((p - 1) * (q - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 3 := ⟨p - 3, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 3 := ⟨q - 3, by omega⟩
  have e1 : a + 3 - 1 = a + 2 := by omega
  have e2 : b + 3 - 1 = b + 2 := by omega
  rw [e1, e2]
  -- distinctness + oddness ⟹ one of the tails is ≥ 2 (i.e. one prime is ≥ 5)
  have h5 : 2 ≤ a ∨ 2 ≤ b := by omega
  have hid : (a + 3) * (b + 3) + (a * b + a + b) = 2 * ((a + 2) * (b + 2)) + 1 := by
    ring
  rcases h5 with h | h
  · nlinarith [Nat.zero_le (a * b), hid]
  · nlinarith [Nat.zero_le (a * b), hid]

/-! ### Main theorem: three distinct prime factors -/

/-- **CLASSICAL (proved): an odd perfect number has at least three
    distinct prime factors.** Route: abundance bound
    `2·∏(p−1) ≤ ∏p` (`perfect_two_mul_prod_pred_le_prod`); with one odd
    prime factor `p ≥ 3` it gives `p ≤ 2`, with two distinct odd primes it
    contradicts `pq < 2(p−1)(q−1)`. NOT a solution to the open problem: merely
    a qualitative narrowing of the domain of the hypothetical witness. -/
theorem odd_perfect_three_le_card_primeFactors {n : ℕ}
    (hodd : Odd n) (hperf : Nat.Perfect n) :
    3 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact (by decide : ¬ Nat.Perfect 1) hperf
  -- all prime factors of odd n are odd and ≥ 3
  have hodd_p : ∀ p ∈ n.primeFactors, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
    have hne2 : p ≠ 2 := by
      rintro rfl
      have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    have h2 := hpp.two_le
    exact ⟨by omega, Nat.odd_iff.mp (hpp.odd_of_ne_two hne2)⟩
  by_contra hlt
  have hlt3 : n.primeFactors.card < 3 := Nat.not_le.mp hlt
  have key := perfect_two_mul_prod_pred_le_prod hn0 hperf
  have hpos : 0 < n.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
  have hc : n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 := by omega
  rcases hc with hc | hc
  · -- one prime factor: 2(p−1) ≤ p with p ≥ 3 is impossible
    obtain ⟨p, hs⟩ := Finset.card_eq_one.mp hc
    have hp := hodd_p p (by rw [hs]; exact Finset.mem_singleton_self p)
    rw [hs, Finset.prod_singleton, Finset.prod_singleton] at key
    omega
  · -- two distinct prime factors: 2(p−1)(q−1) ≤ pq versus pq < 2(p−1)(q−1)
    obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hc
    have hp := hodd_p p (by rw [hs]; exact Finset.mem_insert_self p {q})
    have hq := hodd_p q
      (by rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    rw [hs, Finset.prod_pair hpq, Finset.prod_pair hpq] at key
    exact absurd key
      (Nat.not_le.mpr (two_mul_pred_mul_pred_gt hp.1 hq.1 hpq hp.2 hq.2))

/-! ### Corollaries in the language of the OddPerfectNumber witness -/

/-- A hypothetical odd perfect witness is not a prime. -/
theorem oddPerfect_not_prime (W : OddPerfectNumber) : ¬ W.1.Prime :=
  fun hp => not_perfect_prime hp W.2.2

/-- A hypothetical odd perfect witness is not a prime power
    (a candidate of the form `p^k` is ruled out by the unconditional `not_perfect_prime_pow`). -/
theorem oddPerfect_not_primePow (W : OddPerfectNumber) : ¬ IsPrimePow W.1 := by
  intro h
  obtain ⟨p, k, hp, hk, heq⟩ := (isPrimePow_nat_iff _).mp h
  refine not_perfect_prime_pow hp hk.ne' ?_
  rw [heq]
  exact W.2.2

/-- **Three prime factors of an odd witness (proved):** every
    `W : OddPerfectNumber` has ≥ 3 distinct prime factors. The first
    QUALITATIVE (non-decide-numeric) green narrowing of the witness domain —
    alongside the numeric boundary `oddPerfect_ge_101`. -/
theorem oddPerfect_min_three_prime_factors (W : OddPerfectNumber) :
    3 ≤ W.1.primeFactors.card :=
  odd_perfect_three_le_card_primeFactors W.2.1 W.2.2

#print axioms pred_mul_geomSum_add_one
#print axioms pred_mul_sigma_prime_pow_add_one
#print axioms not_perfect_prime_pow
#print axioms not_perfect_prime
#print axioms perfect_two_mul_prod_pred_le_prod
#print axioms odd_perfect_three_le_card_primeFactors
#print axioms oddPerfect_not_prime
#print axioms oddPerfect_not_primePow
#print axioms oddPerfect_min_three_prime_factors

end EuclidsPath.PerfectNumberBranch
