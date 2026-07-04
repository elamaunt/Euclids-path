/-
  PerfectNumberBranch — perfect numbers: the green Euclid–Euler theorem and the odd witness.

  GREEN MODULE (everything proved, no sorry/axiom):
    * Euclid (ch. 34 of the Elements thread, IX.36): Mersenne prime ⟹ even perfect —
      perfect_of_mersennePrime / perfect_of_mersennePrime';
    * Euler (ch. 43 of the thread): even perfect ⟹ form 2^k · (2^(k+1) − 1) with a Mersenne
      prime — evenPerfect_eq. Both sides are re-exports from the mathlib Archive
      (Archive.Wiedijk100Theorems.PerfectNumbers, author Aaron Anderson, Apache 2.0);
    * pointwise decidability of perfection: instance DecidablePred Nat.Perfect,
      perfect_6, perfect_28, not_perfect_945 (machine-checked);
    * odd witness: OddPerfectNumber — the type of witnesses to the open problem;
      noOddPerfect_iff_no_witness; oddPerfect_ge_101 — every odd perfect witness
      is ≥ 101 (machine-checked for small cases);
    * bridge to MersenneBranch: mersennePrimesInfinite_iff_evenPerfectUnbounded —
      goal-marker MersennePrimesInfinite ⟺ unboundedness of even perfect numbers.

  ⚠️ HONESTY: both sides of the equivalence are OPEN problems. What is green here is
  only the equivalence ITSELF: the Elements question about infinitely many even perfect
  numbers = the question about infinitely many Mersenne primes, machine-verified. Infinitely many
  Mersenne primes is NOT claimed (marker NoMersenneInfinitudeClaimed); existence or
  non-existence of an odd perfect number is NOT claimed — but the predicate itself is
  pointwise decidable, and every concrete candidate is checked by computation.
-/
import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers
import EuclidsPath.Engine.MersenneBranch

set_option autoImplicit false

namespace EuclidsPath.PerfectNumberBranch

open EuclidsPath

/-! ### Pointwise decidability of perfection -/

/-- Perfection is decidable: `Nat.Perfect n` is by definition
    `∑ i ∈ properDivisors n, i = n ∧ 0 < n`, and both parts are computable. -/
instance : DecidablePred Nat.Perfect :=
  fun n => decidable_of_iff (∑ i ∈ Nat.properDivisors n, i = n ∧ 0 < n) Iff.rfl

/-- `6 = 2^1 · (2^2 − 1)` — the first perfect number (machine-checked). -/
theorem perfect_6 : Nat.Perfect 6 := by decide

/-- `28 = 2^2 · (2^3 − 1)` — the second perfect number (machine-checked). -/
theorem perfect_28 : Nat.Perfect 28 := by decide

set_option maxRecDepth 4000 in
/-- `945` — the smallest odd abundant number — is not perfect (machine-checked). -/
theorem not_perfect_945 : ¬ Nat.Perfect 945 := by decide

/-! ### Odd perfect witness -/

/-- The conjecture "there are no odd perfect numbers" (open problem, INPUT). -/
def NoOddPerfect : Prop := ∀ N : ℕ, Odd N → ¬ Nat.Perfect N

/-- The type of witnesses to the open problem: an odd perfect number together
    with proofs of both properties. -/
abbrev OddPerfectNumber : Type := {N : ℕ // Odd N ∧ Nat.Perfect N}

/-- The conjecture `NoOddPerfect` ⟺ the witness type is empty. -/
theorem noOddPerfect_iff_no_witness :
    NoOddPerfect ↔ ¬ Nonempty OddPerfectNumber := by
  constructor
  · rintro h ⟨⟨N, hodd, hperf⟩⟩
    exact h N hodd hperf
  · intro h N hodd hperf
    exact h ⟨⟨N, hodd, hperf⟩⟩

/-- Every odd perfect witness is ≥ 101: all smaller odd numbers are
    eliminated by machine-checking (pointwise decidability in action). -/
theorem oddPerfect_ge_101 (W : OddPerfectNumber) : 101 ≤ W.1 := by
  obtain ⟨N, hodd, hperf⟩ := W
  show 101 ≤ N
  by_contra h
  exact (by decide : ∀ M, M < 101 → M % 2 = 1 → ¬ Nat.Perfect M) N (by omega)
    (Nat.odd_iff.mp hodd) hperf

/-! ### Euclid: Mersenne prime ⟹ even perfect (green, Elements IX.36) -/

/-- **EUCLID (proved, re-export from mathlib Archive):** if `2^(k+1) − 1` is prime,
    then `2^k · (2^(k+1) − 1)` is perfect. -/
theorem perfect_of_mersennePrime {k : ℕ} (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) :=
  Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k pr

/-- Euclid in p-form: for `2 ≤ p` and prime `mersenne p` the number
    `2^(p−1) · mersenne p` is perfect. -/
theorem perfect_of_mersennePrime' {p : ℕ} (hp : 2 ≤ p) (pr : (mersenne p).Prime) :
    Nat.Perfect (2 ^ (p - 1) * mersenne p) := by
  have h : p - 1 + 1 = p := by omega
  simpa [h] using perfect_of_mersennePrime (k := p - 1) (by rwa [h])

/-! ### Euler: even perfect ⟹ Euclid form (green) -/

/-- **EULER (proved, re-export from mathlib Archive):** every even perfect
    number has the form `2^k · (2^(k+1) − 1)` with a prime Mersenne factor. -/
theorem evenPerfect_eq {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) :=
  Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf

/-! ### Bridge to MersenneBranch: marker ⟺ unboundedness of even perfect numbers -/

/-- Unboundedness of even perfect numbers (the Elements question, open). -/
def EvenPerfectUnbounded : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Even n ∧ Nat.Perfect n

/-- **BRIDGE (proved):** goal-marker `MersennePrimesInfinite` from MersenneBranch ⟺
    unboundedness of even perfect numbers. Both sides are open; what is green is
    the equivalence itself: two questions are the same one, machine-verified. -/
theorem mersennePrimesInfinite_iff_evenPerfectUnbounded :
    MersenneBranch.MersennePrimesInfinite ↔ EvenPerfectUnbounded := by
  constructor
  · -- infinitely many Mersenne primes ⟹ even perfect numbers are unbounded
    intro H N
    obtain ⟨p, hNp, hp, hmp⟩ := H N
    refine ⟨2 ^ (p - 1) * mersenne p, ?_, ?_, perfect_of_mersennePrime' hp.two_le hmp⟩
    · -- N < p < 2^p = 2^(p−1)·2 ≤ 2^(p−1)·mersenne p
      have hm2 : 2 ≤ mersenne p := hmp.two_le
      have hsplit : 2 ^ p = 2 ^ (p - 1) * 2 := by
        conv_lhs => rw [show p = p - 1 + 1 from by omega]
        rw [pow_succ]
      calc N < p := hNp
        _ < 2 ^ p := p.lt_two_pow_self
        _ = 2 ^ (p - 1) * 2 := hsplit
        _ ≤ 2 ^ (p - 1) * mersenne p := Nat.mul_le_mul (Nat.le_refl _) hm2
    · -- p ≥ 2 ⟹ 2^(p−1) is even ⟹ the product is even
      have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
      exact (Nat.even_pow.mpr ⟨even_two, h1⟩).mul_right _
  · -- even perfect numbers are unbounded ⟹ infinitely many Mersenne primes
    intro H N
    obtain ⟨n, hn, hev, hperf⟩ := H (2 ^ (2 * N + 2))
    obtain ⟨k, hkpr, rfl⟩ := evenPerfect_eq hev hperf
    have hk0 : k ≠ 0 := Theorems100.Nat.ne_zero_of_prime_mersenne k hkpr
    -- exponent k+1 is prime (Fermat: primality of 2^m − 1 requires prime m)
    have hpow : (2 ^ (k + 1) - 1).Prime := hkpr
    have hkp : (k + 1).Prime :=
      (Nat.prime_of_pow_sub_one_prime (a := 2) (n := k + 1) (by omega) hpow).2
    refine ⟨k + 1, ?_, hkp, hkpr⟩
    -- N < k+1: otherwise n = 2^k·(2^(k+1)−1) < 2^(2k+1) ≤ 2^(2N+2) < n
    by_contra hle
    have h1 : mersenne (k + 1) < 2 ^ (k + 1) :=
      Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
    have h2 : 2 ^ k * mersenne (k + 1) < 2 ^ k * 2 ^ (k + 1) :=
      mul_lt_mul_of_pos_left h1 (Nat.two_pow_pos k)
    have h3 : 2 ^ k * 2 ^ (k + 1) = 2 ^ (2 * k + 1) := by
      rw [← pow_add, show k + (k + 1) = 2 * k + 1 from by omega]
    have h4 : 2 ^ (2 * k + 1) ≤ 2 ^ (2 * N + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcontra : (2 : ℕ) ^ (2 * N + 2) < 2 ^ (2 * N + 2) :=
      calc (2 : ℕ) ^ (2 * N + 2) < 2 ^ k * mersenne (k + 1) := hn
        _ < 2 ^ k * 2 ^ (k + 1) := h2
        _ = 2 ^ (2 * k + 1) := h3
        _ ≤ 2 ^ (2 * N + 2) := h4
    exact absurd hcontra (lt_irrefl _)

/-! ### Honesty -/

/-- **HONESTY (scope):** infinitely many Mersenne primes (⟺ unboundedness of
    even perfect numbers, bridge above) is NOT claimed and NOT proved — both sides
    of the equivalence are open. Existence of an odd perfect number is likewise
    open: it is only shown here that any witness is pointwise checkable and ≥ 101. -/
abbrev NoMersenneInfinitudeClaimed : Prop := True

theorem noMersenneInfinitudeClaimed : NoMersenneInfinitudeClaimed := trivial

#print axioms perfect_of_mersennePrime'
#print axioms not_perfect_945
#print axioms oddPerfect_ge_101
#print axioms evenPerfect_eq
#print axioms mersennePrimesInfinite_iff_evenPerfectUnbounded

end EuclidsPath.PerfectNumberBranch
