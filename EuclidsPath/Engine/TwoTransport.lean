/-
  Wave 5: conclusion — conditional reduction of the twin prime conjecture to the block core.
  Prose: prose/18_ReductionAndFrontier.md (after green Lean).

  Here we assemble the VERIFIED non-circular reduction: the twin prime conjecture follows from
  the block statement (at every scale there exists a carrier above N in which bad < carrier, and every
  survivor is a twin-center). This isolates exactly the open core (carrier estimate = CarrierInput;
  bad-upper via fan/cycle; survivor⟹twin). We also show that the direction survivor⟹twin
  is ELEMENTARY (sieve to the root ⟹ primality) — meaning all the difficulty lies in the carrier/bad count.

  Everything is elementary (Finset + minimal prime theory). No analysis / distribution / sieve.
-/
import EuclidsPath.Engine.NonCover

set_option autoImplicit false

namespace EuclidsPath

/-- One block: `carrier > bad` and `survivor ⟹ twin` yield a twin-center above `N`. -/
theorem twin_center_of_block {N : ℕ} {carrier bad : Finset ℕ}
    (habove : ∀ m ∈ carrier, N < m)
    (hcov : bad.card < carrier.card)
    (htwin : ∀ m ∈ carrier, m ∉ bad → IsTwinCenter m) :
    ∃ m, N < m ∧ IsTwinCenter m := by
  obtain ⟨m, hm, hmb⟩ := survivor_of_not_covered hcov
  exact ⟨m, habove m hm, htwin m hm hmb⟩

/--
  **Conditional reduction of the twin prime conjecture to the block core.**
  If at every scale `N` there exists a carrier (centers above `N`) in which the "bad" set is
  strictly smaller than carrier and every survivor is a twin-center, then there are infinitely many twin primes.
  This is a machine-verified non-circular bridge: conjecture ⟸ block core.
-/
theorem twin_prime_conjecture_of_blocks
    (h : ∀ N : ℕ, ∃ carrier bad : Finset ℕ,
           (∀ m ∈ carrier, N < m) ∧ bad.card < carrier.card ∧
           (∀ m ∈ carrier, m ∉ bad → IsTwinCenter m)) :
    TwinLowers.Infinite := by
  apply infinite_of_unbounded_centers
  intro N
  obtain ⟨carrier, bad, habove, hcov, htwin⟩ := h N
  exact twin_center_of_block habove hcov htwin

/--
  **Sieve to the root ⟹ primality.** If `n ≥ 2` and no prime `p` with `p² ≤ n` divides `n`,
  then `n` is prime. (Elementary: otherwise the minimal prime divisor `p=minFac n` gives `p²≤n` and `p∣n`.)
-/
theorem prime_of_no_small_prime_factor {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ p, p.Prime → p * p ≤ n → ¬ p ∣ n) : n.Prime := by
  by_contra hnp
  have hpp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hpd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hnp
  have hpsq : n.minFac * n.minFac ≤ n :=
    le_trans (Nat.mul_le_mul (le_refl _) hle) (Nat.mul_div_le n n.minFac)
  exact h n.minFac hpp hpsq hpd

/--
  **Survivor ⟹ twin (elementary).** If both `6m−1, 6m+1 ≥ 2` and no prime up to their root
  divides the respective side, then `m` is a twin-center. The difficulty therefore lies not here but in the carrier/bad count.
-/
theorem isTwinCenter_of_root_sieve {m : ℕ} (h1 : 2 ≤ 6 * m - 1) (h2 : 2 ≤ 6 * m + 1)
    (s1 : ∀ p, p.Prime → p * p ≤ 6 * m - 1 → ¬ p ∣ (6 * m - 1))
    (s2 : ∀ p, p.Prime → p * p ≤ 6 * m + 1 → ¬ p ∣ (6 * m + 1)) :
    IsTwinCenter m :=
  ⟨prime_of_no_small_prime_factor h1 s1, prime_of_no_small_prime_factor h2 s2⟩

end EuclidsPath
