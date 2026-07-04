/-
  MersenneBranch — an honest bridge Mersenne ↔ twins.

  ⚠️ CORE HONESTY: the infinitude of Mersenne primes does NOT follow from the twin-prime
  hypothesis — neither trivially nor by any known route. These are INDEPENDENT open
  problems: twins yield ∞ twin-centers, but say nothing about the exponentially
  rare Mersenne centers. The implication "twins ⟹ Mersenne" is NOT claimed here
  (marker NoTwinsToMersenneImplicationClaimed).

  WHAT IS PROVEN (mathlib mersenne, std axioms, no sorry):
    * mersenne_eq_sixCenter_add_one — EMBEDDING into the programme's language: for odd p
      the Mersenne number 2^p − 1 = 6·m_p + 1 — the PLUS side of the center
      m_p = (2^(p−1) − 1)/3;
    * isTwinCenter_mersenneCenter_iff — twin-center criterion for a Mersenne center:
      m_p is a twin-center ⟺ 2^p − 3 and 2^p − 1 are both prime;
    * mersenne_twin_instances — concrete Mersenne twins: p = 3 gives (5, 7),
      p = 5 gives (29, 31);
    * twinLowersInfinite_of_mersenneTwins — THE ONLY trivial implication,
      and it goes in the REVERSE direction: ∞ Mersenne twins ⟹ twin-prime conjecture.
  MersennePrimesInfinite — a goal-marker, derived from nothing here.
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.MersenneBranch

open EuclidsPath

/-- Mersenne center: `m_p = (2^(p−1) − 1)/3` (for odd `p` the division is exact). -/
def mersenneCenter (p : ℕ) : ℕ := (2 ^ (p - 1) - 1) / 3

/-- **EMBEDDING INTO THE PROGRAMME'S LANGUAGE (proven):** for odd `p` the Mersenne number is the
    PLUS side of the center: `2^p − 1 = 6·m_p + 1`. -/
theorem mersenne_eq_sixCenter_add_one {p : ℕ} (hp : Odd p) :
    mersenne p = 6 * mersenneCenter p + 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h4 : 4 ^ k % 3 = 1 := by
    have h := Nat.pow_mod 4 k 3
    simpa using h
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨c, hcc⟩ : 3 ∣ 4 ^ k - 1 := by omega
  have hexp : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    ring
  have h2pow : (2 : ℕ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  have hc : mersenneCenter (2 * k + 1) = c := by
    unfold mersenneCenter
    rw [Nat.add_sub_cancel, h2pow, hcc]
    exact Nat.mul_div_cancel_left c (by norm_num)
  have hval : 2 * 4 ^ k - 1 = 6 * c + 1 := by omega
  calc mersenne (2 * k + 1)
      = 2 ^ (2 * k + 1) - 1 := rfl
    _ = 2 * 4 ^ k - 1 := by rw [hexp]
    _ = 6 * c + 1 := hval
    _ = 6 * mersenneCenter (2 * k + 1) + 1 := by rw [hc]

/-- **TWIN-CENTER CRITERION FOR THE MERSENNE CENTER (proven):** center `m_p` is a twin-center ⟺
    `2^p − 3` and `2^p − 1` are both prime. -/
theorem isTwinCenter_mersenneCenter_iff {p : ℕ} (hp : Odd p) (h2 : 2 ≤ p) :
    IsTwinCenter (mersenneCenter p) ↔
      (2 ^ p - 3).Prime ∧ (mersenne p).Prime := by
  have heq := mersenne_eq_sixCenter_add_one hp
  have hpow : 4 ≤ 2 ^ p := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h2
  unfold mersenne at heq ⊢
  unfold IsTwinCenter
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have : 6 * mersenneCenter p - 1 = 2 ^ p - 3 := by omega
      rwa [this] at hlo
    · have : 6 * mersenneCenter p + 1 = 2 ^ p - 1 := by omega
      rwa [this] at hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · have : 6 * mersenneCenter p - 1 = 2 ^ p - 3 := by omega
      rw [this]; exact hlo
    · have : 6 * mersenneCenter p + 1 = 2 ^ p - 1 := by omega
      rw [this]; exact hhi

/-- Concrete Mersenne twins: `p = 3` gives the pair `(5, 7)`, `p = 5` gives `(29, 31)`. -/
theorem mersenne_twin_instances :
    IsTwinCenter (mersenneCenter 3) ∧ IsTwinCenter (mersenneCenter 5) := by
  constructor
  · rw [isTwinCenter_mersenneCenter_iff ⟨1, by norm_num⟩ (by norm_num)]
    constructor <;> norm_num [mersenne]
  · rw [isTwinCenter_mersenneCenter_iff ⟨2, by norm_num⟩ (by norm_num)]
    constructor <;> norm_num [mersenne]

/-- Unboundedness of Mersenne twins (named input hypothesis, much stronger than twins). -/
def MersenneTwinCentersUnbounded : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < 2 ^ p - 3 ∧ (2 ^ p - 3).Prime ∧ (mersenne p).Prime

/-- **HONEST DIRECTION (proven):** Mersenne twins ⟹ twins.
    This is THE ONLY trivial implication between the topics — and it goes in THIS direction. -/
theorem twinLowersInfinite_of_mersenneTwins
    (H : MersenneTwinCentersUnbounded) : TwinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, h1, h2⟩ := H B
  have h5 : 5 ≤ 2 ^ p := by
    have := h1.two_le
    omega
  have hmem : (2 ^ p - 3) ∈ TwinLowers := by
    show IsTwinPair (2 ^ p - 3)
    refine ⟨h1, ?_⟩
    have hstep : 2 ^ p - 3 + 2 = mersenne p := by
      unfold mersenne
      omega
    rw [hstep]
    exact h2
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- Goal-marker: infinitude of Mersenne primes. NOT derived here from anything. -/
def MersennePrimesInfinite : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (mersenne p).Prime

/-- **HONESTY (coverage):** the implication `twins ⟹ Mersenne` is NOT claimed,
    NOT proven, and NOT known to mathematics: twins yield ∞ twin-centers, but
    say nothing about Mersenne centers (exponentially rare). The converse is
    trivial and proven above. -/
abbrev NoTwinsToMersenneImplicationClaimed : Prop := True

theorem noTwinsToMersenneImplicationClaimed :
    NoTwinsToMersenneImplicationClaimed := trivial

end EuclidsPath.MersenneBranch
