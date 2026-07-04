/-
  FermatMersenneLadder — arithmetic ladder Fermat ↔ Mersenne:
  parity of the Fermat twin index, fragment of the §16 heuristic, and
  the multiplicative bridge between the two branches.

  WHAT IS PROVED (mathlib Nat.fermatNumber + mersenne, standard axioms,
  no sorry, no native_decide, quarantine NOT imported):

    (a) PARITY OF THE FERMAT TWIN INDEX:
      * two_pow_mod_three_of_odd — 2^k ≡ 2 (mod 3) for odd k;
      * seven_dvd_fermatNumber_add_two_of_odd — 7 ∣ F_k + 2 for odd k
        (2^k ≡ 2 mod 3 ⟹ 2^(2^k) ≡ 4 mod 7 ⟹ F_k + 2 ≡ 0 mod 7);
        ⚠️ CAVEAT k = 1: divisibility holds there too, but F₁ + 2 = 7 is
        ITSELF prime, so the pair (5, 7) survives; divisibility kills only
        for k ≥ 2 (then F_k + 2 > 7);
      * fermatNumber_add_two_not_prime_of_odd — for odd k ≥ 2 the upper
        member F_k + 2 is composite;
      * fermat_twin_index_eq_one_or_even — a Fermat twin-center is possible
        only for k = 1 or even k: HALF the indices drop out green, the
        witness domain FermatTwinAbsenceAbove narrows by half;
      * fermat_twin_non_instance_of_parity — k = 3 (259 = 7·37) is now a
        CONSEQUENCE of the general parity law (formerly a separate check
        FermatBranch.fermat_twin_non_instance).

    (b) FRAGMENT OF THE §16 HEURISTIC (until now lived ONLY as a comment in
        CausalClosureAxiom:2606 and MersenneManifestationFront:35):
      * five_dvd_two_pow_sub_three_of_three_mod_four — 5 ∣ 2^p − 3 for
        p ≡ 3 (mod 4); mirror of the pearl `sophieGermain_divides_mersenne`;
        ⚠️ CAVEAT p = 3: 2³ − 3 = 5 is divisible by 5 AND itself prime —
        the pair (5, 7) survives; kills only for p > 3;
      * two_pow_sub_three_not_prime_of_three_mod_four — for p > 3,
        p ≡ 3 (mod 4) the number 2^p − 3 is composite;
      * mersenneTwin_exponent_one_mod_four — the exponent of a Mersenne twin
        above p = 3 must be ≡ 1 (mod 4): §16's rejection of the
        `mersenneBoundary` decree now has a green proof INSIDE the repo;
      * mersenne_twin_non_instance_seven — p = 7 yields no pair (125 = 5³).

    (c) MULTIPLICATIVE BRIDGE BETWEEN BRANCHES:
      * mersenne_two_pow_eq_prod_fermatNumber — mersenne (2^n) = ∏_{k<n} F_k
        (telescope (x−1)(x+1) = x²−1; rewriting via Nat.prod_fermatNumber);
        minus-side of the grid (Mersenne) = product of plus-sides (Fermat);
      * mersenne_two_pow_not_prime — for n ≥ 2 the number mersenne (2^n)
        is composite (divisible by F₀ = 3): it is machine-visible why the
        domain MersenneTwinAbsenceAbove effectively ranges only over prime p.
      HONESTY (anti-duplicate): the wrapper "(mersenne n).Prime → n.Prime" is
      NOT stated — the fact is already consumed inline via
      Nat.prime_of_pow_sub_one_prime in PerfectNumberBranch.lean:136-138;
      a named duplicate is forbidden by the skeptic's verdict.

    (d) GOLDBACH PAIRWISE COPRIMALITY IN THE LANGUAGE OF THE BRIDGE:
      * fermatNumber_index_eq_of_prime_dvd — a prime divides AT MOST one
        Fermat number (pairwise coprimality,
        Nat.coprime_fermatNumber_fermatNumber — Goldbach's letter to Euler);
      * mersenne_two_pow_prime_dvd_iff — the prime divisors of mersenne (2^n)
        are EXACTLY the prime divisors of Fermat numbers F₀ … F_{n−1};
      * mersenne_two_pow_prime_divisor_unique — each prime divisor of
        mersenne (2^n) divides EXACTLY ONE Fermat number: the ladder layers
        do not intersect.

  HONESTY (frame). This is NOT a resolution of the question of infinitely many
  Fermat or Mersenne twins, and NOT Gödel — only elementary modular
  arithmetic, green-narrowing the OPEN inputs FermatTwinCentersUnbounded /
  MersenneTwinCentersUnbounded: half the Fermat indices and half the odd
  Mersenne exponents drop out. Everything is paid by kernel computation modulo
  3, 5, 7 (Nat.pow_mod) and ready-made mathlib facts; no new axioms, the
  repository taint does not change.
-/
import Mathlib
import EuclidsPath.Engine.FermatBranch
import EuclidsPath.Engine.MersenneBranch

set_option autoImplicit false

namespace EuclidsPath.FermatMersenneLadder

open EuclidsPath
open EuclidsPath.FermatBranch
open EuclidsPath.MersenneBranch

/-! ## (a) Parity of the Fermat twin index: 7 ∣ F_k + 2 for odd k -/

/-- Period 2 modulo 3: for odd `k` we have `2^k ≡ 2 (mod 3)`
    (`2 ≡ −1`, odd power remains `−1`). -/
theorem two_pow_mod_three_of_odd {k : ℕ} (hk : Odd k) : 2 ^ k % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hk
  have h4 : 4 ^ m % 3 = 1 := by
    have h := Nat.pow_mod 4 m 3
    simpa using h
  have hexp : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num [mul_comm]
  rw [hexp]
  omega

/-- **PARITY OF THE INDEX (proved): `7 ∣ F_k + 2` for odd `k`.**
    Route: `2^n mod 7` has cycle 3 (`2, 4, 1`); for odd `k`
    the exponent `2^k ≡ 2 (mod 3)`, so `2^(2^k) ≡ 4 (mod 7)` and
    `F_k + 2 = 2^(2^k) + 3 ≡ 0 (mod 7)`.
    ⚠️ CAVEAT `k = 1`: divisibility holds there too (`F₁ + 2 = 7`), but 7 is
    ITSELF prime, so the pair `(5, 7)` survives; compositeness of the upper
    member begins at `k ≥ 2` (see next theorem). -/
theorem seven_dvd_fermatNumber_add_two_of_odd {k : ℕ} (hk : Odd k) :
    7 ∣ Nat.fermatNumber k + 2 := by
  have h3 := two_pow_mod_three_of_odd hk
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = 3 * q + 2 := ⟨2 ^ k / 3, by omega⟩
  have h8 : 8 ^ q % 7 = 1 := by
    have h := Nat.pow_mod 8 q 7
    simpa using h
  have hpow : (2 : ℕ) ^ 2 ^ k = 8 ^ q * 4 := by
    rw [hq, pow_add, pow_mul]
    norm_num
  have h7 : 2 ^ 2 ^ k % 7 = 4 := by
    rw [hpow, Nat.mul_mod, h8]
  show 7 ∣ 2 ^ 2 ^ k + 1 + 2
  omega

/-- For odd `k ≥ 2` the upper member of the twin candidate, `F_k + 2`,
    is COMPOSITE: it is divisible by 7 and strictly greater than 7 (`F_k ≥ F_2 = 17`). -/
theorem fermatNumber_add_two_not_prime_of_odd {k : ℕ} (hk : Odd k) (h2 : 2 ≤ k) :
    ¬ (Nat.fermatNumber k + 2).Prime := by
  intro hP
  have hdvd : 7 ∣ Nat.fermatNumber k + 2 := seven_dvd_fermatNumber_add_two_of_odd hk
  have hge : Nat.fermatNumber 2 ≤ Nat.fermatNumber k := Nat.fermatNumber_mono h2
  rw [Nat.fermatNumber_two] at hge
  rcases hP.eq_one_or_self_of_dvd 7 hdvd with h | h <;> omega

/-- **NARROWING OF THE OPEN INPUT (proved):** a Fermat twin-center is possible
    only for `k = 1` or EVEN `k` — half the indices drop out green, the
    witness domain `FermatTwinAbsenceAbove` narrows by half. Machine-verified
    support for the §17 thesis about the inverted heuristic sign (until now
    held only by prose). NOTHING is claimed about even `k` — that question is OPEN. -/
theorem fermat_twin_index_eq_one_or_even {k : ℕ} (hk : 1 ≤ k)
    (htwin : IsTwinCenter (fermatCenter k)) : k = 1 ∨ Even k := by
  rcases Nat.even_or_odd k with he | ho
  · exact Or.inr he
  · left
    by_contra hne
    have h2 : 2 ≤ k := by
      obtain ⟨m, hm⟩ := ho
      omega
    have hpair := (isTwinCenter_fermatCenter_iff hk).mp htwin
    exact fermatNumber_add_two_not_prime_of_odd ho h2 hpair.2

/-- Failure of `k = 3` (259 = 7·37) — now a CONSEQUENCE of the general parity
    law, not a separate numeric check (`FermatBranch.fermat_twin_non_instance`
    proved the same by direct computation). -/
theorem fermat_twin_non_instance_of_parity :
    ¬ IsTwinCenter (fermatCenter 3) := by
  intro h
  rcases fermat_twin_index_eq_one_or_even (by norm_num) h with h1 | he
  · norm_num at h1
  · have h32 := Nat.even_iff.mp he
    omega

/-! ## (b) Fragment of the §16 heuristic: 5 ∣ 2^p − 3 for p ≡ 3 (mod 4) -/

/-- **FRAGMENT OF THE §16 HEURISTIC (proved): `5 ∣ 2^p − 3` for `p ≡ 3 (mod 4)`.**
    `2^n mod 5` has cycle 4 (`2, 4, 3, 1`); for `p ≡ 3` we get
    `2^p ≡ 3 (mod 5)`. Before this lemma the fact lived ONLY as a comment
    (CausalClosureAxiom:2606, MersenneManifestationFront:35) — §16's rejection
    of the `mersenneBoundary` decree is now green-justified inside the repo.
    Mirror of the pearl `sophieGermain_divides_mersenne`.
    ⚠️ CAVEAT `p = 3`: `2³ − 3 = 5` is divisible by 5 AND itself prime —
    the pair `(5, 7)` survives; compositeness begins at `p > 3`. -/
theorem five_dvd_two_pow_sub_three_of_three_mod_four {p : ℕ} (hp : p % 4 = 3) :
    5 ∣ 2 ^ p - 3 := by
  obtain ⟨q, hq⟩ : ∃ q, p = 4 * q + 3 := ⟨p / 4, by omega⟩
  have h16 : 16 ^ q % 5 = 1 := by
    have h := Nat.pow_mod 16 q 5
    simpa using h
  have hpow : (2 : ℕ) ^ p = 16 ^ q * 8 := by
    rw [hq, pow_add, pow_mul]
    norm_num
  have h5 : 2 ^ p % 5 = 3 := by
    rw [hpow, Nat.mul_mod, h16]
  have hge : 8 ≤ 2 ^ p := by
    rw [hpow]
    have h1 : 1 ≤ 16 ^ q := Nat.one_le_pow _ _ (by norm_num)
    omega
  omega

/-- For `p > 3`, `p ≡ 3 (mod 4)` the number `2^p − 3` is COMPOSITE: divisible
    by 5 and strictly greater than 5 (`2^p ≥ 2^7 = 128`). -/
theorem two_pow_sub_three_not_prime_of_three_mod_four {p : ℕ}
    (hp : p % 4 = 3) (h3 : 3 < p) : ¬ (2 ^ p - 3).Prime := by
  intro hP
  have hdvd := five_dvd_two_pow_sub_three_of_three_mod_four hp
  have hge : 128 ≤ 2 ^ p := by
    calc (128 : ℕ) = 2 ^ 7 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hP.eq_one_or_self_of_dvd 5 hdvd with h | h <;> omega

/-- **NARROWING OF THE SECOND OPEN INPUT (proved):** the exponent of a
    Mersenne twin above `p = 3` must be `≡ 1 (mod 4)` — half the odd
    exponents drop out green (consistent with known instances: p = 5 ≡ 1,
    while p = 3 is the boundary exception `2³−3 = 5`).
    The hypothesis `Odd p` is mandatory: the criterion
    `isTwinCenter_mersenneCenter_iff` is meaningful only on the odd grid
    (for even p the center `m_p` is an artifact of integer division). -/
theorem mersenneTwin_exponent_one_mod_four {p : ℕ} (hodd : Odd p) (h3 : 3 < p)
    (htwin : IsTwinCenter (mersenneCenter p)) : p % 4 = 1 := by
  have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h | h
  · exact h
  · exfalso
    have hpair := (isTwinCenter_mersenneCenter_iff hodd (by omega)).mp htwin
    exact two_pow_sub_three_not_prime_of_three_mod_four h h3 hpair.1

/-- Failure of `p = 7` (2⁷ − 3 = 125 = 5³) — consequence of the `≡ 1 (mod 4)`
    law; complements the instances `mersenne_twin_instances` (p = 3, 5) from
    the other side. -/
theorem mersenne_twin_non_instance_seven :
    ¬ IsTwinCenter (mersenneCenter 7) := by
  intro h
  have h1 := mersenneTwin_exponent_one_mod_four ⟨3, by norm_num⟩ (by norm_num) h
  omega

/-! ## (c) Bridge: mersenne (2^n) = product of Fermat numbers -/

/-- **MULTIPLICATIVE BRIDGE BETWEEN BRANCHES (proved):**
    `mersenne (2^n) = ∏_{k<n} F_k` — telescope `(x−1)(x+1) = x²−1`,
    rewritten from `Nat.prod_fermatNumber` into the language of the Mersenne branch.
    The minus-side of the grid (`2^(2^n) − 1`) = product of the plus-sides
    (`2^(2^k) + 1`): the first substantive green bridge between the branches.
    FORMAL LINK: paid by the ready-made mathlib induction
    (`Nat.prod_fermatNumber`) + kernel rewriting of definitions. -/
theorem mersenne_two_pow_eq_prod_fermatNumber (n : ℕ) :
    mersenne (2 ^ n) = ∏ k ∈ Finset.range n, Nat.fermatNumber k := by
  rw [Nat.prod_fermatNumber]
  show 2 ^ 2 ^ n - 1 = 2 ^ 2 ^ n + 1 - 2
  omega

/-- For `n ≥ 2` the number `mersenne (2^n)` is COMPOSITE (divisible by `F₀ = 3`
    and strictly larger: `mersenne (2^n) ≥ mersenne 4 = 15`). It is
    machine-visible why the domain `MersenneTwinAbsenceAbove` effectively
    ranges only over PRIME exponents: power exponents drop out green.
    HONESTY (anti-duplicate): the general wrapper `(mersenne n).Prime → n.Prime`
    is deliberately NOT stated — it is already consumed inline via
    `Nat.prime_of_pow_sub_one_prime` in PerfectNumberBranch.lean:136-138. -/
theorem mersenne_two_pow_not_prime {n : ℕ} (hn : 2 ≤ n) :
    ¬ (mersenne (2 ^ n)).Prime := by
  intro hP
  have h3 : (3 : ℕ) ∣ mersenne (2 ^ n) := by
    rw [mersenne_two_pow_eq_prod_fermatNumber]
    simpa using
      Finset.dvd_prod_of_mem Nat.fermatNumber
        (Finset.mem_range.mpr (show 0 < n by omega))
  have h4 : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hge : 15 ≤ mersenne (2 ^ n) := by
    calc (15 : ℕ) = mersenne 4 := by norm_num [mersenne]
    _ ≤ mersenne (2 ^ n) := mersenne_le_mersenne.mpr h4
  rcases hP.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega

/-! ## (d) Goldbach pairwise coprimality in the language of the bridge -/

/-- **UNIQUENESS OF THE LAYER (proved):** a prime divides AT MOST one
    Fermat number — direct consequence of pairwise coprimality
    (`Nat.coprime_fermatNumber_fermatNumber`, Goldbach's letter to Euler 1730). -/
theorem fermatNumber_index_eq_of_prime_dvd {q i j : ℕ} (hq : q.Prime)
    (hi : q ∣ Nat.fermatNumber i) (hj : q ∣ Nat.fermatNumber j) : i = j := by
  by_contra hne
  have hco : Nat.Coprime (Nat.fermatNumber i) (Nat.fermatNumber j) :=
    Nat.coprime_fermatNumber_fermatNumber hne
  have h1 : q ∣ Nat.gcd (Nat.fermatNumber i) (Nat.fermatNumber j) :=
    Nat.dvd_gcd hi hj
  rw [hco.gcd_eq_one] at h1
  exact hq.ne_one (Nat.dvd_one.mp h1)

/-- **BRIDGE OF DIVISORS (proved):** the prime divisors of `mersenne (2^n)` are
    EXACTLY the prime divisors of the Fermat numbers `F₀ … F_{n−1}`. The
    minus-side of the power index brings NO new primes: its entire supply is
    the Fermat ladder. -/
theorem mersenne_two_pow_prime_dvd_iff {q n : ℕ} (hq : q.Prime) :
    q ∣ mersenne (2 ^ n) ↔ ∃ i < n, q ∣ Nat.fermatNumber i := by
  rw [mersenne_two_pow_eq_prod_fermatNumber, hq.prime.dvd_finsetProd_iff]
  simp only [Finset.mem_range]

/-- **THE LADDER DOES NOT INTERSECT (proved):** each prime divisor of
    `mersenne (2^n)` divides EXACTLY ONE Fermat number `F_i`, `i < n` —
    existence is given by the bridge of divisors, uniqueness by Goldbach
    pairwise coprimality. The ladder layers carry pairwise fresh primes.
    HONESTY: this is a green fact about DIVISORS; the infinitude of Fermat
    PRIME NUMBERS remains a red open input (heuristic sign against — §17). -/
theorem mersenne_two_pow_prime_divisor_unique {q n : ℕ} (hq : q.Prime)
    (hdvd : q ∣ mersenne (2 ^ n)) :
    ∃! i, i < n ∧ q ∣ Nat.fermatNumber i := by
  obtain ⟨i, hi, hqi⟩ := (mersenne_two_pow_prime_dvd_iff hq).mp hdvd
  refine ⟨i, ⟨hi, hqi⟩, ?_⟩
  intro j hj
  exact fermatNumber_index_eq_of_prime_dvd hq hj.2 hqi

/-! ## Axiom audit: the entire module is green (standard triple), taint does not change -/
#print axioms two_pow_mod_three_of_odd
#print axioms seven_dvd_fermatNumber_add_two_of_odd
#print axioms fermatNumber_add_two_not_prime_of_odd
#print axioms fermat_twin_index_eq_one_or_even
#print axioms fermat_twin_non_instance_of_parity
#print axioms five_dvd_two_pow_sub_three_of_three_mod_four
#print axioms two_pow_sub_three_not_prime_of_three_mod_four
#print axioms mersenneTwin_exponent_one_mod_four
#print axioms mersenne_twin_non_instance_seven
#print axioms mersenne_two_pow_eq_prod_fermatNumber
#print axioms mersenne_two_pow_not_prime
#print axioms fermatNumber_index_eq_of_prime_dvd
#print axioms mersenne_two_pow_prime_dvd_iff
#print axioms mersenne_two_pow_prime_divisor_unique

end EuclidsPath.FermatMersenneLadder
