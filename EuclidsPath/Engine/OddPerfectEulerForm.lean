/-
  OddPerfectEulerForm — TIER FLAGSHIP: Euler's theorem on odd perfect numbers.
  Report section: "Perfect numbers (odd witness)".
  Neighbouring steps: Engine/PerfectNumberBranch.lean (witness type, oddPerfect_ge_101),
  Engine/OddPerfectThreePrimes.lean (≥ 3 prime divisors, abundance estimate).

  GREEN MODULE (everything proved, no sorry/axiom/native_decide, quarantine NOT imported):
    * exists_unique_odd_exponent — EXACTLY ONE prime divisor of an odd perfect
      number has an odd exponent (step 1);
    * special_prime_one_mod_four — that special prime q ≡ 1 (mod 4) (step 2);
    * exponent_one_mod_four — its exponent α ≡ 1 (mod 4) (step 3);
    * odd_perfect_euler_form — FULL EULER FORM: an odd perfect number
      n = q^α · m² with q prime, q ≡ α ≡ 1 (mod 4), q ∤ m (step 4);
    * oddPerfect_euler_form — the same form in the language of the witness OddPerfectNumber.

  MATHEMATICS (Euler, classical 18th century). σ(n) = 2n, and for odd n the factor
  of two enters 2n to exactly the first power. σ is multiplicative: σ(n) = ∏_p σ(p^{a_p})
  over the factorization. For odd p the sum σ(p^a) = 1 + p + … + p^a consists of a+1
  odd summands, hence is even ⟺ a is odd. Therefore the odd exponent belongs to exactly
  ONE prime q (zero would make σ(n) odd, two would give 4 ∣ σ(n) = 2n —
  both branches break the oddness of n). The remaining exponents are even — their part
  assembles into a perfect square m². For q itself: σ(q^α) ∣ 2n implies σ(q^α) ≡ 2 (mod 4);
  if q ≡ 3 (mod 4), the pairs q^{2i} + q^{2i+1} would give 1 + 3 ≡ 0 (mod 4) — the whole
  sum would be divisible by 4 (unsigned form: ∑_{i<2t} q^i = (1+q)·∑_{j<t} (q²)^j and
  4 ∣ 1+q); therefore q ≡ 1 (mod 4), and then σ(q^α) ≡ α + 1 (mod 4) gives α ≡ 1 (mod 4).

  HONESTY: this is NOT a solution to the odd perfect number problem (open since
  antiquity) and NOT Gödel — neither the existence nor the
  non-existence of a witness is asserted here. This is proved CLASSICAL mathematics about
  the conditional form of a hypothetical witness: every such witness must be q^α·m².
  There are no data anchors / fronts in this module: all theorems are unconditional
  arithmetic, paid for by mathlib multiplicativity of
  σ₁ (sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul,
  sigma_one_apply_prime_pow) and mod-2/mod-4 counting. Taint 47 does not change.
-/
import Mathlib
import EuclidsPath.Engine.OddPerfectThreePrimes

set_option autoImplicit false

namespace EuclidsPath.PerfectNumberBranch

/-! ### Building blocks: geometric sums modulo 2 and 4 -/

/-- The sum of powers of odd `p` modulo 2 equals the number of summands modulo 2:
    each `p^i` is odd. -/
private theorem sum_pow_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  have h1 : (∑ i ∈ Finset.range k, p ^ i % 2) = ∑ _i ∈ Finset.range k, 1 :=
    Finset.sum_congr rfl fun i _ => by rw [Nat.pow_mod, hp, one_pow]; omega
  rw [Finset.sum_nat_mod, h1]
  simp

/-- The sum of powers of `p ≡ 1 (mod 4)` modulo 4 equals the number of summands modulo 4:
    each `p^i ≡ 1 (mod 4)`. -/
private theorem sum_pow_mod_four {p : ℕ} (hp : p % 4 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 4 = k % 4 := by
  have h1 : (∑ i ∈ Finset.range k, p ^ i % 4) = ∑ _i ∈ Finset.range k, 1 :=
    Finset.sum_congr rfl fun i _ => by rw [Nat.pow_mod, hp, one_pow]; omega
  rw [Finset.sum_nat_mod, h1]
  simp

/-- Pairing of a geometric sum of even length: `∑_{i<2m} p^i = (1+p)·∑_{j<m} (p²)^j`.
    This unsigned factorization is exactly what carries the "pairs q^{2i}+q^{2i+1}" from Euler's route. -/
private theorem sum_pow_two_mul (p m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), p ^ i
      = (1 + p) * ∑ j ∈ Finset.range m, (p ^ 2) ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-! ### σ-factor of a prime divisor in the factorization decomposition -/

/-- The σ₁-factor of prime `p` in the decomposition `σ₁(n) = ∏_p σ₁(p^{a_p})`:
    the sum `1 + p + … + p^{a_p}` over the factorization exponent. -/
private def sigmaFactor (n p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i

/-- The parity of the σ-factor of an odd prime is governed by the exponent:
    `σ₁(p^a) ≡ a + 1 (mod 2)`. -/
private theorem sigmaFactor_mod_two {n p : ℕ} (hp : p % 2 = 1) :
    sigmaFactor n p % 2 = (n.factorization p + 1) % 2 :=
  sum_pow_mod_two hp _

/-- Multiplicative decomposition of perfection: `∏_p σ₁(p^{a_p}) = 2n`
    (factorization form of `σ₁(n) = 2n`). -/
private theorem perfect_prod_sigmaFactor {n : ℕ} (hn : n ≠ 0) (hperf : Nat.Perfect n) :
    ∏ p ∈ n.primeFactors, sigmaFactor n p = 2 * n := by
  have hσ : ArithmeticFunction.sigma 1 n = 2 * n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero hn)).mp hperf
  have hfac : ArithmeticFunction.sigma 1 n
      = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    simpa using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) hn
  rw [← hσ, hfac]
  rfl

/-- Every prime divisor of an odd number is odd. -/
private theorem primeFactor_mod_two {n : ℕ} (hodd : Odd n) {p : ℕ}
    (hp : p ∈ n.primeFactors) : p % 2 = 1 := by
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have hne2 : p ≠ 2 := by
    rintro rfl
    have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  exact Nat.odd_iff.mp (hpp.odd_of_ne_two hne2)

/-- Two prime divisors of an odd perfect number with odd exponents are equal:
    otherwise both σ-factors are even and `4 ∣ 2n` — contradicting the oddness of `n`. -/
private theorem not_two_odd_exponents {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q r : ℕ} (hq : q ∈ n.primeFactors) (hr : r ∈ n.primeFactors)
    (hqodd : Odd (n.factorization q)) (hrodd : Odd (n.factorization r)) : q = r := by
  by_contra hne
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hrq : r ∈ n.primeFactors.erase q :=
    Finset.mem_erase.mpr ⟨fun h => hne h.symm, hr⟩
  have hprod := perfect_prod_sigmaFactor hn0 hperf
  rw [← Finset.mul_prod_erase n.primeFactors (sigmaFactor n) hq,
    ← Finset.mul_prod_erase (n.primeFactors.erase q) (sigmaFactor n) hrq] at hprod
  have hgq : 2 ∣ sigmaFactor n q := by
    have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hq)
    have h1 := Nat.odd_iff.mp hqodd
    omega
  have hgr : 2 ∣ sigmaFactor n r := by
    have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hr)
    have h1 := Nat.odd_iff.mp hrodd
    omega
  have h4 : 2 * 2 ∣ 2 * n := by
    rw [← hprod]
    exact mul_dvd_mul hgq (hgr.mul_right _)
  obtain ⟨t, ht⟩ := h4
  omega

/-! ### STEP 1: exactly one prime with odd exponent -/

/-- **Step 1 (proved): an odd perfect number has EXACTLY ONE prime divisor
    with an odd exponent.** Existence: if all exponents were even,
    all σ-factors would be odd and `σ(n) = 2n` would be odd. Uniqueness:
    two even σ-factors would give `4 ∣ 2n` — contradicting the oddness of `n`
    (`not_two_odd_exponents`). NOT a solution to the open problem: the form of a hypothetical
    witness. -/
theorem exists_unique_odd_exponent {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) :
    ∃! q, q ∈ n.primeFactors ∧ Odd (n.factorization q) := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hex : ∃ q, q ∈ n.primeFactors ∧ Odd (n.factorization q) := by
    by_contra hno
    push Not at hno
    have hall : ∀ p ∈ n.primeFactors, sigmaFactor n p % 2 = 1 := by
      intro p hp
      have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hp)
      have hpe : n.factorization p % 2 = 0 :=
        Nat.even_iff.mp ((Nat.even_or_odd _).resolve_right (hno p hp))
      omega
    have hprod := perfect_prod_sigmaFactor hn0 hperf
    have hone : (∏ p ∈ n.primeFactors, sigmaFactor n p) % 2 = 1 := by
      have hcong : (∏ p ∈ n.primeFactors, sigmaFactor n p % 2)
          = ∏ _p ∈ n.primeFactors, 1 := Finset.prod_congr rfl hall
      rw [Finset.prod_nat_mod, hcong]
      simp
    rw [hprod] at hone
    omega
  obtain ⟨q, hq, hqodd⟩ := hex
  exact ⟨q, ⟨hq, hqodd⟩, fun r hrpair =>
    not_two_odd_exponents hodd hperf hrpair.1 hq hrpair.2 hqodd⟩

/-! ### STEP 2: the special prime q ≡ 1 (mod 4) -/

/-- Key mod-4 building block: the σ-factor of the special prime is congruent to 2 modulo 4.
    It is even (odd exponent), while `4 ∣ σ(q^α)` would give `4 ∣ 2n` — contradicting
    the oddness of `n`; from `σ(q^α) ∣ 2n` exactly remainder 2 remains. -/
private theorem sigmaFactor_special_mod_four {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q : ℕ} (hq : q ∈ n.primeFactors) (hqodd : Odd (n.factorization q)) :
    sigmaFactor n q % 4 = 2 := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hprod := perfect_prod_sigmaFactor hn0 hperf
  rw [← Finset.mul_prod_erase n.primeFactors (sigmaFactor n) hq] at hprod
  have hgq : sigmaFactor n q % 2 = 0 := by
    have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hq)
    have h1 := Nat.odd_iff.mp hqodd
    omega
  by_contra hne
  have h40 : sigmaFactor n q % 4 = 0 := by omega
  have h4 : 4 ∣ 2 * n := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h40) _
  obtain ⟨t, ht⟩ := h4
  omega

/-- **Step 2 (proved): Euler's special prime is congruent to 1 modulo 4.**
    If `q ≡ 3 (mod 4)`, the pairs `q^{2i} + q^{2i+1} ≡ 1 + 3 ≡ 0 (mod 4)` would give
    `4 ∣ σ(q^α)` (unsigned pairing `sum_pow_two_mul` + `4 ∣ 1+q`) — contradicting
    `σ(q^α) ≡ 2 (mod 4)`. -/
theorem special_prime_one_mod_four {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q : ℕ} (hq : q ∈ n.primeFactors) (hqodd : Odd (n.factorization q)) :
    q % 4 = 1 := by
  have hq2 : q % 2 = 1 := primeFactor_mod_two hodd hq
  have hmod4 := sigmaFactor_special_mod_four hodd hperf hq hqodd
  by_contra hne
  have hq3 : q % 4 = 3 := by omega
  obtain ⟨t, ht⟩ : ∃ t, n.factorization q + 1 = 2 * t := by
    have h1 := Nat.odd_iff.mp hqodd
    exact ⟨(n.factorization q + 1) / 2, by omega⟩
  have hfac : sigmaFactor n q = (1 + q) * ∑ j ∈ Finset.range t, (q ^ 2) ^ j := by
    unfold sigmaFactor
    rw [ht]
    exact sum_pow_two_mul q t
  have h4 : 4 ∣ sigmaFactor n q := by
    rw [hfac]
    exact dvd_mul_of_dvd_left (by omega : (4 : ℕ) ∣ 1 + q) _
  omega

/-! ### STEP 3: the exponent α ≡ 1 (mod 4) -/

/-- **Step 3 (proved): the exponent of the special prime is congruent to 1 modulo 4.**
    With `q ≡ 1 (mod 4)` the sum `σ(q^α)` of `α + 1` units modulo 4 gives
    `α + 1 ≡ 2 (mod 4)`, i.e. `α ≡ 1 (mod 4)`. -/
theorem exponent_one_mod_four {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q : ℕ} (hq : q ∈ n.primeFactors) (hqodd : Odd (n.factorization q)) :
    n.factorization q % 4 = 1 := by
  have hq4 : q % 4 = 1 := special_prime_one_mod_four hodd hperf hq hqodd
  have hmod4 := sigmaFactor_special_mod_four hodd hperf hq hqodd
  have hsum : sigmaFactor n q % 4 = (n.factorization q + 1) % 4 :=
    sum_pow_mod_four hq4 _
  omega

/-! ### STEP 4: full Euler form n = q^α · m² -/

/-- **EULER'S THEOREM (proved, full form): every odd perfect number
    has the form `n = q^α · m²`, where `q` is prime, `q ≡ 1 (mod 4)`, `α ≡ 1 (mod 4)`
    and `q ∤ m`.** Assembly of steps: the unique odd exponent
    (`exists_unique_odd_exponent`) singles out `q`; its residues are steps 2–3;
    the remaining exponents are even, their product `∏ p^{a_p} = (∏ p^{a_p/2})²`
    packs into `m²`; `q ∤ m` because every factor of `m` is a power of
    a prime different from `q`. NOT a solution to the open problem: the conditional form
    of a hypothetical witness, known since the 18th century. -/
theorem odd_perfect_euler_form {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) :
    ∃ q α m : ℕ, q.Prime ∧ q % 4 = 1 ∧ α % 4 = 1 ∧ n = q ^ α * m ^ 2 ∧ ¬ q ∣ m := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  obtain ⟨q, ⟨hq, hqodd⟩, huniq⟩ := exists_unique_odd_exponent hodd hperf
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  refine ⟨q, n.factorization q,
    ∏ p ∈ n.primeFactors.erase q, p ^ (n.factorization p / 2),
    hqp, special_prime_one_mod_four hodd hperf hq hqodd,
    exponent_one_mod_four hodd hperf hq hqodd, ?_, ?_⟩
  · -- packing into a square: all exponents outside q are even
    have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
      Nat.prod_factorization_pow_eq_self hn0
    have hsplit :
        q ^ n.factorization q * ∏ p ∈ n.primeFactors.erase q, p ^ n.factorization p
          = n := by
      rw [Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) hq]
      exact hself
    have hsq : ∏ p ∈ n.primeFactors.erase q, p ^ n.factorization p
        = (∏ p ∈ n.primeFactors.erase q, p ^ (n.factorization p / 2)) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hp
      have hpe : n.factorization p % 2 = 0 := by
        by_contra hne0
        exact hpne (huniq p ⟨hpmem, Nat.odd_iff.mpr (by omega)⟩)
      rw [← pow_mul]
      congr 1
      omega
    rw [← hsq]
    exact hsplit.symm
  · -- q does not divide m: every factor of m is a power of a prime p ≠ q
    intro hdvd
    obtain ⟨p, hp, hpdvd⟩ := (hqp.prime.dvd_finsetProd_iff _).mp hdvd
    obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have heq : q = p :=
      (Nat.prime_dvd_prime_iff_eq hqp hpp).mp (hqp.dvd_of_dvd_pow hpdvd)
    exact hpne heq.symm

/-! ### Euler form in the language of the witness OddPerfectNumber -/

/-- **Euler form for the hypothetical witness (proved):** every
    `W : OddPerfectNumber` must have the form `q^α · m²` with `q ≡ α ≡ 1 (mod 4)`
    and `q ∤ m` — together with `oddPerfect_ge_101` and `oddPerfect_min_three_prime_factors`
    this is the third green narrowing of the witness domain. -/
theorem oddPerfect_euler_form (W : OddPerfectNumber) :
    ∃ q α m : ℕ, q.Prime ∧ q % 4 = 1 ∧ α % 4 = 1 ∧ W.1 = q ^ α * m ^ 2 ∧ ¬ q ∣ m :=
  odd_perfect_euler_form W.2.1 W.2.2

#print axioms exists_unique_odd_exponent
#print axioms special_prime_one_mod_four
#print axioms exponent_one_mod_four
#print axioms odd_perfect_euler_form
#print axioms oddPerfect_euler_form

end EuclidsPath.PerfectNumberBranch
