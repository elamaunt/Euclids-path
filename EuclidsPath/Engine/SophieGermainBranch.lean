/-
  SophieGermainBranch — Sophie Germain: center doubling and the pearl
  (SG primes kill Mersenne).

  Sophie Germain pair: (p, 2p+1), both prime. Geometry in the language of the program:
    * PLUS-side excluded: if p = 6m+1 (m ≥ 1), then 3 ∣ 2(6m+1)+1 = 12m+3,
      so 2p+1 is not prime — SG primes p > 3 live ONLY on the minus-side;
    * on the minus-side the SG map is CENTER DOUBLING m → 2m:
      2(6m−1)+1 = 6(2m)−1 — related to Mersenne chains 4m+1 and the pentadic 5m+1.

  ⚠️ PEARL (Euler–Lagrange, classical, here FULLY proved):
    p ≡ 3 (mod 4), p > 3, q = 2p+1 prime ⟹ q ∣ M_p and M_p is COMPOSITE.
  Route: q ≡ 7 (mod 8) ⟹ 2 is a quadratic residue mod q
  (ZMod.exists_sq_eq_two_iff) ⟹ Euler's criterion gives 2^p ≡ 1 (mod q)
  ⟹ q ∣ 2^p − 1; for p ≥ 4 we have 2p+1 < 2^p − 1, so the divisor is proper.
  This formalizes a FRAGMENT of the very heuristic that the quarantine §16/ch.43
  deployed against the Mersenne boundary: SG primes with p ≡ 3 (mod 4) individually
  KILL Mersenne candidates. The case p = 3 is honestly excluded: q = 7 = M₃,
  which is itself PRIME (the divisor is not proper).

  WHAT IS PROVED (std axioms, no sorry):
    * not_sophieGermain_of_plusSide — plus-side excluded;
    * sophieGermain_minusSide — SG prime p > 3 ⟹ p ≡ 5 (mod 6);
    * sg_center_doubling / isSGCenter_iff — SG pair = center doubling;
    * sg_instances — pairs (5,11), (11,23), (29,59), (89,179);
    * two_mul_add_one_lt_mersenne — growth: 2p+1 < M_p for p ≥ 4;
    * sophieGermain_divides_mersenne — PEARL (see above);
    * mersenne_composite_examples — 23 ∣ M₁₁ = 2047 = 23·89, M₁₁ composite;
    * mersenneComposites_unbounded_of_sg — CONDITIONAL: unboundedness of
      SG primes with p ≡ 3 (mod 4) ⟹ unboundedness of p with M_p composite;
    * sophieGermain_divides_fermat_side — COMPLEMENT of the pearl: p ≡ 1 (mod 4),
      q = 2p+1 prime ⟹ q ∣ 2^p + 1 (q ≡ 3 (mod 8) ⟹ 2 is a non-residue ⟹
      by Euler 2^p = −1 in ZMod q);
    * sophieGermain_dichotomy / sg_dichotomy_exclusive — full dichotomy:
      for every SG pair q ∣ M_p ∨ q ∣ 2^p + 1, and the sides are incompatible;
    * sg_two_pow_p_eq_one_zmod / sg_orderOf_two_eq_p — crypto-lemma:
      orderOf (2 : ZMod (2p+1)) = p for p ≡ 3 (mod 4) (safe primes).

  ⚠️ HONESTY: the Sophie Germain conjecture (SophieGermainUnbounded,
  SGThreeMod4Unbounded) is OPEN — here it is only an INPUT-marker, derived
  from nothing; no open problems are solved. The UNCONDITIONAL
  infinitude of composite Mersenne numbers is a known theorem in the literature
  (by other methods); here it is obtained only CONDITIONALLY from SG-unboundedness.
  The implication «SG ⟹ twins» is NOT claimed
  (marker NoSGToTwinsImplicationClaimed).
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.SophieGermainBranch

open EuclidsPath

/-- Sophie Germain pair with smaller member `p`: primes `p` and `2p+1`. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- **PLUS-SIDE EXCLUDED (proved):** if `p = 6m+1` (m ≥ 1), then
    `2p+1 = 12m+3` is divisible by 3 and not prime. SG primes `p > 3` live
    only on the minus-side. -/
theorem not_sophieGermain_of_plusSide {m : ℕ} (hm : 1 ≤ m) :
    ¬ (2 * (6 * m + 1) + 1).Prime := by
  intro h
  have hdvd : (3 : ℕ) ∣ 2 * (6 * m + 1) + 1 := ⟨4 * m + 1, by ring⟩
  have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h).mp hdvd
  omega

/-- **MINUS-SIDE (proved):** an SG prime `p > 3` must have the form
    `6m − 1`, i.e. `p ≡ 5 (mod 6)`. -/
theorem sophieGermain_minusSide {p : ℕ} (h : IsSophieGermain p) (h3 : 3 < p) :
    p % 6 = 5 := by
  have h2d : ¬ (2 ∣ p) := by
    intro hd
    rcases h.1.eq_one_or_self_of_dvd 2 hd with h' | h' <;> omega
  have h3d : ¬ (3 ∣ p) := by
    intro hd
    rcases h.1.eq_one_or_self_of_dvd 3 hd with h' | h' <;> omega
  have h15 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases h15 with h1 | h5
  · exfalso
    have hdvd : (3 : ℕ) ∣ 2 * p + 1 := ⟨(2 * p + 1) / 3, by omega⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h.2).mp hdvd
    omega
  · exact h5

/-- **CENTER DOUBLING (proved):** on the minus-side the SG map is
    `m → 2m`: `2(6m−1)+1 = 6(2m)−1`. Related to Mersenne chains `4m+1`
    and the pentadic `5m+1`. -/
theorem sg_center_doubling {m : ℕ} (hm : 1 ≤ m) :
    2 * (6 * m - 1) + 1 = 6 * (2 * m) - 1 := by omega

/-- SG-center: `m` such that `6m−1` and `6(2m)−1` are both prime. -/
def IsSGCenter (m : ℕ) : Prop := (6 * m - 1).Prime ∧ (6 * (2 * m) - 1).Prime

/-- **SG-CENTER CRITERION (proved):** `m` is an SG-center ⟺ `6m−1` is an SG prime. -/
theorem isSGCenter_iff {m : ℕ} (hm : 1 ≤ m) :
    IsSGCenter m ↔ IsSophieGermain (6 * m - 1) := by
  unfold IsSGCenter IsSophieGermain
  have h1 : 2 * (6 * m - 1) + 1 = 6 * (2 * m) - 1 := by omega
  rw [h1]

/-- Concrete SG pairs: (5,11), (11,23), (29,59), (89,179). -/
theorem sg_instances :
    IsSophieGermain 5 ∧ IsSophieGermain 11 ∧
      IsSophieGermain 29 ∧ IsSophieGermain 89 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num

/-- **GROWTH (proved):** for `p ≥ 4` the companion `2p+1` is strictly less than `M_p`,
    so the divisor found below is PROPER. -/
theorem two_mul_add_one_lt_mersenne {p : ℕ} (hp : 4 ≤ p) :
    2 * p + 1 < mersenne p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num [mersenne]
  | succ n hn ih => rw [mersenne_succ]; omega

/-- **PEARL (Euler–Lagrange, proved):** if `p ≡ 3 (mod 4)`, `p > 3`
    and `q = 2p+1` is prime, then `q ∣ M_p` and `M_p` is COMPOSITE.

    Route: `q ≡ 7 (mod 8)` ⟹ `2` is a square in `ZMod q` ⟹ by Euler's criterion
    `2^((q−1)/2) = 2^p = 1` in `ZMod q` ⟹ `q ∣ 2^p − 1 = M_p`;
    for `p ≥ 4` we have `q < M_p`, so `M_p` is not prime.
    The case `p = 3` is honestly excluded: `q = 7 = M₃` is itself prime. -/
theorem sophieGermain_divides_mersenne {p : ℕ}
    (hp : p.Prime) (hmod : p % 4 = 3) (hq : (2 * p + 1).Prime) (hgt : 3 < p) :
    (2 * p + 1) ∣ mersenne p ∧ ¬ (mersenne p).Prime := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  -- `p.Prime` — part of the classical formulation (M_p is meaningful for prime p);
  -- for the divisibility conclusion itself it suffices to have p ≡ 3 (mod 4), p > 3 and q prime.
  have _ := hp.two_le
  -- q = 2p+1 ≡ 7 (mod 8), since p ≡ 3 (mod 4)
  have h8 : (2 * p + 1) % 8 = 7 := by omega
  -- so 2 is a quadratic residue mod q
  have hsq : IsSquare (2 : ZMod (2 * p + 1)) :=
    (ZMod.exists_sq_eq_two_iff (by omega : 2 * p + 1 ≠ 2)).mpr (Or.inr h8)
  have h2ne : (2 : ZMod (2 * p + 1)) ≠ 0 := by
    intro h0
    have hcast : ((2 : ℕ) : ZMod (2 * p + 1)) = 0 := by exact_mod_cast h0
    have hdvd2 : (2 * p + 1) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * p + 1)).mp hcast
    have := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  -- Euler's criterion: 2^((q−1)/2) = 1 in ZMod q, and (q−1)/2 = p
  have heuler : (2 : ZMod (2 * p + 1)) ^ ((2 * p + 1) / 2) = 1 :=
    (ZMod.euler_criterion (2 * p + 1) h2ne).mp hsq
  have hdiv2 : (2 * p + 1) / 2 = p := by omega
  rw [hdiv2] at heuler
  -- back to ℕ: 2^p ≡ 1 (mod q)
  have hmodeq : 2 ^ p ≡ 1 [MOD 2 * p + 1] := by
    have hcast : ((2 ^ p : ℕ) : ZMod (2 * p + 1)) = ((1 : ℕ) : ZMod (2 * p + 1)) := by
      push_cast
      exact heuler
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- so q ∣ 2^p − 1 = M_p
  have hdvd : (2 * p + 1) ∣ mersenne p := by
    have h1le : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by norm_num)
    have := (Nat.modEq_iff_dvd' h1le).mp hmodeq.symm
    simpa [mersenne] using this
  -- divisor is proper: 1 < q < M_p for p ≥ 4
  refine ⟨hdvd, fun hMp => ?_⟩
  have hlt := two_mul_add_one_lt_mersenne (by omega : 4 ≤ p)
  rcases hMp.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega

/-- **DEMONSTRATION (proved):** `p = 11 ≡ 3 (mod 4)`, `q = 23` prime,
    and indeed `23 ∣ M₁₁ = 2047 = 23·89` — `M₁₁` is composite. -/
theorem mersenne_composite_examples :
    (2 * 11 + 1) ∣ mersenne 11 ∧ ¬ (mersenne 11).Prime :=
  sophieGermain_divides_mersenne (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Unboundedness of SG primes with `p ≡ 3 (mod 4)` (INPUT hypothesis, open). -/
def SGThreeMod4Unbounded : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 4 = 3 ∧ (2 * p + 1).Prime

/-- **CONDITIONAL INFINITUDE OF COMPOSITE MERSENNES (proved as implication):**
    from SG-unboundedness (class `3 mod 4`) follows the unboundedness of primes
    `p` with composite `M_p`. Unconditionally this conclusion is known in the literature
    by other methods; here only the SG route is honestly recorded. -/
theorem mersenneComposites_unbounded_of_sg (H : SGThreeMod4Unbounded) :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ¬ (mersenne p).Prime := by
  intro N
  obtain ⟨p, h1, h2, h3, h4⟩ := H (max N 3)
  have hN : N ≤ max N 3 := le_max_left N 3
  have h3le : 3 ≤ max N 3 := le_max_right N 3
  exact ⟨p, by omega, h2, (sophieGermain_divides_mersenne h2 h3 h4 (by omega)).2⟩

/-- Sophie Germain conjecture (INPUT-marker, open): there are infinitely many SG primes. -/
def SophieGermainUnbounded : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsSophieGermain p

/-- **HONESTY (scope):** the implication `SG ⟹ twins` is NOT claimed,
    NOT proved and NOT known to mathematics: the SG conjecture and the twin prime conjecture are
    independent open problems (related only in form `p, p+2` vs
    `p, 2p+1`). No open problems are solved here: both
    unboundedness statements above are only INPUT-markers, and the unconditional infinitude
    of COMPOSITE Mersenne numbers (a known theorem in the literature) is obtained only
    CONDITIONALLY from SG-unboundedness. -/
abbrev NoSGToTwinsImplicationClaimed : Prop := True

theorem noSGToTwinsImplicationClaimed : NoSGToTwinsImplicationClaimed := trivial

/-
  ────────────────────────────────────────────────────────────────────
  FULL DICHOTOMY p mod 4: complement of the pearl and the order crypto-lemma
  ────────────────────────────────────────────────────────────────────

  The pearl above covers the class p ≡ 3 (mod 4): the companion q = 2p+1 divides M_p.
  Below is the second half of the classical Euler–Lagrange picture: for
  p ≡ 1 (mod 4) the companion divides NOT M_p but 2^p + 1 = M_p + 2. Together — full
  dichotomy: for every SG pair the companion takes exactly one of the sides
  2^p ∓ 1, and the sides are incompatible (incompatibility proved separately).

  ⚠️ HONESTY: everything below is classical 18th-century mathematics, paid for by Euler's
  criterion and Fermat's little theorem from mathlib; no open problems are solved
  or touched, the SG conjecture remains an INPUT-marker.
-/

/-- **Auxiliary (proved):** for `p ≥ 1` the element 2 is non-zero
    in `ZMod (2p+1)` — otherwise `2p+1 ∣ 2`, which is impossible for `2p+1 ≥ 3`. -/
theorem sg_two_ne_zero_zmod {p : ℕ} (hp1 : 1 ≤ p) :
    (2 : ZMod (2 * p + 1)) ≠ 0 := by
  intro h0
  have hcast : ((2 : ℕ) : ZMod (2 * p + 1)) = 0 := by exact_mod_cast h0
  have hdvd2 : (2 * p + 1) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * p + 1)).mp hcast
  have := Nat.le_of_dvd (by norm_num) hdvd2
  omega

/-- **COMPLEMENT OF THE PEARL (Euler–Lagrange, second half, proved):**
    if `p ≡ 1 (mod 4)`, `p` prime and `q = 2p+1` prime, then `q ∣ 2^p + 1`.

    Route: `q ≡ 3 (mod 8)` ⟹ `2` is a quadratic NON-residue in `ZMod q`
    (`ZMod.exists_sq_eq_two_iff`) ⟹ by Euler's criterion
    `2^p = 2^((q−1)/2) ≠ 1`; Fermat's little theorem gives `(2^p − 1)(2^p + 1) =
    2^(q−1) − 1 = 0` in the field `ZMod q`, so the right factor vanishes:
    `2^p = −1`, i.e. `q ∣ 2^p + 1`. Classical, not a solution to open problems;
    together with `sophieGermain_divides_mersenne` — full dichotomy
    by `p mod 4`. -/
theorem sophieGermain_divides_fermat_side {p : ℕ}
    (hp : p.Prime) (hmod : p % 4 = 1) (hq : (2 * p + 1).Prime) :
    (2 * p + 1) ∣ 2 ^ p + 1 := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  -- `p.Prime` — part of the classical formulation (SG pair); for the
  -- divisibility itself it suffices to have p ≡ 1 (mod 4) and q prime.
  have _ := hp.two_le
  have h2ne : (2 : ZMod (2 * p + 1)) ≠ 0 := sg_two_ne_zero_zmod (by omega)
  -- q = 2p+1 ≡ 3 (mod 8), so 2 is NOT a square mod q
  have hnsq : ¬ IsSquare (2 : ZMod (2 * p + 1)) := by
    intro hsq
    rcases (ZMod.exists_sq_eq_two_iff (by omega : 2 * p + 1 ≠ 2)).mp hsq
      with h | h <;> omega
  -- Euler's criterion: 2^p = 2^((q−1)/2) ≠ 1 in ZMod q
  have hne1 : (2 : ZMod (2 * p + 1)) ^ p ≠ 1 := by
    intro h1
    exact hnsq ((ZMod.euler_criterion (2 * p + 1) h2ne).mpr
      (by rw [show (2 * p + 1) / 2 = p by omega]; exact h1))
  -- Fermat's little theorem: (2^p)² = 2^(q−1) = 1
  have hferm : (2 : ZMod (2 * p + 1)) ^ (2 * p) = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one h2ne
  have hsq2 : ((2 : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm p 2]; exact hferm
  -- factoring in the field: (2^p − 1)(2^p + 1) = 0, left factor excluded
  have hmul : ((2 : ZMod (2 * p + 1)) ^ p - 1) *
      ((2 : ZMod (2 * p + 1)) ^ p + 1) = 0 := by
    linear_combination hsq2
  rcases mul_eq_zero.mp hmul with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne1
  · -- 2^p + 1 = 0 in ZMod q ⟹ q ∣ 2^p + 1 in ℕ
    have hcast : ((2 ^ p + 1 : ℕ) : ZMod (2 * p + 1)) = 0 := by
      push_cast
      exact h1
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- **DEMONSTRATION (proved):** pair (29, 59) from `sg_instances`:
    `29 ≡ 1 (mod 4)`, and indeed `59 ∣ 2²⁹ + 1 = 536870913 = 59·9099507`. -/
theorem fermat_side_example : (2 * 29 + 1) ∣ 2 ^ 29 + 1 :=
  sophieGermain_divides_fermat_side (by norm_num) (by norm_num) (by norm_num)

/-- **FULL DICHOTOMY (proved):** for every SG pair `(p, 2p+1)` the companion
    divides one of the sides: `q ∣ M_p` (realized when `p ≡ 3 (mod 4)`) or
    `q ∣ 2^p + 1 = M_p + 2` (when `p ≡ 1 (mod 4)`).

    Cheap unconditional route, without case analysis: Fermat's little theorem
    (`ZMod.pow_card_sub_one_eq_one`) gives `2^(q−1) = 2^(2p) = 1` in `ZMod q`,
    and the factorization `(2^p − 1)(2^p + 1) = 0` in the field annihilates one of the factors. -/
theorem sophieGermain_dichotomy {p : ℕ} (h : IsSophieGermain p) :
    (2 * p + 1) ∣ mersenne p ∨ (2 * p + 1) ∣ 2 ^ p + 1 := by
  haveI : Fact (2 * p + 1).Prime := ⟨h.2⟩
  have hp2 : 2 ≤ p := h.1.two_le
  have h2ne : (2 : ZMod (2 * p + 1)) ≠ 0 := sg_two_ne_zero_zmod (by omega)
  have hferm : (2 : ZMod (2 * p + 1)) ^ (2 * p) = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one h2ne
  have hsq2 : ((2 : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm p 2]; exact hferm
  have hmul : ((2 : ZMod (2 * p + 1)) ^ p - 1) *
      ((2 : ZMod (2 * p + 1)) ^ p + 1) = 0 := by
    linear_combination hsq2
  rcases mul_eq_zero.mp hmul with h1 | h1
  · -- 2^p = 1 in ZMod q ⟹ q ∣ 2^p − 1 = M_p (as in the pearl)
    left
    have hcast : ((2 ^ p : ℕ) : ZMod (2 * p + 1)) = ((1 : ℕ) : ZMod (2 * p + 1)) := by
      push_cast
      exact sub_eq_zero.mp h1
    have hmodeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have h1le : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by norm_num)
    have hdvd := (Nat.modEq_iff_dvd' h1le).mp hmodeq.symm
    simpa [mersenne] using hdvd
  · right
    have hcast : ((2 ^ p + 1 : ℕ) : ZMod (2 * p + 1)) = 0 := by
      push_cast
      exact h1
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- **INCOMPATIBILITY OF SIDES (proved):** for `p ≥ 1` the companion cannot
    divide both sides simultaneously — otherwise it would divide their difference `2`,
    but `2p+1 ≥ 3`. The dichotomy above is an exact fork, without overlap. -/
theorem sg_dichotomy_exclusive {p : ℕ} (hp1 : 1 ≤ p) :
    ¬ ((2 * p + 1) ∣ mersenne p ∧ (2 * p + 1) ∣ 2 ^ p + 1) := by
  rintro ⟨h1, h2⟩
  have h1le : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by norm_num)
  have hM : mersenne p = 2 ^ p - 1 := rfl
  rw [hM] at h1
  have hdvd : (2 * p + 1) ∣ 2 ^ p + 1 - (2 ^ p - 1) := Nat.dvd_sub h2 h1
  rw [show 2 ^ p + 1 - (2 ^ p - 1) = 2 by omega] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **Auxiliary (proved, pearl step extracted):**
    for `p ≡ 3 (mod 4)` and prime `q = 2p+1`, in `ZMod q` we have
    `2^p = 1`: `q ≡ 7 (mod 8)` ⟹ `2` is a square ⟹ Euler's criterion. -/
theorem sg_two_pow_p_eq_one_zmod {p : ℕ} (hmod : p % 4 = 3)
    (hq : (2 * p + 1).Prime) : (2 : ZMod (2 * p + 1)) ^ p = 1 := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  have h8 : (2 * p + 1) % 8 = 7 := by omega
  have hsq : IsSquare (2 : ZMod (2 * p + 1)) :=
    (ZMod.exists_sq_eq_two_iff (by omega : 2 * p + 1 ≠ 2)).mpr (Or.inr h8)
  have h2ne : (2 : ZMod (2 * p + 1)) ≠ 0 := sg_two_ne_zero_zmod (by omega)
  have heuler := (ZMod.euler_criterion (2 * p + 1) h2ne).mp hsq
  rwa [show (2 * p + 1) / 2 = p by omega] at heuler

/-- **CRYPTO ORDER LEMMA (proved):** for prime `p ≡ 3 (mod 4)` and
    `q = 2p+1`, the order of 2 in `ZMod q` equals exactly `p`.

    From `2^p = 1` the order divides the prime `p`, and `2 ≠ 1` in `ZMod q` (here
    `q ≥ 7`) excludes order 1 — `orderOf_eq_prime` closes the gap. This is
    the machine version of the prose remark about safe primes (Diffie–Hellman): 2
    generates a subgroup of guaranteed large prime order.
    The formal connection is paid for by Euler's criterion (lemma above) and the mathlib lemma
    `orderOf_eq_prime`; cryptographic SECURITY is of course not claimed
    or proved in any way. -/
theorem sg_orderOf_two_eq_p {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3)
    (hq : (2 * p + 1).Prime) : orderOf (2 : ZMod (2 * p + 1)) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2p := sg_two_pow_p_eq_one_zmod hmod hq
  have h2ne1 : (2 : ZMod (2 * p + 1)) ≠ 1 := by
    intro h1
    have hcast : ((2 : ℕ) : ZMod (2 * p + 1)) = ((1 : ℕ) : ZMod (2 * p + 1)) := by
      exact_mod_cast h1
    have hmodeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have hdvd := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmodeq.symm
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact orderOf_eq_prime h2p h2ne1

/-- **DEMONSTRATION (proved):** the order of 2 in `ZMod 23` equals 11 —
    pair (11, 23) from `sg_instances`, `11 ≡ 3 (mod 4)`. -/
theorem sg_orderOf_example : orderOf (2 : ZMod (2 * 11 + 1)) = 11 :=
  sg_orderOf_two_eq_p (by norm_num) (by norm_num) (by norm_num)

#print axioms sophieGermain_divides_mersenne
#print axioms mersenne_composite_examples
#print axioms sophieGermain_minusSide
#print axioms mersenneComposites_unbounded_of_sg
#print axioms sg_two_ne_zero_zmod
#print axioms sophieGermain_divides_fermat_side
#print axioms fermat_side_example
#print axioms sophieGermain_dichotomy
#print axioms sg_dichotomy_exclusive
#print axioms sg_two_pow_p_eq_one_zmod
#print axioms sg_orderOf_two_eq_p
#print axioms sg_orderOf_example

end EuclidsPath.SophieGermainBranch
