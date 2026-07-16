/-
  GeometricTypeIIBrun — THE BONFERRONI BRIDGE into mathlib's dormant Selberg-sieve
  frame: the even-truncated Möbius weights are upper-Möbius
  (`BoundingSieve.IsUpperMoebius`), so mathlib's
  `siftedSum_le_mainSum_errSum_of_upperMoebius` becomes APPLICABLE to the twin
  sieve with finitely many inclusion–exclusion terms — the machine skeleton of
  Brun's method, stage 1.

  ORIGIN.  Idea-generation session (two-axes program, wave 3, formalization-first
  track).  The algebra panel's discovery: the pin contains a complete but DORMANT
  sieve frame (`Mathlib/NumberTheory/SelbergSieve.lean`: `BoundingSieve`,
  `IsUpperMoebius`, `siftedSum ≤ totalMass·mainSum + errSum`) with NO nontrivial
  upper-Möbius weight instantiated anywhere.  The classical minimal instance is
  Bonferroni truncation: `μ⁺(d) = μ(d)·[ω(d) ≤ t]` for EVEN `t`.  This module
  proves it is upper-Möbius — the first usable key to the dormant frame.

  THE COMBINATORIAL CORE.  For `n` with `k ≥ 1` distinct prime factors,
  `Σ_{d ∣ n, ω(d) ≤ t} μ(d) = Σ_{j ≤ t} (−1)^j C(k,j) = (−1)^t C(k−1,t)` —
  the alternating partial binomial sum closes in ONE term of the next diagonal
  (Pascal), and for even `t` it is `C(k−1,t) ≥ 0`.  The divisor sum reduces to
  the binomial sum through the squarefree-divisors ↔ prime-subsets bijection.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `alternating_partial_binomial` — `Σ_{j≤t} (−1)^j C(k,j) = (−1)^t C(k−1,t)`
      for `k ≥ 1`, ALL `t` (beyond `t ≥ k` both sides vanish automatically);
    * `squarefree_prod_of_primes` — a product of distinct primes is squarefree;
    * `moebius_truncated_divisor_sum` — **THE CLOSED FORM**: for `n ≥ 2`,
      `Σ_{d ∣ n, ω(d) ≤ t} μ(d) = (−1)^t C(ω(n)−1, t)` exactly;
    * `bonferroni_isUpperMoebius` — **THE BRIDGE**: for EVEN `t`, the truncated
      weight `d ↦ μ(d)·[ω(d) ≤ t]` satisfies mathlib's `IsUpperMoebius` — the
      dormant `siftedSum_le_mainSum_errSum_of_upperMoebius` is now applicable
      with a weight of FINITE support order (`ω ≤ t`).

  NUMERIC GROUNDING (wave-3 inline pre-pass): the partial binomial identity for
  all `1 ≤ k ≤ 11`, `t ≤ 11`; the upper-Möbius inequality for `t = 0, 2, 4` over
  all `n` built from up to 6 distinct primes, including non-squarefree `n`
  (exact integer arithmetic, zero failures).

  STAGE 2 (NOT in this module — named so it cannot be silently claimed):
    * the twin instantiation of `BoundingSieve` (`ν(d) = 2^ω(d)/d` from the house
      `root_card_crt`, support `= {(6m−1)(6m+1)}`, remainder `|R_d| ≤ 2^ω(d)`);
    * the tail tool `e_j(x) ≤ (Σx)^j / j!` (elementary symmetric domination) for
      the truncated main-term analysis;
    * the qualitative density conclusion via the pin's
      `not_summable_one_div_on_primes` (the pin has NO quantitative Mertens —
      the reachable ceiling is qualitative, disclosed now).

  DISCLOSURES (mandatory reading before quoting):
    * STAGE 1 IS SIEVE INFRASTRUCTURE.  Nothing here bounds any twin quantity yet;
      the module proves a WEIGHT is admissible for a frame, not a theorem about
      twins.  No registered target (CRE, SemiprimeShortRestriction,
      HigherConductorDispersion, LowFreqRootCoherence, OneWingTarget) is touched:
      NOT a §110 event.
    * BRUN'S METHOD CANNOT PROVE TWINS — it is an UPPER-bound method; the
      eventual stage-2 result (twin density zero) is real external mathematics
      made machine-checked, and is STRICTLY WEAKER than anything the wall guards.
      The parity wall is invisible to this track by design; that is exactly why
      it can be completed unconditionally.
    * `ω` is spelled `Nat.primeFactors.card` here (the Finset form matching the
      subsets bijection); the `ArithmeticFunction.cardDistinctFactors` reading is
      the same function (bridge in GeometricTypeIIDilation's genre, not repeated).
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### The combinatorial core -/

/-- **The alternating partial binomial sum**: `Σ_{j≤t} (−1)^j C(k,j) = (−1)^t C(k−1,t)`
    for `k ≥ 1` — Bonferroni's identity; each truncation closes in one term of the
    next Pascal diagonal.  (For `t ≥ k` both sides are `0` automatically.) -/
theorem alternating_partial_binomial {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), ((-1 : ℤ)) ^ j * (k.choose j : ℤ)
      = (-1) ^ t * ((k - 1).choose t : ℤ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ']
      push_cast
      ring

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_of_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact squarefree_one
  | insert p T hpT ih =>
      rw [Finset.prod_insert hpT]
      have hp : p.Prime := hS p (Finset.mem_insert_self p T)
      have hT : ∀ q ∈ T, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (∏ q ∈ T, q) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        exact (Nat.coprime_primes hp (hT q hq)).mpr fun hpq => hpT (hpq ▸ hq)
      exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih hT⟩

/-! ### The divisor sum reduces to the prime-subsets sum -/

/-- For squarefree `d`, `μ(d) = (−1)^{|d.primeFactors|}` (the `ω`-form of the
    Möbius value; local bridge `Ω = ω` on squarefree numbers). -/
private theorem moebius_squarefree_omega {d : ℕ} (hd : Squarefree d) :
    ArithmeticFunction.moebius d = (-1) ^ d.primeFactors.card := by
  have homega : d.primeFactors.card = cardFactors d := by
    have hsq := (cardDistinctFactors_eq_cardFactors_iff_squarefree hd.ne_zero).mpr hd
    rw [← hsq, cardDistinctFactors_apply, ← Nat.toFinset_factors]
    exact List.card_toFinset _
  rw [moebius_apply_of_squarefree hd, homega]

/-- **The truncated Möbius divisor sum, closed form**: for `n ≥ 2` (so `ω(n) ≥ 1`),
    `Σ_{d ∣ n, ω(d) ≤ t} μ(d) = (−1)^t·C(ω(n)−1, t)`.  Route: non-squarefree
    divisors die (`μ = 0`); squarefree divisors biject with subsets of
    `n.primeFactors`; slice the powerset by cardinality; close with the partial
    binomial identity. -/
theorem moebius_truncated_divisor_sum {n : ℕ} (hn : 2 ≤ n) (t : ℕ) :
    ∑ d ∈ n.divisors,
      (if d.primeFactors.card ≤ t then (ArithmeticFunction.moebius d : ℤ) else 0)
      = (-1) ^ t * ((n.primeFactors.card - 1).choose t : ℤ) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hk1 : 1 ≤ n.primeFactors.card := by
    rw [Finset.one_le_card, Nat.nonempty_primeFactors]
    omega
  -- kill non-squarefree divisors
  have hkill : ∑ d ∈ n.divisors,
      (if d.primeFactors.card ≤ t then (ArithmeticFunction.moebius d : ℤ) else 0)
      = ∑ d ∈ n.divisors.filter Squarefree,
        (if d.primeFactors.card ≤ t then (ArithmeticFunction.moebius d : ℤ) else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.divisors Squarefree]
    have hzero : ∑ d ∈ n.divisors.filter (fun d => ¬Squarefree d),
        (if d.primeFactors.card ≤ t then (ArithmeticFunction.moebius d : ℤ) else 0)
        = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      have hnsq : ¬Squarefree d := (Finset.mem_filter.mp hd).2
      rw [moebius_eq_zero_of_not_squarefree hnsq]
      simp
    rw [hzero, add_zero]
  rw [hkill]
  -- biject squarefree divisors with prime subsets
  have hbij : ∑ d ∈ n.divisors.filter Squarefree,
      (if d.primeFactors.card ≤ t then (ArithmeticFunction.moebius d : ℤ) else 0)
      = ∑ S ∈ n.primeFactors.powerset,
        (if S.card ≤ t then ((-1 : ℤ)) ^ S.card else 0) := by
    refine Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p)
      ?_ ?_ ?_ ?_ ?_
    · intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      exact Finset.mem_powerset.mpr (Nat.primeFactors_mono hdvd hn0)
    · intro S hS
      have hsub : S ⊆ n.primeFactors := Finset.mem_powerset.mp hS
      have hprimes : ∀ p ∈ S, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors (hsub hp)
      have hdvd : (∏ p ∈ S, p) ∣ n := by
        refine Finset.prod_primes_dvd n (fun p hp => (hprimes p hp).prime) ?_
        exact fun p hp => Nat.dvd_of_mem_primeFactors (hsub hp)
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hn0⟩,
        squarefree_prod_of_primes hprimes⟩
    · intro d hd
      exact Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd).2
    · intro S hS
      exact Nat.primeFactors_prod fun p hp =>
        Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
    · intro d hd
      have hsq : Squarefree d := (Finset.mem_filter.mp hd).2
      rw [moebius_squarefree_omega hsq]
  rw [hbij]
  -- slice the powerset by cardinality
  rw [Finset.powerset_card_biUnion]
  rw [Finset.sum_biUnion (by
    intro a _ b _ hab
    exact Finset.disjoint_left.mpr fun S hSa hSb => hab (by
      rw [← (Finset.mem_powersetCard.mp hSa).2, ← (Finset.mem_powersetCard.mp hSb).2]))]
  have hslice : ∀ j ∈ Finset.range (n.primeFactors.card + 1),
      ∑ S ∈ Finset.powersetCard j n.primeFactors,
        (if S.card ≤ t then ((-1 : ℤ)) ^ S.card else 0)
      = (if j ≤ t then ((-1 : ℤ)) ^ j * (n.primeFactors.card.choose j : ℤ) else 0) := by
    intro j _
    have hconst : ∀ S ∈ Finset.powersetCard j n.primeFactors,
        (if S.card ≤ t then ((-1 : ℤ)) ^ S.card else 0)
        = (if j ≤ t then ((-1 : ℤ)) ^ j else 0) := by
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
      nsmul_eq_mul]
    by_cases hjt : j ≤ t
    · rw [if_pos hjt, if_pos hjt]
      ring
    · rw [if_neg hjt, if_neg hjt, mul_zero]
  rw [Finset.sum_congr rfl hslice]
  -- close with the partial binomial identity
  set k := n.primeFactors.card with hk
  by_cases htk : t ≤ k
  · have hrange : (Finset.range (k + 1)).filter (fun j => j ≤ t)
        = Finset.range (t + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [Finset.sum_ite, Finset.sum_const, smul_zero, add_zero, hrange]
    exact alternating_partial_binomial hk1 t
  · have hall : ∀ j ∈ Finset.range (k + 1),
        (if j ≤ t then ((-1 : ℤ)) ^ j * (k.choose j : ℤ) else 0)
        = ((-1 : ℤ)) ^ j * (k.choose j : ℤ) := by
      intro j hj
      have hjr : j < k + 1 := Finset.mem_range.mp hj
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hall]
    have hfull := alternating_partial_binomial hk1 k
    have hchoosek : ((k - 1).choose k : ℤ) = 0 := by
      have : (k - 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [this]
      rfl
    have hchooset : ((k - 1).choose t : ℤ) = 0 := by
      have : (k - 1).choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [this]
      rfl
    rw [hchooset, mul_zero, hfull, hchoosek, mul_zero]

/-! ### The bridge into mathlib's dormant sieve frame -/

/-- **THE BONFERRONI BRIDGE**: for EVEN truncation order `t`, the truncated Möbius
    weight `d ↦ μ(d)·[ω(d) ≤ t]` is upper-Möbius in the sense of mathlib's Selberg
    sieve frame — `∀ n, [n = 1] ≤ Σ_{d ∣ n} μ⁺(d)`.  Consequently
    `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius` applies to it: the
    dormant frame is opened with a weight of finite inclusion–exclusion order. -/
theorem bonferroni_isUpperMoebius {t : ℕ} (ht : Even t) :
    BoundingSieve.IsUpperMoebius
      (fun d => if d.primeFactors.card ≤ t
        then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
  intro n
  by_cases hn0 : n = 0
  · subst hn0
    simp
  by_cases hn1 : n = 1
  · subst hn1
    simp
  · rw [if_neg hn1]
    have hn2 : 2 ≤ n := by omega
    have hcast : ∑ d ∈ n.divisors,
        (fun d => if d.primeFactors.card ≤ t
          then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) d
        = ((∑ d ∈ n.divisors,
            (if d.primeFactors.card ≤ t
              then (ArithmeticFunction.moebius d : ℤ) else 0) : ℤ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd : d.primeFactors.card ≤ t <;> simp [hd]
    rw [hcast, moebius_truncated_divisor_sum hn2 t, ht.neg_one_pow]
    have hchoose : (0 : ℤ) ≤ ((n.primeFactors.card - 1).choose t : ℤ) := by
      exact_mod_cast Nat.zero_le _
    have : (0 : ℤ) ≤ 1 * ((n.primeFactors.card - 1).choose t : ℤ) := by linarith
    exact_mod_cast this

/-! ### Axiom audit -/

#print axioms alternating_partial_binomial
#print axioms squarefree_prod_of_primes
#print axioms moebius_truncated_divisor_sum
#print axioms bonferroni_isUpperMoebius

end TypeII
end Geometric
end EuclidsPath
