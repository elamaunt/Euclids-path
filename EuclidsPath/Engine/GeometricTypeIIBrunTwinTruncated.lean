/-
  GeometricTypeIIBrunTwinTruncated — BRUN STAGE 4b: THE TRUNCATED SIEVE.
  The stage-3 evenization ran the sieve at VACUOUS truncation (t ≥ k), paying
  errSum ≤ 3^k = 3^{π(z)} — useless for z beyond ~log N.  This module runs the
  sieve at SMALL t and pays the honest truncation price on the main term:

      twins(N) ≤ N·( 9/log²z + e^{9·loglog z + 18}/2^{t+1} )
                  + (t+1)·(2z)^t + z/6 + 1        (all N, z ≥ 3, even t).

  ORIGIN.  Autonomous continuation (stage 4b, the named remaining step of the
  Brun track).  Design adversarially verified (4b pre-pass); the three moves:
    * MAIN-TERM DEFECT.  mainSum(μ⁺_t) − ∏(1−2/p) = −Σ_{d∣P(z), ω(d)>t} μ(d)ν(d);
      since P(z) is squarefree, its divisors biject with subsets of the sieve
      primes (the stage-1 bijection, reused), so the defect is at most the
      elementary-symmetric tail Σ_{j>t} e_j(2/p).
    * TAIL.  e_j ≤ X^j/j! (the stage-2 dormant tool, now consumed) with
      X = Σ 2/p; then Σ_{j>t} X^j/j! ≤ (X^{t+1}/(t+1)!)·e^X ≤ e^{3X}/2^{t+1}
      — the (t+1)-st term is split off by (t+1)!·(j−t−1)! ∣ j!, and
      X^{t+1}/(t+1)! ≤ e^{2X}/2^{t+1} because (2X)^{t+1}/(t+1)! sits inside
      the exponential series.  Stage 4b-A's Mertens upper bound
      (Σ 2/p ≤ 3·loglog z + 6) makes the tail EXPLICIT: e^{3X} ≤ e^{9·loglog z+18}.
    * ERROR.  errSum(μ⁺_t) ≤ Σ_{j≤t} 2^j·C(k,j) ≤ (t+1)·(2z)^t — polynomial
      in z for fixed t, in place of the stage-3 3^{π(z)}.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `sum_divisors_sieveProd_eq` — the divisors↔subsets transport for ANY
      summand (stage-1 bijection, made reusable);
    * `twin_mainSum_truncated_le` — mainSum(μ⁺_t) ≤ ∏(1−2/p) + e^{3X}/2^{t+1};
    * `twin_errSum_truncated_le` — errSum(μ⁺_t) ≤ (t+1)·(2z)^t;
    * `twin_count_brun_truncated` — **THE TRUNCATED BRUN BOUND** displayed
      above.  PROSE READING (not Lean-stated): choosing t ≈ 11·log₂loglog… i.e.
      2^t ≈ (log z)^{11} makes the bracket O(1/log²z) while (t+1)(2z)^t stays
      z^{O(log log z)}; with z ≈ N^{1/(4t)} this gives the TRUE Brun shape
      twins(N) = O(N·(loglog N)²/log²N) — the constants are NOT optimized and
      that asymptotic reading is NOT claimed as a Lean theorem.

  NUMERIC GROUNDING (4b pre-pass): at z = 10⁴, t = 40: ∏(1−2/p)·log²z = 2.48,
  tail e^{3X}/2^{41} ≈ e^{25.6}/2^{41} ≈ 0.06 — the truncation price is
  subordinate to the main term exactly as designed; errSum (t+1)(2z)^t ≈ 10^{174}
  forces N ≥ 10^{180}-scale before the bound bites (disclosed: the instantiated
  numerical threshold is astronomically large, as for every honest Brun
  constant chain — the VALUE is the machine-checked parametric family).

  DISCLOSURES.
    * Upper bounds only; Brun's method is structurally blind to the parity
      wall — CRE / OneWingTarget / LowFreqRootCoherence /
      SemiprimeShortRestriction / HigherConductorDispersion are UNTOUCHED,
      and this is NOT a §110 event.
    * The constants (9, 3·loglog+6, e^{18}, (2z)^t) are honest but crude;
      optimality is neither claimed nor needed for the shape.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIBrunTwinMertens
import EuclidsPath.Engine.GeometricTypeIIBrunTwinMertensUpper

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open Finset ArithmeticFunction

/-! ### Layer 1: the divisors↔subsets transport (stage-1 bijection, reusable) -/

/-- Every divisor of the squarefree `P(z)` is `∏ S` for exactly one subset `S`
of the sieve primes — so ANY sum over divisors transports to the powerset. -/
private theorem sum_divisors_sieveProd_eq (z : ℕ) (F : ℕ → ℝ) :
    ∑ d ∈ (sieveProd z).divisors, F d
      = ∑ S ∈ (sievePrimes z).powerset, F (∏ p ∈ S, p) := by
  classical
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    have hdvd : d ∣ sieveProd z := (Nat.mem_divisors.mp hd).1
    refine Finset.mem_powerset.mpr ?_
    have := Nat.primeFactors_mono hdvd (sieveProd_pos z).ne'
    rwa [primeFactors_sieveProd] at this
  · intro S hS
    have hsub : S ⊆ sievePrimes z := Finset.mem_powerset.mp hS
    have hprimes : ∀ p ∈ S, p.Prime := fun p hp => sievePrimes_prime (hsub hp)
    have hdvd : (∏ p ∈ S, p) ∣ sieveProd z := by
      refine Finset.prod_primes_dvd _ (fun p hp => (hprimes p hp).prime) ?_
      intro p hp
      rw [← primeFactors_sieveProd z] at hsub
      exact Nat.dvd_of_mem_primeFactors (hsub hp)
    exact Nat.mem_divisors.mpr ⟨hdvd, (sieveProd_pos z).ne'⟩
  · intro d hd
    have hsq : Squarefree d :=
      (sieveProd_squarefree z).squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    exact Nat.prod_primeFactors_of_squarefree hsq
  · intro S hS
    exact Nat.primeFactors_prod fun p hp =>
      sievePrimes_prime (Finset.mem_powerset.mp hS hp)
  · intro d hd
    have hsq : Squarefree d :=
      (sieveProd_squarefree z).squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    rw [Nat.prod_primeFactors_of_squarefree hsq]

/-- `ν(∏ S) = ∏_{p∈S} 2/p` for subsets of the sieve primes. -/
private theorem twinNu_prod_subset {z : ℕ} {S : Finset ℕ}
    (hS : S ⊆ sievePrimes z) :
    twinNu (∏ p ∈ S, p) = ∏ p ∈ S, (2 / (p : ℝ)) := by
  have hprimes : ∀ p ∈ S, p.Prime := fun p hp => sievePrimes_prime (hS hp)
  rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime twinNu_mult S hprimes]
  exact Finset.prod_congr rfl fun p hp => twinNu_prime (hprimes p hp)

/-! ### Layer 2: the main-term truncation defect -/

/-- The defect sum transports to the elementary-symmetric tail:
`Σ_{d∣P(z), ω(d)>t} ν(d) = Σ_{j∈(t,k]} e_j(2/p)`. -/
private theorem nu_tail_eq_esymm (z t : ℕ) :
    ∑ d ∈ (sieveProd z).divisors,
        (if t < d.primeFactors.card then twinNu d else 0)
      = ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
          esymmOn (sievePrimes z) (fun p => 2 / (p : ℝ)) j := by
  classical
  rw [sum_divisors_sieveProd_eq]
  have hpt : ∀ S ∈ (sievePrimes z).powerset,
      (if t < (∏ p ∈ S, p).primeFactors.card then twinNu (∏ p ∈ S, p) else 0)
      = (if t < S.card then ∏ p ∈ S, (2 / (p : ℝ)) else 0) := by
    intro S hS
    have hsub : S ⊆ sievePrimes z := Finset.mem_powerset.mp hS
    have hPF : (∏ p ∈ S, p).primeFactors = S :=
      Nat.primeFactors_prod fun p hp => sievePrimes_prime (hsub hp)
    rw [hPF]
    by_cases hcase : t < S.card
    · rw [if_pos hcase, if_pos hcase, twinNu_prod_subset hsub]
    · rw [if_neg hcase, if_neg hcase]
  rw [Finset.sum_congr rfl hpt, Finset.powerset_card_biUnion,
    Finset.sum_biUnion (by
      intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun S hSa hSb => hab (by
        rw [← (Finset.mem_powersetCard.mp hSa).2,
          ← (Finset.mem_powersetCard.mp hSb).2]))]
  have hslice : ∀ j ∈ Finset.range ((sievePrimes z).card + 1),
      ∑ S ∈ Finset.powersetCard j (sievePrimes z),
        (if t < S.card then ∏ p ∈ S, (2 / (p : ℝ)) else 0)
      = (if t < j then esymmOn (sievePrimes z) (fun p => 2 / (p : ℝ)) j
          else 0) := by
    intro j _
    have hcongr : ∀ S ∈ Finset.powersetCard j (sievePrimes z),
        (if t < S.card then ∏ p ∈ S, (2 / (p : ℝ)) else 0)
        = (if t < j then ∏ p ∈ S, (2 / (p : ℝ)) else 0) := by
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hcongr]
    by_cases hcase : t < j
    · rw [if_pos hcase]
      simp only [if_pos hcase]
      rfl
    · rw [if_neg hcase]
      simp only [if_neg hcase, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hslice, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  omega

/-- **The truncated main sum is at most the full product plus the tail**:
`mainSum(μ⁺_t) ≤ ∏(1−2/p) + Σ_{j∈(t,k]} e_j(2/p)`. -/
theorem twin_mainSum_sub_prod_le (N z t : ℕ) :
    (twinSieve N z).mainSum (bonferroniWeight t)
      ≤ (∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)))
        + ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
            esymmOn (sievePrimes z) (fun p => 2 / (p : ℝ)) j := by
  classical
  show ∑ d ∈ (sieveProd z).divisors, bonferroniWeight t d * twinNu d ≤ _
  have hfull : ∑ d ∈ (sieveProd z).divisors,
      bonferroniWeight ((sievePrimes z).card) d * twinNu d
      = ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)) :=
    twin_mainSum_eq N z _ le_rfl
  -- the pointwise split: w_t·ν = w_k·ν − (defect term)
  have hsplit : ∀ d ∈ (sieveProd z).divisors,
      bonferroniWeight t d * twinNu d
      = bonferroniWeight ((sievePrimes z).card) d * twinNu d
        - (if t < d.primeFactors.card
            then ((ArithmeticFunction.moebius d : ℤ) : ℝ) * twinNu d else 0) := by
    intro d hd
    have hω := omega_le_card_of_mem_divisors hd
    unfold bonferroniWeight
    rw [if_pos hω]
    by_cases hcase : d.primeFactors.card ≤ t
    · rw [if_pos hcase, if_neg (by omega)]
      ring
    · rw [if_neg hcase, if_pos (by omega)]
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hfull]
  -- the defect is bounded by the unsigned tail
  have habs : |∑ d ∈ (sieveProd z).divisors,
      (if t < d.primeFactors.card
        then ((ArithmeticFunction.moebius d : ℤ) : ℝ) * twinNu d else 0)|
      ≤ ∑ d ∈ (sieveProd z).divisors,
          (if t < d.primeFactors.card then twinNu d else 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
    by_cases hcase : t < d.primeFactors.card
    · rw [if_pos hcase, if_pos hcase, abs_mul]
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hν : 0 ≤ twinNu d := by
        rw [twinNu_apply hd0.ne']
        positivity
      have hsq : Squarefree d :=
        (sieveProd_squarefree z).squarefree_of_dvd (Nat.mem_divisors.mp hd).1
      have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
        push_cast
        rw [abs_pow, abs_neg, abs_one, one_pow]
      rw [hμ, one_mul, abs_of_nonneg hν]
    · rw [if_neg hcase, if_neg hcase, abs_zero]
  have hbridge := nu_tail_eq_esymm z t
  linarith [neg_abs_le (∑ d ∈ (sieveProd z).divisors,
    (if t < d.primeFactors.card
      then ((ArithmeticFunction.moebius d : ℤ) : ℝ) * twinNu d else 0))]

/-! ### Layer 3: the exponential tail -/

/-- **The elementary-symmetric tail is exponentially small in `t`**:
`Σ_{j∈(t,k]} e_j(2/p) ≤ e^{3X}/2^{t+1}` with `X = Σ 2/p`. -/
theorem esymm_tail_le (z t : ℕ) :
    ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
        esymmOn (sievePrimes z) (fun p => 2 / (p : ℝ)) j
      ≤ Real.exp (3 * ∑ p ∈ sievePrimes z, 2 / (p : ℝ)) / 2 ^ (t + 1) := by
  classical
  have hx : ∀ p ∈ sievePrimes z, 0 ≤ 2 / ((p : ℝ)) := fun p _ => by positivity
  have hX0 : 0 ≤ ∑ p ∈ sievePrimes z, 2 / ((p : ℝ)) := Finset.sum_nonneg hx
  set X := ∑ p ∈ sievePrimes z, 2 / ((p : ℝ)) with hXdef
  -- the split-off single term: X^{t+1}/(t+1)! ≤ e^{2X}/2^{t+1}
  have hsingle : X ^ (t + 1) / ((t + 1).factorial : ℝ)
      ≤ Real.exp (2 * X) / 2 ^ (t + 1) := by
    have h1 : (2 * X) ^ (t + 1) / (((t + 1).factorial : ℕ) : ℝ)
        ≤ Real.exp (2 * X) := by
      have hmem : t + 1 ∈ Finset.range (t + 2) := by
        simp
      have hle := Finset.single_le_sum
        (f := fun i => (2 * X) ^ i / ((i.factorial : ℕ) : ℝ))
        (fun i _ => by positivity) hmem
      exact hle.trans (Real.sum_le_exp_of_nonneg (by linarith) _)
    have h2 : X ^ (t + 1) / (((t + 1).factorial : ℕ) : ℝ)
        = ((2 * X) ^ (t + 1) / (((t + 1).factorial : ℕ) : ℝ)) / 2 ^ (t + 1) := by
      rw [mul_pow]
      field_simp
    rw [h2]
    gcongr
  calc ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
        esymmOn (sievePrimes z) (fun p => 2 / (p : ℝ)) j
      ≤ ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
          X ^ j / ((j.factorial : ℕ) : ℝ) :=
        Finset.sum_le_sum fun j _ => esymmOn_le_pow_div_factorial hx j
    _ ≤ ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
          (X ^ (t + 1) / (((t + 1).factorial : ℕ) : ℝ))
            * (X ^ (j - (t + 1)) / (((j - (t + 1)).factorial : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : t + 1 ≤ j := (Finset.mem_Ioc.mp hj).1
        have hfac : (((t + 1).factorial * (j - (t + 1)).factorial : ℕ) : ℝ)
            ≤ ((j.factorial : ℕ) : ℝ) := by
          have hdvd := Nat.factorial_mul_factorial_dvd_factorial_add
            (t + 1) (j - (t + 1))
          rw [show (t + 1) + (j - (t + 1)) = j by omega] at hdvd
          exact_mod_cast Nat.le_of_dvd j.factorial_pos hdvd
        have hXj : X ^ j = X ^ (t + 1) * X ^ (j - (t + 1)) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hXj, div_mul_div_comm, ← Nat.cast_mul]
        gcongr
    _ = (X ^ (t + 1) / (((t + 1).factorial : ℕ) : ℝ))
          * ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
              X ^ (j - (t + 1)) / (((j - (t + 1)).factorial : ℕ) : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (X ^ (t + 1) / (((t + 1).factorial : ℕ) : ℝ)) * Real.exp X := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hre : ∑ j ∈ Finset.Ioc t (sievePrimes z).card,
            X ^ (j - (t + 1)) / (((j - (t + 1)).factorial : ℕ) : ℝ)
            = ∑ i ∈ Finset.range ((sievePrimes z).card - t),
                X ^ i / ((i.factorial : ℕ) : ℝ) := by
          refine Finset.sum_nbij' (fun j => j - (t + 1)) (fun i => i + (t + 1))
            ?_ ?_ ?_ ?_ ?_
          · intro j hj
            have := Finset.mem_Ioc.mp hj
            rw [Finset.mem_range]
            omega
          · intro i hi
            have := Finset.mem_range.mp hi
            rw [Finset.mem_Ioc]
            omega
          · intro j hj
            have := Finset.mem_Ioc.mp hj
            omega
          · intro i _
            omega
          · intro j _
            rfl
        rw [hre]
        exact Real.sum_le_exp_of_nonneg hX0 _
    _ ≤ (Real.exp (2 * X) / 2 ^ (t + 1)) * Real.exp X :=
        mul_le_mul_of_nonneg_right hsingle (Real.exp_nonneg _)
    _ = Real.exp (3 * X) / 2 ^ (t + 1) := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        ring_nf

/-- **The truncated main sum, explicit form**:
`mainSum(μ⁺_t) ≤ ∏(1−2/p) + e^{3X}/2^{t+1}`. -/
theorem twin_mainSum_truncated_le (N z t : ℕ) :
    (twinSieve N z).mainSum (bonferroniWeight t)
      ≤ (∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)))
        + Real.exp (3 * ∑ p ∈ sievePrimes z, 2 / (p : ℝ)) / 2 ^ (t + 1) := by
  have h1 := twin_mainSum_sub_prod_le N z t
  have h2 := esymm_tail_le z t
  linarith

/-! ### Layer 4: the truncated error budget -/

/-- **The truncated error budget is polynomial in `z`**:
`errSum(μ⁺_t) ≤ (t+1)·(2z)^t`. -/
theorem twin_errSum_truncated_le (N z t : ℕ) (hz : 1 ≤ z) :
    (twinSieve N z).errSum (bonferroniWeight t)
      ≤ ((t : ℝ) + 1) * (2 * (z : ℝ)) ^ t := by
  classical
  refine (twin_errSum_le N z t).trans ?_
  rw [sum_divisors_sieveProd_eq]
  have hpt : ∀ S ∈ (sievePrimes z).powerset,
      (if (∏ p ∈ S, p).primeFactors.card ≤ t
        then (2 : ℝ) ^ (∏ p ∈ S, p).primeFactors.card else 0)
      = (if S.card ≤ t then (2 : ℝ) ^ S.card else 0) := by
    intro S hS
    have hPF : (∏ p ∈ S, p).primeFactors = S :=
      Nat.primeFactors_prod fun p hp =>
        sievePrimes_prime (Finset.mem_powerset.mp hS hp)
    rw [hPF]
  rw [Finset.sum_congr rfl hpt, Finset.powerset_card_biUnion,
    Finset.sum_biUnion (by
      intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun S hSa hSb => hab (by
        rw [← (Finset.mem_powersetCard.mp hSa).2,
          ← (Finset.mem_powersetCard.mp hSb).2]))]
  have hslice : ∀ j ∈ Finset.range ((sievePrimes z).card + 1),
      ∑ S ∈ Finset.powersetCard j (sievePrimes z),
        (if S.card ≤ t then (2 : ℝ) ^ S.card else 0)
      = (if j ≤ t
          then (((sievePrimes z).card.choose j : ℕ) : ℝ) * 2 ^ j else 0) := by
    intro j _
    have hcongr : ∀ S ∈ Finset.powersetCard j (sievePrimes z),
        (if S.card ≤ t then (2 : ℝ) ^ S.card else 0)
        = (if j ≤ t then (2 : ℝ) ^ j else 0) := by
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const,
      Finset.card_powersetCard, nsmul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_congr rfl hslice, ← Finset.sum_filter]
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := Nat.one_le_cast.mpr hz
  -- pointwise: C(k,j)·2^j ≤ (2z)^j, then push into range (t+1)
  have hstep1 : ∑ j ∈ (Finset.range ((sievePrimes z).card + 1)).filter
        (fun j => j ≤ t),
        (((sievePrimes z).card.choose j : ℕ) : ℝ) * 2 ^ j
      ≤ ∑ j ∈ (Finset.range ((sievePrimes z).card + 1)).filter
        (fun j => j ≤ t), (2 * (z : ℝ)) ^ j := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hC : (((sievePrimes z).card.choose j : ℕ) : ℝ) ≤ (z : ℝ) ^ j := by
      calc (((sievePrimes z).card.choose j : ℕ) : ℝ)
          ≤ ((sievePrimes z).card : ℝ) ^ j / ((j.factorial : ℕ) : ℝ) :=
            Nat.choose_le_pow_div j _
        _ ≤ ((sievePrimes z).card : ℝ) ^ j :=
            div_le_self (by positivity) (Nat.one_le_cast.mpr j.factorial_pos)
        _ ≤ (z : ℝ) ^ j := by
            gcongr
            exact_mod_cast sievePrimes_card_le z
    calc (((sievePrimes z).card.choose j : ℕ) : ℝ) * 2 ^ j
        ≤ (z : ℝ) ^ j * 2 ^ j :=
          mul_le_mul_of_nonneg_right hC (by positivity)
      _ = (2 * (z : ℝ)) ^ j := by
          rw [mul_pow]
          ring
  have hstep2 : ∑ j ∈ (Finset.range ((sievePrimes z).card + 1)).filter
        (fun j => j ≤ t), (2 * (z : ℝ)) ^ j
      ≤ ∑ j ∈ Finset.range (t + 1), (2 * (z : ℝ)) ^ j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      have := Finset.mem_filter.mp hj
      rw [Finset.mem_range]
      omega
    · intro j _ _
      positivity
  have hstep3 : ∑ j ∈ Finset.range (t + 1), (2 * (z : ℝ)) ^ j
      ≤ ((t : ℝ) + 1) * (2 * (z : ℝ)) ^ t := by
    have hb : (1 : ℝ) ≤ 2 * (z : ℝ) := by linarith
    have hcard := Finset.sum_le_card_nsmul (Finset.range (t + 1))
      (fun j => (2 * (z : ℝ)) ^ j) ((2 * (z : ℝ)) ^ t)
      (fun j hj => pow_le_pow_right₀ hb (by
        have := Finset.mem_range.mp hj
        omega))
    rw [Finset.card_range, nsmul_eq_mul] at hcard
    calc ∑ j ∈ Finset.range (t + 1), (2 * (z : ℝ)) ^ j
        ≤ ((t + 1 : ℕ) : ℝ) * (2 * (z : ℝ)) ^ t := hcard
      _ = ((t : ℝ) + 1) * (2 * (z : ℝ)) ^ t := by
          push_cast
          ring
  linarith

/-! ### Layer 5: THE TRUNCATED BRUN BOUND (stage 4b assembled) -/

/-- **BRUN STAGE 4b — THE TRUNCATED RATE** (all constants explicit, no
hypotheses beyond `z ≥ 3` and even `t`):

`twins(N) ≤ N·(9/log²z + e^{9·loglog z + 18}/2^{t+1}) + (t+1)·(2z)^t + z/6 + 1`.

Prose reading (NOT Lean-stated): `2^t ≈ (log z)^{11}`, `z ≈ N^{1/(4t)}` give
the true Brun shape `O(N·(loglog N)²/log²N)`. -/
theorem twin_count_brun_truncated (N z t : ℕ) (ht : Even t) (hz : 3 ≤ z) :
    (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      ≤ (N : ℝ) * (9 / Real.log z ^ 2
            + Real.exp (9 * Real.log (Real.log z) + 18) / 2 ^ (t + 1))
        + ((t : ℝ) + 1) * (2 * (z : ℝ)) ^ t + ((z : ℝ) / 6 + 1) := by
  have hupper := brun_twin_upper N z t ht
  have hmain := twin_mainSum_truncated_le N z t
  have hprod := sievePrimes_prod_le_nine_div_log_sq z (by omega)
  have hX := sievePrimes_sum_two_div_le (z := z) hz
  have herr := twin_errSum_truncated_le N z t (by omega)
  -- the tail exponent is monotone in X
  have hexp : Real.exp (3 * ∑ p ∈ sievePrimes z, 2 / (p : ℝ))
      ≤ Real.exp (9 * Real.log (Real.log z) + 18) := by
    rw [Real.exp_le_exp]
    linarith
  have htail : Real.exp (3 * ∑ p ∈ sievePrimes z, 2 / (p : ℝ)) / 2 ^ (t + 1)
      ≤ Real.exp (9 * Real.log (Real.log z) + 18) / 2 ^ (t + 1) := by
    gcongr
  have hmain2 : (twinSieve N z).mainSum (bonferroniWeight t)
      ≤ 9 / Real.log z ^ 2
        + Real.exp (9 * Real.log (Real.log z) + 18) / 2 ^ (t + 1) := by
    linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmulN : (N : ℝ) * (twinSieve N z).mainSum (bonferroniWeight t)
      ≤ (N : ℝ) * (9 / Real.log z ^ 2
          + Real.exp (9 * Real.log (Real.log z) + 18) / 2 ^ (t + 1)) :=
    mul_le_mul_of_nonneg_left hmain2 hN0
  linarith

end TypeII
end Geometric
end EuclidsPath
