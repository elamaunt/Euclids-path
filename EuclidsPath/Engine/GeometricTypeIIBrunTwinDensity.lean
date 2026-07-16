/-
  GeometricTypeIIBrunTwinDensity — BRUN STAGE 3: **TWIN PRIMES HAVE DENSITY
  ZERO**, machine-checked.  The stage-2 sieve bound closes into the qualitative
  limit theorem: `#{m ≤ N : both 6m±1 prime} / N → 0`.

  ORIGIN.  Idea-generation session (two-axes program, wave 3, formalization-first
  track, final stage).  Design adversarially verified (stage-3 pre-pass) with
  FOUR corrections adopted:
    * THE EVENIZATION TRICK: with `t := 2·k` (`k = #sievePrimes z`) the Bonferroni
      truncation is VACUOUS — every divisor of `P(z)` has `ω(d) ≤ k ≤ t` — so the
      Brun weight degenerates to exact Legendre inclusion–exclusion and
      `mainSum = ∏_{5≤p≤z}(1 − 2/p)` EXACTLY.  No tail estimate is needed for a
      qualitative result; the stage-2 tail tool (`esymmOn…`) stays DORMANT here
      (it is the stage-4 quantitative instrument, disclosed);
    * the main-sum evaluation uses the pin's ready-made
      `IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree` — no hand-rolled
      powerset bijection;
    * the naive squeeze route to the `Tendsto` form FAILS structurally (the
      dominating bound depends on `z(ε)`) — the assembly is the ε-form workhorse
      plus the metric characterization;
    * the `range`-vs-`Icc` prime-sum bookkeeping only needs ONE direction, with
      the constant `5/6 = 1/2 + 1/3` (the dropped primes 2, 3).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twin_mainSum_eq` — for `t ≥ k`: `mainSum(μ⁺_t) = ∏_{p∈sievePrimes z}(1 − 2/p)`;
    * `twin_errSum_le_const` — `errSum(μ⁺_t) ≤ 3^k` (N-FREE — the whole point);
    * `exists_sievePrimes_sum_ge` — `Σ_{5≤p≤z} 1/p` is unbounded in `z` (the
      pin's prime-reciprocal divergence, bridged through the indicator);
    * `exists_sievePrimes_prod_lt` — `∀ε>0 ∃z, ∏(1 − 2/p) < ε`
      (`1 − x ≤ e^{−x}`, so the product dies under the divergent sum);
    * `twin_count_le_eps` — **THE WORKHORSE**: `∀ε>0 ∃N₀ ∀N≥N₀, twins(N) ≤ ε·N`;
    * `twin_density_zero` — **THE HEADLINE**: `twins(N)/N → 0` (`Tendsto`, `atTop`,
      `nhds 0`).

  NUMERIC GROUNDING (stage-3 pre-pass, exact rationals): mainSum = product
  exactly at `z = 4, 10, 20, 31` (including degenerate `k = 0`); `Σ 2^ω = 3^k`
  exactly; product decay `∏·log²z → ≈2.5` at `z = 10²…10⁵` (the `C/log²z` law);
  the end-to-end chain checked at `(z,N) ∈ {20,50}×{10³,10⁴}`.

  DISCLOSURES (mandatory reading before quoting):
    * QUALITATIVE ONLY — the ceiling disclosed since stage 1: the pin has no
      quantitative Mertens, so no rate (the true rate is `C·N/log²N`; here only
      `o(N)`).  The quantitative stage would wake the dormant `esymmOn` tool and
      needs a Mertens import — named, not claimed.
    * STILL NOT THE TWIN CONJECTURE — an upper bound on the twin count says
      nothing about infinitude; Brun's method is structurally blind to the
      parity wall (upper-bound method), which is exactly why this track closes
      unconditionally.  No registered target (CRE, SemiprimeShortRestriction,
      HigherConductorDispersion, LowFreqRootCoherence, OneWingTarget) is
      touched: NOT a §110 event.
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIBrunTwin

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### The evenized sieve terms -/

/-- Divisors of `P(z)` have at most `k = #sievePrimes z` prime factors. -/
theorem omega_le_card_of_mem_divisors {z d : ℕ}
    (hd : d ∈ (sieveProd z).divisors) :
    d.primeFactors.card ≤ (sievePrimes z).card := by
  have hdvd : d ∣ sieveProd z := (Nat.mem_divisors.mp hd).1
  have hsub : d.primeFactors ⊆ (sieveProd z).primeFactors :=
    Nat.primeFactors_mono hdvd (sieveProd_pos z).ne'
  rw [primeFactors_sieveProd] at hsub
  exact Finset.card_le_card hsub

/-- **The evenized main sum is the exact Legendre product**: for `t ≥ k` the
    truncation is vacuous and `mainSum(μ⁺_t) = ∏_{p∈sievePrimes z}(1 − 2/p)`. -/
theorem twin_mainSum_eq (N z t : ℕ) (hkt : (sievePrimes z).card ≤ t) :
    (twinSieve N z).mainSum (bonferroniWeight t)
      = ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)) := by
  show ∑ d ∈ (sieveProd z).divisors, bonferroniWeight t d * twinNu d = _
  have hcongr : ∀ d ∈ (sieveProd z).divisors,
      bonferroniWeight t d * twinNu d
        = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * twinNu d := by
    intro d hd
    unfold bonferroniWeight
    rw [if_pos ((omega_le_card_of_mem_divisors hd).trans hkt)]
  rw [Finset.sum_congr rfl hcongr,
    ← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      twinNu twinNu_mult (sieveProd_squarefree z),
    primeFactors_sieveProd]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [twinNu_prime (sievePrimes_prime hp)]

/-- **The error budget is `N`-free**: `errSum(μ⁺_t) ≤ 3^k`. -/
theorem twin_errSum_le_const (N z t : ℕ) :
    (twinSieve N z).errSum (bonferroniWeight t)
      ≤ (3 : ℝ) ^ (sievePrimes z).card := by
  refine (twin_errSum_le N z t).trans ?_
  have hstep : ∑ d ∈ (sieveProd z).divisors,
      (if d.primeFactors.card ≤ t then (2 : ℝ) ^ d.primeFactors.card else 0)
      ≤ ∑ d ∈ (sieveProd z).divisors,
          (ArithmeticFunction.prodPrimeFactors fun _ => (2 : ℝ)) d := by
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [ArithmeticFunction.prodPrimeFactors_apply hd0, Finset.prod_const]
    split_ifs
    · exact le_refl _
    · positivity
  refine hstep.trans ?_
  rw [← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)
    (sieveProd_squarefree z), primeFactors_sieveProd]
  have hprod : ∀ p ∈ sievePrimes z,
      (1 : ℝ) + (ArithmeticFunction.prodPrimeFactors fun _ => (2 : ℝ)) p
        = 3 := by
    intro p hp
    have hpp := sievePrimes_prime hp
    rw [ArithmeticFunction.prodPrimeFactors_apply hpp.pos.ne',
      Nat.Prime.primeFactors hpp, Finset.prod_singleton]
    norm_num
  rw [Finset.prod_congr rfl hprod, Finset.prod_const]

/-! ### The divergence input and the dying product -/

/-- The indicator partial sum is the filtered prime sum. -/
private theorem sum_range_indicator_primes (n : ℕ) :
    ∑ i ∈ Finset.range n,
      Set.indicator {p | Nat.Prime p} (fun m : ℕ => (1 : ℝ) / m) i
      = ∑ p ∈ (Finset.range n).filter Nat.Prime, 1 / (p : ℝ) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : Nat.Prime i
  · rw [if_pos hi]
    exact Set.indicator_of_mem hi _
  · rw [if_neg hi]
    exact Set.indicator_of_notMem hi _

/-- Dropping `p = 2, 3` costs at most `5/6`. -/
private theorem sum_sievePrimes_one_div_ge (n : ℕ) :
    (∑ p ∈ (Finset.range n).filter Nat.Prime, 1 / (p : ℝ)) - 5 / 6
      ≤ ∑ p ∈ sievePrimes n, 1 / (p : ℝ) := by
  classical
  set A := (Finset.range n).filter Nat.Prime with hA
  have hsub : A \ ({2, 3} : Finset ℕ) ⊆ sievePrimes n := by
    intro p hp
    obtain ⟨hpA, hp23⟩ := Finset.mem_sdiff.mp hp
    have hpp : p.Prime := (Finset.mem_filter.mp hpA).2
    have hpn : p < n := Finset.mem_range.mp (Finset.mem_filter.mp hpA).1
    have h2 : p ≠ 2 := fun h => hp23 (by simp [h])
    have h3 : p ≠ 3 := fun h => hp23 (by simp [h])
    have h4 : p ≠ 4 := fun h => absurd (h ▸ hpp) (by norm_num)
    have h5 : 5 ≤ p := by
      have := hpp.two_le
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h5, by omega⟩, hpp⟩
  have hle : ∑ p ∈ A \ ({2, 3} : Finset ℕ), 1 / (p : ℝ)
      ≤ ∑ p ∈ sievePrimes n, 1 / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  have hsdiff : ∑ p ∈ A \ ({2, 3} : Finset ℕ), 1 / (p : ℝ)
      = (∑ p ∈ A, 1 / (p : ℝ)) - ∑ p ∈ A ∩ ({2, 3} : Finset ℕ), 1 / (p : ℝ) := by
    rw [← Finset.sdiff_inter_self_left A ({2, 3} : Finset ℕ)]
    exact Finset.sum_sdiff_eq_sub Finset.inter_subset_left
  have hsmall : ∑ p ∈ A ∩ ({2, 3} : Finset ℕ), 1 / (p : ℝ) ≤ 5 / 6 := by
    have hs : ∑ p ∈ A ∩ ({2, 3} : Finset ℕ), 1 / (p : ℝ)
        ≤ ∑ p ∈ ({2, 3} : Finset ℕ), 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        fun p _ _ => by positivity
    refine hs.trans ?_
    rw [Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
    norm_num
  linarith

/-- **The sieve prime-reciprocal sum is unbounded** — the pin's divergence
    bridged through the indicator partial sums. -/
theorem exists_sievePrimes_sum_ge (C : ℝ) :
    ∃ z : ℕ, C ≤ ∑ p ∈ sievePrimes z, 1 / (p : ℝ) := by
  have hnn : ∀ i : ℕ,
      0 ≤ Set.indicator {p | Nat.Prime p} (fun m : ℕ => (1 : ℝ) / m) i :=
    fun i => Set.indicator_nonneg (fun a _ => by positivity) i
  have htends := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp
    not_summable_one_div_on_primes
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp htends (C + 5 / 6)).exists
  refine ⟨n, ?_⟩
  rw [sum_range_indicator_primes] at hn
  have := sum_sievePrimes_one_div_ge n
  linarith

/-- **The Legendre product dies**: `∀ε>0 ∃z, ∏_{p∈sievePrimes z}(1 − 2/p) < ε`. -/
theorem exists_sievePrimes_prod_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)) < ε := by
  obtain ⟨z, hz⟩ := exists_sievePrimes_sum_ge ((-Real.log ε) / 2 + 1)
  refine ⟨z, ?_⟩
  have h0 : ∀ p ∈ sievePrimes z, (0 : ℝ) ≤ 1 - 2 / (p : ℝ) := by
    intro p hp
    have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast sievePrimes_five_le hp
    have hdiv : 2 / (p : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have h1 : ∀ p ∈ sievePrimes z,
      (1 : ℝ) - 2 / (p : ℝ) ≤ Real.exp (-(2 / (p : ℝ))) := by
    intro p _
    have := Real.add_one_le_exp (-(2 / (p : ℝ)))
    linarith
  have hprod : ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ sievePrimes z, Real.exp (-(2 / (p : ℝ))) :=
    Finset.prod_le_prod h0 h1
  have hexp : ∏ p ∈ sievePrimes z, Real.exp (-(2 / (p : ℝ)))
      = Real.exp (∑ p ∈ sievePrimes z, -(2 / (p : ℝ))) :=
    (Real.exp_sum _ _).symm
  have hsum : ∑ p ∈ sievePrimes z, -(2 / (p : ℝ))
      = -2 * ∑ p ∈ sievePrimes z, 1 / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hlt : Real.exp (-2 * ∑ p ∈ sievePrimes z, 1 / (p : ℝ)) < ε := by
    have harg : -2 * ∑ p ∈ sievePrimes z, 1 / (p : ℝ) < Real.log ε := by
      nlinarith [hz]
    calc Real.exp (-2 * ∑ p ∈ sievePrimes z, 1 / (p : ℝ))
        < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr harg
      _ = ε := Real.exp_log hε
  calc ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ sievePrimes z, -(2 / (p : ℝ))) := hprod.trans hexp.le
    _ = Real.exp (-2 * ∑ p ∈ sievePrimes z, 1 / (p : ℝ)) := by rw [hsum]
    _ < ε := hlt

/-! ### The density theorem -/

/-- **THE WORKHORSE (ε-form)**: for every `ε > 0` there is `N₀` beyond which
    the twin count is at most `ε·N`. -/
theorem twin_count_le_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ) ≤ ε * N := by
  obtain ⟨z, hz⟩ := exists_sievePrimes_prod_lt (half_pos hε)
  set k := (sievePrimes z).card with hk
  set C : ℝ := (3 : ℝ) ^ k + ((z : ℝ) / 6 + 1) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨⌈2 * C / ε⌉₊, fun N hN => ?_⟩
  have hCN : C ≤ ε / 2 * N := by
    have hle : 2 * C / ε ≤ (N : ℝ) := by
      have := Nat.ceil_le.mp (le_refl ⌈2 * C / ε⌉₊)
      calc 2 * C / ε ≤ (⌈2 * C / ε⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    rw [div_le_iff₀ hε] at hle
    linarith
  have hmain := twin_mainSum_eq N z (2 * k) (by omega)
  have herr := twin_errSum_le_const N z (2 * k)
  have hupper := brun_twin_upper N z (2 * k) (even_two_mul k)
  rw [hmain] at hupper
  have hprodN : (N : ℝ) * ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ))
      ≤ (N : ℝ) * (ε / 2) := by
    have hprod0 : 0 ≤ ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast sievePrimes_five_le hp
      have : 2 / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith
    exact mul_le_mul_of_nonneg_left hz.le (Nat.cast_nonneg N)
  linarith

/-- **THE HEADLINE — TWIN PRIMES HAVE DENSITY ZERO**:
    `#{m ≤ N : both 6m±1 prime} / N → 0`.  Machine-checked, unconditional, on
    standard axioms — the first standalone classical theorem of the
    formalization-first track. -/
theorem twin_density_zero :
    Filter.Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ) / N)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, h⟩ := twin_count_le_eps (half_pos hε)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hcount := h N hN₀
  calc (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ) / N
      ≤ (ε / 2 * N) / N := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-! ### Axiom audit -/

#print axioms twin_mainSum_eq
#print axioms twin_errSum_le_const
#print axioms exists_sievePrimes_sum_ge
#print axioms exists_sievePrimes_prod_lt
#print axioms twin_count_le_eps
#print axioms twin_density_zero

end TypeII
end Geometric
end EuclidsPath
