/-
  GeometricTypeIIBrunTwin — BRUN STAGE 2: the twin sieve INSTANTIATED.  Mathlib's
  dormant `BoundingSieve` frame is filled with the twin data — support = the
  values `(6m−1)(6m+1)`, density `ν(d) = 2^ω(d)/d`, remainder `|R_d| ≤ 2^ω(d)` —
  and closed against the stage-1 Bonferroni key into the UNCONDITIONAL upper
  bound: for all `N, z` and even `t`,

      #{m ≤ N : both 6m±1 prime} ≤ N·mainSum(μ⁺_t) + errSum(μ⁺_t) + z/6 + 1.

  ORIGIN.  Idea-generation session (two-axes program, wave 3, formalization-first
  track, stage 2 of the Brun module).  Stage 1 (`GeometricTypeIIBrun`) proved the
  Bonferroni weight is upper-Möbius; this module builds the sieve it feeds on.
  Design adversarially verified (wave-3b pre-pass): exact rational arithmetic at
  7 parameter points (0 failures), root counts brute-forced for all squarefree
  `d ≤ 1200` coprime to 6, class-count bracket exhaustive for `d ≤ 120`.

  TWO PRE-PASS CORRECTIONS (recorded so they cannot regress):
    * the boundary split is at `6m−1 > z`, NOT `6m+1 > z` — at `z = 29, m = 5`
      the wings are `29, 31`, both prime, `31 > z`, yet `29 ∣ gcd(P(29), v(5))`;
    * the house `root_card_crt` is ONLY CRT multiplicativity of `#{C² = 1}`;
      the `2^ω` count needs three new lemmas here (local count 2 at odd primes =
      reuse `rootFourier_card_prime`; Finset induction over the prime factors;
      the unit-6 bridge `{(6r)² = 1} ≃ {C² = 1}`, valid since `gcd(d, 6) = 1`).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twinValue` + `twinValue_eq`/`twinValue_injOn` — the value map
      `m ↦ (6m−1)(6m+1) = 36m² − 1`, injective on `m ≥ 1`;
    * `sievePrimes`/`sieveProd` — the sifting primes are EXACTLY `[5, z]`
      (`p = 2, 3` never divide `36m² − 1`; moreover `ν(2) = 1` would violate the
      frame and `ν(3) = 2/3` would make `rem 3` unbounded — exclusion is forced
      AND free);
    * `twinNu` — `ν(d) = 2^ω(d)/d` as a multiplicative `ArithmeticFunction`
      (`prodPrimeFactors` divided pointwise by `id`);
    * `twinSieve` — **THE INSTANCE**: mathlib's `BoundingSieve` filled with the
      twin data; `twinSieve_multSum`/`twinSieve_siftedSum` pull the frame's sums
      back to honest `m`-counts;
    * `residue_class_bracket`/`residue_class_err` — `⌊N/d⌋ ≤ #class ≤ ⌊N/d⌋ + 1`,
      hence `|#class − N/d| ≤ 1` — pure-ℕ, no Fact instances;
    * `sq_roots_card_prod`/`root_res_card` — **THE 2^ω ROOT COUNT**:
      `#{r mod d : d ∣ 36r² − 1} = 2^ω(d)` for squarefree `d` coprime to 6
      (reuse `rootFourier_card_prime` + `root_card_crt`, then the unit-6 bridge);
    * `twinSieve_rem_bound` — **THE REMAINDER**: `|rem d| ≤ 2^ω(d)` for every
      `d ∣ P(z)` (fiberwise over the `2^ω` root classes, one unit per class);
    * `brun_twin_upper` — **THE UNCONDITIONAL BOUND** displayed above, valid for
      ALL `N, z, t` with `t` even (degenerate cases included: `z < 5` gives
      `P = 1` and the trivial bound; `N = 0` and `t = 0` checked);
    * `twin_errSum_le` — the error budget in symbolic form:
      `errSum ≤ Σ_{d ∣ P(z), ω(d) ≤ t} 2^ω(d)` (stage-3 seam);
    * `esymmOn_le_pow_div_factorial` — **THE TAIL TOOL**: `e_j(x) ≤ (Σx)^j / j!`
      for nonneg weights (the elementary-symmetric domination via
      `(j+1)e_{j+1} ≤ (Σx)e_j`, double counting) — the stage-3 instrument for
      the truncated main-term analysis, proved now.

  DISCLOSURES (mandatory reading before quoting):
    * STILL NOT A TWIN-DENSITY THEOREM.  `mainSum` and `errSum` stay SYMBOLIC:
      stage 3 must choose `z, t` as functions of `N` and evaluate
      `Σ_{d ∣ P, ω ≤ t} μ(d)2^ω(d)/d` against the product `∏(1 − 2/p)` using the
      tail tool; the pin has only QUALITATIVE prime-reciprocal divergence
      (`not_summable_one_div_on_primes`), so the reachable ceiling is a
      qualitative `o(N)` — disclosed since stage 1.
    * BRUN IS STRUCTURALLY BLIND TO THE PARITY WALL (upper-bound method) — that
      is why this track completes unconditionally.  No registered target (CRE,
      SemiprimeShortRestriction, HigherConductorDispersion, LowFreqRootCoherence,
      OneWingTarget) is touched: NOT a §110 event.
    * The numeric grounding above is the pre-pass verifier's, recorded in its
      scratchpad script; the Lean statements carry no numerics.
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIBrun
import EuclidsPath.Engine.GeometricTypeIICompletion

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### Section A — the value map -/

/-- The twin value map `m ↦ (6m−1)(6m+1)`.  A named structural object, NOT a
    target.  (`twinValue 0 = 0` by ℕ-truncation — every lemma carries `1 ≤ m`.) -/
def twinValue (m : ℕ) : ℕ := (6 * m - 1) * (6 * m + 1)

theorem twinValue_eq {m : ℕ} (hm : 1 ≤ m) : twinValue m = 36 * m ^ 2 - 1 := by
  have h1 : 1 ≤ 6 * m := by omega
  have h2 : 1 ≤ 36 * m ^ 2 := by
    have := Nat.one_le_pow 2 m (by omega)
    omega
  unfold twinValue
  zify [h1, h2]
  ring

theorem twinValue_injOn {N : ℕ} : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N,
    twinValue a = twinValue b → a = b := by
  intro a ha b hb h
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  rw [twinValue_eq ha1, twinValue_eq hb1] at h
  have ha2 : 1 ≤ 36 * a ^ 2 := by
    have := Nat.one_le_pow 2 a (by omega)
    omega
  have hb2 : 1 ≤ 36 * b ^ 2 := by
    have := Nat.one_le_pow 2 b (by omega)
    omega
  have hsq : a ^ 2 = b ^ 2 := by omega
  exact Nat.pow_left_injective (by norm_num) hsq

/-! ### Section B — the sieve primes `[5, z]` -/

/-- The sifting primes: `5 ≤ p ≤ z`.  `p = 2, 3` never divide `36m² − 1`
    (`36m² − 1 ≡ 1 (mod 2)`, `≡ 2 (mod 3)`), and the frame itself forbids them
    (`ν(2) = 1`, unbounded `rem 3`) — exclusion is forced and free. -/
def sievePrimes (z : ℕ) : Finset ℕ := (Finset.Icc 5 z).filter Nat.Prime

/-- The squarefree sifting modulus `P(z) = ∏_{5 ≤ p ≤ z} p`. -/
def sieveProd (z : ℕ) : ℕ := ∏ p ∈ sievePrimes z, p

theorem sievePrimes_prime {z p : ℕ} (hp : p ∈ sievePrimes z) : p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem sievePrimes_five_le {z p : ℕ} (hp : p ∈ sievePrimes z) : 5 ≤ p :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1

theorem sieveProd_squarefree (z : ℕ) : Squarefree (sieveProd z) :=
  squarefree_prod_of_primes fun _ hp => sievePrimes_prime hp

theorem sieveProd_pos (z : ℕ) : 0 < sieveProd z :=
  Nat.pos_of_ne_zero (sieveProd_squarefree z).ne_zero

theorem primeFactors_sieveProd (z : ℕ) :
    (sieveProd z).primeFactors = sievePrimes z :=
  Nat.primeFactors_prod fun _ hp => sievePrimes_prime hp

/-- Prime divisors of `P(z)` lie in `[5, z]`. -/
theorem prime_dvd_sieveProd {z p : ℕ} (hp : p.Prime) (hdvd : p ∣ sieveProd z) :
    5 ≤ p ∧ p ≤ z := by
  have hmem : p ∈ (sieveProd z).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hdvd, (sieveProd_squarefree z).ne_zero⟩
  rw [primeFactors_sieveProd] at hmem
  exact Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1

/-- Divisors of `P(z)` are coprime to 6. -/
theorem coprime_six_of_dvd_sieveProd {z d : ℕ} (hd : d ∣ sieveProd z) :
    Nat.Coprime d 6 := by
  have h2 : ¬ (2 : ℕ) ∣ d := by
    intro hdvd2
    have h := prime_dvd_sieveProd (by norm_num : (2 : ℕ).Prime) (hdvd2.trans hd)
    omega
  have h3 : ¬ (3 : ℕ) ∣ d := by
    intro hdvd3
    have h := prime_dvd_sieveProd (by norm_num : (3 : ℕ).Prime) (hdvd3.trans hd)
    omega
  have hc2 : Nat.Coprime d 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h2
  have hc3 : Nat.Coprime d 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3
  have hsix : (6 : ℕ) = 2 * 3 := by norm_num
  rw [hsix]
  exact Nat.Coprime.mul_right hc2 hc3

/-! ### Section C — the density `ν(d) = 2^ω(d)/d` -/

/-- The twin sieve density `ν(d) = 2^ω(d)/d` as an arithmetic function:
    `prodPrimeFactors (const 2)` divided pointwise by `id`. -/
noncomputable def twinNu : ArithmeticFunction ℝ :=
  (ArithmeticFunction.prodPrimeFactors fun _ => (2 : ℝ)).pdiv
    ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

theorem twinNu_mult : twinNu.IsMultiplicative := by
  unfold twinNu
  arith_mult

theorem twinNu_apply {d : ℕ} (hd : d ≠ 0) :
    twinNu d = 2 ^ d.primeFactors.card / d := by
  unfold twinNu
  rw [ArithmeticFunction.pdiv_apply,
    ArithmeticFunction.prodPrimeFactors_apply hd, Finset.prod_const,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]

theorem twinNu_prime {p : ℕ} (hp : p.Prime) : twinNu p = 2 / p := by
  rw [twinNu_apply hp.ne_zero, Nat.Prime.primeFactors hp, Finset.card_singleton,
    pow_one]

/-! ### Section D — the BoundingSieve instance -/

/-- **THE TWIN SIEVE INSTANCE**: mathlib's `BoundingSieve` filled with the twin
    data — support = the values `(6m−1)(6m+1)` for `m ∈ [1, N]`, unit weights,
    total mass `N`, sifting modulus `P(z)`, density `ν(d) = 2^ω(d)/d`. -/
noncomputable def twinSieve (N z : ℕ) : BoundingSieve where
  support := (Finset.Icc 1 N).image twinValue
  prodPrimes := sieveProd z
  prodPrimes_squarefree := sieveProd_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := twinNu
  nu_mult := twinNu_mult
  nu_pos_of_prime := fun p hp _ => by
    rw [twinNu_prime hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := fun p hp hdvd => by
    rw [twinNu_prime hp]
    have h5 := (prime_dvd_sieveProd hp hdvd).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [div_lt_one hp0]
    exact_mod_cast (by omega : 2 < p)

/-- The frame's `multSum` pulls back to the honest `m`-count. -/
theorem twinSieve_multSum (N z d : ℕ) :
    (twinSieve N z).multSum d
      = (((Finset.Icc 1 N).filter fun m => d ∣ twinValue m).card : ℝ) := by
  show ∑ n ∈ (Finset.Icc 1 N).image twinValue,
      (if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_image twinValue_injOn, Finset.sum_boole]

/-- The frame's `siftedSum` pulls back to the honest `m`-count. -/
theorem twinSieve_siftedSum (N z : ℕ) :
    (twinSieve N z).siftedSum
      = (((Finset.Icc 1 N).filter fun m =>
          Nat.Coprime (sieveProd z) (twinValue m)).card : ℝ) := by
  show ∑ n ∈ (Finset.Icc 1 N).image twinValue,
      (if Nat.Coprime (sieveProd z) n then (1 : ℝ) else 0) = _
  rw [Finset.sum_image twinValue_injOn, Finset.sum_boole]

/-! ### Section E — the residue-class bracket (pure ℕ) -/

/-- `⌊N/d⌋ ≤ #{m ∈ [1,N] : m ≡ v (mod d)} ≤ ⌊N/d⌋ + 1` — the exact ℕ bracket,
    no primality, no instances. -/
theorem residue_class_bracket {d : ℕ} (hd : 0 < d) {v : ℕ} (hv : v < d) (N : ℕ) :
    N / d ≤ ((Finset.Icc 1 N).filter fun m => m % d = v).card
      ∧ ((Finset.Icc 1 N).filter fun m => m % d = v).card ≤ N / d + 1 := by
  constructor
  · -- lower bound: inject the first ⌊N/d⌋ members of the class
    by_cases hv0 : v = 0
    · subst hv0
      have hinj : ∀ k ∈ Finset.Icc 1 (N / d), ∀ l ∈ Finset.Icc 1 (N / d),
          d * k = d * l → k = l := fun k _ l _ h =>
        Nat.eq_of_mul_eq_mul_left hd h
      have hmaps : ∀ k ∈ Finset.Icc 1 (N / d),
          d * k ∈ (Finset.Icc 1 N).filter fun m => m % d = 0 := by
        intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        have hle : d * (N / d) ≤ N := by
          rw [mul_comm]
          exact Nat.div_mul_le_self N d
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
        · have : 1 * 1 ≤ d * k := Nat.mul_le_mul hd hk1
          omega
        · have : d * k ≤ d * (N / d) := Nat.mul_le_mul_left d hk2
          omega
        · exact Nat.mul_mod_right d k
      have := Finset.card_le_card_of_injOn (fun k => d * k)
        (fun k hk => hmaps k hk) (fun k hk l hl h => hinj k hk l hl h)
      rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
    · have hv1 : 1 ≤ v := by omega
      have hmaps : ∀ q ∈ Finset.range (N / d),
          d * q + v ∈ (Finset.Icc 1 N).filter fun m => m % d = v := by
        intro q hq
        have hqlt : q < N / d := Finset.mem_range.mp hq
        have hle : d * (N / d) ≤ N := by
          rw [mul_comm]
          exact Nat.div_mul_le_self N d
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
        · have : d * q + d ≤ d * (N / d) := by
            have : d * (q + 1) ≤ d * (N / d) := Nat.mul_le_mul_left d (by omega)
            omega
          omega
        · rw [Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt hv
      have hinj : ∀ q ∈ Finset.range (N / d), ∀ r ∈ Finset.range (N / d),
          d * q + v = d * r + v → q = r := by
        intro q _ r _ h
        have h' : d * q = d * r := by omega
        exact Nat.eq_of_mul_eq_mul_left hd h'
      have := Finset.card_le_card_of_injOn (fun q => d * q + v)
        (fun q hq => hmaps q hq) (fun q hq r hr h => hinj q hq r hr h)
      rwa [Finset.card_range] at this
  · -- upper bound: divide out
    have hmaps : ∀ m ∈ (Finset.Icc 1 N).filter fun m => m % d = v,
        m / d ∈ Finset.range (N / d + 1) := by
      intro m hm
      have hmN : m ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
      exact Finset.mem_range.mpr (by
        have := Nat.div_le_div_right (c := d) hmN
        omega)
    have hinj : ∀ m ∈ (Finset.Icc 1 N).filter fun m => m % d = v,
        ∀ n ∈ (Finset.Icc 1 N).filter fun m => m % d = v,
        m / d = n / d → m = n := by
      intro m hm n hn h
      have hmv : m % d = v := (Finset.mem_filter.mp hm).2
      have hnv : n % d = v := (Finset.mem_filter.mp hn).2
      have hm' := Nat.div_add_mod m d
      have hn' := Nat.div_add_mod n d
      have : d * (m / d) = d * (n / d) := by rw [h]
      omega
    have := Finset.card_le_card_of_injOn (fun m => m / d)
      (fun m hm => hmaps m hm) (fun m hm n hn h => hinj m hm n hn h)
    rwa [Finset.card_range] at this

/-- The real form: `|#class − N/d| ≤ 1`. -/
theorem residue_class_err {d : ℕ} (hd : 0 < d) {v : ℕ} (hv : v < d) (N : ℕ) :
    |((((Finset.Icc 1 N).filter fun m => m % d = v).card : ℝ)) - (N : ℝ) / d| ≤ 1 := by
  obtain ⟨hlow, hup⟩ := residue_class_bracket hd hv N
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hfl : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hfu : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hd0]
    have hN : N < (N / d + 1) * d := by
      have hexp : (N / d + 1) * d = d * (N / d) + d := by ring
      have hmod := Nat.div_add_mod N d
      have hlt : N % d < d := Nat.mod_lt _ hd
      omega
    exact_mod_cast hN
  have hcl : ((N / d : ℕ) : ℝ)
      ≤ ((((Finset.Icc 1 N).filter fun m => m % d = v).card : ℝ)) := by
    exact_mod_cast hlow
  have hcu : ((((Finset.Icc 1 N).filter fun m => m % d = v).card : ℝ))
      ≤ ((N / d : ℕ) : ℝ) + 1 := by
    exact_mod_cast hup
  rw [abs_le]
  constructor <;> linarith

/-! ### Section F — the `2^ω` root count -/

/-- Over a product of DISTINCT ODD primes, `#{C : C² = 1} = 2^{#primes}` — reuse
    of `rootFourier_card_prime` (local count 2, odd primes only) chained by the
    house `root_card_crt` (CRT multiplicativity).  The modulus is a plain
    variable with an equation so the Finset induction never rewrites a type
    index (`subst` handles the dependency). -/
theorem sq_roots_card_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (n : ℕ) [NeZero n] (hn : n = ∏ p ∈ S, p) :
    (Finset.univ.filter fun C : ZMod n => C ^ 2 = 1).card = 2 ^ S.card := by
  classical
  induction S using Finset.induction_on generalizing n with
  | empty =>
      rw [Finset.prod_empty] at hn
      subst hn
      simp only [Finset.card_empty, pow_zero]
      rw [Finset.filter_true_of_mem (fun C _ => Subsingleton.elim _ _),
        Finset.card_univ, ZMod.card]
  | insert p T hpT ih =>
      obtain ⟨hp, hp2⟩ := hS p (Finset.mem_insert_self p T)
      have hT : ∀ q ∈ T, q.Prime ∧ 2 < q := fun q hq =>
        hS q (Finset.mem_insert_of_mem hq)
      haveI hpF : Fact p.Prime := ⟨hp⟩
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hprodpos : 0 < ∏ q ∈ T, q :=
        Finset.prod_pos fun q hq => (hT q hq).1.pos
      haveI : NeZero (∏ q ∈ T, q) := ⟨hprodpos.ne'⟩
      have hcop : Nat.Coprime p (∏ q ∈ T, q) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        exact (Nat.coprime_primes hp (hT q hq).1).mpr fun hpq => hpT (hpq ▸ hq)
      rw [Finset.prod_insert hpT] at hn
      subst hn
      rw [root_card_crt hcop, rootFourier_card_prime hp2,
        ih hT (∏ q ∈ T, q) rfl,
        Finset.card_insert_of_notMem hpT, pow_succ]
      ring

/-- **THE `2^ω` ROOT COUNT**: for squarefree `d` coprime to 6,
    `#{r mod d : (6r)² = 1} = 2^ω(d)` — the unit-6 bridge composed with the
    prime-product count. -/
theorem root_res_card {d : ℕ} [NeZero d] (hd : Squarefree d)
    (h6 : Nat.Coprime d 6) :
    (Finset.univ.filter fun r : ZMod d => (6 * r) ^ 2 = 1).card
      = 2 ^ d.primeFactors.card := by
  classical
  have hunit : IsUnit ((6 : ℕ) : ZMod d) :=
    (ZMod.isUnit_iff_coprime 6 d).mpr h6.symm
  have h6cast : ((6 : ℕ) : ZMod d) = (6 : ZMod d) := by push_cast; rfl
  rw [h6cast] at hunit
  -- the unit-6 bridge
  have hbij : (Finset.univ.filter fun r : ZMod d => (6 * r) ^ 2 = 1).card
      = (Finset.univ.filter fun C : ZMod d => C ^ 2 = 1).card := by
    refine Finset.card_bij' (fun r _ => (6 : ZMod d) * r)
      (fun C _ => (6 : ZMod d)⁻¹ * C) ?_ ?_ ?_ ?_
    · intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hr).2⟩
    · intro C hC
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hCsq : C ^ 2 = 1 := (Finset.mem_filter.mp hC).2
      have hrec : (6 : ZMod d) * ((6 : ZMod d)⁻¹ * C) = C := by
        rw [← mul_assoc, ZMod.mul_inv_of_unit _ hunit, one_mul]
      rw [hrec]
      exact hCsq
    · intro r _
      rw [← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul]
    · intro C _
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hunit, one_mul]
  -- the prime factors of d are odd primes
  have hprimes : ∀ p ∈ d.primeFactors, p.Prime ∧ 2 < p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hp6 : Nat.Coprime p 6 := Nat.Coprime.coprime_dvd_left hdvd h6
    have h2 : p ≠ 2 := by
      rintro rfl
      exact absurd hp6 (by decide)
    have h3 : p ≠ 3 := by
      rintro rfl
      exact absurd hp6 (by decide)
    have := hpp.two_le
    exact ⟨hpp, by omega⟩
  have key := sq_roots_card_prod d.primeFactors hprimes d
    (Nat.prod_primeFactors_of_squarefree hd).symm
  rw [hbij, key]

/-- The divisibility event in residue form: for `d` coprime to 6 and `m ≥ 1`,
    `d ∣ (6m−1)(6m+1) ↔ (6·m̄)² = 1` in `ZMod d`. -/
theorem dvd_twinValue_iff {d m : ℕ} [NeZero d] (hm : 1 ≤ m) :
    d ∣ twinValue m ↔ (6 * (m : ZMod d)) ^ 2 = 1 := by
  have h2 : 1 ≤ 36 * m ^ 2 := by
    have := Nat.one_le_pow 2 m (by omega)
    omega
  rw [twinValue_eq hm, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2]
  push_cast
  rw [sub_eq_zero]
  constructor <;> intro h <;> linear_combination h

/-! ### Section G — the remainder bound `|rem d| ≤ 2^ω(d)` -/

/-- The divisibility count fibers over the `2^ω` root classes. -/
theorem multSum_classes {N d : ℕ} [NeZero d] :
    ((Finset.Icc 1 N).filter fun m => d ∣ twinValue m).card
      = ∑ r ∈ Finset.univ.filter (fun r : ZMod d => (6 * r) ^ 2 = 1),
          ((Finset.Icc 1 N).filter fun m => m % d = (r : ZMod d).val).card := by
  classical
  have hmaps : ∀ m ∈ (Finset.Icc 1 N).filter fun m => d ∣ twinValue m,
      ((m : ZMod d))
        ∈ Finset.univ.filter (fun r : ZMod d => (6 * r) ^ 2 = 1) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (dvd_twinValue_iff hm1).mp (Finset.mem_filter.mp hm).2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun r hr => ?_
  congr 1
  have hroot : (6 * r) ^ 2 = 1 := (Finset.mem_filter.mp hr).2
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hm1, hmN⟩, _⟩, hclass⟩
    refine ⟨⟨hm1, hmN⟩, ?_⟩
    have hcast : ((m : ZMod d)) = ((r.val : ℕ) : ZMod d) := by
      rw [ZMod.natCast_zmod_val]
      exact hclass
    have hmod := (ZMod.natCast_eq_natCast_iff' m r.val d).mp hcast
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt r)] at hmod
  · rintro ⟨⟨hm1, hmN⟩, hmod⟩
    have hclass : ((m : ZMod d)) = r := by
      conv_rhs => rw [← ZMod.natCast_zmod_val r]
      rw [ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt (ZMod.val_lt r)]
      exact hmod
    exact ⟨⟨⟨hm1, hmN⟩, (dvd_twinValue_iff hm1).mpr (by
      rw [hclass]; exact hroot)⟩, hclass⟩

/-- **THE REMAINDER BOUND**: `|rem d| ≤ 2^ω(d)` for every divisor `d` of `P(z)` —
    one unit of error per root class. -/
theorem twinSieve_rem_bound {N z d : ℕ} (hdvd : d ∣ sieveProd z) :
    |(twinSieve N z).rem d| ≤ (2 : ℝ) ^ d.primeFactors.card := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (sieveProd_pos z)
  haveI : NeZero d := ⟨hd0.ne'⟩
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hdvd (sieveProd_squarefree z)
  have h6 := coprime_six_of_dvd_sieveProd hdvd
  have hrem : (twinSieve N z).rem d
      = ∑ r ∈ Finset.univ.filter (fun r : ZMod d => (6 * r) ^ 2 = 1),
          ((((Finset.Icc 1 N).filter
              fun m => m % d = (r : ZMod d).val).card : ℝ) - (N : ℝ) / d) := by
    show (twinSieve N z).multSum d
        - (twinSieve N z).nu d * (twinSieve N z).totalMass = _
    rw [twinSieve_multSum]
    show _ - twinNu d * (N : ℝ) = _
    rw [twinNu_apply hd0.ne', multSum_classes, Finset.sum_sub_distrib,
      Nat.cast_sum, Finset.sum_const, root_res_card hsq h6, nsmul_eq_mul]
    push_cast
    ring
  rw [hrem]
  calc |∑ r ∈ Finset.univ.filter (fun r : ZMod d => (6 * r) ^ 2 = 1),
          ((((Finset.Icc 1 N).filter
              fun m => m % d = (r : ZMod d).val).card : ℝ) - (N : ℝ) / d)|
      ≤ ∑ r ∈ Finset.univ.filter (fun r : ZMod d => (6 * r) ^ 2 = 1),
          |(((Finset.Icc 1 N).filter
              fun m => m % d = (r : ZMod d).val).card : ℝ) - (N : ℝ) / d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Finset.univ.filter (fun r : ZMod d => (6 * r) ^ 2 = 1), (1 : ℝ) :=
        Finset.sum_le_sum fun r _ => residue_class_err hd0 (ZMod.val_lt r) N
    _ = (2 : ℝ) ^ d.primeFactors.card := by
        rw [Finset.sum_const, root_res_card hsq h6, nsmul_eq_mul, mul_one]
        push_cast
        ring

/-! ### Section H — the boundary and the unconditional bound -/

/-- Prime wings above `z` make the value coprime to `P(z)` — the CORRECTED split
    (at `6m−1 > z`; the `6m+1` split is FALSE: `z = 29, m = 5`). -/
theorem coprime_sieveProd_of_prime_wings {z m : ℕ}
    (hp : (6 * m - 1).Prime) (hq : (6 * m + 1).Prime) (hz : z < 6 * m - 1) :
    Nat.Coprime (sieveProd z) (twinValue m) := by
  unfold twinValue sieveProd
  rw [Nat.coprime_prod_left_iff]
  intro p hp'
  have hpp := sievePrimes_prime hp'
  have hple : p ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp').1).2
  refine Nat.Coprime.mul_right ?_ ?_
  · exact (Nat.coprime_primes hpp hp).mpr (by omega)
  · exact (Nat.coprime_primes hpp hq).mpr (by omega)

/-- The boundary set `{m : 6m−1 ≤ z}` has at most `(z+1)/6` members. -/
theorem boundary_card (N z : ℕ) :
    ((Finset.Icc 1 N).filter fun m => 6 * m - 1 ≤ z).card ≤ (z + 1) / 6 := by
  have hsub : ((Finset.Icc 1 N).filter fun m => 6 * m - 1 ≤ z)
      ⊆ Finset.Icc 1 ((z + 1) / 6) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨hm1, _⟩, hmz⟩ := hm
    refine ⟨hm1, ?_⟩
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  calc ((Finset.Icc 1 N).filter fun m => 6 * m - 1 ≤ z).card
      ≤ (Finset.Icc 1 ((z + 1) / 6)).card := Finset.card_le_card hsub
    _ = (z + 1) / 6 + 1 - 1 := by rw [Nat.card_Icc]
    _ ≤ (z + 1) / 6 := by omega

/-- The Bonferroni weight, as a named def unfolding to the stage-1 lambda. -/
noncomputable def bonferroniWeight (t : ℕ) : ℕ → ℝ := fun d =>
  if d.primeFactors.card ≤ t then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

theorem bonferroniWeight_isUpperMoebius {t : ℕ} (ht : Even t) :
    BoundingSieve.IsUpperMoebius (bonferroniWeight t) :=
  bonferroni_isUpperMoebius ht

/-- **THE UNCONDITIONAL BRUN BOUND FOR TWINS**: for ALL `N, z` and even `t`,
    `#{m ≤ N : both 6m±1 prime} ≤ N·mainSum(μ⁺_t) + errSum(μ⁺_t) + z/6 + 1`.
    The sieve terms stay symbolic (stage 3 evaluates); the inequality itself is
    exact, unconditional, and degenerates gracefully (`z < 5`, `N = 0`, `t = 0`
    all checked in the pre-pass). -/
theorem brun_twin_upper (N z t : ℕ) (ht : Even t) :
    (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      ≤ (N : ℝ) * (twinSieve N z).mainSum (bonferroniWeight t)
        + (twinSieve N z).errSum (bonferroniWeight t) + ((z : ℝ) / 6 + 1) := by
  have hsplit : ((Finset.Icc 1 N).filter fun m =>
      (6 * m - 1).Prime ∧ (6 * m + 1).Prime)
      ⊆ ((Finset.Icc 1 N).filter fun m =>
          Nat.Coprime (sieveProd z) (twinValue m))
        ∪ ((Finset.Icc 1 N).filter fun m => 6 * m - 1 ≤ z) := by
    intro m hm
    have hmf := Finset.mem_filter.mp hm
    have hmIcc := hmf.1
    have hp := hmf.2.1
    have hq := hmf.2.2
    by_cases hz : 6 * m - 1 ≤ z
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmIcc, hz⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmIcc,
        coprime_sieveProd_of_prime_wings hp hq (by omega)⟩)
  have hcard : ((Finset.Icc 1 N).filter fun m =>
      (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card
      ≤ ((Finset.Icc 1 N).filter fun m =>
          Nat.Coprime (sieveProd z) (twinValue m)).card
        + ((Finset.Icc 1 N).filter fun m => 6 * m - 1 ≤ z).card :=
    (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have hsieve : (twinSieve N z).siftedSum
      ≤ (twinSieve N z).totalMass * (twinSieve N z).mainSum (bonferroniWeight t)
        + (twinSieve N z).errSum (bonferroniWeight t) :=
    BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius _
      (bonferroniWeight_isUpperMoebius ht)
  rw [twinSieve_siftedSum] at hsieve
  have htotal : (twinSieve N z).totalMass = (N : ℝ) := rfl
  rw [htotal] at hsieve
  have hbound := boundary_card N z
  have hboundR : ((((Finset.Icc 1 N).filter
      fun m => 6 * m - 1 ≤ z).card : ℕ) : ℝ) ≤ (z : ℝ) / 6 + 1 := by
    calc ((((Finset.Icc 1 N).filter fun m => 6 * m - 1 ≤ z).card : ℕ) : ℝ)
        ≤ (((z + 1) / 6 : ℕ) : ℝ) := by exact_mod_cast hbound
      _ ≤ ((z + 1 : ℕ) : ℝ) / 6 := Nat.cast_div_le
      _ ≤ (z : ℝ) / 6 + 1 := by push_cast; linarith
  have hcardR : (((Finset.Icc 1 N).filter fun m =>
      (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      ≤ (((Finset.Icc 1 N).filter fun m =>
          Nat.Coprime (sieveProd z) (twinValue m)).card : ℝ)
        + ((((Finset.Icc 1 N).filter fun m => 6 * m - 1 ≤ z).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The error budget in symbolic form (the stage-3 seam):
    `errSum(μ⁺_t) ≤ Σ_{d ∣ P(z), ω(d) ≤ t} 2^ω(d)`. -/
theorem twin_errSum_le (N z t : ℕ) :
    (twinSieve N z).errSum (bonferroniWeight t)
      ≤ ∑ d ∈ (sieveProd z).divisors,
          (if d.primeFactors.card ≤ t then (2 : ℝ) ^ d.primeFactors.card else 0) := by
  show ∑ d ∈ (sieveProd z).divisors,
      |bonferroniWeight t d| * |(twinSieve N z).rem d| ≤ _
  refine Finset.sum_le_sum fun d hd => ?_
  have hdvd : d ∣ sieveProd z := (Nat.mem_divisors.mp hd).1
  by_cases hom : d.primeFactors.card ≤ t
  · rw [if_pos hom]
    have hmu : |bonferroniWeight t d| ≤ 1 := by
      unfold bonferroniWeight
      rw [if_pos hom]
      have habs : |ArithmeticFunction.moebius d| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)|
          = ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by
            rw [Int.cast_abs]
        _ ≤ 1 := by exact_mod_cast habs
    calc |bonferroniWeight t d| * |(twinSieve N z).rem d|
        ≤ 1 * ((2 : ℝ) ^ d.primeFactors.card) :=
          mul_le_mul hmu (twinSieve_rem_bound hdvd) (abs_nonneg _) one_pos.le
      _ = (2 : ℝ) ^ d.primeFactors.card := one_mul _
  · rw [if_neg hom]
    unfold bonferroniWeight
    rw [if_neg hom, abs_zero, zero_mul]

/-! ### The elementary-symmetric tail tool (stage-3 instrument, proved now) -/

/-- The elementary symmetric sum `e_j(x)` over a Finset of indices. -/
noncomputable def esymmOn (s : Finset ℕ) (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ T ∈ s.powersetCard j, ∏ p ∈ T, x p

theorem esymmOn_zero (s : Finset ℕ) (x : ℕ → ℝ) : esymmOn s x 0 = 1 := by
  unfold esymmOn
  rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]

theorem esymmOn_nonneg {s : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ p ∈ s, 0 ≤ x p)
    (j : ℕ) : 0 ≤ esymmOn s x j :=
  Finset.sum_nonneg fun _T hT => Finset.prod_nonneg fun p hp =>
    hx p ((Finset.mem_powersetCard.mp hT).1 hp)

/-- The double-counting step: `(j+1)·e_{j+1} ≤ (Σx)·e_j` for nonneg weights —
    each `(j+1)`-set arises `j+1` times as `(p, S ∪ {p})`, and dropping the
    `p ∈ S` collisions only adds nonneg terms. -/
theorem succ_mul_esymmOn_succ_le {s : Finset ℕ} {x : ℕ → ℝ}
    (hx : ∀ p ∈ s, 0 ≤ x p) (j : ℕ) :
    ((j : ℝ) + 1) * esymmOn s x (j + 1) ≤ (∑ p ∈ s, x p) * esymmOn s x j := by
  classical
  -- A: pairs (T, p) with |T| = j+1, p ∈ T;  B: pairs (p, S) with |S| = j, p ∉ S
  set A := ((s.powersetCard (j + 1)) ×ˢ s).filter (fun q => q.2 ∈ q.1) with hA
  set B := (s ×ˢ s.powersetCard j).filter (fun q => q.1 ∉ q.2) with hB
  have h1 : ((j : ℝ) + 1) * esymmOn s x (j + 1) = ∑ q ∈ A, ∏ r ∈ q.1, x r := by
    rw [hA, Finset.sum_filter, Finset.sum_product]
    unfold esymmOn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const]
    have hTs : T ⊆ s := (Finset.mem_powersetCard.mp hT).1
    have hfil : s.filter (fun p => p ∈ T) = T := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTs]
    rw [hfil, (Finset.mem_powersetCard.mp hT).2, nsmul_eq_mul]
    push_cast
    ring
  have h2 : ∑ q ∈ A, ∏ r ∈ q.1, x r = ∑ q ∈ B, x q.1 * ∏ r ∈ q.2, x r := by
    refine Finset.sum_nbij' (fun q => (q.2, q.1.erase q.2))
      (fun q => (insert q.1 q.2, q.1)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hqprod, hqmem⟩ := Finset.mem_filter.mp hq
      obtain ⟨hT, hps⟩ := Finset.mem_product.mp hqprod
      obtain ⟨hTs, hTcard⟩ := Finset.mem_powersetCard.mp hT
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hps, ?_⟩, ?_⟩
      · refine Finset.mem_powersetCard.mpr ⟨(Finset.erase_subset _ _).trans hTs, ?_⟩
        rw [Finset.card_erase_of_mem hqmem, hTcard]
        omega
      · exact Finset.notMem_erase _ _
    · intro q hq
      obtain ⟨hqprod, hqnot⟩ := Finset.mem_filter.mp hq
      obtain ⟨hps, hS⟩ := Finset.mem_product.mp hqprod
      obtain ⟨hSs, hScard⟩ := Finset.mem_powersetCard.mp hS
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, hps⟩, ?_⟩
      · refine Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset_iff.mpr ⟨hps, hSs⟩, ?_⟩
        rw [Finset.card_insert_of_notMem hqnot, hScard]
      · exact Finset.mem_insert_self _ _
    · intro q hq
      obtain ⟨_, hqmem⟩ := Finset.mem_filter.mp hq
      exact Prod.ext (Finset.insert_erase hqmem) rfl
    · intro q hq
      obtain ⟨_, hqnot⟩ := Finset.mem_filter.mp hq
      exact Prod.ext rfl (Finset.erase_insert hqnot)
    · intro q hq
      obtain ⟨_, hqmem⟩ := Finset.mem_filter.mp hq
      exact (Finset.mul_prod_erase q.1 x hqmem).symm
  have h3 : ∑ q ∈ B, x q.1 * ∏ r ∈ q.2, x r
      ≤ ∑ q ∈ s ×ˢ s.powersetCard j, x q.1 * ∏ r ∈ q.2, x r := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro q hq _
    obtain ⟨hps, hS⟩ := Finset.mem_product.mp hq
    exact mul_nonneg (hx _ hps) (Finset.prod_nonneg fun r hr =>
      hx r ((Finset.mem_powersetCard.mp hS).1 hr))
  have h4 : ∑ q ∈ s ×ˢ s.powersetCard j, x q.1 * ∏ r ∈ q.2, x r
      = (∑ p ∈ s, x p) * esymmOn s x j := by
    unfold esymmOn
    rw [Finset.sum_mul_sum, Finset.sum_product]
  rw [h1, ← h4]
  calc ∑ q ∈ A, ∏ r ∈ q.1, x r
      = ∑ q ∈ B, x q.1 * ∏ r ∈ q.2, x r := h2
    _ ≤ ∑ q ∈ s ×ˢ s.powersetCard j, x q.1 * ∏ r ∈ q.2, x r := h3

/-- **THE TAIL TOOL**: `e_j(x) ≤ (Σx)^j / j!` for nonneg weights. -/
theorem esymmOn_le_pow_div_factorial {s : Finset ℕ} {x : ℕ → ℝ}
    (hx : ∀ p ∈ s, 0 ≤ x p) (j : ℕ) :
    esymmOn s x j ≤ (∑ p ∈ s, x p) ^ j / j.factorial := by
  induction j with
  | zero =>
      rw [esymmOn_zero]
      simp
  | succ j ih =>
      have hstep := succ_mul_esymmOn_succ_le hx j
      have hsum0 : (0 : ℝ) ≤ ∑ p ∈ s, x p := Finset.sum_nonneg hx
      have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hfac : (0 : ℝ) < (j.factorial : ℝ) := by
        exact_mod_cast j.factorial_pos
      have hstep' : esymmOn s x (j + 1)
          ≤ (∑ p ∈ s, x p) * esymmOn s x j / ((j : ℝ) + 1) :=
        (le_div_iff₀' hj1).mpr hstep
      calc esymmOn s x (j + 1)
          ≤ (∑ p ∈ s, x p) * esymmOn s x j / ((j : ℝ) + 1) := hstep'
        _ ≤ (∑ p ∈ s, x p) * ((∑ p ∈ s, x p) ^ j / j.factorial)
              / ((j : ℝ) + 1) := by
            gcongr
        _ = (∑ p ∈ s, x p) ^ (j + 1) / (j + 1).factorial := by
            rw [Nat.factorial_succ]
            push_cast
            field_simp
            ring

/-! ### Axiom audit -/

#print axioms twinValue_injOn
#print axioms twinNu_mult
#print axioms twinSieve_multSum
#print axioms residue_class_bracket
#print axioms root_res_card
#print axioms twinSieve_rem_bound
#print axioms coprime_sieveProd_of_prime_wings
#print axioms brun_twin_upper
#print axioms twin_errSum_le
#print axioms succ_mul_esymmOn_succ_le
#print axioms esymmOn_le_pow_div_factorial

end TypeII
end Geometric
end EuclidsPath
