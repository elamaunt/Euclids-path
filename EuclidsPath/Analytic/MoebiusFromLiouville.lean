/-
  Analytic/MoebiusFromLiouville — STAGE M5-A of the Tauberian campaign:
  **THE MERTENS CANCELLATION `M(x) = Σ_{n≤x} μ(n) = o(x)`**, derived
  from the campaign's Liouville cancellation by the exact square
  convolution.

  Chain: `μ = λ ⍟ h` where `h` is supported on squares with
  `h(d²) = μ(d)` (Dirichlet: `1/ζ(s) = (ζ(2s)/ζ(s)) · (1/ζ(2s))`); the
  hyperbola swap turns the partial sum into
  `M(x) = Σ_{d ≤ √x} μ(d)·L(x/d²)` with `L = Σλ`; the `ε`-split at a
  fixed `d₀` (small `d`: the P-D4 cancellation; large `d`: the trivial
  bound and the telescoping tail `Σ_{d>d₀} 1/d² ≤ 1/d₀`) closes the
  limit.  Everything unconditional and axiom-clean.

  DISCLOSURES.
    * `M(x) = o(x)` is the classical PNT-equivalent Mertens statement —
      machinery, no face of the parity wall is touched, NOT a §110
      event.  Face E's content is the μ-SIGNED aggregation across
      incommensurable moduli in SHORT windows (registered disclosure
      stands verbatim); the full-line Möbius average does not close it.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Analytic.LiouvilleConvolution
import EuclidsPath.Analytic.LiouvilleCancellation

set_option maxHeartbeats 3200000

namespace EuclidsPath
namespace Analytic

open ArithmeticFunction Finset Filter
open scoped BigOperators

/-! ### The square-supported Möbius companion -/

/-- The square-supported companion: `h(d²) = μ(d)`, `0` off squares
(the coefficients of `1/ζ(2s)`). -/
noncomputable def sqMoebius : ArithmeticFunction ℤ :=
  ⟨fun n => if IsSquare n then moebius n.sqrt else 0, by simp⟩

theorem sqMoebius_apply {n : ℕ} :
    sqMoebius n = if IsSquare n then moebius n.sqrt else 0 := rfl

theorem sqMoebius_sq {d : ℕ} : sqMoebius (d * d) = moebius d := by
  rw [sqMoebius_apply, if_pos ⟨d, rfl⟩, Nat.sqrt_eq]

/-- Prime powers are squares exactly at even exponents. -/
theorem isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) :
    IsSquare (p ^ k) ↔ Even k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  rw [isSquare_iff_even_factorization hpk]
  constructor
  · intro h
    have := h p
    rwa [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this
  · intro hk q
    rw [Nat.Prime.factorization_pow hp]
    rcases eq_or_ne q p with rfl | hq
    · rwa [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne hq]
      exact ⟨0, rfl⟩

theorem sqMoebius_prime_pow {p k : ℕ} (hp : p.Prime) :
    sqMoebius (p ^ k) = if k = 0 then 1 else if k = 2 then -1 else 0 := by
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨j, rfl⟩ := he
    have hsq : p ^ (j + j) = (p ^ j) * (p ^ j) := by ring
    rw [hsq, sqMoebius_sq]
    match j with
    | 0 => simp
    | 1 =>
      rw [pow_one, moebius_apply_prime hp]
      norm_num
    | (j + 2) =>
      rw [moebius_apply_prime_pow hp (by omega)]
      have h1 : ¬(j + 2 = 1) := by omega
      have h2 : ¬(j + 2 + (j + 2) = 0) := by omega
      have h3 : ¬(j + 2 + (j + 2) = 2) := by omega
      rw [if_neg h1, if_neg h2, if_neg h3]
  · have hns : ¬IsSquare (p ^ k) := by
      rw [isSquare_prime_pow_iff hp]
      exact Nat.not_even_iff_odd.mpr ho
    have hk0 : ¬(k = 0) := by
      rcases ho with ⟨j, hj⟩
      omega
    have hk2 : ¬(k = 2) := by
      rcases ho with ⟨j, hj⟩
      omega
    rw [sqMoebius_apply, if_neg hns, if_neg hk0, if_neg hk2]

theorem isMultiplicative_sqMoebius : sqMoebius.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [sqMoebius_apply, if_pos ⟨1, rfl⟩]
    simp
  · intro m n hco
    rcases eq_or_ne m 0 with rfl | hm0
    · have hn1 : n = 1 := Nat.coprime_zero_left n |>.mp hco
      subst hn1
      simp [sqMoebius_apply]
    rcases eq_or_ne n 0 with rfl | hn0
    · have hm1 : m = 1 := Nat.coprime_zero_right m |>.mp hco
      subst hm1
      simp [sqMoebius_apply]
    by_cases hsq : IsSquare (m * n)
    · obtain ⟨hmsq, hnsq⟩ := isSquare_of_coprime_mul hm0 hn0 hco hsq
      obtain ⟨a, ha⟩ := hmsq
      obtain ⟨b, hb⟩ := hnsq
      subst ha
      subst hb
      have hab : Nat.Coprime a b := by
        have h1 : Nat.Coprime a (b * b) :=
          Nat.Coprime.coprime_dvd_left (Dvd.intro a rfl) hco
        exact Nat.Coprime.coprime_dvd_right (Dvd.intro b rfl) h1
      have hprod : (a * a) * (b * b) = (a * b) * (a * b) := by ring
      rw [hprod, sqMoebius_sq, sqMoebius_sq, sqMoebius_sq,
        isMultiplicative_moebius.map_mul_of_coprime hab]
    · rw [sqMoebius_apply, if_neg hsq]
      by_cases hmsq : IsSquare m
      · have hnsq : ¬IsSquare n := by
          intro hn
          obtain ⟨a, ha⟩ := hmsq
          obtain ⟨b, hb⟩ := hn
          exact hsq ⟨a * b, by rw [ha, hb]; ring⟩
        rw [sqMoebius_apply (n := n), if_neg hnsq, mul_zero]
      · rw [sqMoebius_apply (n := m), if_neg hmsq, zero_mul]

/-! ### The exact convolution identity `λ ⍟ h = μ` -/

/-- **The square convolution**: `λ ⍟ sqMoebius = μ` (Dirichlet
`(ζ(2s)/ζ(s))·(1/ζ(2s)) = 1/ζ(s)`) — at prime powers the sum telescopes
by the parity of `λ`. -/
theorem liouville_mul_sqMoebius_eq_moebius :
    (ArithmeticFunction.liouville * sqMoebius : ArithmeticFunction ℤ)
      = moebius := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_liouville.mul isMultiplicative_sqMoebius) _
    isMultiplicative_moebius).mpr ?_
  intro p i hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal'
    (f := fun a b => ArithmeticFunction.liouville a * sqMoebius b),
    Nat.sum_divisors_prime_pow hp]
  have hterm : ∀ j ∈ Finset.range (i + 1),
      ArithmeticFunction.liouville (p ^ i / p ^ j) * sqMoebius (p ^ j)
        = (if j = 0 then ((-1 : ℤ)) ^ i else 0)
          + (if j = 2 then -((-1 : ℤ)) ^ i else 0) := by
    intro j hj
    have hji : j ≤ i := by
      have := Finset.mem_range.mp hj
      omega
    have hdiv : p ^ i / p ^ j = p ^ (i - j) := Nat.pow_div hji hp.pos
    rw [hdiv, ArithmeticFunction.liouville_apply (pow_ne_zero _ hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp,
      sqMoebius_prime_pow hp]
    rcases eq_or_ne j 0 with rfl | hj0
    · simp
    rcases eq_or_ne j 2 with rfl | hj2
    · have hi2 : 2 ≤ i := hji
      have hpar : ((-1 : ℤ)) ^ (i - 2) = ((-1 : ℤ)) ^ i := by
        have h2 : (i - 2) + 2 = i := by omega
        calc ((-1 : ℤ)) ^ (i - 2)
            = ((-1 : ℤ)) ^ (i - 2) * ((-1 : ℤ)) ^ 2 := by ring
          _ = ((-1 : ℤ)) ^ ((i - 2) + 2) := by rw [pow_add]
          _ = ((-1 : ℤ)) ^ i := by rw [h2]
      have e1 : (if (2 : ℕ) = 0 then (1 : ℤ) else
          if (2 : ℕ) = 2 then -1 else 0) = -1 := by norm_num
      have e2 : (if (2 : ℕ) = 0 then ((-1 : ℤ)) ^ i else 0) = 0 := by
        norm_num
      have e3 : (if (2 : ℕ) = 2 then -((-1 : ℤ)) ^ i else 0)
          = -((-1 : ℤ)) ^ i := by norm_num
      rw [e1, e2, e3, ← hpar]
      ring
    · simp only [if_neg hj0, if_neg hj2]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (i + 1)) 0
      (fun _ => ((-1 : ℤ)) ^ i),
    Finset.sum_ite_eq' (Finset.range (i + 1)) 2
      (fun _ => -((-1 : ℤ)) ^ i)]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  match i with
  | 0 => simp
  | 1 =>
    have h1 : moebius (p ^ 1) = -1 := by
      rw [pow_one, moebius_apply_prime hp]
    rw [if_neg (by simp), h1]
    norm_num
  | (i + 2) =>
    rw [if_pos (Finset.mem_range.mpr (by omega)),
      moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    ring

/-! ### The hyperbola swap -/

/-- The partial sum of a Dirichlet product, fibered over the second
factor: `Σ_{n≤x} (f⍟g)(n) = Σ_{b≤x} g(b)·Σ_{a≤x/b} f(a)`. -/
theorem sum_Icc_mul_eq (f g : ArithmeticFunction ℤ) (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, (f * g) n
      = ∑ b ∈ Finset.Icc 1 x, g b * (∑ a ∈ Finset.Icc 1 (x / b), f a) := by
  simp_rw [ArithmeticFunction.mul_apply, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun q => (⟨q.2.2, q.2.1⟩ : Σ _b : ℕ, ℕ))
    (j := fun q => (⟨q.2 * q.1, (q.2, q.1)⟩ : Σ _n : ℕ, ℕ × ℕ))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, a, b⟩ hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hn, hab⟩ := hq
    dsimp only at hn hab ⊢
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_divisorsAntidiagonal] at hab
    dsimp only at hab
    obtain ⟨hprod, hn0⟩ := hab
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, zero_mul] at hprod
      omega
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, mul_zero] at hprod
      omega
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
    dsimp only
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · have : b ≤ a * b := Nat.le_mul_of_pos_left b (by omega)
      omega
    · rw [Nat.le_div_iff_mul_le (by omega)]
      omega
  · rintro ⟨b, a⟩ hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hb, ha⟩ := hq
    dsimp only at hb ha ⊢
    rw [Finset.mem_Icc] at hb ha
    obtain ⟨hb1, hbx⟩ := hb
    obtain ⟨ha1, hab⟩ := ha
    rw [Nat.le_div_iff_mul_le (by omega)] at hab
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    dsimp only
    refine ⟨⟨?_, hab⟩, rfl, by positivity⟩
    have : 1 * 1 ≤ a * b := Nat.mul_le_mul ha1 hb1
    omega
  · rintro ⟨n, a, b⟩ hq
    rw [Finset.mem_sigma] at hq
    have hab := hq.2
    dsimp only at hab ⊢
    rw [Nat.mem_divisorsAntidiagonal] at hab
    dsimp only at hab
    simp only [Sigma.mk.injEq]
    exact ⟨hab.1, HEq.rfl⟩
  · rintro ⟨b, a⟩ _
    simp
  · rintro ⟨n, a, b⟩ _
    simp only
    ring

/-- **THE SQUARE-SCALE REPRESENTATION**: `M(x) = Σ_{d≤√x} μ(d)·L(x/d²)`. -/
theorem moebius_sum_eq_liouville_sums (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, moebius n
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt x),
          moebius d * (∑ a ∈ Finset.Icc 1 (x / (d * d)),
            ArithmeticFunction.liouville a) := by
  conv_lhs =>
    rw [← liouville_mul_sqMoebius_eq_moebius, sum_Icc_mul_eq]
  rw [← Finset.sum_filter_of_ne
    (p := fun b => IsSquare b)
    (f := fun b => sqMoebius b * (∑ a ∈ Finset.Icc 1 (x / b),
      ArithmeticFunction.liouville a))
    (hp := by
      intro b _ hb
      by_contra hbs
      rw [sqMoebius_apply, if_neg hbs, zero_mul] at hb
      exact hb rfl)]
  refine (Finset.sum_nbij' (i := fun d => d * d) (j := fun b => b.sqrt)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_Icc] at hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩, d, rfl⟩
    exact Nat.le_sqrt.mp hd.2
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, hbx⟩, r, hr⟩ := hb
    rw [Finset.mem_Icc]
    subst hr
    rw [Nat.sqrt_eq]
    constructor
    · by_contra h
      push Not at h
      interval_cases r
      omega
    · rw [Nat.le_sqrt]
      exact hbx
  · intro d hd
    rw [Nat.sqrt_eq]
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨_, r, hr⟩ := hb
    subst hr
    rw [Nat.sqrt_eq]
  · intro d hd
    rw [sqMoebius_sq]

/-! ### The tail estimates -/

/-- Telescoping tail, exact form: `Σ_{d₀<d≤n} 1/d² ≤ 1/d₀ − 1/n`. -/
theorem sum_inv_sq_Ioc_le_sub {d₀ : ℕ} (h : 1 ≤ d₀) {n : ℕ} (hn : d₀ ≤ n) :
    ∑ d ∈ Finset.Ioc d₀ n, (1 : ℝ) / ((d : ℝ) * (d : ℝ))
      ≤ 1 / (d₀ : ℝ) - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show Finset.Ioc d₀ d₀ = ∅ from Finset.Ioc_eq_empty (by omega)]
    simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := le_trans h hn
      exact_mod_cast this
    have hlast : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
        ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [div_sub_div _ _ (by positivity) (by push_cast; positivity),
        div_le_div_iff₀ (by push_cast; positivity)
          (by push_cast; positivity)]
      push_cast
      nlinarith
    have hstep := add_le_add ih hlast
    calc (∑ d ∈ Finset.Ioc d₀ n, (1 : ℝ) / ((d : ℝ) * (d : ℝ)))
          + (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
        ≤ (1 / (d₀ : ℝ) - 1 / (n : ℝ))
          + (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := hstep
      _ = 1 / (d₀ : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by ring

/-- Telescoping tail: `Σ_{d₀<d≤n} 1/d² ≤ 1/d₀`. -/
theorem sum_inv_sq_Ioc_le {d₀ : ℕ} (h : 1 ≤ d₀) (n : ℕ) :
    ∑ d ∈ Finset.Ioc d₀ n, (1 : ℝ) / ((d : ℝ) * (d : ℝ))
      ≤ 1 / (d₀ : ℝ) := by
  rcases Nat.lt_or_ge n d₀ with hn | hn
  · rw [show Finset.Ioc d₀ n = ∅ from Finset.Ioc_eq_empty (by omega)]
    simp
  · have h1 := sum_inv_sq_Ioc_le_sub h hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have h2 : 1 ≤ n := le_trans h hn
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h2
    have h3 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith

/-- Full inverse-square partial sum: `Σ_{1≤d≤n} 1/d² ≤ 2`. -/
theorem sum_inv_sq_Icc_le (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / ((d : ℝ) * (d : ℝ)) ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsplit : Finset.Icc 1 n = insert 1 (Finset.Ioc 1 n) := by
    ext k
    rw [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Ioc]; omega)]
  have h1 := sum_inv_sq_Ioc_le (le_refl 1) n
  norm_num at h1 ⊢
  linarith

/-! ### Trivial bounds -/

theorem abs_moebius_le_one (n : ℕ) : |(moebius n : ℝ)| ≤ 1 := by
  by_cases hsf : Squarefree n
  · rw [moebius_apply_of_squarefree hsf]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [moebius_eq_zero_of_not_squarefree hsf]
    norm_num

theorem abs_liouville_sum_le (y : ℕ) :
    |∑ a ∈ Finset.Icc 1 y, ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
      ≤ (y : ℝ) := by
  calc |∑ a ∈ Finset.Icc 1 y, ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
      ≤ ∑ a ∈ Finset.Icc 1 y,
          |((ArithmeticFunction.liouville a : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.Icc 1 y, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have ha0 : a ≠ 0 := by
          have := (Finset.mem_Icc.mp ha).1
          omega
        rw [ArithmeticFunction.liouville_apply ha0]
        push_cast
        rw [abs_pow, abs_neg, abs_one, one_pow]
    _ = ((Finset.Icc 1 y).card : ℝ) := by rw [Finset.sum_const]; simp
    _ ≤ (y : ℝ) := by
        rw [Nat.card_Icc]
        have h1 : y + 1 - 1 = y := by omega
        rw [h1]

/-! ### THE MERTENS CANCELLATION -/

/-- **`M(x) = o(x)`** — the Möbius partial sums cancel (the classical
Mertens PNT-equivalent), UNCONDITIONAL, from the campaign's Liouville
cancellation through the square-scale representation. -/
theorem moebius_partialSum_tendsto :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (moebius n : ℝ)) / x)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hLev := Metric.tendsto_nhds.mp liouville_partialSum_tendsto
    (ε / 8) (by positivity)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hLev
  set Y₁ : ℕ := ⌈max Y₀ 1⌉₊ with hY₁def
  have hLnat : ∀ y : ℕ, Y₁ ≤ y →
      |∑ a ∈ Finset.Icc 1 y, ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
        ≤ ε / 8 * y := by
    intro y hy
    have hyR : Y₀ ≤ (y : ℝ) := by
      calc Y₀ ≤ max Y₀ 1 := le_max_left _ _
        _ ≤ (Y₁ : ℝ) := Nat.le_ceil _
        _ ≤ (y : ℝ) := by exact_mod_cast hy
    have hy1 : (1 : ℝ) ≤ (y : ℝ) := by
      calc (1 : ℝ) ≤ max Y₀ 1 := le_max_right _ _
        _ ≤ (Y₁ : ℝ) := Nat.le_ceil _
        _ ≤ (y : ℝ) := by exact_mod_cast hy
    have h := hY₀ (y : ℝ) hyR
    rw [Real.dist_eq, sub_zero, Nat.floor_natCast] at h
    have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
    rw [abs_div, abs_of_pos hy0, div_lt_iff₀ hy0] at h
    exact le_of_lt h
  set d₀ : ℕ := max 1 ⌈8 / ε⌉₊ with hd₀def
  have hd₀1 : 1 ≤ d₀ := le_max_left _ _
  have hd₀ε : 8 / ε ≤ (d₀ : ℝ) := by
    calc (8 : ℝ) / ε ≤ (⌈8 / ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (d₀ : ℝ) := by exact_mod_cast le_max_right _ _
  have hMnat : ∀ X : ℕ, Y₁ * (d₀ * d₀) ≤ X →
      |∑ n ∈ Finset.Icc 1 X, (moebius n : ℝ)| ≤ ε / 2 * X := by
    intro X hX
    have hXR : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
    have hrep := moebius_sum_eq_liouville_sums X
    have hrepR : ∑ n ∈ Finset.Icc 1 X, (moebius n : ℝ)
        = ∑ d ∈ Finset.Icc 1 (Nat.sqrt X),
            (moebius d : ℝ) * (∑ a ∈ Finset.Icc 1 (X / (d * d)),
              ((ArithmeticFunction.liouville a : ℤ) : ℝ)) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hrep
      push_cast at h
      exact h
    rw [hrepR]
    have habs : |∑ d ∈ Finset.Icc 1 (Nat.sqrt X),
        (moebius d : ℝ) * (∑ a ∈ Finset.Icc 1 (X / (d * d)),
          ((ArithmeticFunction.liouville a : ℤ) : ℝ))|
        ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt X),
            |∑ a ∈ Finset.Icc 1 (X / (d * d)),
              ((ArithmeticFunction.liouville a : ℤ) : ℝ)| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun d _ => ?_
      rw [abs_mul]
      calc |(moebius d : ℝ)| * |∑ a ∈ Finset.Icc 1 (X / (d * d)),
            ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
          ≤ 1 * |∑ a ∈ Finset.Icc 1 (X / (d * d)),
              ((ArithmeticFunction.liouville a : ℤ) : ℝ)| :=
            mul_le_mul_of_nonneg_right (abs_moebius_le_one d) (abs_nonneg _)
        _ = _ := one_mul _
    refine le_trans habs ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (Nat.sqrt X))
      (fun d => d ≤ d₀)]
    have hsmall : ∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ≤ d₀),
        |∑ a ∈ Finset.Icc 1 (X / (d * d)),
          ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
        ≤ ε / 4 * X := by
      have hterm : ∀ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter
          (fun d => d ≤ d₀),
          |∑ a ∈ Finset.Icc 1 (X / (d * d)),
            ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
            ≤ ε / 8 * X * (1 / ((d : ℝ) * (d : ℝ))) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, _⟩, hdd₀⟩ := hd
        have hdd : d * d ≤ d₀ * d₀ := Nat.mul_le_mul hdd₀ hdd₀
        have hscale : Y₁ ≤ X / (d * d) := by
          rw [Nat.le_div_iff_mul_le (by positivity)]
          calc Y₁ * (d * d) ≤ Y₁ * (d₀ * d₀) :=
              Nat.mul_le_mul_left _ hdd
            _ ≤ X := hX
        have hL := hLnat (X / (d * d)) hscale
        refine le_trans hL ?_
        have hcast : ((X / (d * d) : ℕ) : ℝ)
            ≤ (X : ℝ) / ((d : ℝ) * (d : ℝ)) := by
          have h1 : ((X / (d * d) : ℕ) : ℝ) ≤ (X : ℝ) / ((d * d : ℕ) : ℝ) :=
            Nat.cast_div_le
          have h2 : ((d * d : ℕ) : ℝ) = (d : ℝ) * (d : ℝ) := by
            push_cast
            ring
          rw [h2] at h1
          exact h1
        calc ε / 8 * ((X / (d * d) : ℕ) : ℝ)
            ≤ ε / 8 * ((X : ℝ) / ((d : ℝ) * (d : ℝ))) :=
              mul_le_mul_of_nonneg_left hcast (by positivity)
          _ = ε / 8 * X * (1 / ((d : ℝ) * (d : ℝ))) := by ring
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      have hsub : ∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ≤ d₀),
          (1 : ℝ) / ((d : ℝ) * (d : ℝ))
          ≤ ∑ d ∈ Finset.Icc 1 d₀, (1 : ℝ) / ((d : ℝ) * (d : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun d _ _ => by positivity)
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        rw [Finset.mem_Icc]
        exact ⟨hd.1.1, hd.2⟩
      calc ε / 8 * (X : ℝ) * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter
            (fun d => d ≤ d₀), (1 : ℝ) / ((d : ℝ) * (d : ℝ))
          ≤ ε / 8 * (X : ℝ) * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact le_trans hsub (sum_inv_sq_Icc_le d₀)
        _ = ε / 4 * X := by ring
    have hlarge : ∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter
        (fun d => ¬(d ≤ d₀)),
        |∑ a ∈ Finset.Icc 1 (X / (d * d)),
          ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
        ≤ ε / 8 * X := by
      have hterm : ∀ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter
          (fun d => ¬(d ≤ d₀)),
          |∑ a ∈ Finset.Icc 1 (X / (d * d)),
            ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
            ≤ (X : ℝ) * (1 / ((d : ℝ) * (d : ℝ))) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        refine le_trans (abs_liouville_sum_le _) ?_
        have hcast : ((X / (d * d) : ℕ) : ℝ)
            ≤ (X : ℝ) / ((d : ℝ) * (d : ℝ)) := by
          have h1 : ((X / (d * d) : ℕ) : ℝ) ≤ (X : ℝ) / ((d * d : ℕ) : ℝ) :=
            Nat.cast_div_le
          have h2 : ((d * d : ℕ) : ℝ) = (d : ℝ) * (d : ℝ) := by
            push_cast
            ring
          rw [h2] at h1
          exact h1
        calc ((X / (d * d) : ℕ) : ℝ)
            ≤ (X : ℝ) / ((d : ℝ) * (d : ℝ)) := hcast
          _ = (X : ℝ) * (1 / ((d : ℝ) * (d : ℝ))) := by ring
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      have hsub : ∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter
          (fun d => ¬(d ≤ d₀)), (1 : ℝ) / ((d : ℝ) * (d : ℝ))
          ≤ ∑ d ∈ Finset.Ioc d₀ (Nat.sqrt X),
              (1 : ℝ) / ((d : ℝ) * (d : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun d _ _ => by positivity)
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        rw [Finset.mem_Ioc]
        omega
      have htail := sum_inv_sq_Ioc_le hd₀1 (Nat.sqrt X)
      have hd₀inv : (1 : ℝ) / (d₀ : ℝ) ≤ ε / 8 := by
        have hd₀0 : (0 : ℝ) < (d₀ : ℝ) := by
          have h1 : (1 : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast hd₀1
          linarith
        rw [div_le_iff₀ hd₀0]
        calc (1 : ℝ) = ε / 8 * (8 / ε) := by field_simp
          _ ≤ ε / 8 * d₀ :=
            mul_le_mul_of_nonneg_left hd₀ε (by positivity)
      calc (X : ℝ) * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter
            (fun d => ¬(d ≤ d₀)), (1 : ℝ) / ((d : ℝ) * (d : ℝ))
          ≤ (X : ℝ) * (1 / (d₀ : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hXR
            exact le_trans hsub htail
        _ ≤ (X : ℝ) * (ε / 8) :=
            mul_le_mul_of_nonneg_left hd₀inv hXR
        _ = ε / 8 * X := by ring
    calc (∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ≤ d₀),
          |∑ a ∈ Finset.Icc 1 (X / (d * d)),
            ((ArithmeticFunction.liouville a : ℤ) : ℝ)|)
        + ∑ d ∈ (Finset.Icc 1 (Nat.sqrt X)).filter (fun d => ¬(d ≤ d₀)),
            |∑ a ∈ Finset.Icc 1 (X / (d * d)),
              ((ArithmeticFunction.liouville a : ℤ) : ℝ)|
        ≤ ε / 4 * X + ε / 8 * X := add_le_add hsmall hlarge
      _ ≤ ε / 2 * X := by nlinarith
  refine ⟨max ((Y₁ * (d₀ * d₀) : ℕ) : ℝ) 1 + 1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ max ((Y₁ * (d₀ * d₀) : ℕ) : ℝ) 1 := le_max_right _ _
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hfl : Y₁ * (d₀ * d₀) ≤ ⌊x⌋₊ := by
    have h1 : ((Y₁ * (d₀ * d₀) : ℕ) : ℝ) ≤ x - 1 := by
      have h2 := le_max_left ((Y₁ * (d₀ * d₀) : ℕ) : ℝ) 1
      linarith
    have h2 : ((Y₁ * (d₀ * d₀) : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      have hfl1 : x - 1 < (⌊x⌋₊ : ℝ) := by
        linarith [Nat.lt_floor_add_one x]
      linarith
    exact_mod_cast h2
  have hM := hMnat ⌊x⌋₊ hfl
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hx0, div_lt_iff₀ hx0]
  have hflx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (le_of_lt hx0)
  calc |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (moebius n : ℝ)|
      ≤ ε / 2 * (⌊x⌋₊ : ℝ) := hM
    _ ≤ ε / 2 * x := mul_le_mul_of_nonneg_left hflx (by positivity)
    _ < ε * x := by nlinarith

end Analytic
end EuclidsPath
