/-
  GeometricTypeIIGram — the exact Gram matrix of the residual family `Z_a` and the zero-sum
  isometry: the local parity component.

  ORIGIN (parity_wall Prime-Chaos session dossier §5 / §6 / §7). The row-average of the survival
  field `Y_a` is exactly the Type-I projection `G` (`Grow`), so `Z_a = Y_a − G` annihilates in the
  row direction too (`Σ_{a≠0} Z_a(n) = 0`).  The Gram matrix of the residual family is EXACT:
  `⟨Z_a,Z_a⟩ = p(p−2)/(p−1)³`, `⟨Z_a,Z_b⟩ = −p/(p−1)³` (`a ≠ b`).  Consequently, on the zero-sum
  subspace the family is — up to the scalar `p/(p−1)² ≍ p^{−1}` — an ISOMETRY:
  `‖Σ c_a Z_a‖² = (p/(p−1)²) Σ c_a²`.  So `Zrow_mean_zero` does NOT mean smallness: `Z` is the
  local parity component itself.  The mean mode `G − 1` carries only `p^{−3}` energy
  (`Σ p^{−3} < ∞`), orthogonal to the parity mode (`p^{−1}`, `Σ p^{−1} = ∞`).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `Grow_eq_row_average`, `Zrow_sum_over_a_zero` — `G` is the row-average; `Z` annihilates in `a`;
    * `gram_diag` / `gram_off` — the EXACT Gram entries `p(p−2)/(p−1)³` and `−p/(p−1)³`;
    * `gram_quadratic_form` — `Σ_n (Σ_a c_a Z_a(n))² = (p²/(p−1)³)((p−1)Σc² − (Σc)²)`;
    * `zero_sum_isometry` — on `Σc = 0`, `‖Σ c_a Z_a‖² = (p/(p−1)²) Σ c_a²` (the isometry);
    * `mean_mode_energy` — `‖G − 1‖² = 1/(p−1)³` (the summable `p^{−3}` mean mode);
    * `mean_parity_orthogonal` — `⟨G − 1, Z_a⟩ = 0`.

  DISCLOSURE. These are exact local identities; the parity mode `Z` is the divergent `p^{−1}` layer.
  Nothing here proves twins. twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIProjection

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## Preliminaries -/

private theorem two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) : (2 : ZMod p) ≠ 0 := by
  have : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
  simpa using this

/-- `Drow a 0 = 0`: the forbidden class never sits at `n = 0` (since `2 ≠ 0`). -/
theorem Drow_at_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (a : ZMod p) :
    Drow a (0 : ZMod p) = 0 := by
  unfold Drow
  rw [mul_zero, zero_add, if_neg (two_ne_zero_zmod hp2)]

/-- `Drow 0 n = 0`: the zero row is never forbidden. -/
theorem Drow_zero_left {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (n : ZMod p) :
    Drow (0 : ZMod p) n = 0 := by
  unfold Drow
  rw [zero_mul, zero_add, if_neg (two_ne_zero_zmod hp2)]

/-- **Pointwise residual formula.** `Z_a(n) = (p/(p−1)²)(1 − [n=0]) − (p/(p−1)) D_a(n)`. -/
theorem Zrow_eq {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (a n : ZMod p) :
    Zrow a n = (p : ℝ) / ((p : ℝ) - 1) ^ 2 * (1 - (if n = 0 then (1 : ℝ) else 0))
        - (p : ℝ) / ((p : ℝ) - 1) * Drow a n := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  unfold Zrow Yrow Grow
  by_cases hn : n = 0
  · subst hn
    rw [Drow_at_zero hp2 a]
    simp
  · simp only [if_neg hn]
    field_simp
    ring

/-- `Z_a(0) = 0`. -/
theorem Zrow_at_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (a : ZMod p) :
    Zrow a (0 : ZMod p) = 0 := by
  rw [Zrow_eq hp2 a 0, Drow_at_zero hp2 a]; simp

/-! ## Elementary sum facts -/

private theorem sum_ite_zero_eq {p : ℕ} [Fact p.Prime] (X : ℝ) :
    ∑ n : ZMod p, (if n = 0 then X else 0) = X := by
  rw [Finset.sum_eq_single (0 : ZMod p)]
  · rw [if_pos rfl]
  · intro n _ hn; rw [if_neg hn]
  · intro h; exact absurd (Finset.mem_univ (0 : ZMod p)) h

private theorem sum_1subI0_sq {p : ℕ} [Fact p.Prime] :
    ∑ n : ZMod p, (1 - (if n = 0 then (1 : ℝ) else 0)) * (1 - (if n = 0 then (1 : ℝ) else 0))
      = (p : ℝ) - 1 := by
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  have h : ∀ n : ZMod p,
      (1 - (if n = 0 then (1 : ℝ) else 0)) * (1 - (if n = 0 then (1 : ℝ) else 0))
        = 1 - (if n = 0 then (1 : ℝ) else 0) := by
    intro n; by_cases hn : n = 0 <;> simp [hn]
  rw [Finset.sum_congr rfl (fun n _ => h n), Finset.sum_sub_distrib, sum_ite_zero_eq,
    Finset.sum_const, hcard, nsmul_eq_mul, mul_one]

private theorem sum_1subI0_D {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0) :
    ∑ n : ZMod p, (1 - (if n = 0 then (1 : ℝ) else 0)) * Drow a n = 1 := by
  have h : ∀ n : ZMod p, (1 - (if n = 0 then (1 : ℝ) else 0)) * Drow a n
      = Drow a n - (if n = 0 then (1 : ℝ) else 0) * Drow a n := by intro n; ring
  rw [Finset.sum_congr rfl (fun n _ => h n), Finset.sum_sub_distrib, row_sum_one ha]
  have hI0D : ∑ n : ZMod p, (if n = 0 then (1 : ℝ) else 0) * Drow a n = 0 := by
    apply Finset.sum_eq_zero; intro n _; by_cases hn : n = 0
    · rw [if_pos hn, one_mul, hn, Drow_at_zero hp2 a]
    · rw [if_neg hn, zero_mul]
  rw [hI0D, sub_zero]

private theorem sum_D_sq {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    ∑ n : ZMod p, Drow a n * Drow a n = 1 := by
  have h : ∀ n : ZMod p, Drow a n * Drow a n = Drow a n := by
    intro n; unfold Drow; by_cases hh : a * n + 2 = 0 <;> simp [hh]
  rw [Finset.sum_congr rfl (fun n _ => h n), row_sum_one ha]

/-- **Column sum (§5).** `Σ_a D_a(n) = [n ≠ 0]`. -/
theorem sum_over_a_Drow {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (n : ZMod p) :
    ∑ a : ZMod p, Drow a n = if n = 0 then 0 else 1 := by
  have h2 := two_ne_zero_zmod hp2
  unfold Drow
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro a _
    rw [mul_zero, zero_add, if_neg h2]
  · rw [if_neg hn, Finset.sum_boole]
    have hfilter : (Finset.univ.filter (fun a : ZMod p => a * n + 2 = 0)) = {(-2) / n} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [eq_div_iff hn]
      constructor
      · intro h; linear_combination h
      · intro h; linear_combination h
    rw [hfilter, Finset.card_singleton, Nat.cast_one]

/-! ## Row-average and row-direction annihilation (§5) -/

private theorem card_erase_zero_cast {p : ℕ} [Fact p.Prime] :
    ((Finset.univ.erase (0 : ZMod p)).card : ℝ) = (p : ℝ) - 1 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  have hc : (Finset.univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  rw [hc, Nat.cast_sub hp, Nat.cast_one]

/-- **Residual annihilation in the row direction (§5).** `Σ_{a≠0} Z_a(n) = 0`. -/
theorem Zrow_sum_over_a_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (n : ZMod p) :
    ∑ a ∈ Finset.univ.erase (0 : ZMod p), Zrow a n = 0 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hDsum : ∑ a ∈ Finset.univ.erase (0 : ZMod p), Drow a n = if n = 0 then (0 : ℝ) else 1 := by
    have her : ∑ a ∈ Finset.univ.erase (0 : ZMod p), Drow a n = ∑ a : ZMod p, Drow a n := by
      apply Finset.sum_erase
      exact Drow_zero_left hp2 n
    rw [her]; exact sum_over_a_Drow hp2 n
  rw [Finset.sum_congr rfl (fun a _ => Zrow_eq hp2 a n), Finset.sum_sub_distrib,
    Finset.sum_const, ← Finset.mul_sum, hDsum, nsmul_eq_mul, card_erase_zero_cast]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_neg hn]; field_simp; ring

/-- **Row-average is the Type-I projection (§5).** `G(n) = (1/(p−1)) Σ_{a≠0} Y_a(n)`. -/
theorem Grow_eq_row_average {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (n : ZMod p) :
    Grow (p := p) n = (1 / ((p : ℝ) - 1)) * ∑ a ∈ Finset.univ.erase (0 : ZMod p), Yrow a n := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hYZ : ∀ a : ZMod p, Yrow a n = Zrow a n + Grow (p := p) n := by
    intro a; unfold Zrow; ring
  rw [Finset.sum_congr rfl (fun a _ => hYZ a), Finset.sum_add_distrib,
    Zrow_sum_over_a_zero hp2 n, Finset.sum_const, nsmul_eq_mul, card_erase_zero_cast, zero_add]
  field_simp

/-! ## The exact Gram entries (§6) -/

private theorem zzSum_diag {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0) :
    ∑ n : ZMod p, Zrow a n * Zrow a n = (p : ℝ) ^ 2 * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 3 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  set c : ℝ := (p : ℝ) / ((p : ℝ) - 1) ^ 2 with hc
  set e : ℝ := (p : ℝ) / ((p : ℝ) - 1) with he
  have expand : ∀ n : ZMod p, Zrow a n * Zrow a n
      = c * c * ((1 - (if n = 0 then (1 : ℝ) else 0)) * (1 - (if n = 0 then (1 : ℝ) else 0)))
        - c * e * ((1 - (if n = 0 then (1 : ℝ) else 0)) * Drow a n)
        - c * e * ((1 - (if n = 0 then (1 : ℝ) else 0)) * Drow a n)
        + e * e * (Drow a n * Drow a n) := by
    intro n; rw [Zrow_eq hp2 a n, hc, he]; ring
  have h1 : ∑ n : ZMod p,
      c * c * ((1 - (if n = 0 then (1 : ℝ) else 0)) * (1 - (if n = 0 then (1 : ℝ) else 0)))
        = c * c * ((p : ℝ) - 1) := by rw [← Finset.mul_sum, sum_1subI0_sq]
  have h2 : ∑ n : ZMod p, c * e * ((1 - (if n = 0 then (1 : ℝ) else 0)) * Drow a n)
        = c * e * 1 := by rw [← Finset.mul_sum, sum_1subI0_D hp2 ha]
  have h4 : ∑ n : ZMod p, e * e * (Drow a n * Drow a n) = e * e * 1 := by
    rw [← Finset.mul_sum, sum_D_sq ha]
  rw [Finset.sum_congr rfl (fun n _ => expand n), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2, h4, hc, he]
  field_simp; ring

private theorem zzSum_off {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∑ n : ZMod p, Zrow a n * Zrow b n = -(p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 3 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  set c : ℝ := (p : ℝ) / ((p : ℝ) - 1) ^ 2 with hc
  set e : ℝ := (p : ℝ) / ((p : ℝ) - 1) with he
  have expand : ∀ n : ZMod p, Zrow a n * Zrow b n
      = c * c * ((1 - (if n = 0 then (1 : ℝ) else 0)) * (1 - (if n = 0 then (1 : ℝ) else 0)))
        - c * e * ((1 - (if n = 0 then (1 : ℝ) else 0)) * Drow b n)
        - c * e * ((1 - (if n = 0 then (1 : ℝ) else 0)) * Drow a n)
        + e * e * (Drow a n * Drow b n) := by
    intro n; rw [Zrow_eq hp2 a n, Zrow_eq hp2 b n, hc, he]; ring
  have h1 : ∑ n : ZMod p,
      c * c * ((1 - (if n = 0 then (1 : ℝ) else 0)) * (1 - (if n = 0 then (1 : ℝ) else 0)))
        = c * c * ((p : ℝ) - 1) := by rw [← Finset.mul_sum, sum_1subI0_sq]
  have h2b : ∑ n : ZMod p, c * e * ((1 - (if n = 0 then (1 : ℝ) else 0)) * Drow b n)
        = c * e * 1 := by rw [← Finset.mul_sum, sum_1subI0_D hp2 hb]
  have h2a : ∑ n : ZMod p, c * e * ((1 - (if n = 0 then (1 : ℝ) else 0)) * Drow a n)
        = c * e * 1 := by rw [← Finset.mul_sum, sum_1subI0_D hp2 ha]
  have h4 : ∑ n : ZMod p, e * e * (Drow a n * Drow b n) = e * e * 0 := by
    rw [← Finset.mul_sum, two_row_energy_zero hp2 hab]
  rw [Finset.sum_congr rfl (fun n _ => expand n), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2b, h2a, h4, hc, he]
  field_simp; ring

/-- **Gram diagonal (§6).** `⟨Z_a,Z_a⟩ = p(p−2)/(p−1)³`. -/
theorem gram_diag {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0) :
    (∑ n : ZMod p, Zrow a n * Zrow a n) / p = (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 3 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  rw [zzSum_diag hp2 ha]; field_simp

/-- **Gram off-diagonal (§6).** `⟨Z_a,Z_b⟩ = −p/(p−1)³` for `a ≠ b`. -/
theorem gram_off {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (∑ n : ZMod p, Zrow a n * Zrow b n) / p = -(p : ℝ) / ((p : ℝ) - 1) ^ 3 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  rw [zzSum_off hp2 ha hb hab]; field_simp

/-! ## The zero-sum isometry (§6) -/

private theorem zzSum_val {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ n : ZMod p, Zrow a n * Zrow b n
      = -(p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 3
          + (if a = b then (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 else 0) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  by_cases hab : a = b
  · subst hab
    rw [zzSum_diag hp2 ha, if_pos rfl]; field_simp; ring
  · rw [zzSum_off hp2 ha hb hab, if_neg hab]; ring

/-- **Gram quadratic form (§6).** `Σ_n (Σ_a c_a Z_a(n))² = (p²/(p−1)³)((p−1)Σc² − (Σc)²)`. -/
theorem gram_quadratic_form {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (c : ZMod p → ℝ) :
    ∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) ^ 2
      = ((p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 3)
          * (((p : ℝ) - 1) * (∑ a ∈ Finset.univ.erase (0 : ZMod p), (c a) ^ 2)
              - (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a) ^ 2) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  set s : Finset (ZMod p) := Finset.univ.erase (0 : ZMod p) with hs
  have step : ∑ n : ZMod p, (∑ a ∈ s, c a * Zrow a n) ^ 2
      = ∑ a ∈ s, ∑ b ∈ s, c a * c b * (∑ n : ZMod p, Zrow a n * Zrow b n) := by
    have e1 : ∀ n : ZMod p, (∑ a ∈ s, c a * Zrow a n) ^ 2
        = ∑ a ∈ s, ∑ b ∈ s, c a * c b * (Zrow a n * Zrow b n) := by
      intro n
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring
    rw [Finset.sum_congr rfl (fun n _ => e1 n), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    rw [← Finset.mul_sum]
  rw [step]
  have hsub : ∑ a ∈ s, ∑ b ∈ s, c a * c b * (∑ n : ZMod p, Zrow a n * Zrow b n)
      = (-(p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 3) * (∑ a ∈ s, ∑ b ∈ s, c a * c b)
        + ((p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2)
            * (∑ a ∈ s, ∑ b ∈ s, (if a = b then c a * c b else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b hb
    rw [zzSum_val hp2 (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb)]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab]; ring
    · rw [if_neg hab, if_neg hab]; ring
  rw [hsub]
  have hsq : ∑ a ∈ s, ∑ b ∈ s, c a * c b = (∑ a ∈ s, c a) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  have hdiag : ∑ a ∈ s, ∑ b ∈ s, (if a = b then c a * c b else 0) = ∑ a ∈ s, (c a) ^ 2 := by
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.sum_ite_eq s a (fun b => c a * c b), if_pos ha, pow_two]
  rw [hsq, hdiag]
  field_simp
  ring

/-- **Zero-sum isometry (§6).** On the mean-zero subspace `Σ c_a = 0`, the residual family is an
    isometry up to the scalar `p/(p−1)²`: `‖Σ c_a Z_a‖² = (p/(p−1)²) Σ c_a²`. -/
theorem zero_sum_isometry {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (c : ZMod p → ℝ)
    (hzero : ∑ a ∈ Finset.univ.erase (0 : ZMod p), c a = 0) :
    (∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) ^ 2) / p
      = ((p : ℝ) / ((p : ℝ) - 1) ^ 2) * ∑ a ∈ Finset.univ.erase (0 : ZMod p), (c a) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  rw [gram_quadratic_form hp2 c, hzero]
  field_simp
  ring

/-! ## The mean mode (§7) -/

/-- **Mean mode energy (§7).** `‖G − 1‖² = 1/(p−1)³` — the summable `p^{−3}` mode. -/
theorem mean_mode_energy {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    (∑ n : ZMod p, (Grow (p := p) n - 1) ^ 2) / p = 1 / ((p : ℝ) - 1) ^ 3 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  have hval : ∀ n : ZMod p, (Grow (p := p) n - 1) ^ 2
      = (if n = 0 then (1 / ((p : ℝ) - 1)) ^ 2 else (1 / ((p : ℝ) - 1) ^ 2) ^ 2) := by
    intro n; unfold Grow; by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]; field_simp; ring
    · rw [if_neg hn, if_neg hn]; field_simp; ring
  have hsplit : ∀ n : ZMod p,
      (if n = 0 then (1 / ((p : ℝ) - 1)) ^ 2 else (1 / ((p : ℝ) - 1) ^ 2) ^ 2)
        = (1 / ((p : ℝ) - 1) ^ 2) ^ 2
          + (if n = 0 then (1 / ((p : ℝ) - 1)) ^ 2 - (1 / ((p : ℝ) - 1) ^ 2) ^ 2 else 0) := by
    intro n; by_cases hn : n = 0 <;> simp [hn]
  rw [Finset.sum_congr rfl (fun n _ => hval n), Finset.sum_congr rfl (fun n _ => hsplit n),
    Finset.sum_add_distrib, sum_ite_zero_eq, Finset.sum_const, hcard, nsmul_eq_mul]
  field_simp
  ring

/-- **Mean–parity orthogonality (§7).** `⟨G − 1, Z_a⟩ = 0`. -/
theorem mean_parity_orthogonal {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0) :
    ∑ n : ZMod p, (Grow (p := p) n - 1) * Zrow a n = 0 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hval : ∀ n : ZMod p, (Grow (p := p) n - 1) * Zrow a n
      = (-1 / ((p : ℝ) - 1) ^ 2) * Zrow a n
        + (1 / ((p : ℝ) - 1) + 1 / ((p : ℝ) - 1) ^ 2)
            * ((if n = 0 then (1 : ℝ) else 0) * Zrow a n) := by
    intro n; unfold Grow; by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]; field_simp; ring
    · rw [if_neg hn, if_neg hn]; field_simp; ring
  rw [Finset.sum_congr rfl (fun n _ => hval n), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Zrow_mean_zero hp2 ha]
  have hZ0 : ∑ n : ZMod p, (if n = 0 then (1 : ℝ) else 0) * Zrow a n = 0 := by
    apply Finset.sum_eq_zero; intro n _; by_cases hn : n = 0
    · rw [if_pos hn, one_mul, hn, Zrow_at_zero hp2 a]
    · rw [if_neg hn, zero_mul]
  rw [hZ0]; ring

end TypeII
end Geometric
end EuclidsPath
