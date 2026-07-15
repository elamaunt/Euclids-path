/-
  GeometricTypeIIProjection — the exact local Type-I projection Y_p = G_p + Z_p and the
  two-row diagonal covariance.

  ORIGIN (parity_wall dossier §35 / §113): after conditioning the local prime-survival
  field `Y_p` on the divisibility coordinate one gets the Type-I part `G_p` and a pure
  residual `Z_p = Y_p − G_p` with zero mean.  For two rows `m₁,m₂` the wing-indicators
  `D_i(n) = 1_{p | m_i n + 2}` have EXACTLY negative covariance `−1/p²` (survival form
  `−1/(p−1)²`), a genuine summability gain (`Σ 1/(p−1)² < ∞`).  This generalizes the single
  twin-center diagonal of `Geometric.DiagCov` to two arbitrary rows.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `Drow_mul_zero` — for distinct rows the two forbidden classes never coincide, so
      `D₁·D₂ = 0` pointwise;
    * `row_sum_one` — each wing residue class is hit exactly once per period;
    * `two_row_cov` — `E[(D₁−1/p)(D₂−1/p)] = −1/p²` EXACTLY (§113.1);
    * `two_row_cov_survival` — the survival fields satisfy `E[(Y₁−1)(Y₂−1)] = −1/(p−1)²`
      (§113.2), a summability gain (`two_row_summability`);
    * `Zp_mean_zero` — the pure residual `Z_p = Y_p − G_p` has zero mean (the "pure
      nonprincipal residual").

  DISCLOSURE. These are exact local identities; on the full CRT they annihilate the first
  parity-divergent layer, but the interval transfer is the open target (`Geometric.TypeII`
  map → `CRE`). Nothing here proves twins. twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-- The row wing-indicator `D(a, n) = 1_{a·n + 2 ≡ 0 (mod p)}` (row `a = m mod p`). -/
def Drow {p : ℕ} (a n : ZMod p) : ℝ := if a * n + 2 = 0 then 1 else 0

/-! ## Two forbidden classes never coincide (§113) -/

/-- **Rows never coincide (§113).** For `2 < p` prime and distinct rows `a ≠ b`, the two
    wing-indicators have product zero: the forbidden classes `n ≡ −2a⁻¹`, `n ≡ −2b⁻¹` differ. -/
theorem Drow_mul_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p} (hab : a ≠ b)
    (n : ZMod p) : Drow a n * Drow b n = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
      intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
    simpa using this
  unfold Drow
  by_cases hA : a * n + 2 = 0
  · by_cases hB : b * n + 2 = 0
    · exfalso
      have hab0 : (a - b) * n = 0 := by linear_combination hA - hB
      rcases mul_eq_zero.mp hab0 with h | h
      · exact hab (by rwa [sub_eq_zero] at h)
      · rw [h, mul_zero, zero_add] at hA; exact h2 hA
    · simp [hB]
  · simp [hA]

/-! ## Marginals and the exact covariance (§113.1) -/

/-- **Row marginal (§113).** Over a full residue period the wing is hit exactly once. -/
theorem row_sum_one {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    ∑ n : ZMod p, Drow a n = 1 := by
  unfold Drow
  rw [Finset.sum_boole]
  have hfilter : (Finset.univ.filter (fun n : ZMod p => a * n + 2 = 0)) = {(-2) / a} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [eq_div_iff ha]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  rw [hfilter, Finset.card_singleton, Nat.cast_one]

/-- **Diagonal energy is zero (§113).** For distinct rows the product energy vanishes. -/
theorem two_row_energy_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p} (hab : a ≠ b) :
    ∑ n : ZMod p, Drow a n * Drow b n = 0 :=
  Finset.sum_eq_zero fun n _ => Drow_mul_zero hp2 hab n

/-- **Exact two-row covariance (§113.1).** `E[(D₁−1/p)(D₂−1/p)] = −1/p²`, unconditionally. -/
theorem two_row_cov {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (∑ n : ZMod p, Drow a n * Drow b n) / p
        - ((∑ n : ZMod p, Drow a n) / p) * ((∑ n : ZMod p, Drow b n) / p)
      = - 1 / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : 0 < p := by omega
    positivity
  rw [two_row_energy_zero hp2 hab, row_sum_one ha, row_sum_one hb]
  field_simp
  ring

/-! ## The centered survival energy and the summability gain (§113.2) -/

/-- The centered wing energy `Σ (D₁−1/p)(D₂−1/p) = −1/p`. -/
theorem centered_energy_sum {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∑ n : ZMod p, (Drow a n - 1 / p) * (Drow b n - 1 / p) = - 1 / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : 0 < p := by omega
    positivity
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    simp [ZMod.card]
  have hexp : ∀ n : ZMod p, (Drow a n - 1 / p) * (Drow b n - 1 / p)
      = Drow a n * Drow b n - (1 / p) * Drow b n - (1 / p) * Drow a n + (1 / p) * (1 / p) := by
    intro n; ring
  rw [Finset.sum_congr rfl (fun n _ => hexp n)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    hcard, nsmul_eq_mul]
  rw [two_row_energy_zero hp2 hab, row_sum_one ha, row_sum_one hb]
  field_simp
  ring

/-- The survival field `Y(a,n) = (1 − D)/(1 − 1/p)`. -/
noncomputable def Yrow {p : ℕ} (a n : ZMod p) : ℝ := (1 - Drow a n) * ((p : ℝ) / ((p : ℝ) - 1))

/-- `Y − 1 = −(D − 1/p)/(1 − 1/p)`. -/
theorem Yrow_sub_one {p : ℕ} (hp2 : 2 < p) (a n : ZMod p) :
    Yrow a n - 1 = - (Drow a n - 1 / p) * ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  unfold Yrow
  field_simp
  ring

/-- **Survival covariance (§113.2).** `E[(Y₁−1)(Y₂−1)] = −1/(p−1)²`. -/
theorem two_row_cov_survival {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (∑ n : ZMod p, (Yrow a n - 1) * (Yrow b n - 1)) / p = - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hexp : ∀ n : ZMod p, (Yrow a n - 1) * (Yrow b n - 1)
      = ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 * ((Drow a n - 1 / p) * (Drow b n - 1 / p)) := by
    intro n
    rw [Yrow_sub_one hp2, Yrow_sub_one hp2]; ring
  rw [Finset.sum_congr rfl (fun n _ => hexp n), ← Finset.mul_sum,
    centered_energy_sum hp2 ha hb hab]
  field_simp

/-- **Summability gain (§113.3).** `1/(p−1)² ≤ 1/(p−2) − 1/(p−1)`, so the survival covariance
    telescopes: `Σ_p 1/(p−1)² < ∞`. -/
theorem two_row_summability {p : ℕ} (hp : 3 ≤ p) :
    (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
  have hpp : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le (mul_pos h2 h1)
  nlinarith [hpp]

/-! ## The pure residual Z_p = Y_p − G_p has zero mean (§35) -/

/-- The Type-I projection `G_p = E(Y_p | p | m n)`: `p/(p−1)` on `n ≡ 0`, else `p(p−2)/(p−1)²`. -/
noncomputable def Grow {p : ℕ} (n : ZMod p) : ℝ :=
  if n = 0 then (p : ℝ) / ((p : ℝ) - 1) else (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2

/-- The pure residual `Z_p = Y_p − G_p`. -/
noncomputable def Zrow {p : ℕ} (a n : ZMod p) : ℝ := Yrow a n - Grow n

/-- **Residual mean is zero (§35).** The pure nonprincipal residual has zero full mean. -/
theorem Zrow_mean_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0) :
    ∑ n : ZMod p, Zrow a n = 0 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  have hY : ∑ n : ZMod p, Yrow a n = (p : ℝ) := by
    unfold Yrow
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, hcard, row_sum_one ha,
      nsmul_eq_mul, mul_one]
    field_simp
  have hG : ∑ n : ZMod p, Grow (p := p) n = (p : ℝ) := by
    unfold Grow
    have hsplit : ∀ n : ZMod p,
        (if n = 0 then (p : ℝ) / ((p : ℝ) - 1) else (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2)
          = (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2
            + (if n = 0 then (p : ℝ) / ((p : ℝ) - 1)
                - (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 else 0) := by
      intro n; by_cases h : n = 0 <;> simp [h]
    rw [Finset.sum_congr rfl (fun n _ => hsplit n), Finset.sum_add_distrib, Finset.sum_const,
      hcard, nsmul_eq_mul,
      Finset.sum_ite_eq' Finset.univ (0 : ZMod p)
        (fun _ => (p : ℝ) / ((p : ℝ) - 1) - (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2)]
    simp only [Finset.mem_univ, if_true]
    field_simp
    ring
  unfold Zrow
  rw [Finset.sum_sub_distrib, hY, hG, sub_self]

end TypeII
end Geometric
end EuclidsPath
