/-
  GeometricDiagonalCovariance — the diagonal (p = q) covariance of the two wings, made
  UNCONDITIONAL and EXACT.  The one genuine forward micro-advance of the geometric pass.

  ORIGIN (user's geometric program, §XXVI §44 of `geometric_twin_prime_program_full.md`):
  the normal curvature of the twin problem is Σ_{p,q} Cov(D_p^-, D_q^+); its diagonal part
  (p = q) was marked [B] (conditional on a one-prime density estimate).  Here it is made
  [A]: for p ≥ 5 the two wing-indicators NEVER coincide (their product is identically
  zero), so the diagonal covariance is EXACTLY minus the product of the marginals — a
  sign-definite quantity with no positive part — and over a full residue period it equals
  −1/p² exactly, with no error term.  This DISCHARGES §44's conditional label and isolates
  the entire remaining barrier into the off-diagonal p ≠ q term (§45/§81).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `Dwing_mul_zero` — for p ≥ 5 the wing-indicators satisfy D⁻·D⁺ = 0 pointwise
      (the wings never coincide: p ∤ 2);
    * `diag_energy_zero` — hence the diagonal "energy" Σ w·D⁻·D⁺ = 0 for any weighting;
    * `diag_cov_eq_neg_prod` — the diagonal covariance is EXACTLY −E[D⁻]·E[D⁺];
    * `wing_marginal_minus/plus` — over a full residue period each wing is hit exactly once;
    * `diag_cov_period_exact` — the period-exact diagonal covariance is −1/p² (no error);
    * `inv_sq_le_telescope` — 1/p² ≤ 1/(p−1) − 1/p, so the diagonal sum telescopes
      (summable / o(1) tail) — honest, no `o(1)` inside a badged statement.

  DISCLOSURE.  This is a real sharpening of the TARGET, NOT a move of the twin wall: the
  diagonal is a convergent, sign-definite O(1) piece and was never the wall (the wall is
  the off-diagonal §45/§81 two-prime mixing, still 🔴 — see `GeometricRouteClassification`).
  twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace DiagCov

open scoped BigOperators

/-- The lower-wing indicator `D⁻(k) = 1_{p | 6k−1}`, as a residue condition on `ZMod p`. -/
def Dminus (p : ℕ) (k : ZMod p) : ℝ := if (6 * k - 1 : ZMod p) = 0 then 1 else 0

/-- The upper-wing indicator `D⁺(k) = 1_{p | 6k+1}`. -/
def Dplus (p : ℕ) (k : ZMod p) : ℝ := if (6 * k + 1 : ZMod p) = 0 then 1 else 0

/-! ## The wings never coincide (§44) -/

/-- **Wings never coincide (§44).** For `p ≥ 5` the two wing-indicators have product zero:
    `p` cannot divide both `6k−1` and `6k+1` (their difference is `2`). -/
theorem Dwing_mul_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (k : ZMod p) :
    Dminus p k * Dplus p k = 0 := by
  unfold Dminus Dplus
  by_cases hA : (6 * k - 1 : ZMod p) = 0
  · by_cases hB : (6 * k + 1 : ZMod p) = 0
    · exfalso
      have h2 : (2 : ZMod p) = 0 := by linear_combination hB - hA
      have hdvd : p ∣ 2 := by
        have hc : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
        exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hc
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · simp [hB]
  · simp [hA]

/-! ## The exact diagonal covariance (§44) -/

/-- **Diagonal energy is zero (§44).** For any weighting, the diagonal energy vanishes. -/
theorem diag_energy_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (w : ZMod p → ℝ) :
    ∑ k : ZMod p, w k * (Dminus p k * Dplus p k) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  rw [Dwing_mul_zero hp5 k, mul_zero]

/-- **Exact diagonal covariance (§44 [B]→[A]).** The diagonal covariance of the two wings
    is EXACTLY minus the product of the marginals — sign-definite, with no positive part —
    UNCONDITIONALLY.  (Here `E[f] = (∑ f)/p` is the uniform-period expectation.) -/
theorem diag_cov_eq_neg_prod {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ k : ZMod p, (Dminus p k * Dplus p k)) / p
        - ((∑ k : ZMod p, Dminus p k) / p) * ((∑ k : ZMod p, Dplus p k) / p)
      = - (((∑ k : ZMod p, Dminus p k) / p) * ((∑ k : ZMod p, Dplus p k) / p)) := by
  have h0 : ∑ k : ZMod p, (Dminus p k * Dplus p k) = 0 := by
    have := diag_energy_zero hp5 (fun _ => (1 : ℝ))
    simpa using this
  rw [h0]
  simp

/-! ## The period marginals and the exact −1/p² (§44) -/

/-- A single wing residue class is hit exactly once per period. -/
theorem wing_sum_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a : ZMod p) :
    ∑ k : ZMod p, (if 6 * k + a = 0 then (1 : ℝ) else 0) = 1 := by
  have hp : p.Prime := Fact.out
  have h6 : (6 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 6) := by
      intro hdvd
      have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases p
      · exact absurd hdvd (by decide)
      · exact absurd hp (by decide)
    have h60 : ((6 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 6]; exact hnd
    simpa using h60
  rw [Finset.sum_boole]
  have hfilter : (Finset.univ.filter (fun k : ZMod p => 6 * k + a = 0)) = {(-a) / 6} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      rw [eq_div_iff h6]
      linear_combination hk
    · intro hk
      subst hk
      field_simp
      ring
  rw [hfilter, Finset.card_singleton, Nat.cast_one]

/-- **Wing marginal (§44).** Over a full residue period the lower wing is hit exactly once. -/
theorem wing_marginal_minus {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k : ZMod p, Dminus p k = 1 := by
  unfold Dminus
  simp only [sub_eq_add_neg]
  exact wing_sum_one hp5 (-1)

/-- **Wing marginal (§44).** Over a full residue period the upper wing is hit exactly once. -/
theorem wing_marginal_plus {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k : ZMod p, Dplus p k = 1 := by
  unfold Dplus
  exact wing_sum_one hp5 1

/-- **Period-exact diagonal covariance (§44 [B]→[A]).** Over a full residue period the
    diagonal covariance is `−1/p²` EXACTLY, with no error term.  This is the honest
    unconditional replacement for §44's conditional one-prime density input. -/
theorem diag_cov_period_exact {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ k : ZMod p, (Dminus p k * Dplus p k)) / p
        - ((∑ k : ZMod p, Dminus p k) / p) * ((∑ k : ZMod p, Dplus p k) / p)
      = - 1 / (p : ℝ) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := by
    have : 0 < p := hp.pos
    positivity
  rw [diag_cov_eq_neg_prod hp5, wing_marginal_minus hp5, wing_marginal_plus hp5]
  field_simp

/-! ## The diagonal tail telescopes (§44) -/

/-- **Summable diagonal (§44).** `1/p² ≤ 1/(p−1) − 1/p`, so the diagonal sum telescopes:
    the diagonal contribution is `O(1)` with an `o(1)` tail (kept in prose, not badged). -/
theorem inv_sq_le_telescope {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
  have hpp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have key : 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) = 1 / (((p : ℝ) - 1) * p) := by
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le (mul_pos h1 hp0)
  nlinarith [hpp]

end DiagCov
end Geometric
end EuclidsPath
