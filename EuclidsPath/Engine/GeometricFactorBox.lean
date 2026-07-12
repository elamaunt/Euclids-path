/-
  GeometricFactorBox — the factor-box polynomial, its volume, its discriminant, and the
  hyperbolic shape (anisotropy) of a semiprime.

  ORIGIN (user's geometric program, §XXVII / §XXVIII of
  `geometric_twin_prime_program_full.md`): a number n = q₁⋯qᵣ (with multiplicity) is a
  hyperbox B_n = ∏[0, 1/qᵢ] of volume 1/n and dimension Ω(n); its geometric polynomial
  Φ_n(u) = ∏(1 + qᵢ u) has discriminant ∏_{i<j}(qᵢ−qⱼ)² (a Vandermonde square), so the
  BALANCED locus qᵢ = qⱼ is the multiple-root locus.  For a semiprime the shape
  anisotropy is I₂ = cosh(d/2), d = |log(q/p)|.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `factorBox_volume` — ∏(1/qᵢ) = 1/∏ qᵢ (Vol B_n = 1/n);
    * `factorBoxPoly_eval_zero` — Φ_n(0) = 1; `factorBox_single_natDegree` — a prime
      (single factor) gives a degree-1 factor box;
    * `factorBoxPoly_semiprime` — Φ_{pq}(u) = 1 + (p+q)u + (pq)u²;
    * `factorBox_disc_semiprime` — the discriminant (p+q)² − 4·pq = (p−q)² and
      `factorBox_balanced_iff` — it vanishes iff p = q (the balanced / multiple-root
      locus);
    * `vandermonde_sq` — the discriminant shape ∏_{i<j}(vⱼ−vᵢ)² is the square of the
      Vandermonde determinant;
    * `anisotropy2_eq_cosh` — I₂ = cosh(½ log(q/p)); `anisotropy2_ge_one` — I₂ ≥ 1.

  DISCLOSURE.  Pure geometry of factorization shape.  It classifies the SHAPE of composite
  defects (near-balanced semiprimes sit at the isoperimetric diagonal) but does not force
  both sides of a center to be prime.  Nothing here feeds the wall.  twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace FactorBox

open Polynomial

/-! ## The factor-box polynomial and its volume (§46–47) -/

/-- The factor-box polynomial `Φ_n(u) = ∏ (1 + qᵢ u)`. -/
noncomputable def factorBoxPoly (qs : List ℝ) : ℝ[X] :=
  (qs.map (fun q => 1 + Polynomial.C q * Polynomial.X)).prod

/-- **Factor-box volume (§46).** `∏ (1/qᵢ) = 1/∏ qᵢ`: the box `B_n = ∏[0,1/qᵢ]` has volume
    `1/n`. -/
theorem factorBox_volume (qs : List ℝ) :
    (qs.map (fun q => q⁻¹)).prod = (qs.prod)⁻¹ := by
  induction qs with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, mul_inv]

/-- **Constant term (§47).** `Φ_n(0) = 1`. -/
theorem factorBoxPoly_eval_zero (qs : List ℝ) : (factorBoxPoly qs).eval 0 = 1 := by
  unfold factorBoxPoly
  induction qs with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **Prime ⟹ degree one (§47).** A prime (a single factor) gives a degree-1 factor box. -/
theorem factorBox_single_natDegree {q : ℝ} (hq : q ≠ 0) :
    (factorBoxPoly [q]).natDegree = 1 := by
  unfold factorBoxPoly
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [add_comm, ← Polynomial.C_1]
  exact Polynomial.natDegree_linear hq

/-- **Semiprime expansion (§48).** `Φ_{pq}(u) = 1 + (p+q)u + (pq)u²`. -/
theorem factorBoxPoly_semiprime (p q : ℝ) :
    factorBoxPoly [p, q]
      = 1 + Polynomial.C (p + q) * X + Polynomial.C (p * q) * X ^ 2 := by
  unfold factorBoxPoly
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Polynomial.C_add, Polynomial.C_mul]
  ring

/-! ## The discriminant is a Vandermonde square (§48) -/

/-- **Semiprime discriminant (§48).** The discriminant `b² − 4ac` of the quadratic factor
    box `pq·u² + (p+q)·u + 1` equals `(p−q)²`. -/
theorem factorBox_disc_semiprime (p q : ℝ) :
    (p + q) ^ 2 - 4 * (p * q) = (p - q) ^ 2 := by ring

/-- **Balanced locus (§48).** The semiprime discriminant vanishes exactly on the balanced
    locus `p = q` (the multiple-root locus). -/
theorem factorBox_balanced_iff (p q : ℝ) :
    (p + q) ^ 2 - 4 * (p * q) = 0 ↔ p = q := by
  rw [factorBox_disc_semiprime, pow_eq_zero_iff (two_ne_zero), sub_eq_zero]

/-- **Discriminant = Vandermonde² (§48).** The discriminant shape `∏_{i<j} (vⱼ−vᵢ)²` is the
    square of the Vandermonde determinant. -/
theorem vandermonde_sq {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.vandermonde v).det ^ 2
      = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) ^ 2 := by
  rw [Matrix.det_vandermonde, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_pow]

/-! ## Hyperbolic shape of a semiprime (§52) -/

/-- The semiprime shape anisotropy `I₂ = (p+q)/(2√(pq))`. -/
noncomputable def anisotropy2 (p q : ℝ) : ℝ := (p + q) / (2 * Real.sqrt (p * q))

/-- **Hyperbolic shape (§52).** `I₂ = cosh(½ log(q/p))`. -/
theorem anisotropy2_eq_cosh {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    anisotropy2 p q = Real.cosh (Real.log (q / p) / 2) := by
  have hexp : ∀ a : ℝ, 0 < a → Real.exp (Real.log a / 2) = Real.sqrt a := by
    intro a ha
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha, mul_one_div]
  have harg : -(Real.log (q / p) / 2) = Real.log (p / q) / 2 := by
    rw [Real.log_div hq.ne' hp.ne', Real.log_div hp.ne' hq.ne']
    ring
  rw [Real.cosh_eq, anisotropy2, hexp (q / p) (div_pos hq hp), harg,
    hexp (p / q) (div_pos hp hq), Real.sqrt_div hq.le, Real.sqrt_div hp.le,
    Real.sqrt_mul hp.le]
  have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsq : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsp2 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have hsq2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  field_simp
  nlinarith [hsp2, hsq2, hsp, hsq]

/-- **Shape is at least round (§51/§52).** `I₂ ≥ 1` (AM–GM). -/
theorem anisotropy2_ge_one {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    1 ≤ anisotropy2 p q := by
  have hsp2 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have hsq2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  have hs : (0 : ℝ) < Real.sqrt (p * q) := Real.sqrt_pos.mpr (mul_pos hp hq)
  have hpq : Real.sqrt (p * q) = Real.sqrt p * Real.sqrt q := Real.sqrt_mul hp.le q
  rw [anisotropy2, le_div_iff₀ (by positivity), one_mul]
  nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q), hsp2, hsq2, hpq]

end FactorBox
end Geometric
end EuclidsPath
