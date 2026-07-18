/-
  Tauberian/LaplaceFinite — STAGE N-B of the Tauberian campaign: the finite
  Laplace transform `S_T`, the Newman kernel, and the circle toolbox.

  ORIGIN.  Newman's analytic theorem (stage N-C) compares the finite Laplace
  transform `S_T(z) = ∫_0^T f(t) e^{−zt} dt` of a bounded function with its
  holomorphic extension `g` via Zagier's contour.  This module builds the
  `S_T` layer: `S_T` is ENTIRE (dominated differentiation with a complex
  parameter), the tail `g − S_T` is explicitly bounded on `Re z > 0`, `S_T`
  is bounded on `Re z < 0`, and the Newman kernel `e^{zT}(1 + z²/R²)` obeys
  the EXACT Zagier weight identity `(1 + z²/R²)/z = 2·Re z/R²` on `|z| = R`.
  On top: the full-circle Cauchy formula for `S_T·K` and the splitting of the
  circle into the right and left arcs, plus FTC helpers used by the dented
  contour of N-C.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `laplacePartial` (= `S_T`) with integrability, `S_T(0) = ∫_0^T f`;
    * `differentiable_laplacePartial` — `S_T` is entire;
    * `norm_laplacePartial_le` (left half-plane), `laplace_sub_partial` +
      `norm_laplace_tail_le` (right half-plane tail);
    * `newmanKernel`, `circle_weight_eq` — the exact weight identity,
      `norm_kernel_div_self`;
    * `circle_cauchy_laplacePartial` — `∮ K·S_T/z = 2πi·S_T(0)`;
    * `circleIntegral_eq_rightArc_add_leftArc` — the arc splitting;
    * `arcInt_eq_sub` / `horizInt_eq_sub` / `vertInt_eq_sub` — FTC per piece.

  NUMERIC GROUNDING: `scripts/newman_prepass.py` — ALL CHECKS PASSED
  (weight identity to 1e−12 on random circle points, ledger orientation).

  DISCLOSURES.
    * Pure complex-analytic infrastructure: no arithmetic content, no face
      of the parity wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Tauberian.StadiumPrimitive

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Tauberian

open Complex MeasureTheory Metric Set intervalIntegral
open scoped Interval Real

/-! ### Layer 1: the finite Laplace transform -/

/-- The finite Laplace transform `S_T(z) = ∫_0^T f(t) e^{−zt} dt`
(as a set integral over `Ioc 0 T`, so that `T ≤ 0` gives `0`). -/
noncomputable def laplacePartial (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Set.Ioc 0 T, f t * Complex.exp (-(z * t))

section Bounded

variable {f : ℝ → ℂ} {M : ℝ}
  (hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hf_bdd : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f t‖ ≤ M)

include hf_meas in
/-- The integrand of `S_T` is a.e. strongly measurable on any `Ioc 0 T`. -/
theorem aestronglyMeasurable_laplace_integrand (z : ℂ) (T : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => f t * Complex.exp (-(z * t)))
      (volume.restrict (Set.Ioc 0 T)) := by
  have hsub : volume.restrict (Set.Ioc (0 : ℝ) T) ≤ volume.restrict (Set.Ioi 0) :=
    Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl
  exact (hf_meas.mono_measure hsub).mul
    (Continuous.aestronglyMeasurable (by fun_prop))

include hf_meas hf_bdd in
/-- The integrand of `S_T` is integrable on `Ioc 0 T`. -/
theorem integrableOn_laplacePartial_integrand (z : ℂ) (T : ℝ) :
    IntegrableOn (fun t : ℝ => f t * Complex.exp (-(z * t))) (Set.Ioc 0 T) := by
  refine Integrable.mono' (integrable_const (M * Real.exp (|z.re| * |T|)))
    (aestronglyMeasurable_laplace_integrand hf_meas z T) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul, Complex.norm_exp]
  have h1 : ‖f t‖ ≤ M := hf_bdd t (Set.mem_Ioi.mpr ht.1)
  have h2 : (-(z * t)).re ≤ |z.re| * |T| := by
    have : (-(z * t)).re = -(z.re * t) := by simp
    rw [this]
    have ht0 : 0 < t := ht.1
    have htT : t ≤ |T| := le_trans ht.2 (le_abs_self T)
    calc -(z.re * t) ≤ |z.re| * t := by nlinarith [abs_nonneg z.re, neg_abs_le z.re]
      _ ≤ |z.re| * |T| := by nlinarith [abs_nonneg z.re]
  have h3 : Real.exp (-(z * t)).re ≤ Real.exp (|z.re| * |T|) := Real.exp_le_exp.mpr h2
  have h0 : 0 ≤ ‖f t‖ := norm_nonneg _
  have hM : 0 ≤ M := le_trans h0 h1
  calc ‖f t‖ * Real.exp (-(z * t)).re
      ≤ M * Real.exp (|z.re| * |T|) := by
        exact mul_le_mul h1 h3 (Real.exp_nonneg _) hM

end Bounded

/-- At `z = 0` the finite Laplace transform is the plain integral. -/
theorem laplacePartial_zero {f : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) :
    laplacePartial f T 0 = ∫ t in (0 : ℝ)..T, f t := by
  rw [intervalIntegral.integral_of_le hT]
  unfold laplacePartial
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp

section Bounded

variable {f : ℝ → ℂ} {M : ℝ}
  (hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hf_bdd : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f t‖ ≤ M)

include hf_meas hf_bdd in
/-- **`S_T` is ENTIRE**: dominated differentiation under the integral sign
with a COMPLEX parameter on the finite window `Ioc 0 T`. -/
theorem differentiable_laplacePartial (T : ℝ) :
    Differentiable ℂ (laplacePartial f T) := by
  intro z₀
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hf_bdd 1 (by norm_num))
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => f t * Complex.exp (-(z * t)))
      (volume.restrict (Set.Ioc 0 T)) :=
    fun z => aestronglyMeasurable_laplace_integrand hf_meas z T
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => f t * (Complex.exp (-(z₀ * t)) * (-(t : ℂ))))
      (volume.restrict (Set.Ioc 0 T)) := by
    have hsub : volume.restrict (Set.Ioc (0 : ℝ) T) ≤ volume.restrict (Set.Ioi 0) :=
      Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl
    exact (hf_meas.mono_measure hsub).mul
      (Continuous.aestronglyMeasurable (by fun_prop))
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ x ∈ Metric.ball z₀ 1,
      ‖f t * (Complex.exp (-(x * t)) * (-(t : ℂ)))‖
        ≤ M * (Real.exp ((‖z₀‖ + 1) * |T|) * |T|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
    have ht0 : 0 < t := ht.1
    have htT : t ≤ |T| := le_trans ht.2 (le_abs_self T)
    have hxn : ‖x‖ ≤ ‖z₀‖ + 1 := by
      have h1 : ‖x‖ ≤ ‖z₀‖ + ‖x - z₀‖ := by
        calc ‖x‖ = ‖z₀ + (x - z₀)‖ := by ring_nf
          _ ≤ ‖z₀‖ + ‖x - z₀‖ := norm_add_le _ _
      have h2 : ‖x - z₀‖ < 1 := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hx
      linarith
    have hexp : Real.exp ((-(x * (t : ℂ))).re) ≤ Real.exp ((‖z₀‖ + 1) * |T|) := by
      apply Real.exp_le_exp.mpr
      have hrecalc : (-(x * (t : ℂ))).re = -(x.re * t) := by
        simp [Complex.mul_re]
      rw [hrecalc]
      have hz1 : (0 : ℝ) ≤ ‖z₀‖ + 1 := by positivity
      nlinarith [Complex.abs_re_le_norm x, neg_abs_le x.re]
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg, Complex.norm_real]
    have h1 : ‖f t‖ ≤ M := hf_bdd t (Set.mem_Ioi.mpr ht0)
    have htabs : |t| ≤ |T| := by rw [abs_of_pos ht0]; exact htT
    have h2 : Real.exp ((-(x * (t : ℂ))).re) * |t|
        ≤ Real.exp ((‖z₀‖ + 1) * |T|) * |T| :=
      mul_le_mul hexp htabs (abs_nonneg t) (Real.exp_nonneg _)
    exact mul_le_mul h1 h2 (by positivity) hM
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ x ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z : ℂ => f t * Complex.exp (-(z * t)))
        (f t * (Complex.exp (-(x * t)) * (-(t : ℂ)))) x := by
    refine Filter.Eventually.of_forall fun t x _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => -(z * (t : ℂ))) (-(t : ℂ)) x := by
      simpa [mul_neg] using hasDerivAt_mul_const (x := x) (-(t : ℂ))
    exact (h1.cexp).const_mul (f t)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z (t : ℝ) => f t * Complex.exp (-(z * t)))
    (F' := fun z (t : ℝ) => f t * (Complex.exp (-(z * t)) * (-(t : ℂ))))
    (bound := fun _ => M * (Real.exp ((‖z₀‖ + 1) * |T|) * |T|))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall hmeas)
    (integrableOn_laplacePartial_integrand hf_meas hf_bdd z₀ T)
    hmeas' hbound (integrable_const _) hdiff
  exact key.2.differentiableAt

include hf_meas hf_bdd in
/-- The left-half-plane bound: `‖S_T(z)‖ ≤ M·e^{−Re z·T}/(−Re z)` for `Re z < 0`. -/
theorem norm_laplacePartial_le (hM : 0 ≤ M) {T : ℝ} (hT : 0 ≤ T)
    {z : ℂ} (hz : z.re < 0) :
    ‖laplacePartial f T z‖ ≤ M * Real.exp (-z.re * T) / (-z.re) := by
  have ha : (0 : ℝ) < -z.re := by linarith
  have hnorm : ‖laplacePartial f T z‖
      ≤ ∫ t in Set.Ioc (0 : ℝ) T, M * Real.exp (-z.re * t) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on
      (integrableOn_laplacePartial_integrand hf_meas hf_bdd z T).norm
      (Continuous.integrableOn_Ioc (by fun_prop)) measurableSet_Ioc ?_
    intro t ht
    rw [norm_mul, Complex.norm_exp]
    have h2 : (-(z * (t : ℂ))).re = -z.re * t := by simp [Complex.mul_re]
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hf_bdd t (Set.mem_Ioi.mpr ht.1))
      (Real.exp_nonneg _)
  have hftc : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u : ℝ => Real.exp (-z.re * u) / (-z.re))
        (Real.exp (-z.re * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -z.re * u) (-z.re) x := by
      simpa using (hasDerivAt_id x).const_mul (-z.re)
    have h2 := (Real.hasDerivAt_exp (-z.re * x)).comp x h1
    have h3 := h2.div_const (-z.re)
    have hcancel : Real.exp (-z.re * x) * -z.re / -z.re = Real.exp (-z.re * x) :=
      mul_div_cancel_right₀ _ (ne_of_gt ha)
    rw [hcancel] at h3
    exact h3
  have hval : ∫ t in (0 : ℝ)..T, Real.exp (-z.re * t)
      = Real.exp (-z.re * T) / (-z.re) - Real.exp (-z.re * 0) / (-z.re) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hftc
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hint : ∫ t in Set.Ioc (0 : ℝ) T, M * Real.exp (-z.re * t)
      ≤ M * (Real.exp (-z.re * T) / (-z.re)) := by
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hT, hval]
    have hexp1 : (0 : ℝ) < Real.exp (-z.re * 0) := Real.exp_pos _
    have hdiv : (0 : ℝ) < Real.exp (-z.re * 0) / (-z.re) := by positivity
    nlinarith [Real.exp_pos (-z.re * T)]
  calc ‖laplacePartial f T z‖
      ≤ ∫ t in Set.Ioc (0 : ℝ) T, M * Real.exp (-z.re * t) := hnorm
    _ ≤ M * (Real.exp (-z.re * T) / (-z.re)) := hint
    _ = M * Real.exp (-z.re * T) / (-z.re) := (mul_div_assoc _ _ _).symm

include hf_meas hf_bdd in
/-- The Laplace integrand is integrable on the full half-line for `Re z > 0`. -/
theorem integrableOn_laplace_integrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => f t * Complex.exp (-(z * t))) (Set.Ioi 0) := by
  refine Integrable.mono'
    ((integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) 0).const_mul M)
    (hf_meas.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_exp]
  have h2 : (-(z * (t : ℂ))).re = -z.re * t := by simp [Complex.mul_re]
  rw [h2]
  exact mul_le_mul_of_nonneg_right (hf_bdd t ht) (Real.exp_nonneg _)

include hf_meas hf_bdd in
/-- The representation splits: `g(z) − S_T(z)` is exactly the Laplace tail. -/
theorem laplace_sub_partial {g : ℂ → ℂ}
    (hrep : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (0 : ℝ), f t * Complex.exp (-(z * t)))
    {z : ℂ} (hz : 0 < z.re) {T : ℝ} (hT : 0 ≤ T) :
    g z - laplacePartial f T z = ∫ t in Set.Ioi T, f t * Complex.exp (-(z * t)) := by
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), f t * Complex.exp (-(z * t))
      = (∫ t in Set.Ioc (0 : ℝ) T, f t * Complex.exp (-(z * t)))
        + ∫ t in Set.Ioi T, f t * Complex.exp (-(z * t)) := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi
      ((integrableOn_laplace_integrand hf_meas hf_bdd hz).mono_set
        Set.Ioc_subset_Ioi_self)
      ((integrableOn_laplace_integrand hf_meas hf_bdd hz).mono_set
        (Set.Ioi_subset_Ioi hT)),
      Set.Ioc_union_Ioi_eq_Ioi hT]
  rw [hrep z hz, hsplit]
  unfold laplacePartial
  ring

include hf_meas hf_bdd in
/-- The tail bound: `‖∫_T^∞ f e^{−zt}‖ ≤ M·e^{−Re z·T}/Re z` for `Re z > 0`. -/
theorem norm_laplace_tail_le {z : ℂ} (hz : 0 < z.re) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in Set.Ioi T, f t * Complex.exp (-(z * t))‖
      ≤ M * Real.exp (-z.re * T) / z.re := by
  have hInt : IntegrableOn (fun t : ℝ => f t * Complex.exp (-(z * t))) (Set.Ioi T) :=
    (integrableOn_laplace_integrand hf_meas hf_bdd hz).mono_set
      (Set.Ioi_subset_Ioi hT)
  have h1 : ‖∫ t in Set.Ioi T, f t * Complex.exp (-(z * t))‖
      ≤ ∫ t in Set.Ioi T, M * Real.exp (-z.re * t) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hInt.norm
      ((integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) T).const_mul M)
      measurableSet_Ioi ?_
    intro t ht
    rw [norm_mul, Complex.norm_exp]
    have h2 : (-(z * (t : ℂ))).re = -z.re * t := by simp [Complex.mul_re]
    rw [h2]
    have htpos : (0 : ℝ) < t := lt_of_le_of_lt hT ht
    exact mul_le_mul_of_nonneg_right (hf_bdd t (Set.mem_Ioi.mpr htpos))
      (Real.exp_nonneg _)
  have h2 : ∫ t in Set.Ioi T, M * Real.exp (-z.re * t)
      = M * Real.exp (-z.re * T) / z.re := by
    rw [MeasureTheory.integral_const_mul,
      integral_exp_mul_Ioi (by linarith : -z.re < 0) T]
    ring
  exact h1.trans_eq h2

end Bounded

/-! ### Layer 2: the Newman kernel and the exact weight identity -/

/-- The Newman kernel `e^{zT}(1 + z²/R²)`. -/
noncomputable def newmanKernel (R T : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * T) * (1 + z ^ 2 / (R : ℂ) ^ 2)

@[simp] theorem newmanKernel_zero {R T : ℝ} : newmanKernel R T 0 = 1 := by
  simp [newmanKernel]

theorem differentiable_newmanKernel {R T : ℝ} :
    Differentiable ℂ (newmanKernel R T) := by
  unfold newmanKernel
  fun_prop

theorem continuous_newmanKernel {R T : ℝ} : Continuous (newmanKernel R T) :=
  differentiable_newmanKernel.continuous

/-- **The exact Zagier weight identity**: on the circle `|z| = R` the
weight `(1 + z²/R²)/z` collapses to the REAL quantity `2·Re z/R²`. -/
theorem circle_weight_eq {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ = R)
    (hz0 : z ≠ 0) :
    (1 + z ^ 2 / (R : ℂ) ^ 2) / z = ((2 * z.re : ℝ) : ℂ) / (R : ℂ) ^ 2 := by
  have hR2 : (R : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_cast
  have hadd : z + (starRingEnd ℂ) z = ((2 * z.re : ℝ) : ℂ) := Complex.add_conj z
  have hRne : (R : ℂ) ^ 2 ≠ 0 := by
    have h0 : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
    exact pow_ne_zero 2 h0
  rw [div_eq_div_iff hz0 hRne]
  have expand : (1 + z ^ 2 / (R : ℂ) ^ 2) * (R : ℂ) ^ 2 = (R : ℂ) ^ 2 + z ^ 2 := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hRne]
  rw [expand, hR2]
  linear_combination z * hadd

/-- The norm of the weighted kernel on the circle: for `|z| = R`,
`‖K(z)/z‖ = e^{T·Re z}·2|Re z|/R²` — the ML input for both arc estimates. -/
theorem norm_kernel_div_self {R : ℝ} (hR : 0 < R) (T : ℝ) {z : ℂ}
    (hz : ‖z‖ = R) (hz0 : z ≠ 0) :
    ‖newmanKernel R T z / z‖ = Real.exp (T * z.re) * (2 * |z.re|) / R ^ 2 := by
  unfold newmanKernel
  rw [mul_div_assoc, circle_weight_eq hR hz hz0, norm_mul, Complex.norm_exp,
    norm_div, Complex.norm_real, norm_pow, Complex.norm_real]
  have h1 : (z * (T : ℂ)).re = T * z.re := by
    simp [Complex.mul_re, mul_comm]
  have h2 : |2 * z.re| = 2 * |z.re| := by
    rw [abs_mul]; norm_num
  have h3 : |R| = R := abs_of_pos hR
  rw [h1, Real.norm_eq_abs, Real.norm_eq_abs, h2, h3]
  ring

/-! ### Layer 3: the full-circle Cauchy formula for `S_T·K` -/

section Bounded

variable {f : ℝ → ℂ} {M : ℝ}
  (hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hf_bdd : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f t‖ ≤ M)

include hf_meas hf_bdd in
/-- Cauchy's formula on the full circle for the ENTIRE function `S_T·K`:
`∮ (S_T·K)(z)/z = 2πi·S_T(0)` (the kernel is `1` at the origin). -/
theorem circle_cauchy_laplacePartial {R : ℝ} (hR : 0 < R) (T : ℝ) :
    (∮ z in C(0, R), z⁻¹ • (laplacePartial f T z * newmanKernel R T z))
      = (2 * (Real.pi : ℂ) * Complex.I) * laplacePartial f T 0 := by
  have hdiff : Differentiable ℂ
      (fun z => laplacePartial f T z * newmanKernel R T z) :=
    (differentiable_laplacePartial hf_meas hf_bdd T).mul differentiable_newmanKernel
  have key := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ)) (c := 0) (w := 0)
    (f := fun z => laplacePartial f T z * newmanKernel R T z)
    Set.countable_empty (Metric.mem_ball_self hR)
    hdiff.continuous.continuousOn
    (fun x _ => hdiff x)
  simpa [newmanKernel_zero, smul_eq_mul, mul_comm, mul_assoc] using key

end Bounded

/-! ### Layer 4: arcs of the circle and FTC helpers for contour pieces -/

/-- The arc integral `∫_{θ₁}^{θ₂} (circleMap R)'(θ) • h(circleMap R θ) dθ`
(center `0`); the circle integral is the `(0, 2π)` case. -/
noncomputable def arcInt (R θ₁ θ₂ : ℝ) (h : ℂ → ℂ) : ℂ :=
  ∫ θ in θ₁..θ₂, deriv (circleMap 0 R) θ • h (circleMap 0 R θ)

/-- The circle splits into the RIGHT arc `(−π/2, π/2)` and the LEFT arc
`(π/2, 3π/2)` — Zagier's two hemispheres. -/
theorem circleIntegral_eq_rightArc_add_leftArc {R : ℝ} (hR : 0 ≤ R) {h : ℂ → ℂ}
    (hcont : ContinuousOn h (Metric.sphere 0 R)) :
    (∮ z in C(0, R), h z)
      = arcInt R (-(π / 2)) (π / 2) h + arcInt R (π / 2) (3 * π / 2) h := by
  have hF : Continuous
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h (circleMap 0 R θ)) := by
    simp only [deriv_circleMap, smul_eq_mul]
    exact ((continuous_circleMap 0 R).mul continuous_const).mul
      (hcont.comp_continuous (continuous_circleMap 0 R)
        (fun θ => circleMap_mem_sphere (0 : ℂ) hR θ))
  have hper : Function.Periodic
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h (circleMap 0 R θ)) (2 * π) := by
    intro θ
    simp only [deriv_circleMap, (periodic_circleMap 0 R) θ]
  have hcirc : (∮ z in C(0, R), h z)
      = ∫ θ in (0 : ℝ)..(2 * π),
          deriv (circleMap 0 R) θ • h (circleMap 0 R θ) := rfl
  have hshift := hper.intervalIntegral_add_eq 0 (-(π / 2))
  rw [hcirc, show (2 * π : ℝ) = 0 + 2 * π by ring, hshift,
    show (-(π / 2) + 2 * π : ℝ) = 3 * π / 2 by ring,
    ← intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable hF _ _)
      (Continuous.intervalIntegrable hF _ _)]
  rfl

/-- FTC along an arc: if `Φ` is a primitive of `h` on an open set containing
the arc, the arc integral telescopes to boundary values. -/
theorem arcInt_eq_sub {R θ₁ θ₂ : ℝ} {S : Set ℂ} {Φ h : ℂ → ℂ}
    (hcont : ContinuousOn h S) (hprim : ∀ z ∈ S, HasDerivAt Φ (h z) z)
    (hmem : ∀ θ ∈ Set.uIcc θ₁ θ₂, circleMap 0 R θ ∈ S) :
    arcInt R θ₁ θ₂ h = Φ (circleMap 0 R θ₂) - Φ (circleMap 0 R θ₁) := by
  have hderiv : ∀ θ ∈ Set.uIcc θ₁ θ₂,
      HasDerivAt (fun θ : ℝ => Φ (circleMap 0 R θ))
        (deriv (circleMap 0 R) θ • h (circleMap 0 R θ)) θ := by
    intro θ hθ
    have hc := (hprim _ (hmem θ hθ)).comp_of_eq θ (hasDerivAt_circleMap 0 R θ) rfl
    simpa [Function.comp_def, deriv_circleMap, smul_eq_mul, mul_comm] using hc
  have hint : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h (circleMap 0 R θ))
      volume θ₁ θ₂ := by
    apply ContinuousOn.intervalIntegrable
    simp only [deriv_circleMap, smul_eq_mul]
    exact (((continuous_circleMap 0 R).mul continuous_const).continuousOn).mul
      (hcont.comp ((continuous_circleMap 0 R).continuousOn)
        (fun θ hθ => hmem θ hθ))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- FTC along a horizontal segment `x ↦ x + c·i`. -/
theorem horizInt_eq_sub {a b c : ℝ} {S : Set ℂ} {Φ h : ℂ → ℂ}
    (hcont : ContinuousOn h S) (hprim : ∀ z ∈ S, HasDerivAt Φ (h z) z)
    (hmem : ∀ x ∈ Set.uIcc a b, (x : ℂ) + (c : ℂ) * Complex.I ∈ S) :
    ∫ x in a..b, h ((x : ℂ) + (c : ℂ) * Complex.I)
      = Φ ((b : ℂ) + (c : ℂ) * Complex.I) - Φ ((a : ℂ) + (c : ℂ) * Complex.I) := by
  have hinner : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) 1 x := by
    intro x
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((c : ℂ) * Complex.I)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => Φ ((x : ℂ) + (c : ℂ) * Complex.I))
        (h ((x : ℂ) + (c : ℂ) * Complex.I)) x := by
    intro x hx
    have hc := (hprim _ (hmem x hx)).comp_of_eq x (hinner x) rfl
    simpa [Function.comp_def] using hc
  have hint : IntervalIntegrable
      (fun x : ℝ => h ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact hcont.comp ((by fun_prop : Continuous
        (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I)).continuousOn)
      (fun x hx => hmem x hx)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- FTC along a vertical segment `y ↦ c + y·i` (integrand weighted by `i`). -/
theorem vertInt_eq_sub {a b c : ℝ} {S : Set ℂ} {Φ h : ℂ → ℂ}
    (hcont : ContinuousOn h S) (hprim : ∀ z ∈ S, HasDerivAt Φ (h z) z)
    (hmem : ∀ y ∈ Set.uIcc a b, (c : ℂ) + (y : ℂ) * Complex.I ∈ S) :
    ∫ y in a..b, Complex.I * h ((c : ℂ) + (y : ℂ) * Complex.I)
      = Φ ((c : ℂ) + (b : ℂ) * Complex.I) - Φ ((c : ℂ) + (a : ℂ) * Complex.I) := by
  have hinner : ∀ y : ℝ,
      HasDerivAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * Complex.I) Complex.I y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
    simpa using h1.const_add ((c : ℂ))
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Φ ((c : ℂ) + (y : ℂ) * Complex.I))
        (Complex.I * h ((c : ℂ) + (y : ℂ) * Complex.I)) y := by
    intro y hy
    have hc := (hprim _ (hmem y hy)).comp_of_eq y (hinner y) rfl
    simpa [Function.comp_def, mul_comm] using hc
  have hint : IntervalIntegrable
      (fun y : ℝ => Complex.I * h ((c : ℂ) + (y : ℂ) * Complex.I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (hcont.comp ((by fun_prop : Continuous
        (fun y : ℝ => (c : ℂ) + (y : ℂ) * Complex.I)).continuousOn)
      (fun y hy => hmem y hy))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

end Tauberian
end EuclidsPath
