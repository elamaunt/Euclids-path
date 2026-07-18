/-
  Tauberian/NewmanMellin — STAGE N-D of the Tauberian campaign: the
  MELLIN-FACING corollary of Newman's analytic theorem.

  The arithmetic consumers (PNT, PNT in progressions, Liouville
  cancellation) present their data as Mellin transforms
  `G(s) = ∫_1^∞ A(t)·t^{−s−1} dt − c/(s−1)` of functions of at most linear
  growth (`‖A t‖ ≤ M·t`).  The substitution `t = e^u` turns this exactly
  into the Laplace frame of N-C with `f(u) = A(e^u)e^{−u} − c`, and the
  conclusion transports back through `X = e^T`:
  `∫_1^X (A(t) − c·t)/t² dt → G(1)`.

  Hypothesis note: `Measurable A` (not a.e.-measurable) is deliberate —
  it transports through `∘ exp` for free, and the arithmetic consumers
  (step functions like `ψ`) satisfy it trivially.

  DISCLOSURES.
    * Pure analysis: no arithmetic content, no face of the parity wall is
      touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Tauberian.NewmanAnalytic

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Tauberian

open Complex MeasureTheory Metric Set intervalIntegral
open scoped Interval Real

/-! ### D1: images of the exponential -/

theorem image_exp_Ioi_zero : Real.exp '' Set.Ioi 0 = Set.Ioi 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Set.mem_Ioi.mpr (Real.one_lt_exp_iff.mpr hu)
  · intro ht
    exact ⟨Real.log t, Real.log_pos ht, Real.exp_log (by linarith [Set.mem_Ioi.mp ht])⟩

theorem image_exp_Ioc_zero {X : ℝ} (hX : 1 < X) :
    Real.exp '' Set.Ioc 0 (Real.log X) = Set.Ioc 1 X := by
  ext t
  constructor
  · rintro ⟨u, ⟨hu0, huX⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp u := Real.exp_lt_exp.mpr hu0
    · calc Real.exp u ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr huX
        _ = X := Real.exp_log (by linarith)
  · rintro ⟨ht1, htX⟩
    refine ⟨Real.log t, ⟨Real.log_pos ht1, ?_⟩, Real.exp_log (by linarith)⟩
    exact Real.log_le_log (by linarith) htX

/-! ### D3: complex powers of positive real exponentials -/

/-- `(e^u)^w = e^{w·u}` for real `u` — the cpow bridge. -/
theorem exp_real_cpow (u : ℝ) (w : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ w = Complex.exp (w * u) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]),
    mul_comm]

/-! ### D2: the substitution `t = e^u` -/

theorem setIntegral_comp_exp_Ioi (h : ℝ → ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), h t
      = ∫ u in Set.Ioi (0 : ℝ), Real.exp u • h (Real.exp u) := by
  rw [← image_exp_Ioi_zero,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [abs_of_pos (Real.exp_pos u)]

theorem setIntegral_comp_exp_Ioc {X : ℝ} (hX : 1 < X) (h : ℝ → ℂ) :
    ∫ t in Set.Ioc (1 : ℝ) X, h t
      = ∫ u in Set.Ioc (0 : ℝ) (Real.log X), Real.exp u • h (Real.exp u) := by
  rw [← image_exp_Ioc_zero hX,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn h]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [abs_of_pos (Real.exp_pos u)]

/-! ### D4: THE MELLIN COROLLARY -/

/-- **Newman's theorem in Mellin form** — the arithmetic-facing statement.
If `A` is measurable of at most linear growth and
`G(s) = ∫_1^∞ A(t)t^{−s−1} dt − c/(s−1)` on `Re s > 1` extends
holomorphically to an open `U ⊇ {Re ≥ 1}`, then
`∫_1^X (A(t) − ct)/t² dt → G(1)`. -/
theorem newman_tauberian_mellin {A : ℝ → ℂ} {c : ℂ} {M : ℝ} {U : Set ℂ}
    {G : ℂ → ℂ} (hA_meas : Measurable A)
    (hA_bdd : ∀ t ∈ Set.Ioi (1 : ℝ), ‖A t‖ ≤ M * t)
    (hU_open : IsOpen U) (hU_mem : {s : ℂ | 1 ≤ s.re} ⊆ U)
    (hG : DifferentiableOn ℂ G U)
    (hrep : ∀ s : ℂ, 1 < s.re →
      G s = (∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-s - 1)) - c / (s - 1)) :
    Filter.Tendsto
      (fun X : ℝ => ∫ t in (1 : ℝ)..X, (A t - c * t) / (t : ℂ) ^ 2)
      Filter.atTop (nhds (G 1)) := by
  set f : ℝ → ℂ := fun u => A (Real.exp u) * Complex.exp (-(u : ℂ)) - c
    with hfdef
  have hM0 : 0 ≤ M := by
    have h2 := hA_bdd 2 (by norm_num)
    nlinarith [norm_nonneg (A 2)]
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)) := by
    rw [hfdef]
    apply Measurable.aestronglyMeasurable
    exact ((hA_meas.comp Real.measurable_exp).mul (by fun_prop)).sub
      measurable_const
  have hf_bdd : ∀ u ∈ Set.Ioi (0 : ℝ), ‖f u‖ ≤ M + ‖c‖ := by
    intro u hu
    rw [hfdef]
    have h1 : (1 : ℝ) < Real.exp u := Real.one_lt_exp_iff.mpr hu
    have hA := hA_bdd (Real.exp u) (Set.mem_Ioi.mpr h1)
    calc ‖A (Real.exp u) * Complex.exp (-(u : ℂ)) - c‖
        ≤ ‖A (Real.exp u) * Complex.exp (-(u : ℂ))‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ M + ‖c‖ := by
          rw [norm_mul, Complex.norm_exp]
          have hre : (-(u : ℂ)).re = -u := by simp
          rw [hre]
          have hmul : ‖A (Real.exp u)‖ * Real.exp (-u)
              ≤ M * Real.exp u * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
          have hcollapse : M * Real.exp u * Real.exp (-u) = M := by
            rw [mul_assoc, ← Real.exp_add]
            simp
          rw [hcollapse] at hmul
          linarith
  have hU'_open : IsOpen ((fun z : ℂ => z + 1) ⁻¹' U) :=
    hU_open.preimage (by fun_prop)
  have hU'_mem : {z : ℂ | 0 ≤ z.re} ⊆ (fun z : ℂ => z + 1) ⁻¹' U := by
    intro z hz
    apply hU_mem
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.one_re]
    have : 0 ≤ z.re := hz
    linarith
  have hg : DifferentiableOn ℂ (fun z => G (z + 1))
      ((fun z : ℂ => z + 1) ⁻¹' U) := by
    intro z hz
    exact ((hG _ hz).comp z
      ((differentiable_id.add_const 1) z).differentiableWithinAt
      (fun w hw => hw))
  have hrep' : ∀ z : ℂ, 0 < z.re →
      (fun z => G (z + 1)) z
        = ∫ u in Set.Ioi (0 : ℝ), f u * Complex.exp (-(z * u)) := by
    intro z hz
    have hs1 : 1 < (z + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hz
      simp at hz
    simp only []
    rw [hrep (z + 1) hs1, add_sub_cancel_right]
    have hMel : ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1) - 1)
        = ∫ u in Set.Ioi (0 : ℝ),
            A (Real.exp u) * Complex.exp (-((z + 1) * u)) := by
      rw [setIntegral_comp_exp_Ioi
        (fun t => A t * (t : ℂ) ^ (-(z + 1) - 1))]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [exp_real_cpow, Complex.real_smul, Complex.ofReal_exp]
      have hcomb : Complex.exp ((-(z + 1) - 1) * u) * Complex.exp (u : ℂ)
          = Complex.exp (-((z + 1) * u)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      linear_combination A (Real.exp u) * hcomb
    have hc_int : ∫ u in Set.Ioi (0 : ℝ), c * Complex.exp (-(z * u)) = c / z := by
      rw [MeasureTheory.integral_const_mul]
      have hval := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
      have hcongr : ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-(z * u))
          = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-z * u) :=
        setIntegral_congr_fun measurableSet_Ioi fun u _ => by ring_nf
      rw [hcongr, hval]
      simp
      rw [div_eq_mul_inv]
    have hInt1 : IntegrableOn
        (fun u : ℝ => A (Real.exp u) * Complex.exp (-((z + 1) * u)))
        (Set.Ioi 0) := by
      refine Integrable.mono'
        ((integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) 0).const_mul M)
        (Measurable.aestronglyMeasurable
          ((hA_meas.comp Real.measurable_exp).mul (by fun_prop))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, Complex.norm_exp]
      have hre2 : (-((z + 1) * (u : ℂ))).re = -((z.re + 1) * u) := by
        simp [Complex.mul_re]
      rw [hre2]
      have h1 : (1 : ℝ) < Real.exp u := Real.one_lt_exp_iff.mpr hu
      have hA := hA_bdd (Real.exp u) (Set.mem_Ioi.mpr h1)
      have hstep : ‖A (Real.exp u)‖ * Real.exp (-((z.re + 1) * u))
          ≤ M * Real.exp u * Real.exp (-((z.re + 1) * u)) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
      have hcollapse : M * Real.exp u * Real.exp (-((z.re + 1) * u))
          = M * Real.exp (-z.re * u) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [hcollapse] at hstep
      exact hstep
    have hInt2 : IntegrableOn (fun u : ℝ => c * Complex.exp (-(z * u)))
        (Set.Ioi 0) := by
      have hbase : IntegrableOn (fun u : ℝ => Complex.exp (-z * u))
          (Set.Ioi 0) := integrableOn_exp_mul_complex_Ioi (by simpa using hz) 0
      have hbase' : IntegrableOn (fun u : ℝ => Complex.exp (-(z * u)))
          (Set.Ioi 0) := by
        apply hbase.congr_fun ?_ measurableSet_Ioi
        intro u _
        ring_nf
      exact hbase'.const_mul c
    have hsplit : ∫ u in Set.Ioi (0 : ℝ), f u * Complex.exp (-(z * u))
        = (∫ u in Set.Ioi (0 : ℝ),
            A (Real.exp u) * Complex.exp (-((z + 1) * u)))
          - ∫ u in Set.Ioi (0 : ℝ), c * Complex.exp (-(z * u)) := by
      rw [← MeasureTheory.integral_sub hInt1 hInt2]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [hfdef]
      have hcomb : Complex.exp (-(u : ℂ)) * Complex.exp (-(z * u))
          = Complex.exp (-((z + 1) * u)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      linear_combination A (Real.exp u) * hcomb
    rw [hsplit, hMel, hc_int]
  have hNewman := newman_tauberian hf_meas hf_bdd hU'_open hU'_mem hg hrep'
  simp only [zero_add] at hNewman
  have hcomp := hNewman.comp Real.tendsto_log_atTop
  apply hcomp.congr'
  filter_upwards [Filter.eventually_gt_atTop 1] with X hX
  simp only [Function.comp_apply]
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  rw [intervalIntegral.integral_of_le hlogpos.le,
    intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ X),
    setIntegral_comp_exp_Ioc hX (fun t => (A t - c * t) / (t : ℂ) ^ 2)]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [Complex.real_smul, Complex.ofReal_exp]
  have hfu : f u = A (Real.exp u) * Complex.exp (-(u : ℂ)) - c := rfl
  rw [hfu, Complex.exp_neg]
  have hne : Complex.exp ((u : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

end Tauberian
end EuclidsPath
