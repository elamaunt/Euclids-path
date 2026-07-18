/-
  Tauberian/NewmanAnalytic — STAGE N-C of the Tauberian campaign: NEWMAN'S
  ANALYTIC THEOREM (the Tauberian core), by Zagier's contour on the stadium.

  STATEMENT.  `f` measurable and bounded on `(0,∞)`; its Laplace transform
  `g(z) = ∫_0^∞ f e^{−zt}` extends holomorphically to an open `U ⊇ {Re ≥ 0}`.
  Then `∫_0^T f → g(0)` as `T → ∞`.

  ARCHITECTURE (the contour-free ledger, validated numerically by
  `scripts/newman_prepass.py` before construction):
    * the stadium fits inside `U` by compact thickening (C1);
    * `φ := dslope (g·K) 0` is holomorphic on the stadium — removable
      singularity (C3) — hence HAS A PRIMITIVE there (N-A);
    * the dented contour = right arc + two horizontal jogs + one vertical
      segment; `rightArc φ + dentInt φ = 0` by PURE TELESCOPING of the
      primitive (C8) — no closed-contour theorem, no DCT, no `δ → 0`;
    * `rightArc(1/z) = dentInt(1/z) = πi` (C9, C10 — explicit calculus);
    * the master identity (C12):
      `2πi(g0 − S_T0) = rightArc((g−S_T)K/z) + dentInt(gK/z) − leftArc(S_T·K/z)`;
    * estimates: E1, E2 `≤ 2πM/R` (the EXACT Zagier weight cancellation),
      E3 `→ 0` at rate `2RC₀e^{−δT} + 2C₀/T`;
    * `newman_tauberian` (C16) with the ε-schedule `R := max 1 (4M/ε + 1)`.

  DISCLOSURES.
    * Pure complex-analytic infrastructure: no arithmetic content, no face
      of the parity wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Tauberian.LaplaceFinite

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Tauberian

open Complex MeasureTheory Metric Set intervalIntegral
open scoped Interval Real

/-! ### C1: the stadium fits inside any open `U ⊇ {Re ≥ 0}` -/

/-- Compactness + thickening: for every radius there is a dent depth `δ`
with `stadium R' δ ⊆ U`.  Witness for the thickening: `z − Re z`. -/
theorem exists_stadium_subset {U : Set ℂ} (hU_open : IsOpen U)
    (hU_mem : {z : ℂ | 0 ≤ z.re} ⊆ U) {R' : ℝ} (_hR' : 0 < R') :
    ∃ δ > 0, stadium R' δ ⊆ U := by
  have hKc : IsCompact (Metric.closedBall (0 : ℂ) R' ∩ {z : ℂ | 0 ≤ z.re}) :=
    (isCompact_closedBall 0 R').inter_right
      (isClosed_le continuous_const Complex.continuous_re)
  have hKU : Metric.closedBall (0 : ℂ) R' ∩ {z : ℂ | 0 ≤ z.re} ⊆ U :=
    fun z hz => hU_mem hz.2
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_thickening_subset_open hU_open hKU
  refine ⟨δ, hδ, fun z hz => ?_⟩
  rw [mem_stadium_iff] at hz
  by_cases hre : 0 ≤ z.re
  · exact hU_mem hre
  · push Not at hre
    apply hsub
    rw [Metric.mem_thickening_iff]
    refine ⟨z - (z.re : ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have him : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [him, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
      exact le_trans (Complex.abs_im_le_norm z) hz.1.le
    · simp [Set.mem_setOf_eq]
    · have hzz : z - (z - (z.re : ℂ)) = (z.re : ℂ) := by ring
      rw [dist_eq_norm, hzz, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg hre]
      linarith [hz.2]

/-! ### C2–C5: the pole-subtracted integrand `φ` and its primitive -/

/-- The pole-subtracted weighted extension: `φ = dslope (g·K) 0`, i.e.
`φ(z) = (g(z)K(z) − g(0))/z` off `0` and `(gK)′(0)` at `0`. -/
noncomputable def phiAux (R T : ℝ) (g : ℂ → ℂ) : ℂ → ℂ :=
  dslope (fun z => g z * newmanKernel R T z) 0

/-- `φ` is holomorphic on any stadium inside `U`: off `0` it is a quotient,
at `0` the singularity is REMOVABLE (`g·K` is differentiable there). -/
theorem differentiableOn_phiAux {U : Set ℂ} {g : ℂ → ℂ}
    (hU_open : IsOpen U) (hg : DifferentiableOn ℂ g U)
    {R' δ' : ℝ} (hsub : stadium R' δ' ⊆ U) (R T : ℝ) :
    DifferentiableOn ℂ (phiAux R T g) (stadium R' δ') := by
  unfold phiAux
  have hgK : ∀ z ∈ stadium R' δ',
      DifferentiableAt ℂ (fun z => g z * newmanKernel R T z) z := by
    intro z hz
    exact (hg.differentiableAt (hU_open.mem_nhds (hsub hz))).mul
      (differentiable_newmanKernel z)
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    have hev : ∀ᶠ w in nhdsWithin 0 {(0 : ℂ)}ᶜ,
        DifferentiableAt ℂ (dslope (fun z => g z * newmanKernel R T z) 0) w := by
      have hmem : stadium R' δ' ∈ nhds (0 : ℂ) := isOpen_stadium.mem_nhds hz
      filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with w hw hw0
      exact (differentiableAt_dslope_of_ne (by simpa using hw0)).mpr (hgK w hw)
    have hcont : ContinuousAt (dslope (fun z => g z * newmanKernel R T z) 0) 0 :=
      continuousAt_dslope_same.mpr (hgK 0 hz)
    exact ((Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hev hcont).differentiableAt).differentiableWithinAt
  · exact ((differentiableAt_dslope_of_ne hz0).mpr (hgK z hz)).differentiableWithinAt

/-- Off the origin, the weighted integrand splits: `gK/z = φ + g(0)/z`. -/
theorem gK_div_eq {R T : ℝ} {g : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    g z * newmanKernel R T z / z = phiAux R T g z + g 0 / z := by
  unfold phiAux
  rw [dslope_of_ne _ hz, slope_def_field, sub_zero, newmanKernel_zero, mul_one]
  field_simp
  ring

/-! ### C6–C8: the dented contour and the telescoping identity -/

theorem circleMap_re {R θ : ℝ} : (circleMap 0 R θ).re = R * Real.cos θ := by
  simp [circleMap]

theorem circleMap_pi_div_two {R : ℝ} :
    circleMap 0 R (π / 2) = (R : ℂ) * Complex.I := by
  rw [circleMap_zero, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

theorem circleMap_neg_pi_div_two {R : ℝ} :
    circleMap 0 R (-(π / 2)) = -((R : ℂ) * Complex.I) := by
  rw [circleMap_zero, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two,
    Complex.sin_pi_div_two]
  ring

theorem circleMap_three_pi_div_two {R : ℝ} :
    circleMap 0 R (3 * π / 2) = -((R : ℂ) * Complex.I) := by
  rw [show (3 * π / 2 : ℝ) = -(π / 2) + 2 * π by ring,
    (periodic_circleMap 0 R) (-(π / 2)), circleMap_neg_pi_div_two]

/-- The DENT: from `R·i` jog left to `−δ + R·i`, descend to `−δ − R·i`,
jog right back to `−R·i`.  Together with the right arc this closes the
stadium contour. -/
noncomputable def dentInt (R δ : ℝ) (h : ℂ → ℂ) : ℂ :=
  (∫ x in (0 : ℝ)..(-δ), h ((x : ℂ) + (R : ℂ) * Complex.I))
    + (∫ y in R..(-R), Complex.I * h (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
    + (∫ x in (-δ : ℝ)..0, h ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))

/-- Horizontal jog points lie in the enclosing stadium. -/
theorem horiz_piece_mem_stadium {R δ R' δ' : ℝ} (hδ0 : 0 ≤ δ)
    (hRδ : R + δ < R') (hδδ' : δ < δ') {x : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) (-δ))
    {c : ℝ} (hc : |c| ≤ R) :
    (x : ℂ) + (c : ℂ) * Complex.I ∈ stadium R' δ' := by
  rw [Set.uIcc_of_ge (by linarith : -δ ≤ 0)] at hx
  rw [mem_stadium_iff]
  constructor
  · calc ‖(x : ℂ) + (c : ℂ) * Complex.I‖
        ≤ ‖(x : ℂ)‖ + ‖(c : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |x| + |c| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I,
            mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ δ + R := by
          have h1 : |x| ≤ δ := abs_le.mpr ⟨hx.1, le_trans hx.2 hδ0⟩
          linarith
      _ < R' := by linarith
  · have hre : ((x : ℂ) + (c : ℂ) * Complex.I).re = x := by simp
    rw [hre]
    linarith [hx.1]

/-- Vertical segment points lie in the enclosing stadium. -/
theorem vert_piece_mem_stadium {R δ R' δ' : ℝ} (hδ0 : 0 ≤ δ) (hR0 : 0 ≤ R)
    (hRδ : R + δ < R') (hδδ' : δ < δ') {y : ℝ} (hy : y ∈ Set.uIcc R (-R)) :
    ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ stadium R' δ' := by
  rw [Set.uIcc_of_ge (by linarith : -R ≤ R)] at hy
  rw [mem_stadium_iff]
  constructor
  · calc ‖((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I‖
        ≤ ‖((-δ : ℝ) : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |(-δ : ℝ)| + |y| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I,
            mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ δ + R := by
          have h1 : |(-δ : ℝ)| = δ := by rw [abs_neg, abs_of_nonneg hδ0]
          have h2 : |y| ≤ R := abs_le.mpr ⟨hy.1, hy.2⟩
          linarith
      _ < R' := by linarith
  · have hre : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = -δ := by simp
    rw [hre]
    linarith

/-- Right-arc points lie in the enclosing stadium (the arc has `Re ≥ 0`). -/
theorem arc_mem_stadium {R R' δ' : ℝ} (hR0 : 0 ≤ R) (hRR' : R < R')
    (hδ'0 : 0 < δ') {θ : ℝ} (hθ : θ ∈ Set.uIcc (-(π / 2)) (π / 2)) :
    circleMap 0 R θ ∈ stadium R' δ' := by
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : -(π / 2) ≤ π / 2)] at hθ
  rw [mem_stadium_iff]
  constructor
  · rw [norm_circleMap_zero, abs_of_nonneg hR0]
    exact hRR'
  · rw [circleMap_re]
    have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
    nlinarith

/-- **The dent telescopes**: with a primitive `Φ` of `h` on the enclosing
stadium, the three dent pieces collapse to `Φ(−R·i) − Φ(R·i)`. -/
theorem dentInt_eq_sub {R δ R' δ' : ℝ} (hδ0 : 0 ≤ δ) (hR0 : 0 ≤ R)
    (hRδ : R + δ < R') (hδδ' : δ < δ') {Φ h : ℂ → ℂ}
    (hcont : ContinuousOn h (stadium R' δ'))
    (hprim : ∀ z ∈ stadium R' δ', HasDerivAt Φ (h z) z) :
    dentInt R δ h = Φ (-((R : ℂ) * Complex.I)) - Φ ((R : ℂ) * Complex.I) := by
  unfold dentInt
  rw [horizInt_eq_sub hcont hprim
      (fun x hx => horiz_piece_mem_stadium hδ0 hRδ hδδ' hx
        (by rw [abs_of_nonneg hR0])),
    vertInt_eq_sub hcont hprim
      (fun y hy => vert_piece_mem_stadium hδ0 hR0 hRδ hδδ' hy),
    horizInt_eq_sub hcont hprim
      (fun x hx => horiz_piece_mem_stadium hδ0 hRδ hδδ'
        (Set.uIcc_comm (-δ : ℝ) 0 ▸ hx)
        (by rw [abs_neg, abs_of_nonneg hR0]))]
  have e1 : ((0 : ℝ) : ℂ) + (R : ℂ) * Complex.I = (R : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : ((0 : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I
      = -((R : ℂ) * Complex.I) := by
    push_cast; ring
  have e3 : ((-δ : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I
      = ((-δ : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I := rfl
  rw [e1, e2]
  abel

/-- **THE CLOSED-CONTOUR IDENTITY, FOR FREE**: right arc + dent of any
function with a primitive on the enclosing stadium is `0` — pure
telescoping, no Cauchy theorem. -/
theorem rightArc_add_dentInt_eq_zero {R δ R' δ' : ℝ} (hδ0 : 0 ≤ δ)
    (hR0 : 0 ≤ R) (hRR' : R < R') (hRδ : R + δ < R') (hδδ' : δ < δ')
    (hδ'0 : 0 < δ') {Φ h : ℂ → ℂ}
    (hcont : ContinuousOn h (stadium R' δ'))
    (hprim : ∀ z ∈ stadium R' δ', HasDerivAt Φ (h z) z) :
    arcInt R (-(π / 2)) (π / 2) h + dentInt R δ h = 0 := by
  rw [arcInt_eq_sub hcont hprim
      (fun θ hθ => arc_mem_stadium hR0 hRR' hδ'0 hθ),
    dentInt_eq_sub hδ0 hR0 hRδ hδδ' hcont hprim,
    circleMap_pi_div_two, circleMap_neg_pi_div_two]
  abel

/-! ### C9–C10: the two `πi` sub-identities -/

/-- On the right arc the weighted integrand of `1/z` is constantly `i`:
`rightArc(1/z) = πi`. -/
theorem rightArc_inv {R : ℝ} (hR : 0 < R) :
    arcInt R (-(π / 2)) (π / 2) (fun z => z⁻¹) = ((π : ℝ) : ℂ) * Complex.I := by
  unfold arcInt
  have hcongr : ∀ θ ∈ Set.uIcc (-(π / 2)) (π / 2),
      deriv (circleMap 0 R) θ • (circleMap 0 R θ)⁻¹ = Complex.I := by
    intro θ _
    rw [deriv_circleMap, smul_eq_mul, mul_comm (circleMap 0 R θ) Complex.I,
      mul_assoc, mul_inv_cancel₀ (circleMap_ne_center (ne_of_gt hR)), mul_one]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const,
    show (π / 2 - -(π / 2) : ℝ) = π by ring, Complex.real_smul]

/-- The primitive `log(−z)` on the left slit plane differentiates to `1/z`. -/
theorem hasDerivAt_log_neg {z : ℂ} (hz : -z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => Complex.log (-z)) z⁻¹ z := by
  have h1 := (Complex.hasDerivAt_log hz).comp_of_eq z (hasDerivAt_neg z) rfl
  simpa [Function.comp_def, inv_neg] using h1

/-- The dent sees `1/z` through the SAME telescoping primitive `log(−z)`:
`dentInt(1/z) = πi` (the second half of the `2πi` residue). -/
theorem dentInt_inv {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    dentInt R δ (fun z => z⁻¹) = ((π : ℝ) : ℂ) * Complex.I := by
  set S : Set ℂ := (fun z : ℂ => -z) ⁻¹' Complex.slitPlane with hSdef
  set L : ℂ → ℂ := fun z => Complex.log (-z) with hLdef
  have hprim : ∀ z ∈ S, HasDerivAt L z⁻¹ z := fun z hz => hasDerivAt_log_neg hz
  have hcont : ContinuousOn (fun z : ℂ => z⁻¹) S := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro z hz h0
    subst h0
    rw [hSdef, Set.mem_preimage, neg_zero] at hz
    simp [Complex.mem_slitPlane_iff] at hz
  have hm1 : ∀ x ∈ Set.uIcc (0 : ℝ) (-δ),
      (x : ℂ) + (R : ℂ) * Complex.I ∈ S := by
    intro x _
    rw [hSdef, Set.mem_preimage, Complex.mem_slitPlane_iff]
    right
    simp [hR.ne']
  have hm2 : ∀ y ∈ Set.uIcc R (-R),
      ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ S := by
    intro y _
    rw [hSdef, Set.mem_preimage, Complex.mem_slitPlane_iff]
    left
    simp [hδ]
  have hm3 : ∀ x ∈ Set.uIcc (-δ : ℝ) 0,
      (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I ∈ S := by
    intro x _
    rw [hSdef, Set.mem_preimage, Complex.mem_slitPlane_iff]
    right
    simp [hR.ne']
  unfold dentInt
  rw [horizInt_eq_sub hcont hprim hm1, vertInt_eq_sub hcont hprim hm2,
    horizInt_eq_sub hcont hprim hm3]
  have e1 : ((0 : ℝ) : ℂ) + (R : ℂ) * Complex.I = (R : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : ((0 : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I
      = -((R : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e1, e2]
  have hlog : L (-((R : ℂ) * Complex.I)) - L ((R : ℂ) * Complex.I)
      = ((π : ℝ) : ℂ) * Complex.I := by
    rw [hLdef]
    simp only [neg_neg]
    apply Complex.ext
    · simp [Complex.log_re]
    · rw [Complex.sub_im, Complex.log_im, Complex.log_im]
      have hargI : Complex.arg ((R : ℂ) * Complex.I) = π / 2 := by
        rw [Complex.arg_real_mul Complex.I hR, Complex.arg_I]
      have hargnI : Complex.arg (-((R : ℂ) * Complex.I)) = -(π / 2) := by
        rw [show -((R : ℂ) * Complex.I) = (R : ℂ) * (-Complex.I) by ring,
          Complex.arg_real_mul (-Complex.I) hR, Complex.arg_neg_I]
      rw [hargI, hargnI]
      simp
  linear_combination hlog

/-! ### Linearity of the arc and dent functionals -/

/-- Integrability of the arc integrand from continuity on any covering set. -/
theorem intervalIntegrable_arc {R θ₁ θ₂ : ℝ} {S : Set ℂ} {h : ℂ → ℂ}
    (hcont : ContinuousOn h S)
    (hmem : ∀ θ ∈ Set.uIcc θ₁ θ₂, circleMap 0 R θ ∈ S) :
    IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h (circleMap 0 R θ))
      volume θ₁ θ₂ := by
  apply ContinuousOn.intervalIntegrable
  simp only [deriv_circleMap, smul_eq_mul]
  exact (((continuous_circleMap 0 R).mul continuous_const).continuousOn).mul
    (hcont.comp ((continuous_circleMap 0 R).continuousOn)
      (fun θ hθ => hmem θ hθ))

theorem arcInt_congr {R θ₁ θ₂ : ℝ} {h₁ h₂ : ℂ → ℂ}
    (h : ∀ θ ∈ Set.uIcc θ₁ θ₂, h₁ (circleMap 0 R θ) = h₂ (circleMap 0 R θ)) :
    arcInt R θ₁ θ₂ h₁ = arcInt R θ₁ θ₂ h₂ := by
  unfold arcInt
  exact intervalIntegral.integral_congr (fun θ hθ => by rw [h θ hθ])

theorem arcInt_add {R θ₁ θ₂ : ℝ} {h₁ h₂ : ℂ → ℂ}
    (hi₁ : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h₁ (circleMap 0 R θ)) volume θ₁ θ₂)
    (hi₂ : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h₂ (circleMap 0 R θ)) volume θ₁ θ₂) :
    arcInt R θ₁ θ₂ (fun z => h₁ z + h₂ z)
      = arcInt R θ₁ θ₂ h₁ + arcInt R θ₁ θ₂ h₂ := by
  unfold arcInt
  rw [← intervalIntegral.integral_add hi₁ hi₂]
  exact intervalIntegral.integral_congr
    (fun θ _ => by simp [smul_eq_mul, mul_add])

theorem arcInt_sub {R θ₁ θ₂ : ℝ} {h₁ h₂ : ℂ → ℂ}
    (hi₁ : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h₁ (circleMap 0 R θ)) volume θ₁ θ₂)
    (hi₂ : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap 0 R) θ • h₂ (circleMap 0 R θ)) volume θ₁ θ₂) :
    arcInt R θ₁ θ₂ (fun z => h₁ z - h₂ z)
      = arcInt R θ₁ θ₂ h₁ - arcInt R θ₁ θ₂ h₂ := by
  unfold arcInt
  rw [← intervalIntegral.integral_sub hi₁ hi₂]
  exact intervalIntegral.integral_congr
    (fun θ _ => by simp [smul_eq_mul, mul_sub])

theorem arcInt_const_mul {R θ₁ θ₂ : ℝ} (c : ℂ) (h : ℂ → ℂ) :
    arcInt R θ₁ θ₂ (fun z => c * h z) = c * arcInt R θ₁ θ₂ h := by
  unfold arcInt
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr
    (fun θ _ => by simp only [smul_eq_mul]; ring)

theorem dentInt_congr {R δ : ℝ} {h₁ h₂ : ℂ → ℂ}
    (hp1 : ∀ x ∈ Set.uIcc (0 : ℝ) (-δ),
      h₁ ((x : ℂ) + (R : ℂ) * Complex.I) = h₂ ((x : ℂ) + (R : ℂ) * Complex.I))
    (hp2 : ∀ y ∈ Set.uIcc R (-R),
      h₁ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        = h₂ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
    (hp3 : ∀ x ∈ Set.uIcc (-δ : ℝ) 0,
      h₁ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
        = h₂ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) :
    dentInt R δ h₁ = dentInt R δ h₂ := by
  unfold dentInt
  rw [intervalIntegral.integral_congr
      (f := fun x : ℝ => h₁ ((x : ℂ) + (R : ℂ) * Complex.I))
      (g := fun x : ℝ => h₂ ((x : ℂ) + (R : ℂ) * Complex.I))
      (fun x hx => hp1 x hx),
    intervalIntegral.integral_congr
      (f := fun y : ℝ => Complex.I * h₁ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      (g := fun y : ℝ => Complex.I * h₂ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      (fun y hy => by simp only [hp2 y hy]),
    intervalIntegral.integral_congr
      (f := fun x : ℝ => h₁ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      (g := fun x : ℝ => h₂ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      (fun x hx => hp3 x hx)]

theorem dentInt_add {R δ : ℝ} {S : Set ℂ} {h₁ h₂ : ℂ → ℂ}
    (hc₁ : ContinuousOn h₁ S) (hc₂ : ContinuousOn h₂ S)
    (hm1 : ∀ x ∈ Set.uIcc (0 : ℝ) (-δ), (x : ℂ) + (R : ℂ) * Complex.I ∈ S)
    (hm2 : ∀ y ∈ Set.uIcc R (-R), ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ S)
    (hm3 : ∀ x ∈ Set.uIcc (-δ : ℝ) 0, (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I ∈ S) :
    dentInt R δ (fun z => h₁ z + h₂ z) = dentInt R δ h₁ + dentInt R δ h₂ := by
  have hpath1 : Continuous (fun x : ℝ => (x : ℂ) + (R : ℂ) * Complex.I) := by
    fun_prop
  have hpath2 : Continuous (fun y : ℝ => ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    fun_prop
  have hpath3 : Continuous (fun x : ℝ => (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  have i1a : IntervalIntegrable (fun x : ℝ => h₁ ((x : ℂ) + (R : ℂ) * Complex.I))
      volume 0 (-δ) :=
    (hc₁.comp hpath1.continuousOn (fun x hx => hm1 x hx)).intervalIntegrable
  have i1b : IntervalIntegrable (fun x : ℝ => h₂ ((x : ℂ) + (R : ℂ) * Complex.I))
      volume 0 (-δ) :=
    (hc₂.comp hpath1.continuousOn (fun x hx => hm1 x hx)).intervalIntegrable
  have i2a : IntervalIntegrable
      (fun y : ℝ => Complex.I * h₁ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      volume R (-R) :=
    (continuousOn_const.mul
      (hc₁.comp hpath2.continuousOn (fun y hy => hm2 y hy))).intervalIntegrable
  have i2b : IntervalIntegrable
      (fun y : ℝ => Complex.I * h₂ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      volume R (-R) :=
    (continuousOn_const.mul
      (hc₂.comp hpath2.continuousOn (fun y hy => hm2 y hy))).intervalIntegrable
  have i3a : IntervalIntegrable
      (fun x : ℝ => h₁ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) volume (-δ) 0 :=
    (hc₁.comp hpath3.continuousOn (fun x hx => hm3 x hx)).intervalIntegrable
  have i3b : IntervalIntegrable
      (fun x : ℝ => h₂ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) volume (-δ) 0 :=
    (hc₂.comp hpath3.continuousOn (fun x hx => hm3 x hx)).intervalIntegrable
  have h1 : ∫ x in (0 : ℝ)..(-δ),
        (h₁ ((x : ℂ) + (R : ℂ) * Complex.I) + h₂ ((x : ℂ) + (R : ℂ) * Complex.I))
      = (∫ x in (0 : ℝ)..(-δ), h₁ ((x : ℂ) + (R : ℂ) * Complex.I))
        + ∫ x in (0 : ℝ)..(-δ), h₂ ((x : ℂ) + (R : ℂ) * Complex.I) :=
    intervalIntegral.integral_add i1a i1b
  have h2 : ∫ y in R..(-R),
        Complex.I * (h₁ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          + h₂ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y in R..(-R), Complex.I * h₁ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        + ∫ y in R..(-R), Complex.I * h₂ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_add i2a i2b]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have h3 : ∫ x in (-δ : ℝ)..0,
        (h₁ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
          + h₂ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      = (∫ x in (-δ : ℝ)..0, h₁ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        + ∫ x in (-δ : ℝ)..0, h₂ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) :=
    intervalIntegral.integral_add i3a i3b
  unfold dentInt
  linear_combination h1 + h2 + h3

theorem dentInt_const_mul {R δ : ℝ} (c : ℂ) (h : ℂ → ℂ) :
    dentInt R δ (fun z => c * h z) = c * dentInt R δ h := by
  have h1 : ∫ x in (0 : ℝ)..(-δ), c * h ((x : ℂ) + (R : ℂ) * Complex.I)
      = c * ∫ x in (0 : ℝ)..(-δ), h ((x : ℂ) + (R : ℂ) * Complex.I) :=
    intervalIntegral.integral_const_mul c _
  have h2 : ∫ y in R..(-R),
        Complex.I * (c * h (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = c * ∫ y in R..(-R),
          Complex.I * h (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have h3 : ∫ x in (-δ : ℝ)..0, c * h ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
      = c * ∫ x in (-δ : ℝ)..0, h ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) :=
    intervalIntegral.integral_const_mul c _
  unfold dentInt
  linear_combination h1 + h2 + h3

/-! ### C11–C12: the ledger and the master identity -/

/-- **The `g`-side of the ledger**: `rightArc(gK/z) + dentInt(gK/z) = 2πi·g(0)`
— split off the pole (`gK/z = φ + g(0)/z`), telescope `φ`, and collect the
two `πi` halves of the residue. -/
theorem rightArc_gK_add_dentInt_gK {R δ R' δ' : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hRR' : R < R') (hRδ : R + δ < R') (hδδ' : δ < δ') (hδ'0 : 0 < δ')
    {U : Set ℂ} {g : ℂ → ℂ} (hU_open : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hsub : stadium R' δ' ⊆ U) (T : ℝ) :
    arcInt R (-(π / 2)) (π / 2) (fun z => g z * newmanKernel R T z / z)
      + dentInt R δ (fun z => g z * newmanKernel R T z / z)
      = 2 * ((π : ℝ) : ℂ) * Complex.I * g 0 := by
  have hR'0 : 0 < R' := lt_trans hR hRR'
  have hφdiff := differentiableOn_phiAux hU_open hg hsub R T
  have hφcont : ContinuousOn (phiAux R T g) (stadium R' δ') := hφdiff.continuousOn
  obtain ⟨Φ, hΦ⟩ := DifferentiableOn.isExactOn_stadium hR'0 hδ'0 hφdiff
  have harc_mem : ∀ θ ∈ Set.uIcc (-(π / 2)) (π / 2),
      circleMap 0 R θ ∈ stadium R' δ' :=
    fun θ hθ => arc_mem_stadium hR.le hRR' hδ'0 hθ
  have hm1 : ∀ x ∈ Set.uIcc (0 : ℝ) (-δ),
      (x : ℂ) + (R : ℂ) * Complex.I ∈ stadium R' δ' :=
    fun x hx => horiz_piece_mem_stadium hδ.le hRδ hδδ' hx
      (by rw [abs_of_nonneg hR.le])
  have hm2 : ∀ y ∈ Set.uIcc R (-R),
      ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ stadium R' δ' :=
    fun y hy => vert_piece_mem_stadium hδ.le hR.le hRδ hδδ' hy
  have hm3 : ∀ x ∈ Set.uIcc (-δ : ℝ) 0,
      (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I ∈ stadium R' δ' :=
    fun x hx => horiz_piece_mem_stadium hδ.le hRδ hδδ'
      (Set.uIcc_comm (-δ : ℝ) 0 ▸ hx) (by rw [abs_neg, abs_of_nonneg hR.le])
  have hz1 : ∀ x : ℝ, (x : ℂ) + (R : ℂ) * Complex.I ≠ 0 := by
    intro x h0
    have him : ((x : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
    rw [h0] at him
    simp at him
    exact hR.ne' him.symm
  have hz2 : ∀ y : ℝ, ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro y h0
    have hre : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = -δ := by simp
    rw [h0] at hre
    simp at hre
    exact hδ.ne' hre
  have hz3 : ∀ x : ℝ, (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro x h0
    have him : ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im = -R := by simp
    rw [h0] at him
    simp at him
    exact hR.ne' him
  have hsplit : ∀ z : ℂ, z ≠ 0 →
      g z * newmanKernel R T z / z = phiAux R T g z + g 0 * z⁻¹ := by
    intro z hz
    rw [gK_div_eq hz, div_eq_mul_inv]
  have ha : arcInt R (-(π / 2)) (π / 2)
        (fun z => g z * newmanKernel R T z / z)
      = arcInt R (-(π / 2)) (π / 2) (fun z => phiAux R T g z + g 0 * z⁻¹) :=
    arcInt_congr (fun θ _ => hsplit _ (circleMap_ne_center hR.ne'))
  have hd : dentInt R δ (fun z => g z * newmanKernel R T z / z)
      = dentInt R δ (fun z => phiAux R T g z + g 0 * z⁻¹) :=
    dentInt_congr (fun x _ => hsplit _ (hz1 x)) (fun y _ => hsplit _ (hz2 y))
      (fun x _ => hsplit _ (hz3 x))
  have hinv_cont : ContinuousOn (fun z : ℂ => g 0 * z⁻¹) {(0 : ℂ)}ᶜ :=
    continuousOn_const.mul (continuousOn_inv₀.mono (fun z hz => by simpa using hz))
  have harc_add : arcInt R (-(π / 2)) (π / 2)
        (fun z => phiAux R T g z + g 0 * z⁻¹)
      = arcInt R (-(π / 2)) (π / 2) (phiAux R T g)
        + arcInt R (-(π / 2)) (π / 2) (fun z => g 0 * z⁻¹) :=
    arcInt_add (intervalIntegrable_arc hφcont harc_mem)
      (intervalIntegrable_arc hinv_cont
        (fun θ _ => by simp; exact hR.ne'))
  have hdent_add : dentInt R δ (fun z => phiAux R T g z + g 0 * z⁻¹)
      = dentInt R δ (phiAux R T g) + dentInt R δ (fun z => g 0 * z⁻¹) :=
    dentInt_add (S := stadium R' δ' ∩ {(0 : ℂ)}ᶜ)
      (hφcont.mono Set.inter_subset_left)
      (hinv_cont.mono Set.inter_subset_right)
      (fun x hx => ⟨hm1 x hx, by simpa using hz1 x⟩)
      (fun y hy => ⟨hm2 y hy, by simpa using hz2 y⟩)
      (fun x hx => ⟨hm3 x hx, by simpa using hz3 x⟩)
  have hφzero : arcInt R (-(π / 2)) (π / 2) (phiAux R T g)
      + dentInt R δ (phiAux R T g) = 0 :=
    rightArc_add_dentInt_eq_zero hδ.le hR.le hRR' hRδ hδδ' hδ'0 hφcont hΦ
  have harc_cm : arcInt R (-(π / 2)) (π / 2) (fun z => g 0 * z⁻¹)
      = g 0 * arcInt R (-(π / 2)) (π / 2) (fun z => z⁻¹) :=
    arcInt_const_mul (g 0) _
  have hdent_cm : dentInt R δ (fun z => g 0 * z⁻¹)
      = g 0 * dentInt R δ (fun z => z⁻¹) :=
    dentInt_const_mul (g 0) _
  rw [ha, hd, harc_add, hdent_add, harc_cm, hdent_cm, rightArc_inv hR,
    dentInt_inv hR hδ]
  linear_combination hφzero

section Bounded

variable {f : ℝ → ℂ} {M : ℝ}
  (hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hf_bdd : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f t‖ ≤ M)

include hf_meas hf_bdd in
/-- **THE MASTER IDENTITY (Zagier's ledger)**:
`2πi(g(0) − S_T(0)) = rightArc((g−S_T)K/z) + dentInt(gK/z) − leftArc(S_T·K/z)`. -/
theorem contour_master {R δ R' δ' : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hRR' : R < R') (hRδ : R + δ < R') (hδδ' : δ < δ') (hδ'0 : 0 < δ')
    {U : Set ℂ} {g : ℂ → ℂ} (hU_open : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hsub : stadium R' δ' ⊆ U) (T : ℝ) :
    2 * ((π : ℝ) : ℂ) * Complex.I * (g 0 - laplacePartial f T 0)
      = arcInt R (-(π / 2)) (π / 2)
          (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z)
        + dentInt R δ (fun z => g z * newmanKernel R T z / z)
        - arcInt R (π / 2) (3 * π / 2)
            (fun z => laplacePartial f T z * newmanKernel R T z / z) := by
  have hR'0 : 0 < R' := lt_trans hR hRR'
  have hSK_cont : Continuous
      (fun z => laplacePartial f T z * newmanKernel R T z) :=
    ((differentiable_laplacePartial hf_meas hf_bdd T).mul
      differentiable_newmanKernel).continuous
  have hcauchy := circle_cauchy_laplacePartial hf_meas hf_bdd hR T
  have hfun : (fun z : ℂ =>
        z⁻¹ • (laplacePartial f T z * newmanKernel R T z))
      = fun z : ℂ => laplacePartial f T z * newmanKernel R T z / z := by
    funext z
    rw [smul_eq_mul, ← div_eq_inv_mul]
  rw [hfun] at hcauchy
  have hsphere_cont : ContinuousOn
      (fun z : ℂ => laplacePartial f T z * newmanKernel R T z / z)
      (Metric.sphere 0 R) := by
    apply ContinuousOn.div hSK_cont.continuousOn continuousOn_id
    intro z hz h0
    simp only [id_eq] at h0
    rw [mem_sphere_iff_norm, sub_zero] at hz
    rw [h0, norm_zero] at hz
    exact hR.ne' hz.symm
  have hsplitarc := circleIntegral_eq_rightArc_add_leftArc hR.le hsphere_cont
  rw [hcauchy] at hsplitarc
  have hgk := rightArc_gK_add_dentInt_gK hR hδ hRR' hRδ hδδ' hδ'0
    hU_open hg hsub T
  have hgK_cont : ContinuousOn (fun z => g z * newmanKernel R T z / z)
      (stadium R' δ' ∩ {(0 : ℂ)}ᶜ) :=
    ContinuousOn.div
      (((hg.continuousOn.mono hsub).mono Set.inter_subset_left).mul
        (continuous_newmanKernel.continuousOn))
      continuousOn_id (fun z hz => by simpa using hz.2)
  have hSKz_cont : ContinuousOn
      (fun z => laplacePartial f T z * newmanKernel R T z / z) {(0 : ℂ)}ᶜ :=
    ContinuousOn.div hSK_cont.continuousOn continuousOn_id
      (fun z hz => by simpa using hz)
  have harc_split : arcInt R (-(π / 2)) (π / 2)
        (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z)
      = arcInt R (-(π / 2)) (π / 2) (fun z => g z * newmanKernel R T z / z)
        - arcInt R (-(π / 2)) (π / 2)
            (fun z => laplacePartial f T z * newmanKernel R T z / z) := by
    have hptw : arcInt R (-(π / 2)) (π / 2)
          (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z)
        = arcInt R (-(π / 2)) (π / 2)
            (fun z => g z * newmanKernel R T z / z
              - laplacePartial f T z * newmanKernel R T z / z) :=
      arcInt_congr (fun θ _ => by ring)
    rw [hptw]
    exact arcInt_sub
      (intervalIntegrable_arc hgK_cont
        (fun θ hθ => ⟨arc_mem_stadium hR.le hRR' hδ'0 hθ,
          by simp; exact hR.ne'⟩))
      (intervalIntegrable_arc hSKz_cont
        (fun θ _ => by simp; exact hR.ne'))
  linear_combination -hgk - hsplitarc - harc_split

/-! ### C13–C14: the two arc estimates (E1, E2) -/

/-- A.e. avoidance of a single angle (degenerate arc endpoints are null). -/
theorem ae_ne_angle (a : ℝ) : ∀ᵐ θ : ℝ ∂volume, θ ≠ a := by
  have hset : {θ : ℝ | ¬θ ≠ a} = {a} := by ext θ; simp
  rw [MeasureTheory.ae_iff, hset]
  exact measure_singleton _

include hf_meas hf_bdd in
/-- **E1**: on the right arc the tail bound and the weight EXACTLY cancel the
exponentials: `‖rightArc((g−S_T)K/z)‖ ≤ 2πM/R`. -/
theorem norm_rightArc_le {R : ℝ} (hR : 0 < R) {T : ℝ} (hT : 0 ≤ T)
    {g : ℂ → ℂ}
    (hrep : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (0 : ℝ), f t * Complex.exp (-(z * t))) :
    ‖arcInt R (-(π / 2)) (π / 2)
        (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z)‖
      ≤ 2 * π * M / R := by
  unfold arcInt
  have hab : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have key : ‖∫ θ in (-(π / 2))..(π / 2),
      deriv (circleMap 0 R) θ •
        ((g (circleMap 0 R θ) - laplacePartial f T (circleMap 0 R θ))
          * newmanKernel R T (circleMap 0 R θ) / circleMap 0 R θ)‖
      ≤ ∫ _ in (-(π / 2))..(π / 2), 2 * M / R := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab ?_
      intervalIntegral.intervalIntegrable_const
    filter_upwards [ae_ne_angle (π / 2)] with θ hθne hθmem
    have hθIoo : θ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨hθmem.1, lt_of_le_of_ne hθmem.2 hθne⟩
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθIoo
    have hzre_pos : 0 < (circleMap 0 R θ).re := by
      rw [circleMap_re]; exact mul_pos hR hcos
    have hznorm : ‖circleMap 0 R θ‖ = R := by
      rw [norm_circleMap_zero, abs_of_pos hR]
    have hz0 : circleMap 0 R θ ≠ 0 := circleMap_ne_center hR.ne'
    have hgS : ‖g (circleMap 0 R θ) - laplacePartial f T (circleMap 0 R θ)‖
        ≤ M * Real.exp (-(circleMap 0 R θ).re * T) / (circleMap 0 R θ).re := by
      rw [laplace_sub_partial hf_meas hf_bdd hrep hzre_pos hT]
      exact norm_laplace_tail_le hf_meas hf_bdd hzre_pos hT
    have hker := norm_kernel_div_self hR T hznorm hz0
    rw [deriv_circleMap, smul_eq_mul, norm_mul, norm_mul, Complex.norm_I,
      mul_one, norm_circleMap_zero, abs_of_pos hR, mul_div_assoc, norm_mul,
      hker, abs_of_pos hzre_pos]
    calc R * (‖g (circleMap 0 R θ) - laplacePartial f T (circleMap 0 R θ)‖
          * (Real.exp (T * (circleMap 0 R θ).re) * (2 * (circleMap 0 R θ).re)
            / R ^ 2))
        ≤ R * ((M * Real.exp (-(circleMap 0 R θ).re * T) / (circleMap 0 R θ).re)
          * (Real.exp (T * (circleMap 0 R θ).re) * (2 * (circleMap 0 R θ).re)
            / R ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hR.le
          apply mul_le_mul_of_nonneg_right hgS
          positivity
      _ = 2 * M / R := by
          rw [show (-(circleMap 0 R θ).re * T : ℝ)
              = -(T * (circleMap 0 R θ).re) by ring, Real.exp_neg]
          have he : Real.exp (T * (circleMap 0 R θ).re) ≠ 0 := Real.exp_ne_zero _
          field_simp
  refine le_trans key ?_
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show (π / 2 - -(π / 2) : ℝ) = π by ring]
  rw [show (2 * π * M / R : ℝ) = π * (2 * M / R) by ring]

include hf_meas hf_bdd in
/-- **E2**: on the left arc the `S_T` bound and the weight cancel the same
way: `‖leftArc(S_T·K/z)‖ ≤ 2πM/R`. -/
theorem norm_leftArc_le (hM : 0 ≤ M) {R : ℝ} (hR : 0 < R) {T : ℝ} (hT : 0 ≤ T) :
    ‖arcInt R (π / 2) (3 * π / 2)
        (fun z => laplacePartial f T z * newmanKernel R T z / z)‖
      ≤ 2 * π * M / R := by
  unfold arcInt
  have hab : π / 2 ≤ 3 * π / 2 := by linarith [Real.pi_pos]
  have key : ‖∫ θ in (π / 2)..(3 * π / 2),
      deriv (circleMap 0 R) θ •
        (laplacePartial f T (circleMap 0 R θ)
          * newmanKernel R T (circleMap 0 R θ) / circleMap 0 R θ)‖
      ≤ ∫ _ in (π / 2)..(3 * π / 2), 2 * M / R := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab ?_
      intervalIntegral.intervalIntegrable_const
    filter_upwards [ae_ne_angle (3 * π / 2)] with θ hθne hθmem
    have hθIoo : θ ∈ Set.Ioo (π / 2) (3 * π / 2) :=
      ⟨hθmem.1, lt_of_le_of_ne hθmem.2 hθne⟩
    have hcos : Real.cos θ < 0 := by
      apply Real.cos_neg_of_pi_div_two_lt_of_lt hθIoo.1
      linarith [hθIoo.2]
    have hzre_neg : (circleMap 0 R θ).re < 0 := by
      rw [circleMap_re]
      exact mul_neg_of_pos_of_neg hR hcos
    have hznorm : ‖circleMap 0 R θ‖ = R := by
      rw [norm_circleMap_zero, abs_of_pos hR]
    have hz0 : circleMap 0 R θ ≠ 0 := circleMap_ne_center hR.ne'
    have hS := norm_laplacePartial_le hf_meas hf_bdd hM hT hzre_neg
    have hker := norm_kernel_div_self hR T hznorm hz0
    rw [deriv_circleMap, smul_eq_mul, norm_mul, norm_mul, Complex.norm_I,
      mul_one, norm_circleMap_zero, abs_of_pos hR, mul_div_assoc, norm_mul,
      hker, abs_of_neg hzre_neg]
    calc R * (‖laplacePartial f T (circleMap 0 R θ)‖
          * (Real.exp (T * (circleMap 0 R θ).re) * (2 * -(circleMap 0 R θ).re)
            / R ^ 2))
        ≤ R * ((M * Real.exp (-(circleMap 0 R θ).re * T)
            / -(circleMap 0 R θ).re)
          * (Real.exp (T * (circleMap 0 R θ).re) * (2 * -(circleMap 0 R θ).re)
            / R ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hR.le
          apply mul_le_mul_of_nonneg_right hS
          have hpos : 0 < -(circleMap 0 R θ).re := by linarith
          positivity
      _ = 2 * M / R := by
          rw [show (-(circleMap 0 R θ).re * T : ℝ)
              = -(T * (circleMap 0 R θ).re) by ring, Real.exp_neg]
          have he : Real.exp (T * (circleMap 0 R θ).re) ≠ 0 := Real.exp_ne_zero _
          have hne' : (circleMap 0 R θ).re ≠ 0 := ne_of_lt hzre_neg
          field_simp
  refine le_trans key ?_
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show (3 * π / 2 - π / 2 : ℝ) = π by ring]
  rw [show (2 * π * M / R : ℝ) = π * (2 * M / R) by ring]

end Bounded

/-! ### C15: the dent dies (E3) -/

/-- **E3**: at fixed `(R, δ)` the dent contribution of `gK/z` tends to `0`
as `T → ∞` — the jogs die like `C₀/T`, the vertical segment like
`C₀·e^{−δT}·2R`. -/
theorem tendsto_dentInt_gK {R δ R' δ' : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hRδ : R + δ < R') (hδδ' : δ < δ')
    {U : Set ℂ} {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hsub : stadium R' δ' ⊆ U) :
    Filter.Tendsto
      (fun T : ℝ => dentInt R δ (fun z => g z * newmanKernel R T z / z))
      Filter.atTop (nhds 0) := by
  set w : ℂ → ℂ := fun z => g z * (1 + z ^ 2 / (R : ℂ) ^ 2) / z with hwdef
  have hhw : ∀ (T : ℝ) (z : ℂ),
      g z * newmanKernel R T z / z = Complex.exp (z * T) * w z := by
    intro T z
    rw [hwdef]
    unfold newmanKernel
    ring
  have hm1 : ∀ x ∈ Set.uIcc (0 : ℝ) (-δ),
      (x : ℂ) + (R : ℂ) * Complex.I ∈ stadium R' δ' :=
    fun x hx => horiz_piece_mem_stadium hδ.le hRδ hδδ' hx
      (by rw [abs_of_nonneg hR.le])
  have hm2 : ∀ y ∈ Set.uIcc R (-R),
      ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ stadium R' δ' :=
    fun y hy => vert_piece_mem_stadium hδ.le hR.le hRδ hδδ' hy
  have hm3 : ∀ x ∈ Set.uIcc (-δ : ℝ) 0,
      (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I ∈ stadium R' δ' :=
    fun x hx => horiz_piece_mem_stadium hδ.le hRδ hδδ'
      (Set.uIcc_comm (-δ : ℝ) 0 ▸ hx) (by rw [abs_neg, abs_of_nonneg hR.le])
  have hz1 : ∀ x : ℝ, (x : ℂ) + (R : ℂ) * Complex.I ≠ 0 := by
    intro x h0
    have him : ((x : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
    rw [h0] at him
    simp at him
    exact hR.ne' him.symm
  have hz2 : ∀ y : ℝ, ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro y h0
    have hre : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = -δ := by simp
    rw [h0] at hre
    simp at hre
    exact hδ.ne' hre
  have hz3 : ∀ x : ℝ, (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro x h0
    have him : ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im = -R := by simp
    rw [h0] at him
    simp at him
    exact hR.ne' him
  have hwcont : ContinuousOn w (stadium R' δ' ∩ {(0 : ℂ)}ᶜ) := by
    rw [hwdef]
    exact ContinuousOn.div
      (((hg.continuousOn.mono hsub).mono Set.inter_subset_left).mul
        ((by fun_prop : Continuous
          (fun z : ℂ => 1 + z ^ 2 / (R : ℂ) ^ 2)).continuousOn))
      continuousOn_id (fun z hz => by simpa using hz.2)
  set Kset : Set ℂ :=
    ((fun x : ℝ => (x : ℂ) + (R : ℂ) * Complex.I) '' Set.uIcc (0 : ℝ) (-δ))
      ∪ ((fun y : ℝ => ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) '' Set.uIcc R (-R))
      ∪ ((fun x : ℝ => (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
          '' Set.uIcc (-δ : ℝ) 0) with hKdef
  have hKcompact : IsCompact Kset := by
    rw [hKdef]
    exact ((isCompact_uIcc.image (by fun_prop)).union
      (isCompact_uIcc.image (by fun_prop))).union
      (isCompact_uIcc.image (by fun_prop))
  have hKsub : Kset ⊆ stadium R' δ' ∩ {(0 : ℂ)}ᶜ := by
    rw [hKdef]
    rintro z (( ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩)
    · exact ⟨hm1 x hx, by simpa using hz1 x⟩
    · exact ⟨hm2 y hy, by simpa using hz2 y⟩
    · exact ⟨hm3 x hx, by simpa using hz3 x⟩
  obtain ⟨C₀, hC₀⟩ :=
    hKcompact.exists_bound_of_continuousOn (hwcont.mono hKsub)
  have hC₀0 : 0 ≤ C₀ :=
    le_trans (norm_nonneg _)
      (hC₀ _ (Set.mem_union_left _ (Set.mem_union_left _
        ⟨0, Set.left_mem_uIcc, rfl⟩)))
  have hFTC : ∀ T : ℝ, 0 < T →
      ∫ x in (-δ : ℝ)..0, C₀ * Real.exp (T * x) ≤ C₀ / T := by
    intro T hT
    have hderiv : ∀ x ∈ Set.uIcc (-δ : ℝ) 0,
        HasDerivAt (fun u : ℝ => C₀ * (Real.exp (T * u) / T))
          (C₀ * Real.exp (T * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun u : ℝ => T * u) T x := by
        simpa using (hasDerivAt_id x).const_mul T
      have h2 := (Real.hasDerivAt_exp (T * x)).comp_of_eq x h1 rfl
      have h3 := (h2.div_const T).const_mul C₀
      have hcancel : Real.exp (T * x) * T / T = Real.exp (T * x) :=
        mul_div_cancel_right₀ _ (ne_of_gt hT)
      simpa [Function.comp_def, hcancel] using h3
    have hval : ∫ x in (-δ : ℝ)..0, C₀ * Real.exp (T * x)
        = C₀ * (Real.exp (T * 0) / T) - C₀ * (Real.exp (T * (-δ)) / T) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [hval]
    have he1 : Real.exp (T * 0) = 1 := by rw [mul_zero, Real.exp_zero]
    have he2 : 0 < Real.exp (T * (-δ)) := Real.exp_pos _
    rw [he1]
    have hTC : 0 ≤ C₀ / T := by positivity
    have h2 : 0 ≤ C₀ * (Real.exp (T * (-δ)) / T) := by positivity
    calc C₀ * (1 / T) - C₀ * (Real.exp (T * (-δ)) / T)
        ≤ C₀ * (1 / T) := by linarith
      _ = C₀ / T := by ring
  apply squeeze_zero_norm'
    (a := fun T : ℝ => C₀ / T + C₀ * Real.exp (-δ * T) * (2 * R) + C₀ / T)
  · filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    have hdc : dentInt R δ (fun z => g z * newmanKernel R T z / z)
        = dentInt R δ (fun z => Complex.exp (z * T) * w z) :=
      dentInt_congr (fun x _ => hhw T _) (fun y _ => hhw T _)
        (fun x _ => hhw T _)
    rw [hdc]
    unfold dentInt
    have hnorm_exp : ∀ (x c : ℝ),
        ‖Complex.exp (((x : ℂ) + (c : ℂ) * Complex.I) * (T : ℂ))‖
          = Real.exp (x * T) := by
      intro x c
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    have hbound1 : ‖∫ x in (0 : ℝ)..(-δ),
        Complex.exp (((x : ℂ) + (R : ℂ) * Complex.I) * (T : ℂ))
          * w ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤ C₀ / T := by
      rw [intervalIntegral.integral_symm, norm_neg]
      refine le_trans ?_ (hFTC T hT)
      apply intervalIntegral.norm_integral_le_of_norm_le
        (by linarith : (-δ : ℝ) ≤ 0) ?_
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      filter_upwards with x hx
      rw [norm_mul, hnorm_exp]
      have hxu : x ∈ Set.uIcc (0 : ℝ) (-δ) := by
        rw [Set.uIcc_of_ge (by linarith : (-δ : ℝ) ≤ 0)]
        exact ⟨hx.1.le, hx.2⟩
      have hwb : ‖w ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤ C₀ :=
        hC₀ _ (Set.mem_union_left _ (Set.mem_union_left _ ⟨x, hxu, rfl⟩))
      calc Real.exp (x * T) * ‖w ((x : ℂ) + (R : ℂ) * Complex.I)‖
          ≤ Real.exp (x * T) * C₀ :=
            mul_le_mul_of_nonneg_left hwb (Real.exp_nonneg _)
        _ = C₀ * Real.exp (T * x) := by rw [mul_comm x T]; ring
    have hbound3 : ‖∫ x in (-δ : ℝ)..0,
        Complex.exp (((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) * (T : ℂ))
          * w ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ ≤ C₀ / T := by
      refine le_trans ?_ (hFTC T hT)
      apply intervalIntegral.norm_integral_le_of_norm_le
        (by linarith : (-δ : ℝ) ≤ 0) ?_
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      filter_upwards with x hx
      rw [norm_mul, hnorm_exp]
      have hxu : x ∈ Set.uIcc (-δ : ℝ) 0 := by
        rw [Set.uIcc_of_le (by linarith : (-δ : ℝ) ≤ 0)]
        exact ⟨hx.1.le, hx.2⟩
      have hwb : ‖w ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ ≤ C₀ :=
        hC₀ _ (Set.mem_union_right _ ⟨x, hxu, rfl⟩)
      calc Real.exp (x * T) * ‖w ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖
          ≤ Real.exp (x * T) * C₀ :=
            mul_le_mul_of_nonneg_left hwb (Real.exp_nonneg _)
        _ = C₀ * Real.exp (T * x) := by rw [mul_comm x T]; ring
    have hbound2 : ‖∫ y in R..(-R),
        Complex.I * (Complex.exp ((((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) * (T : ℂ))
          * w (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
        ≤ C₀ * Real.exp (-δ * T) * (2 * R) := by
      have hconst : ∀ y ∈ Set.uIoc R (-R),
          ‖Complex.I * (Complex.exp ((((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
              * (T : ℂ)) * w (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
            ≤ C₀ * Real.exp (-δ * T) := by
        intro y hy
        rw [norm_mul, Complex.norm_I, one_mul, norm_mul, hnorm_exp]
        have hyu : y ∈ Set.uIcc R (-R) := Set.uIoc_subset_uIcc hy
        have hwb : ‖w (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C₀ :=
          hC₀ _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨y, hyu, rfl⟩))
        calc Real.exp (-δ * T) * ‖w (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
            ≤ Real.exp (-δ * T) * C₀ :=
              mul_le_mul_of_nonneg_left hwb (Real.exp_nonneg _)
          _ = C₀ * Real.exp (-δ * T) := by ring
      refine le_trans
        (intervalIntegral.norm_integral_le_of_norm_le_const hconst) ?_
      have habs : |(-R : ℝ) - R| = 2 * R := by
        rw [show (-R - R : ℝ) = -(2 * R) by ring, abs_neg,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * R)]
      rw [habs]
    calc ‖(∫ x in (0 : ℝ)..(-δ),
          Complex.exp (((x : ℂ) + (R : ℂ) * Complex.I) * (T : ℂ))
            * w ((x : ℂ) + (R : ℂ) * Complex.I))
        + (∫ y in R..(-R),
            Complex.I * (Complex.exp ((((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
              * (T : ℂ)) * w (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
        + ∫ x in (-δ : ℝ)..0,
            Complex.exp (((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) * (T : ℂ))
              * w ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖∫ x in (0 : ℝ)..(-δ),
            Complex.exp (((x : ℂ) + (R : ℂ) * Complex.I) * (T : ℂ))
              * w ((x : ℂ) + (R : ℂ) * Complex.I)‖
          + ‖∫ y in R..(-R),
              Complex.I * (Complex.exp ((((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
                * (T : ℂ)) * w (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
          + ‖∫ x in (-δ : ℝ)..0,
              Complex.exp (((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) * (T : ℂ))
                * w ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ :=
        norm_add₃_le
      _ ≤ C₀ / T + C₀ * Real.exp (-δ * T) * (2 * R) + C₀ / T :=
        add_le_add (add_le_add hbound1 hbound2) hbound3
  · have h1 : Filter.Tendsto (fun T : ℝ => C₀ / T) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul C₀
    have h2 : Filter.Tendsto (fun T : ℝ => C₀ * Real.exp (-δ * T) * (2 * R))
        Filter.atTop (nhds 0) := by
      have hlin : Filter.Tendsto (fun T : ℝ => δ * T) Filter.atTop
          Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hδ Filter.tendsto_id
      have hbase : Filter.Tendsto (fun T : ℝ => Real.exp (-δ * T))
          Filter.atTop (nhds 0) := by
        simpa [Function.comp_def, neg_mul]
          using Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
      simpa using (hbase.const_mul C₀).mul_const (2 * R)
    simpa using (h1.add h2).add h1


/-! ### C16: NEWMAN'S ANALYTIC THEOREM -/

/-- **NEWMAN'S ANALYTIC THEOREM (the Tauberian core)**.  Let `f` be
a.e.-measurable and bounded on `(0,∞)`, and suppose its Laplace transform
`g(z) = ∫_0^∞ f(t)e^{−zt} dt` (defined for `Re z > 0`) extends to a
holomorphic function on an open set `U ⊇ {Re ≥ 0}`.  Then the improper
integral converges: `∫_0^T f → g(0)` as `T → ∞`.

ε-schedule: `R := max 1 (4M/ε + 1)`, the stadium fits inside `U` at radius
`R + 1` by compact thickening, and Zagier's ledger gives
`‖g(0) − ∫_0^T f‖ ≤ 2M/R + ‖dent‖/2π` with the dent dying as `T → ∞`. -/
theorem newman_tauberian {f : ℝ → ℂ} {M : ℝ} {U : Set ℂ} {g : ℂ → ℂ}
    (hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hf_bdd : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f t‖ ≤ M)
    (hU_open : IsOpen U) (hU_mem : {z : ℂ | 0 ≤ z.re} ⊆ U)
    (hg : DifferentiableOn ℂ g U)
    (hrep : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (0 : ℝ), f t * Complex.exp (-(z * t))) :
    Filter.Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t)
      Filter.atTop (nhds (g 0)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hf_bdd 1 (by norm_num))
  have hπ0 : (0 : ℝ) < π := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := max 1 (4 * M / ε + 1) with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRM : 4 * M / ε + 1 ≤ R := le_max_right _ _
  obtain ⟨δ₀, hδ₀, hsub₀⟩ := exists_stadium_subset hU_open hU_mem
    (show (0 : ℝ) < R + 1 by linarith)
  set δ' : ℝ := min δ₀ 1 with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ₀ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hsub : stadium (R + 1) δ' ⊆ U := by
    intro z hz
    rw [mem_stadium_iff] at hz
    apply hsub₀
    rw [mem_stadium_iff]
    exact ⟨hz.1, by linarith [min_le_left δ₀ 1, hz.2]⟩
  set δ : ℝ := δ' / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδδ' : δ < δ' := by rw [hδdef]; linarith
  have hRR' : R < R + 1 := by linarith
  have hRδ : R + δ < R + 1 := by
    rw [hδdef]; linarith
  have h2MR : 2 * M / R < ε / 2 := by
    rcases eq_or_lt_of_le hM0 with hM | hM
    · rw [← hM]
      simp
      positivity
    · have h4 : 4 * M / ε < R := lt_of_lt_of_le (by linarith) hRM
      rw [div_lt_iff₀ hR0]
      rw [div_lt_iff₀ hε] at h4
      linarith
  have hE3 := tendsto_dentInt_gK (R := R) (δ := δ) hR0 hδ0 hRδ hδδ' hg hsub
  have hev : ∀ᶠ T in Filter.atTop,
      ‖dentInt R δ (fun z => g z * newmanKernel R T z / z)‖ < π * ε := by
    have hπε : (0 : ℝ) < π * ε := by positivity
    filter_upwards [Metric.tendsto_nhds.mp hE3 (π * ε) hπε] with T hT
    rwa [dist_zero_right] at hT
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    (hev.and (Filter.eventually_ge_atTop 0))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hdent, hTpos⟩ := hT₀ T hT
  have hmaster := contour_master hf_meas hf_bdd hR0 hδ0 hRR' hRδ hδδ' hδ'0
    hU_open hg hsub T
  have hE1 := norm_rightArc_le hf_meas hf_bdd hR0 hTpos hrep
  have hE2 := norm_leftArc_le hf_meas hf_bdd hM0 hR0 hTpos
  have hbound : ‖2 * ((π : ℝ) : ℂ) * Complex.I
      * (g 0 - laplacePartial f T 0)‖
      ≤ 2 * π * M / R + π * ε + 2 * π * M / R := by
    rw [hmaster]
    calc ‖arcInt R (-(π / 2)) (π / 2)
          (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z)
        + dentInt R δ (fun z => g z * newmanKernel R T z / z)
        - arcInt R (π / 2) (3 * π / 2)
            (fun z => laplacePartial f T z * newmanKernel R T z / z)‖
        ≤ ‖arcInt R (-(π / 2)) (π / 2)
            (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z)
          + dentInt R δ (fun z => g z * newmanKernel R T z / z)‖
          + ‖arcInt R (π / 2) (3 * π / 2)
              (fun z => laplacePartial f T z * newmanKernel R T z / z)‖ :=
        norm_sub_le _ _
      _ ≤ ‖arcInt R (-(π / 2)) (π / 2)
            (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z)‖
          + ‖dentInt R δ (fun z => g z * newmanKernel R T z / z)‖
          + ‖arcInt R (π / 2) (3 * π / 2)
              (fun z => laplacePartial f T z * newmanKernel R T z / z)‖ := by
        have := norm_add_le
          (arcInt R (-(π / 2)) (π / 2)
            (fun z => (g z - laplacePartial f T z) * newmanKernel R T z / z))
          (dentInt R δ (fun z => g z * newmanKernel R T z / z))
        linarith
      _ ≤ 2 * π * M / R + π * ε + 2 * π * M / R :=
        add_le_add (add_le_add hE1 hdent.le) hE2
  have hnorm2π : ‖2 * ((π : ℝ) : ℂ) * Complex.I
      * (g 0 - laplacePartial f T 0)‖
      = 2 * π * ‖g 0 - laplacePartial f T 0‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ0]
    norm_num
  rw [hnorm2π] at hbound
  have hdist : dist (∫ t in (0 : ℝ)..T, f t) (g 0)
      = ‖g 0 - laplacePartial f T 0‖ := by
    rw [dist_eq_norm, ← laplacePartial_zero hTpos, norm_sub_rev]
  rw [hdist]
  refine lt_of_mul_lt_mul_left ?_ (by positivity : (0 : ℝ) ≤ 2 * π)
  have hmul := mul_lt_mul_of_pos_left h2MR hπ0
  have heq1 : π * (2 * M / R) = 2 * π * M / R := by ring
  have heq2 : π * (ε / 2) * 2 = π * ε := by ring
  linarith [hbound, hmul, heq1, heq2]

end Tauberian
end EuclidsPath
