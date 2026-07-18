/-
  Tauberian/StadiumPrimitive — STAGE N-A of the Tauberian campaign: primitives
  of holomorphic functions on the Newman STADIUM `ball 0 R ∩ {Re > −δ}`.

  ORIGIN.  The Tauberian campaign (approved plan): Newman's analytic theorem
  needs a primitive of the pole-subtracted integrand on the dented contour
  region.  The pin contains the Morera/wedge machinery for DISCS
  (`Mathlib/Analysis/Complex/HasPrimitives.lean`, upstreamed from the
  PrimeNumberTheoremAnd project); this module transports it to the stadium.

  DESIGN SIMPLIFICATION (found during the port, de-risking the plan's A9):
  the two little-o lemmas need NOT be ported.  At `z` in the stadium, the
  ball `ball z (gap z)` lies inside the stadium (`ball_gap_subset`), so the
  pin's PUBLIC `Complex.IsConservativeOn.hasDerivAt_wedgeIntegral` applied
  to that ball WITH CENTER `z` already differentiates the local wedge
  `wedgeIntegral z · f` at `z`.  Only the PATH-INDEPENDENCE step (the
  eight-integral bookkeeping `Φ(w) − Φ(z) = wedgeIntegral z w f`) needs the
  stadium geometry — and its memberships all reduce to convexity plus one
  corner estimate `(‖z‖ + ρ)² < R²`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `stadium R δ` — open (`isOpen_stadium`), convex (`convex_stadium`),
      with the `gap`-radius safety ball (`ball_gap_subset`);
    * membership lemmas: real projections (`ofReal_re_mem_stadium`), the
      mixed corner (`mix_mem_stadium`), horizontal/vertical segments;
    * `wedgeIntegral_sub_wedgeIntegral_stadium` — path independence of the
      0-anchored wedge integral (the ported eight-integral ledger);
    * `IsConservativeOn.hasDerivAt_wedgeIntegral_stadium` — the primitive's
      derivative at every stadium point;
    * `DifferentiableOn.isExactOn_stadium` — **THE DELIVERABLE**: a
      holomorphic function on the stadium has a primitive there.

  NUMERIC GROUNDING: `scripts/newman_prepass.py` — ALL CHECKS PASSED
  (master contour ledger over the (R, δ, T) grid at machine precision,
  telescoping sub-identities, negative control).

  DISCLOSURES.
    * Pure complex-analytic infrastructure: no arithmetic content, no face
      of the parity wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Tauberian

open Complex MeasureTheory Metric Set
open scoped Interval

/-! ### Layer 1: the stadium and its geometry -/

/-- The Newman stadium: the open disc dented to the half-plane `Re > −δ`. -/
def stadium (R δ : ℝ) : Set ℂ := Metric.ball 0 R ∩ {z : ℂ | -δ < z.re}

theorem mem_stadium_iff {R δ : ℝ} {z : ℂ} :
    z ∈ stadium R δ ↔ ‖z‖ < R ∧ -δ < z.re := by
  unfold stadium
  rw [Set.mem_inter_iff, mem_ball_zero_iff, Set.mem_setOf_eq]

theorem isOpen_stadium {R δ : ℝ} : IsOpen (stadium R δ) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem convex_stadium {R δ : ℝ} : Convex ℝ (stadium R δ) := by
  refine (convex_ball 0 R).inter ?_
  have h : {z : ℂ | -δ < z.re} = Complex.reCLM ⁻¹' Set.Ioi (-δ) := rfl
  rw [h]
  exact (convex_Ioi (-δ)).linear_preimage Complex.reCLM.toLinearMap

theorem zero_mem_stadium {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    (0 : ℂ) ∈ stadium R δ := by
  rw [mem_stadium_iff]
  simpa using ⟨hR, hδ⟩

/-- The safety radius at a stadium point. -/
noncomputable def gap (R δ : ℝ) (z : ℂ) : ℝ := min (R - ‖z‖) (z.re + δ)

theorem gap_pos {R δ : ℝ} {z : ℂ} (hz : z ∈ stadium R δ) : 0 < gap R δ z := by
  rw [mem_stadium_iff] at hz
  unfold gap
  exact lt_min (by linarith [hz.1]) (by linarith [hz.2])

theorem ball_gap_subset {R δ : ℝ} {z : ℂ} (_hz : z ∈ stadium R δ) :
    Metric.ball z (gap R δ z) ⊆ stadium R δ := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  rw [mem_stadium_iff]
  constructor
  · calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ < ‖z‖ + (R - ‖z‖) := by
          have := lt_of_lt_of_le hw (min_le_left _ _)
          linarith
      _ = R := by ring
  · have hre : |w.re - z.re| ≤ ‖w - z‖ := by
      calc |w.re - z.re| = |(w - z).re| := by rw [Complex.sub_re]
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have hlt : |w.re - z.re| < z.re + δ :=
      lt_of_le_of_lt hre (lt_of_lt_of_le hw (min_le_right _ _))
    have h1 := (abs_lt.mp hlt).1
    linarith

/-- Real projections of stadium points lie in the stadium. -/
theorem ofReal_re_mem_stadium {R δ : ℝ} {z : ℂ} (hz : z ∈ stadium R δ) :
    ((z.re : ℝ) : ℂ) ∈ stadium R δ := by
  rw [mem_stadium_iff] at hz ⊢
  refine ⟨?_, by simpa using hz.2⟩
  rw [Complex.norm_real]
  exact lt_of_le_of_lt (Complex.abs_re_le_norm z) hz.1

/-- **The one nontrivial corner**: for `w` in the safety ball of `z`, the
mixed corner `w.re + z.im·I` lies in the stadium (`(‖z‖ + ρ)² < R²`). -/
theorem mix_mem_stadium {R δ : ℝ} {z w : ℂ} (hz : z ∈ stadium R δ)
    (hw : w ∈ Metric.ball z (gap R δ z)) :
    (w.re : ℂ) + z.im * I ∈ stadium R δ := by
  rw [mem_ball, dist_eq_norm] at hw
  have hz' := hz
  rw [mem_stadium_iff] at hz' ⊢
  set ρ := ‖w - z‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρR : ρ < R - ‖z‖ := lt_of_lt_of_le hw (min_le_left _ _)
  have hρδ : ρ < z.re + δ := lt_of_lt_of_le hw (min_le_right _ _)
  have hre : |w.re - z.re| ≤ ρ := by
    calc |w.re - z.re| = |(w - z).re| := by rw [Complex.sub_re]
      _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
  constructor
  · -- ‖w.re + z.im·I‖² = w.re² + z.im² ≤ (‖z‖ + ρ)² < R²
    have hnorm : ‖(w.re : ℂ) + (z.im : ℂ) * I‖ = Real.sqrt (w.re ^ 2 + z.im ^ 2) := by
      rw [Complex.norm_add_mul_I]
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
    have hzn : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      rw [← Complex.norm_add_mul_I, Complex.re_add_im]
    have hzsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [hzn, Real.sq_sqrt (by positivity)]
    have habs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hwre : |w.re| ≤ |z.re| + ρ := by
      have h1 : |w.re| = |z.re + (w.re - z.re)| := by ring_nf
      rw [h1]
      exact le_trans (abs_add_le _ _) (by linarith [hre])
    have hkey : w.re ^ 2 + z.im ^ 2 < R ^ 2 := by
      have h1 : w.re ^ 2 ≤ (|z.re| + ρ) ^ 2 := by
        have hs := sq_abs w.re
        nlinarith [abs_nonneg w.re, abs_nonneg z.re]
      have h2 : (|z.re| + ρ) ^ 2 + z.im ^ 2 ≤ (‖z‖ + ρ) ^ 2 := by
        have hsq := sq_abs z.re
        nlinarith [abs_nonneg z.re]
      have h3 : (‖z‖ + ρ) ^ 2 < R ^ 2 := by nlinarith
      linarith
    have hR0 : (0 : ℝ) < R := lt_of_le_of_lt (by positivity : (0:ℝ) ≤ ‖z‖) hz'.1
    have hRR : R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hR0.le).symm
    rw [hnorm, hRR]
    exact Real.sqrt_lt_sqrt (by positivity) hkey
  · -- Re-part: w.re > z.re − ρ > −δ
    have hre_eq : ((w.re : ℂ) + (z.im : ℂ) * I).re = w.re := by simp
    rw [hre_eq]
    have h1 := (abs_le.mp hre).1
    linarith

/-- Horizontal segments between two stadium points at the same height stay in
the stadium (degenerate-rectangle convexity, mirror of the pin's aux). -/
theorem horiz_seg_subset_stadium {R δ : ℝ} {a₁ a₂ b : ℝ}
    (h₁ : (a₁ : ℂ) + b * I ∈ stadium R δ) (h₂ : (a₂ : ℂ) + b * I ∈ stadium R δ) :
    (fun x : ℝ => (x : ℂ) + b * I) '' Set.uIcc a₁ a₂ ⊆ stadium R δ := by
  convert! Convex.rectangle_subset convex_stadium h₁ h₂ ?_ ?_ using 1 <;>
  simp [horizontalSegment_eq a₁ a₂ b, h₁, h₂, Rectangle]

/-- Vertical segments between two stadium points on the same vertical line. -/
theorem vert_seg_subset_stadium {R δ : ℝ} {a b₁ b₂ : ℝ}
    (h₁ : (a : ℂ) + b₁ * I ∈ stadium R δ) (h₂ : (a : ℂ) + b₂ * I ∈ stadium R δ) :
    (fun y : ℝ => (a : ℂ) + y * I) '' Set.uIcc b₁ b₂ ⊆ stadium R δ := by
  convert! Convex.rectangle_subset convex_stadium h₁ h₂ ?_ ?_ using 1 <;>
  simp [verticalSegment_eq a b₁ b₂, h₁, h₂, Rectangle]

/-! ### Layer 2: path independence of the 0-anchored wedge -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Path independence on the stadium** (the ported eight-integral ledger):
for `w` near `z`, the 0-anchored wedge integral is additive through `z`. -/
theorem wedgeIntegral_sub_wedgeIntegral_stadium {R δ : ℝ} {f : ℂ → E}
    (hR : 0 < R) (hδ : 0 < δ)
    (f_cont : ContinuousOn f (stadium R δ))
    (hf : Complex.IsConservativeOn f (stadium R δ))
    {z : ℂ} (hz : z ∈ stadium R δ) :
    ∀ᶠ w in nhds z,
      Complex.wedgeIntegral 0 w f - Complex.wedgeIntegral 0 z f
        = Complex.wedgeIntegral z w f := by
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball z (gap R δ z), Metric.ball_mem_nhds z (gap_pos hz), fun w hwball => ?_⟩
  have hw : w ∈ stadium R δ := ball_gap_subset hz hwball
  have h0 : (0 : ℂ) ∈ stadium R δ := zero_mem_stadium hR hδ
  have hzre : ((z.re : ℝ) : ℂ) ∈ stadium R δ := ofReal_re_mem_stadium hz
  have hwre : ((w.re : ℝ) : ℂ) ∈ stadium R δ := ofReal_re_mem_stadium hw
  have hmix : (w.re : ℂ) + z.im * I ∈ stadium R δ := mix_mem_stadium hz hwball
  -- the eight integrals with anchor c = 0 (c.re = c.im = 0)
  set I₁ := ∫ x : ℝ in (0:ℝ)..w.re, f ((x : ℂ) + (0:ℝ) * I) with hI₁def
  set I₂ := I • ∫ y : ℝ in (0:ℝ)..w.im, f ((w.re : ℂ) + y * I) with hI₂def
  set I₃ := ∫ x : ℝ in (0:ℝ)..z.re, f ((x : ℂ) + (0:ℝ) * I) with hI₃def
  set I₄ := I • ∫ y : ℝ in (0:ℝ)..z.im, f ((z.re : ℂ) + y * I) with hI₄def
  set I₅ := ∫ x : ℝ in z.re..w.re, f ((x : ℂ) + z.im * I) with hI₅def
  set I₆ := I • ∫ y : ℝ in z.im..w.im, f ((w.re : ℂ) + y * I) with hI₆def
  set I₇ := ∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (0:ℝ) * I) with hI₇def
  set I₈ := I • ∫ y : ℝ in (0:ℝ)..z.im, f ((w.re : ℂ) + y * I) with hI₈def
  have integrableHoriz : ∀ (a₁ a₂ b : ℝ), (a₁ : ℂ) + b * I ∈ stadium R δ →
      (a₂ : ℂ) + b * I ∈ stadium R δ →
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + b * I)) volume a₁ a₂ := by
    intro a₁ a₂ b h₁ h₂
    exact ((f_cont.mono (horiz_seg_subset_stadium h₁ h₂)).comp (by fun_prop)
      (Set.mapsTo_image _ _)).intervalIntegrable
  have integrableVert : ∀ (a b₁ b₂ : ℝ), (a : ℂ) + b₁ * I ∈ stadium R δ →
      (a : ℂ) + b₂ * I ∈ stadium R δ →
      IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + y * I)) volume b₁ b₂ := by
    intro a b₁ b₂ h₁ h₂
    exact ((f_cont.mono (vert_seg_subset_stadium h₁ h₂)).comp (by fun_prop)
      (Set.mapsTo_image _ _)).intervalIntegrable
  have hsplit₁ : I₁ = I₃ + I₇ := by
    rw [hI₁def, hI₃def, hI₇def,
      intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · simpa using h0
    · simpa using hzre
    · simpa using hzre
    · simpa using hwre
  have hsplit₂ : I₂ = I₈ + I₆ := by
    rw [hI₂def, hI₈def, hI₆def, ← smul_add,
      intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · simpa using hwre
    · exact hmix
    · exact hmix
    · simpa using hw
  have hrect : I₇ - I₅ + I₈ - I₄ = 0 := by
    have hU : Rectangle ((z.re : ℂ) + (0:ℝ) * I) ((w.re : ℂ) + z.im * I)
        ⊆ stadium R δ := by
      refine Convex.rectangle_subset convex_stadium ?_ hmix ?_ ?_
      · simpa using hzre
      · simpa using hz
      · simpa using hwre
    have := hf ((z.re : ℂ) + (0:ℝ) * I) ((w.re : ℂ) + z.im * I) hU
    rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq] at this
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im] at this
    -- this : the four-piece rectangle identity; match it to I₇, I₅, I₈, I₄
    rw [hI₇def, hI₅def, hI₈def, hI₄def]
    convert this using 2 <;> norm_num
  -- assemble: wedge(0,w) − wedge(0,z) = (I₁ + I₂) − (I₃ + I₄) = I₅ + I₆ = wedge(z,w)
  show (I₁ + I₂) - (I₃ + I₄) = I₅ + I₆
  have : I₁ + I₂ = I₃ + I₇ + (I₈ + I₆) := by rw [← hsplit₁, ← hsplit₂]
  calc (I₁ + I₂) - (I₃ + I₄)
      = (I₃ + I₇ + (I₈ + I₆)) - (I₃ + I₄) := by rw [this]
    _ = (I₇ - I₅ + I₈ - I₄) + (I₅ + I₆) := by abel
    _ = I₅ + I₆ := by rw [hrect]; abel

/-! ### Layer 3: the primitive -/

variable [CompleteSpace E]

/-- The 0-anchored wedge integral differentiates to `f` at every stadium
point: path independence + the pin's PUBLIC ball theorem at center `z`. -/
theorem IsConservativeOn.hasDerivAt_wedgeIntegral_stadium {R δ : ℝ} {f : ℂ → E}
    (hR : 0 < R) (hδ : 0 < δ)
    (f_cont : ContinuousOn f (stadium R δ))
    (hf : Complex.IsConservativeOn f (stadium R δ))
    {z : ℂ} (hz : z ∈ stadium R δ) :
    HasDerivAt (fun w => Complex.wedgeIntegral 0 w f) (f z) z := by
  -- the local wedge at center z differentiates by the pin's ball theorem
  have hball : Metric.ball z (gap R δ z) ⊆ stadium R δ := ball_gap_subset hz
  have hloc : HasDerivAt (fun w => Complex.wedgeIntegral z w f) (f z) z :=
    (Complex.IsConservativeOn.mono hball hf).hasDerivAt_wedgeIntegral
      (f_cont.mono hball) (mem_ball_self (gap_pos hz))
  -- transport along path independence
  have hpath := wedgeIntegral_sub_wedgeIntegral_stadium hR hδ f_cont hf hz
  have hcongr : (fun w => Complex.wedgeIntegral 0 w f)
      =ᶠ[nhds z] fun w => Complex.wedgeIntegral 0 z f
        + Complex.wedgeIntegral z w f := by
    filter_upwards [hpath] with w hw
    rw [← hw]
    abel
  rw [hasDerivAt_iff_isLittleO] at hloc ⊢
  have hzz : Complex.wedgeIntegral z z f = 0 := by
    simp [Complex.wedgeIntegral]
  refine hloc.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hcongr] with w hw
  simp only [hw, hzz, sub_zero, add_sub_cancel_left]

/-- **THE DELIVERABLE (Morera on the stadium)**: a holomorphic function on
the Newman stadium has a primitive there. -/
theorem DifferentiableOn.isExactOn_stadium {R δ : ℝ} {f : ℂ → E}
    (hR : 0 < R) (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (stadium R δ)) :
    Complex.IsExactOn f (stadium R δ) :=
  ⟨fun z => Complex.wedgeIntegral 0 z f, fun _ hz =>
    IsConservativeOn.hasDerivAt_wedgeIntegral_stadium hR hδ
      hf.continuousOn hf.isConservativeOn hz⟩

end Tauberian
end EuclidsPath
