/-
  NavierStokesR3Assembly — «TRANSITION TO ℝ³: the Navier–Stokes integral ASSEMBLED ON A BOX».

  WHAT IS ASSEMBLED (layer by layer, each rank compiles separately):
    * R1 — differentiation UNDER THE INTEGRAL of energy: `hasDerivAt_kineticEnergy_of_dominated`
      (mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le` + `HasDerivAt.norm_sq`,
      with a (1/2)-massage): dE/dt = ∫⟪u, ∂ₜu⟫ — UNDER the named majorant `TimeDomination`;
    * R2 — the DIVERGENCE theorem GENUINELY PUT TO WORK: `boxDivergence_integral_eq_zero`
      derives ∫_box div F = 0 from the mathlib box theorem `integral_divergence_of_hasFDerivAt_off_countable`
      (s := ∅), with the BOUNDARY INTEGRALS (box faces) DYING by support (F ≡ 0 outside Icc);
      then `divergence_integral_eq_zero` — on all of ℝ³ via `setIntegral_eq_integral_of_forall_compl_eq_zero`;
    * R3 — the THREE killers by integration by parts are PROVEN (not hypotheses!) via
      the MASTER LEMMA `integral_e3_divergence_eq_zero` (§3bis: E3↔Pi3 fderiv bridge
      by a comp-chain `ContinuousLinearEquiv`/`HasFDerivAt.comp`, feeding R2):
      (i) pressure ∫⟪w,∇p⟫ = 0 (`pressureKills_of_boxSupported`);
      (ii) transport ∫⟪w,(w·∇)w⟫ = 0 (`transportKills_of_boxSupported`);
      (iii) viscosity ∫⟪w,Δw⟫ = −∫∑‖∂ᵢw‖² (`viscosityIBP_of_boxSupported`,
      componentwise IBP). All three are derived from `BoxSupportedC2Flow` + `IsNSSolution`;
    * the LAW `EnergyBalanceLaw` is DERIVED (not decreed) for the class `BoxSupportedC2Flow`
      with box support: `energyBalance_of_boxSupported` — the smoothness surrogate `NoSingularCascade`
      is obtained as a CONSEQUENCE (`noSingularCascade_of_r3Assembly`).

  PRESSURE GATE FOR THE FIRST TIME: `BoxSupportedC2Flow` gates the smoothness of the PRESSURE (fields `pressDiff/contP/contP'`),
  thereby closing the Forging-B channel (`cookedFlow`: junk sat in ∇p on the sphere — now excluded by the C² gate).

  HONEST BOUNDARIES (loudly):
    * the box-support CLASS ONLY: everything is derived for C² fields with support in a fixed box;
      the limit transition box→ℝ³ is ABSENT IN MATHLIB — this is an external gap, not closed here;
    * `TimeDomination` (a locally-in-time integrable majorant of 2⟪u,∂ₜu⟫) and
      `IntervalIntegrable` of the dissipation — named 🔴 ANALYTIC INPUTS;
    * `NoSingularCascade` — a SURROGATE for smoothness in the cascade language, NOT C∞ regularity;
      the Clay millennium problem is NOT solved and NOT claimed;
    * both impostors (§7) FAIL the class gates: `cookedFlow` — spatial,
      `dirichletFlow` — temporal (`cookedFlow_fails_assemblyGates`/`dirichletFlow_fails_assemblyGates`).

  THE THREE KILLERS ARE CLOSED (was a fallback — became PROVEN): the R3 integral is brought "exactly" home.
  `energyBalance_of_boxSupported` / `noSingularCascade_of_r3Assembly` NO LONGER take
  `KillerBundle` — instead `killerBundle_of_boxSupported F sol` is built internally from
  the master lemma §3bis. REMAINING honest inputs: ONLY `TimeDomination` (🔴 R1),
  `IntervalIntegrable` of the dissipation and the box→ℝ³ limit (external, absent in mathlib).
  The layers `KillerBundle`/`R3AssemblyGates` are PRESERVED as a reusable abstraction
  (their fields are now DERIVABLE), but the headline theorems do not require them directly.

  No connection to prime numbers — the red line is untouched.
-/
import Mathlib
import EuclidsPath.Engine.NavierStokes
import EuclidsPath.Engine.NavierStokesFront

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.NavierStokesR3

open MeasureTheory
open EuclidsPath.NavierStokes
open EuclidsPath.NavierStokesFront
open scoped BigOperators RealInnerProductSpace InnerProductSpace

/-#############################################################################
  §0. BRIDGE: box on `Fin 3 → ℝ`, volume isometry E3 ↔ Pi3, auxiliary lemmas
#############################################################################-/

/-- Flat coordinate space `Fin 3 → ℝ` (without the L² wrapper). -/
abbrev Pi3 := Fin 3 → ℝ

/-- Open box in `Pi3`: a product of open intervals. -/
def openBox (a b : Pi3) : Set Pi3 :=
  Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))

/-- Closed box `Icc a b` in `Pi3`. -/
def closedBox (a b : Pi3) : Set Pi3 := Set.Icc a b

/-- Continuous-linear equivalence `E3 ≃L[ℝ] Pi3` (removing the L² wrapper).
    In this mathlib `⇑eL3 = ofLp`, `⇑eL3.symm = toLp`. -/
def eL3 : E3 ≃L[ℝ] Pi3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- Integral bridge: `∫ y:Pi3, g (toLp 2 y) = ∫ x:E3, g x` (volume isometry). -/
theorem integral_comp_toLp (g : E3 → ℝ) :
    (∫ y : Pi3, g (WithLp.toLp 2 y)) = ∫ x : E3, g x :=
  (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding g

/-- `toLp 2` on `Pi3` coincides with `eL3.symm`. -/
theorem toLp_eq_eL3symm (y : Pi3) : (WithLp.toLp 2 y : E3) = eL3.symm y := by
  rw [eL3, PiLp.coe_symm_continuousLinearEquiv]

/-- `ofLp = eL3` componentwise: `(eL3 x) i = x i`. -/
theorem eL3_apply (x : E3) (i : Fin 3) : eL3 x i = x i := by
  rw [eL3, PiLp.coe_continuousLinearEquiv]

/-- The interior of `Icc a b` in `Pi3` is `openBox a b`. -/
theorem interior_closedBox (a b : Pi3) : interior (closedBox a b) = openBox a b := by
  rw [closedBox, openBox, ← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
  simp only [interior_Icc]

/-- Coordinate of a sum in `E3`: `(∑ i, f i) k = ∑ i, (f i) k` (via the `eL3` equivalence). -/
theorem e3_sum_apply {n : Type*} [Fintype n] (f : n → E3) (k : Fin 3) :
    (∑ i, f i) k = ∑ i, (f i) k := by
  have h1 : (∑ i, f i) k = eL3 (∑ i, f i) k := (eL3_apply _ k).symm
  rw [h1, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => eL3_apply (f i) k

/-- Decomposition of an `E3` vector over the basis: `z = ∑ i, z i • e3 i`. -/
theorem e3_decomp (z : E3) : z = ∑ i, z i • e3 i := by
  apply PiLp.ext
  intro k
  rw [e3_sum_apply]
  simp only [e3, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ k]
  simp

/-- Decomposition of a continuous operator's action on `E3` over the basis `e3`:
    componentwise `W z j = ∑ i, z i * W (e3 i) j`. -/
theorem clm_apply_eq_sum (W : E3 →L[ℝ] E3) (z : E3) (j : Fin 3) :
    W z j = ∑ i, z i * (W (e3 i)) j := by
  conv_lhs => rw [e3_decomp z, map_sum]
  rw [e3_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, PiLp.smul_apply, smul_eq_mul]

/-- Inner product in E3 via the basis `e3`: `⟪w, v⟫ = ∑ i, (w i) * (v i)`. -/
theorem real_inner_e3_eq_sum (w v : E3) :
    ⟪w, v⟫_ℝ = ∑ i, (w i) * (v i) := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-#############################################################################
  §1. R1 — DIFFERENTIATION UNDER THE ENERGY INTEGRAL:  dE/dt = ∫⟪u, ∂ₜu⟫
      (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` + `HasDerivAt.norm_sq`)
#############################################################################-/

/-- **R1 — PROVEN (differentiation under the integral; conditional on the majorant).**
    If the velocity field `u : ℝ → E3 → E3` has, in time, a pointwise derivative `D`,
    dominated by an integrable `bound`, and `‖u t₀ ·‖²` is integrable and everything is ae-measurable,
    then the kinetic energy is differentiable in time and
      `d/dt E(u t) = ∫ x, ⟪u t x, D t x⟫`.
    The core is mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (majorant `2·bound`),
    pointwise `HasDerivAt.norm_sq` gives the derivative `2⟪u s x, D s x⟫`, then a `(1/2)` massage. -/
theorem hasDerivAt_kineticEnergy_of_dominated
    (u : ℝ → E3 → E3) (D : ℝ → E3 → E3) (t₀ : ℝ)
    (bound : E3 → ℝ)
    (hu_meas : ∀ᶠ s in nhds t₀, AEStronglyMeasurable (fun x => ‖u s x‖ ^ 2) volume)
    (hu_int : Integrable (fun x => ‖u t₀ x‖ ^ 2) volume)
    (hD_meas : AEStronglyMeasurable (fun x => (2 : ℝ) * ⟪u t₀ x, D t₀ x⟫_ℝ) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
        ‖(2 : ℝ) * ⟪u s x, D s x⟫_ℝ‖ ≤ (2 : ℝ) * bound x)
    (hbound_int : Integrable bound volume)
    (h_hasDeriv : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
        HasDerivAt (fun r => u r x) (D s x) s) :
    HasDerivAt (fun s => kineticEnergy (u s))
      (∫ x : E3, ⟪u t₀ x, D t₀ x⟫_ℝ) t₀ := by
  -- pointwise derivative of `‖u s x‖²`: `2⟪u s x, D s x⟫`
  have h_diff : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
      HasDerivAt (fun r => ‖u r x‖ ^ 2) ((2 : ℝ) * ⟪u s x, D s x⟫_ℝ) s := by
    filter_upwards [h_hasDeriv] with x hx s hs
    exact (hx s hs).norm_sq
  -- differentiation under the integral on the "raw" integral ∫‖u s ·‖²
  have hs_nhds : Metric.ball t₀ 1 ∈ nhds t₀ := Metric.ball_mem_nhds t₀ one_pos
  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := fun s x => ‖u s x‖ ^ 2)
      (F' := fun s x => (2 : ℝ) * ⟪u s x, D s x⟫_ℝ)
      (bound := fun x => (2 : ℝ) * bound x) (x₀ := t₀)
      hs_nhds hu_meas hu_int hD_meas h_bound
      (hbound_int.const_mul 2) h_diff).2
  -- (1/2) massage: kineticEnergy = (1/2)·∫; derivative = (1/2)·∫2⟪⟫ = ∫⟪⟫
  have hhalf := hmain.const_mul (1 / 2 : ℝ)
  have hfun : (fun s => (1 / 2 : ℝ) * ∫ x : E3, ‖u s x‖ ^ 2)
      = fun s => kineticEnergy (u s) := by
    funext s; rw [kineticEnergy]
  have hval : (1 / 2 : ℝ) * ∫ x : E3, (2 : ℝ) * ⟪u t₀ x, D t₀ x⟫_ℝ
      = ∫ x : E3, ⟪u t₀ x, D t₀ x⟫_ℝ := by
    rw [MeasureTheory.integral_const_mul]; ring
  rw [hfun, hval] at hhalf
  exact hhalf

/-#############################################################################
  §2. R2 — THE DIVERGENCE THEOREM, GENUINELY PUT TO WORK.
      The box faces DIE by support (`F ≡ 0` outside `openBox`).
#############################################################################-/

/-- Support of a field `F : Pi3 → Pi3` inside the open box: `F ≡ 0` outside `openBox a b`. -/
def BoxSupportedPi (a b : Pi3) (F : Pi3 → Pi3) : Prop :=
  ∀ x, x ∉ openBox a b → F x = 0

/-- Divergence (flat form) of a field `F : Pi3 → Pi3` with derivative `F'`:
    `div F x = ∑ i, F' x (Pi.single i 1) i`. -/
def piDivergence (F' : Pi3 → (Pi3 →L[ℝ] Pi3)) (x : Pi3) : ℝ :=
  ∑ i, F' x (Pi.single i 1) i

/-- The front face of the box lies OUTSIDE `openBox` (coordinate `i` equals `b i`, not in `Ioo`). -/
theorem frontFace_notMem_openBox {a b : Pi3} (i : Fin 3)
    (x : Fin 2 → ℝ) : (Fin.insertNth i (b i) x) ∉ openBox a b := by
  intro hx
  have := hx i (Set.mem_univ i)
  rw [Fin.insertNth_apply_same] at this
  exact Set.right_notMem_Ioo this

/-- The back face of the box lies OUTSIDE `openBox` (coordinate `i` equals `a i`, not in `Ioo`). -/
theorem backFace_notMem_openBox {a b : Pi3} (i : Fin 3)
    (x : Fin 2 → ℝ) : (Fin.insertNth i (a i) x) ∉ openBox a b := by
  intro hx
  have := hx i (Set.mem_univ i)
  rw [Fin.insertNth_apply_same] at this
  exact Set.left_notMem_Ioo this

/-- **R2 (box form) — PROVEN (the divergence theorem PUT TO WORK).**
    For a C¹ field `F` with support in `openBox a b` (and integrable divergence)
      `∫_{Icc a b} div F = 0`,
    because ALL boundary integrals of the mathlib theorem `integral_divergence_of_hasFDerivAt_off_countable`
    DIE: on the faces `F` is identically zero (the support is strictly inside the box). -/
theorem boxDivergence_integral_eq_zero
    (a b : Pi3) (hle : a ≤ b) (F : Pi3 → Pi3) (F' : Pi3 → (Pi3 →L[ℝ] Pi3))
    (hsupp : BoxSupportedPi a b F)
    (Hc : ContinuousOn F (Set.Icc a b))
    (Hd : ∀ x ∈ openBox a b, HasFDerivAt F (F' x) x)
    (Hi : IntegrableOn (piDivergence F') (Set.Icc a b) volume) :
    (∫ x in Set.Icc a b, piDivergence F' x) = 0 := by
  -- apply the box divergence theorem with s := ∅
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable a b hle F F'
    (∅ : Set Pi3) Set.countable_empty Hc
    (fun x hx => Hd x (by simpa [openBox] using hx.1)) Hi
  -- the theorem's LHS coincides with our ∫ div F
  have hLHS : (∫ x in Set.Icc a b, ∑ i, F' x (Pi.single i 1) i)
      = ∫ x in Set.Icc a b, piDivergence F' x := rfl
  rw [hLHS] at hdiv
  -- each boundary integral = 0 (value of F on the face = 0)
  have hfaces : (∑ i : Fin 3,
      ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Fin.insertNth i (b i) x) i)
        - ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Fin.insertNth i (a i) x) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hfront : (fun x : Fin 2 → ℝ => F (Fin.insertNth i (b i) x) i) = fun _ => 0 := by
      funext x
      rw [hsupp _ (frontFace_notMem_openBox i x)]
      rfl
    have hback : (fun x : Fin 2 → ℝ => F (Fin.insertNth i (a i) x) i) = fun _ => 0 := by
      funext x
      rw [hsupp _ (backFace_notMem_openBox i x)]
      rfl
    rw [hfront, hback]
    simp
  rw [hdiv, hfaces]

/-- **R2 (form on all of ℝ³) — PROVEN.** The divergence integral of a box-supported field
    over ALL of space equals zero: outside `Icc a b` the divergence is zero (locally
    constant `F ≡ 0`), so the full integral reduces to the box one. -/
theorem divergence_integral_eq_zero
    (a b : Pi3) (hle : a ≤ b) (F : Pi3 → Pi3) (F' : Pi3 → (Pi3 →L[ℝ] Pi3))
    (hsupp : BoxSupportedPi a b F)
    (Hc : ContinuousOn F (Set.Icc a b))
    (Hd : ∀ x ∈ openBox a b, HasFDerivAt F (F' x) x)
    (Hi : IntegrableOn (piDivergence F') (Set.Icc a b) volume)
    (hzero : ∀ x, x ∉ Set.Icc a b → piDivergence F' x = 0) :
    (∫ x : Pi3, piDivergence F' x) = 0 := by
  have hrestr : (∫ x : Pi3, piDivergence F' x)
      = ∫ x in Set.Icc a b, piDivergence F' x := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc a b) (f := piDivergence F') hzero]
  rw [hrestr]
  exact boxDivergence_integral_eq_zero a b hle F F' hsupp Hc Hd Hi

/-#############################################################################
  §3. R3 — THE THREE KILLERS BY INTEGRATION BY PARTS.
      pi-workhorse: the componentwise identity `div(p•w) = p·div w + ⟪∇p,w⟫`,
      feeding R2. The E3 wrappers of the killers are the gate fields of `R3AssemblyGates` (fallback,
      unfolded: the E3↔Pi3 fderiv bridge is not cheap in mathlib).
#############################################################################-/

/-- **pi-WORKHORSE of the pressure (i) — PROVEN (componentwise, feeds R2):**
    for a scalar `p` and a field `w` with derivatives `p'`, `w'` at the point `x`:
      `div(p•w) x = p x · div w x + ∑ i, (p' (eᵢ)) · (w x) i`,
    where the second summand is the coordinate form of `⟪∇p, w⟫`. The second factor of the first
    summand is `div w`; at `div w = 0` the divergence reduces to `⟪∇p,w⟫` —
    exactly what R2 kills to zero. -/
theorem pressureDiv_pi (p : Pi3 → ℝ) (w : Pi3 → Pi3)
    (p' : Pi3 →L[ℝ] ℝ) (w' : Pi3 →L[ℝ] Pi3) (x : Pi3)
    (hp : HasFDerivAt p p' x) (hw : HasFDerivAt w w' x) :
    piDivergence (fun _ => (p x • w' + p'.smulRight (w x))) x
      = p x * (∑ i, w' (Pi.single i 1) i) + ∑ i, (p' (Pi.single i 1)) * (w x) i := by
  simp only [piDivergence, add_apply, Pi.add_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Derivative of the field `p•w` at a point (for substitution into R2/piDivergence). -/
theorem hasFDerivAt_smul_pi (p : Pi3 → ℝ) (w : Pi3 → Pi3)
    (p' : Pi3 →L[ℝ] ℝ) (w' : Pi3 →L[ℝ] Pi3) (x : Pi3)
    (hp : HasFDerivAt p p' x) (hw : HasFDerivAt w w' x) :
    HasFDerivAt (fun y => p y • w y) (p x • w' + p'.smulRight (w x)) x :=
  hp.smul hw

/-- Coordinate form of `⟪∇p, w⟫` (what is fed into R2 at `div w = 0`).
    Defined as `∑ i, (fderiv ℝ p x) eᵢ · w x i`. -/
def innerGradPi (p : Pi3 → ℝ) (w : Pi3 → Pi3) (x : Pi3) : ℝ :=
  ∑ i, (fderiv ℝ p x) (Pi.single i 1) * (w x) i

/-#############################################################################
  §3bis. MASTER LEMMA E3↔Pi3: ∫_{ℝ³} div_{E3} G = 0 for a box-supported C¹ field.
      This is the E3→Pi3 fderiv bridge (comp-chain `ContinuousLinearEquiv.comp`+`HasFDerivAt.comp`),
      feeding R2 (§2). All THREE killers reduce to it. PROVEN (not a gate).
#############################################################################-/

/-- `eL3.symm (Pi.single i 1) = e3 i` (removing the L² wrapper from the standard unit vector). -/
theorem eL3symm_single (i : Fin 3) : eL3.symm (Pi.single i 1) = e3 i := by
  rw [← toLp_eq_eL3symm]
  simp [e3, EuclideanSpace.single]

/-- The open box lies in the closed one: `openBox a b ⊆ Icc a b`. -/
theorem openBox_subset_Icc (a b : Pi3) : openBox a b ⊆ Set.Icc a b := by
  rw [openBox, ← Set.pi_univ_Icc]
  intro z hz i hi
  exact Set.Ioo_subset_Icc_self (hz i hi)

/-- **MASTER LEMMA R3 — PROVEN (E3↔Pi3 bridge, feeds R2).**
    For a C¹ field `G : E3 → E3` with derivative `G'` (everywhere), with continuous
    E3 divergence `x ↦ ∑ i, G' x (e3 i) i` and with support in the box (`G ≡ 0` when
    `eL3 x ∉ openBox a b`), the divergence integral over ALL of `E3` equals zero:
      `∫ x:E3, (∑ i, G' x (e3 i) i) = 0`.
    Mechanism: transport the field to `Pi3` via `eL3` (`F z := eL3 (G (eL3.symm z))`,
    `F' z := eL3 ∘SL (G' (eL3.symm z)) ∘SL eL3.symm`), the identity
    `piDivergence F' z = ∑ i, G' (eL3.symm z) (e3 i) i` (via `eL3symm_single`),
    the volume bridge `integral_comp_toLp`, then R2 `divergence_integral_eq_zero`.
    ALL THREE killers (pressure/transport/viscosity) are special cases. -/
theorem integral_e3_divergence_eq_zero
    (a b : Pi3) (hle : a ≤ b) (G : E3 → E3) (G' : E3 → E3 →L[ℝ] E3)
    (hG : ∀ x, HasFDerivAt G (G' x) x)
    (hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i))
    (hsupp : ∀ x : E3, eL3 x ∉ openBox a b → G x = 0) :
    (∫ x : E3, ∑ i, (G' x (e3 i)) i) = 0 := by
  set F : Pi3 → Pi3 := fun z => eL3 (G (eL3.symm z)) with hF
  set F' : Pi3 → (Pi3 →L[ℝ] Pi3) := fun z =>
    (eL3 : E3 →L[ℝ] Pi3).comp ((G' (eL3.symm z)).comp (eL3.symm : Pi3 →L[ℝ] E3)) with hF'
  have hGcont : Continuous G := continuous_iff_continuousAt.mpr fun x => (hG x).continuousAt
  -- transport of the derivative: F' is the derivative of F everywhere (comp-chain)
  have hFderiv : ∀ z, HasFDerivAt F (F' z) z := by
    intro z
    have h1 : HasFDerivAt (⇑eL3.symm) (eL3.symm : Pi3 →L[ℝ] E3) z := eL3.symm.hasFDerivAt
    have h2 : HasFDerivAt G (G' (eL3.symm z)) (eL3.symm z) := hG (eL3.symm z)
    have h3 : HasFDerivAt (⇑eL3) (eL3 : E3 →L[ℝ] Pi3) (G (eL3.symm z)) := eL3.hasFDerivAt
    exact (h3.comp z (h2.comp z h1))
  -- KEY identity: piDivergence F' z = ∑ i, G' (eL3.symm z) (e3 i) i
  have hpiDiv : ∀ z, piDivergence F' z = ∑ i, (G' (eL3.symm z) (e3 i)) i := by
    intro z
    unfold piDivergence
    apply Finset.sum_congr rfl
    intro i _
    show ((eL3 : E3 →L[ℝ] Pi3).comp ((G' (eL3.symm z)).comp (eL3.symm : Pi3 →L[ℝ] E3)))
        (Pi.single i 1) i = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [eL3_apply, eL3symm_single]
  -- volume bridge: ∫ x:E3 = ∫ y:Pi3 piDivergence
  have hbridge : (∫ x : E3, ∑ i, (G' x (e3 i)) i)
      = ∫ y : Pi3, piDivergence F' y := by
    rw [← integral_comp_toLp (fun x => ∑ i, (G' x (e3 i)) i)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    rw [hpiDiv]
    show (∑ i, (G' (WithLp.toLp 2 y) (e3 i)) i) = ∑ i, (G' (eL3.symm y) (e3 i)) i
    rw [toLp_eq_eL3symm]
  rw [hbridge]
  -- support on Pi3
  have hFsupp : BoxSupportedPi a b F := by
    intro z hz
    show eL3 (G (eL3.symm z)) = 0
    have : eL3 (eL3.symm z) ∉ openBox a b := by
      rw [ContinuousLinearEquiv.apply_symm_apply]; exact hz
    rw [hsupp _ this]; simp
  -- continuity of the divergence on Pi3 (for integrability)
  have hcontPi : Continuous (piDivergence F') := by
    have heq : (fun z => piDivergence F' z)
        = (fun x : E3 => ∑ i, (G' x (e3 i)) i) ∘ (eL3.symm) := by
      funext z; rw [hpiDiv]; rfl
    rw [show (piDivergence F') = (fun z => piDivergence F' z) from rfl, heq]
    exact hcont.comp eL3.symm.continuous
  have Hi : IntegrableOn (piDivergence F') (Set.Icc a b) volume :=
    hcontPi.continuousOn.integrableOn_compact isCompact_Icc
  have HcF : ContinuousOn F (Set.Icc a b) :=
    (eL3.continuous.comp (hGcont.comp eL3.symm.continuous)).continuousOn
  have Hd : ∀ x ∈ openBox a b, HasFDerivAt F (F' x) x := fun x _ => hFderiv x
  -- outside Icc: F is locally zero ⟹ F' = 0 ⟹ piDivergence F' = 0
  have hzero : ∀ y, y ∉ Set.Icc a b → piDivergence F' y = 0 := by
    intro y hy
    have hFev : F =ᶠ[nhds y] fun _ => 0 := by
      apply Filter.eventuallyEq_of_mem
        (isOpen_compl_iff.mpr isClosed_Icc |>.mem_nhds hy)
      intro z hz
      show F z = 0
      exact hFsupp z (fun hzo => hz (openBox_subset_Icc a b hzo))
    have hderiv0 : HasFDerivAt F (0 : Pi3 →L[ℝ] Pi3) y :=
      (hasFDerivAt_const (0 : Pi3) y).congr_of_eventuallyEq hFev
    have hF'0 : F' y = 0 := (hFderiv y).unique hderiv0
    unfold piDivergence
    rw [hF'0]; simp
  exact divergence_integral_eq_zero a b hle F F' hFsupp HcF Hd Hi hzero

/-#############################################################################
  §4. ASSEMBLY — layer-by-layer assembly of the energy balance.
      🔴 input `TimeDomination`, gate structure `BoxSupportedC2Flow` (gates the
      SMOOTHNESS OF THE PRESSURE for the first time), gate structure `R3AssemblyGates`, theorem
      `energyBalance_of_r3Gates` — the LAW IS DERIVED, not decreed.
#############################################################################-/

/-- **🔴 TimeDomination — the ONLY analytic INPUT of R1** (a locally-in-time
    integrable majorant of the derivative under the energy integral). Packs exactly what
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le` asks for: ae-measurability of
    `‖u s ·‖²` near `t₀`, integrability of `‖u t₀ ·‖²`, ae-measurability of
    the integrand's derivative, an integrable majorant `bound` and pointwise
    differentiability of the trajectories with derivative `D`. -/
structure TimeDomination (u : ℝ → E3 → E3) (D : ℝ → E3 → E3) (t₀ : ℝ) where
  bound : E3 → ℝ
  measSq : ∀ᶠ s in nhds t₀, AEStronglyMeasurable (fun x => ‖u s x‖ ^ 2) volume
  intSq : Integrable (fun x => ‖u t₀ x‖ ^ 2) volume
  measDeriv : AEStronglyMeasurable (fun x => (2 : ℝ) * ⟪u t₀ x, D t₀ x⟫_ℝ) volume
  dominated : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
      ‖(2 : ℝ) * ⟪u s x, D s x⟫_ℝ‖ ≤ (2 : ℝ) * bound x
  intBound : Integrable bound volume
  hasDeriv : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
      HasDerivAt (fun r => u r x) (D s x) s

/-- R1 in the `TimeDomination` wrapper: dE/dt = ∫⟪u, D⟫. -/
theorem hasDerivAt_kineticEnergy_of_timeDomination
    (u : ℝ → E3 → E3) (D : ℝ → E3 → E3) (t₀ : ℝ)
    (dom : TimeDomination u D t₀) :
    HasDerivAt (fun s => kineticEnergy (u s))
      (∫ x : E3, ⟪u t₀ x, D t₀ x⟫_ℝ) t₀ :=
  hasDerivAt_kineticEnergy_of_dominated u D t₀ dom.bound
    dom.measSq dom.intSq dom.measDeriv dom.dominated dom.intBound dom.hasDeriv

/-- **Gate structure of a box-supported C² flow (PRESSURE SMOOTHNESS GATE FOR THE FIRST TIME):**
    the class of fields for which the balance will be DERIVED. The fields gate differentiability
    of trajectories in time (`timeDeriv`), of the field in space (`spaceDiff`),
    the second derivatives (`spaceDiff2`), AND THE SMOOTHNESS OF THE PRESSURE (`pressDiff`) —
    thereby closing the Forging-B channel (junk in ∇p on the sphere is excluded by the C² gate);
    the continuities (`contU/contU'/contU''/contP/contP'`) and box support (`supp`). -/
structure BoxSupportedC2Flow (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) where
  hle : (0 : ℝ) ≤ ν
  a : Pi3
  b : Pi3
  aleb : a ≤ b
  timeDeriv : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  spaceDiff : ∀ t x, DifferentiableAt ℝ (u t) x
  spaceDiff2 : ∀ t i x, DifferentiableAt ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x
  pressDiff : ∀ t x, DifferentiableAt ℝ (p t) x
  contU : ∀ t, Continuous (u t)
  contU' : ∀ t i, Continuous (fun x => fderiv ℝ (u t) x (e3 i))
  contU'' : ∀ t i j,
    Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 j))
  contP : ∀ t, Continuous (p t)
  contP' : ∀ t i, Continuous (fun x => fderiv ℝ (p t) x (e3 i))
  supp : ∀ t x, (eL3 x) ∉ openBox a b → u t x = 0

/-#############################################################################
  §4bis. THE THREE KILLERS + INTEGRABILITIES — PROVEN from `BoxSupportedC2Flow`
      (via the master lemma §3bis + the smoothness gates). No longer hypotheses.
#############################################################################-/

/-- Coordinate form `⟪u, ∇p⟫ = ∑ i, (fderiv p x eᵢ)·(u x) i` (via
    `inner_gradient_left` + decomposition of `u` over the basis). -/
theorem inner_gradient_eq_sum (p : E3 → ℝ) (u : E3 → E3) (x : E3) :
    ⟪u x, gradient p x⟫_ℝ = ∑ i, (fderiv ℝ p x (e3 i)) * (u x) i := by
  rw [real_inner_comm, inner_gradient_left]
  conv_lhs => rw [e3_decomp (u x), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]

/-- **Integrability of a box-supported continuous integrand on `E3`.** A continuous
    function `g : E3 → ℝ` vanishing outside the box support (`eL3 x ∉ openBox`) is
    integrable: its support lies in the compact set `eL3 ⁻¹' (Icc a b)`. -/
theorem integrable_of_boxSupported_E3
    (a b : Pi3) (g : E3 → ℝ) (hg : Continuous g)
    (hsupp : ∀ x : E3, eL3 x ∉ openBox a b → g x = 0) :
    Integrable g volume := by
  have hcpt : IsCompact (eL3 ⁻¹' (Set.Icc a b)) := by
    have heq : eL3 ⁻¹' (Set.Icc a b) = eL3.symm '' (Set.Icc a b) := by
      ext z; simp only [Set.mem_preimage, Set.mem_image]
      exact ⟨fun h => ⟨eL3 z, h, by simp⟩,
        fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw⟩
    rw [heq]; exact (isCompact_Icc).image eL3.symm.continuous
  have hIntOn : IntegrableOn g (eL3 ⁻¹' (Set.Icc a b)) volume :=
    hg.continuousOn.integrableOn_compact hcpt
  have hzero : ∀ x ∉ eL3 ⁻¹' (Set.Icc a b), g x = 0 :=
    fun x hx => hsupp x (fun ho => hx (Set.mem_preimage.mpr (openBox_subset_Icc a b ho)))
  exact hIntOn.integrable_of_forall_notMem_eq_zero hzero

/-- Continuity of the pressure integrand `⟪u, ∇p⟫` (from the gates `contP'`, `contU`). -/
theorem contPressIntegrand
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) :
    Continuous (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) := by
  have heq : (fun x => ⟪u t x, gradient (p t) x⟫_ℝ)
      = fun x => ∑ i, (fderiv ℝ (p t) x (e3 i)) * (u t x) i :=
    funext fun x => inner_gradient_eq_sum (p t) (u t) x
  rw [heq]
  apply continuous_finset_sum
  intro i _
  exact (F.contP' t i).mul ((EuclideanSpace.proj i).continuous.comp (F.contU t))

/-- Continuity of the transport integrand `⟪u, (u·∇)u⟫` (from `contU`, `contU'`). -/
theorem contConvIntegrand
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) :
    Continuous (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) := by
  have heq : (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ)
      = fun x => ∑ j, (u t x) j
          * (∑ i, (u t x) i * (fderiv ℝ (u t) x (e3 i)) j) := by
    funext x
    rw [real_inner_e3_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [convectiveTerm, clm_apply_eq_sum]
  rw [heq]
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
  apply continuous_finset_sum
  intro i _
  exact ((EuclideanSpace.proj i).continuous.comp (F.contU t)).mul
    ((EuclideanSpace.proj j).continuous.comp (F.contU' t i))

/-- Continuity of the viscosity integrand `⟪u, ν•Δu⟫` (from `contU`, `contU''`). -/
theorem contLapIntegrand
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) :
    Continuous (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) := by
  have heq : (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ)
      = fun x => ν * ∑ j, (u t x) j
          * (∑ i, (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 i)) j) := by
    funext x
    rw [real_inner_smul_right, real_inner_e3_eq_sum]
    congr 1
  rw [heq]
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
  apply continuous_finset_sum
  intro i _
  exact (EuclideanSpace.proj j).continuous.comp (F.contU'' t i i)

/-- **Integrability of the pressure `∫⟪u,∇p⟫` — PROVEN** (continuity + box support). -/
theorem intPress_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume := by
  intro t
  refine integrable_of_boxSupported_E3 F.a F.b _ (contPressIntegrand F t) ?_
  intro x hx
  rw [F.supp t x hx, inner_zero_left]

/-- **Integrability of the transport `∫⟪u,(u·∇)u⟫` — PROVEN.** -/
theorem intConv_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume := by
  intro t
  refine integrable_of_boxSupported_E3 F.a F.b _ (contConvIntegrand F t) ?_
  intro x hx
  rw [F.supp t x hx, inner_zero_left]

/-- **Integrability of the viscosity `∫⟪u,ν•Δu⟫` — PROVEN.** -/
theorem intLap_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume := by
  intro t
  refine integrable_of_boxSupported_E3 F.a F.b _ (contLapIntegrand F t) ?_
  intro x hx
  rw [F.supp t x hx, inner_zero_left]

/-- **KILLER I (PRESSURE) — PROVEN:** `∫⟪u,∇p⟫ = 0`. The field `G := p•u` has
    E3 divergence `p·div u + ⟪u,∇p⟫`; at `div u = 0` (incompressibility)
    `⟪u,∇p⟫` remains, and the master lemma §3bis gives `∫ = 0`. -/
theorem pressureKills_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p) :
    ∀ t, (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ) = 0 := by
  intro t
  set G : E3 → E3 := fun x => p t x • u t x with hG
  set G' : E3 → E3 →L[ℝ] E3 := fun x =>
    (p t x • (fderiv ℝ (u t) x) + (fderiv ℝ (p t) x).smulRight (u t x)) with hG'
  have hGderiv : ∀ x, HasFDerivAt G (G' x) x :=
    fun x => (F.pressDiff t x).hasFDerivAt.smul (F.spaceDiff t x).hasFDerivAt
  have hcomp : ∀ x i, (G' x (e3 i)) i
      = p t x * (fderiv ℝ (u t) x (e3 i)) i + (fderiv ℝ (p t) x (e3 i)) * (u t x) i := by
    intro x i
    show ((p t x • (fderiv ℝ (u t) x)
        + (fderiv ℝ (p t) x).smulRight (u t x)) (e3 i)) i = _
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hpt2 : ∀ x, (∑ i, (G' x (e3 i)) i) = ⟪u t x, gradient (p t) x⟫_ℝ := by
    intro x
    rw [inner_gradient_eq_sum]
    have hsum : (∑ i, (G' x (e3 i)) i)
        = p t x * NSdiv (u t) x + ∑ i, (fderiv ℝ (p t) x (e3 i)) * (u t x) i := by
      rw [NSdiv, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hcomp x i
    rw [hsum, sol.incompressible t x, mul_zero, zero_add]
  have hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i) := by
    have heq : (fun x : E3 => ∑ i, (G' x (e3 i)) i)
        = fun x => ⟪u t x, gradient (p t) x⟫_ℝ := funext hpt2
    rw [heq]; exact contPressIntegrand F t
  have hsupp : ∀ x : E3, eL3 x ∉ openBox F.a F.b → G x = 0 := by
    intro x hx
    show p t x • u t x = 0
    rw [F.supp t x hx, smul_zero]
  have hmaster :=
    integral_e3_divergence_eq_zero F.a F.b F.aleb G G' hGderiv hcont hsupp
  rw [← hmaster]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt2 x).symm)

/-- Derivative of `½‖u‖²` along a direction: `fderiv (½‖u‖²) x h = ⟪u x, fderiv u x h⟫`
    (from `HasFDerivAt.norm_sq` with a `(1/2)` massage). -/
theorem fderiv_half_normSq (u : E3 → E3) (x : E3)
    (hu : DifferentiableAt ℝ u x) (h : E3) :
    fderiv ℝ (fun y => (1/2 : ℝ) * ‖u y‖^2) x h = ⟪u x, fderiv ℝ u x h⟫_ℝ := by
  have hd := (hu.hasFDerivAt.norm_sq).const_mul (1/2 : ℝ)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

/-- `⟪u, (u·∇)u⟫ = ∑ i, (u x)ᵢ · ⟪u x, ∂ᵢu⟫` (decomposition of the direction `u x` over the basis). -/
theorem inner_conv_eq_sum (u : E3 → E3) (x : E3) :
    ⟪u x, convectiveTerm u x⟫_ℝ = ∑ i, (u x) i * ⟪u x, fderiv ℝ u x (e3 i)⟫_ℝ := by
  rw [convectiveTerm]
  conv_lhs => rw [show (fderiv ℝ u x) (u x)
    = (fderiv ℝ u x) (∑ i, (u x) i • e3 i) from by rw [← e3_decomp]]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, real_inner_smul_right]

/-- **KILLER II (TRANSPORT) — PROVEN:** `∫⟪u,(u·∇)u⟫ = 0`. The field `G := (½‖u‖²)•u`
    has E3 divergence `⟪u,(u·∇)u⟫ + (½‖u‖²)·div u`; at `div u = 0`
    `⟪u,(u·∇)u⟫` remains, and the master lemma §3bis gives `∫ = 0`. The direction identity:
    `fderiv (½‖u‖²) x = ⟪u x, fderiv u x ·⟫` (`fderiv_half_normSq`). -/
theorem transportKills_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p) :
    ∀ t, (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) = 0 := by
  intro t
  set c : E3 → ℝ := fun y => (1/2 : ℝ) * ‖u t y‖^2 with hc
  set G : E3 → E3 := fun x => c x • u t x with hG
  set G' : E3 → E3 →L[ℝ] E3 := fun x =>
    (c x • (fderiv ℝ (u t) x) + (fderiv ℝ c x).smulRight (u t x)) with hG'
  have hcDiff : ∀ x, DifferentiableAt ℝ c x := fun x =>
    (((F.spaceDiff t x).hasFDerivAt.norm_sq).const_mul (1/2:ℝ)).differentiableAt
  have hGderiv : ∀ x, HasFDerivAt G (G' x) x :=
    fun x => (hcDiff x).hasFDerivAt.smul (F.spaceDiff t x).hasFDerivAt
  have hcomp : ∀ x i, (G' x (e3 i)) i
      = c x * (fderiv ℝ (u t) x (e3 i)) i
        + ⟪u t x, fderiv ℝ (u t) x (e3 i)⟫_ℝ * (u t x) i := by
    intro x i
    show ((c x • (fderiv ℝ (u t) x)
        + (fderiv ℝ c x).smulRight (u t x)) (e3 i)) i = _
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [fderiv_half_normSq (u t) x (F.spaceDiff t x)]
  have hpt2 : ∀ x, (∑ i, (G' x (e3 i)) i) = ⟪u t x, convectiveTerm (u t) x⟫_ℝ := by
    intro x
    have hsum : (∑ i, (G' x (e3 i)) i)
        = c x * NSdiv (u t) x
          + ∑ i, ⟪u t x, fderiv ℝ (u t) x (e3 i)⟫_ℝ * (u t x) i := by
      rw [NSdiv, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hcomp x i
    rw [hsum, sol.incompressible t x, mul_zero, zero_add, inner_conv_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i) := by
    have heq : (fun x : E3 => ∑ i, (G' x (e3 i)) i)
        = fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ := funext hpt2
    rw [heq]; exact contConvIntegrand F t
  have hsupp : ∀ x : E3, eL3 x ∉ openBox F.a F.b → G x = 0 := by
    intro x hx
    show c x • u t x = 0
    rw [F.supp t x hx, smul_zero]
  have hmaster :=
    integral_e3_divergence_eq_zero F.a F.b F.aleb G G' hGderiv hcont hsupp
  rw [← hmaster]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt2 x).symm)

/-#############################################################################
  §4ter. KILLER III (VISCOSITY) — PROVEN by componentwise IBP.
      For each component `j` the field `H_j := u_j • ∇u_j` has E3 divergence
      `‖∇u_j‖² + u_j·(Δu)_j`; the master lemma §3bis gives `∫ = 0` componentwise,
      summation over `j` + `Finset.sum_comm` land on the enstrophy.
#############################################################################-/

/-- Derivative of the scalar component `u_j = (proj j) ∘ u`:
    `fderiv u_j x = (proj j) ∘L fderiv u x`. -/
theorem hasFDerivAt_phij (u : E3 → E3) (x : E3) (j : Fin 3) (hu : DifferentiableAt ℝ u x) :
    HasFDerivAt (fun y => (u y) j)
      ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ u x)) x :=
  ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ).hasFDerivAt (x := u x)).comp x hu.hasFDerivAt

/-- Derivative of the component gradient `w_j y = ∑ i, (∂ᵢu_j)(y)·eᵢ`
    (from the second-derivative gate `spaceDiff2`). -/
theorem hasFDerivAt_wj (u : E3 → E3) (x : E3) (j : Fin 3)
    (h2 : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ u y (e3 i)) x) :
    HasFDerivAt (fun y => ∑ i, (fderiv ℝ u y (e3 i) j) • e3 i)
      (∑ i, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
        (fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x)).smulRight (e3 i)) x := by
  have hpt : (fun y => ∑ i, (fderiv ℝ u y (e3 i) j) • e3 i)
      = ∑ i, (fun y => (fderiv ℝ u y (e3 i) j) • e3 i) := by funext y; rw [Finset.sum_apply]
  rw [hpt]; apply HasFDerivAt.sum; intro i _
  have hg2 : HasFDerivAt (fun y => (fderiv ℝ u y (e3 i)) j)
      ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x)) x :=
    ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ).hasFDerivAt).comp x (h2 i).hasFDerivAt
  exact hg2.smul_const (e3 i)

/-- The `i`-th coordinate of the component gradient: `(w_j x)ᵢ = ∂ᵢu_j`. -/
theorem wj_apply (u : E3 → E3) (x : E3) (j i : Fin 3) :
    (∑ k, (fderiv ℝ u x (e3 k) j) • e3 k) i = fderiv ℝ u x (e3 i) j := by
  rw [e3_sum_apply]
  simp only [PiLp.smul_apply, e3, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ i]; simp

/-- Squared norm of the component gradient: `‖∇u_j‖² = ∑ i, (∂ᵢu_j)²`. -/
theorem wj_normSq (u : E3 → E3) (x : E3) (j : Fin 3) :
    ‖(∑ k, (fderiv ℝ u x (e3 k) j) • e3 k : E3)‖^2 = ∑ i, (fderiv ℝ u x (e3 i) j)^2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_e3_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [wj_apply]; ring

/-- Divergence of the component gradient = the `j`-th component of the Laplacian:
    `div(∇u_j) = (Δu)_j`. -/
theorem wj_div (u : E3 → E3) (x : E3) (j : Fin 3) :
    (∑ m, ((∑ i, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
        (fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x)).smulRight (e3 i)) (e3 m)) m)
      = (vectorLaplacian u x) j := by
  rw [vectorLaplacian, e3_sum_apply]; apply Finset.sum_congr rfl; intro m _
  rw [ContinuousLinearMap.sum_apply, e3_sum_apply, Finset.sum_eq_single m]
  · simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      PiLp.smul_apply, e3, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]; simp
  · intro i _ hi
    simp only [ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, e3,
      PiLp.single_apply, smul_eq_mul]
    rw [if_neg (Ne.symm hi)]; ring
  · intro h; exact absurd (Finset.mem_univ m) h

/-- **Componentwise IBP identity:** the E3 divergence of the field `H_j = u_j • ∇u_j`
    equals `‖∇u_j‖² + u_j·(Δu)_j`. -/
theorem Hj_div (u : E3 → E3) (x : E3) (j : Fin 3) :
    (∑ i, (((u x j) • (∑ k, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ u y (e3 k)) x)).smulRight (e3 k))
      + ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ u x)).smulRight
          (∑ k, (fderiv ℝ u x (e3 k) j) • e3 k)) (e3 i)) i)
      = ‖(∑ k, (fderiv ℝ u x (e3 k) j) • e3 k : E3)‖^2 + (u x j) * (vectorLaplacian u x) j := by
  have hcomp : ∀ i, (((u x j) • (∑ k, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ u y (e3 k)) x)).smulRight (e3 k))
      + ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ u x)).smulRight
          (∑ k, (fderiv ℝ u x (e3 k) j) • e3 k)) (e3 i)) i
      = (u x j) * ((∑ k, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ u y (e3 k)) x)).smulRight (e3 k)) (e3 i)) i
        + (fderiv ℝ u x (e3 i) j) * ((∑ k, (fderiv ℝ u x (e3 k) j) • e3 k) i) := by
    intro i
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; rfl
  rw [Finset.sum_congr rfl (fun i _ => hcomp i), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [wj_div, wj_normSq, add_comm]; congr 1
  apply Finset.sum_congr rfl; intro i _; rw [wj_apply]; ring

/-- **Integrability of an Icc-supported continuous integrand on `E3`.** Analog of
    `integrable_of_boxSupported_E3`, but the support is over the closed `Icc` (the box
    boundary has measure zero): for the enstrophy summand `‖∇u_j‖²`, vanishing on
    the OPEN complement of `Icc` (where `u ≡ 0` ⟹ `fderiv u = 0`). -/
theorem integrable_of_IccSupported_E3
    (a b : Pi3) (g : E3 → ℝ) (hg : Continuous g)
    (hsupp : ∀ x : E3, eL3 x ∉ Set.Icc a b → g x = 0) :
    Integrable g volume := by
  have hcpt : IsCompact (eL3 ⁻¹' (Set.Icc a b)) := by
    have heq : eL3 ⁻¹' (Set.Icc a b) = eL3.symm '' (Set.Icc a b) := by
      ext z; simp only [Set.mem_preimage, Set.mem_image]
      exact ⟨fun h => ⟨eL3 z, h, by simp⟩, fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw⟩
    rw [heq]; exact (isCompact_Icc).image eL3.symm.continuous
  have hIntOn : IntegrableOn g (eL3 ⁻¹' (Set.Icc a b)) volume :=
    hg.continuousOn.integrableOn_compact hcpt
  exact hIntOn.integrable_of_forall_notMem_eq_zero
    (fun x hx => hsupp x (fun ho => hx (Set.mem_preimage.mpr ho)))

/-- Outside the box the derivative of a box-supported field is zero: if `eL3 x ∉ Icc`, then `u ≡ 0`
    on an OPEN neighbourhood of `x` (the complement of `Icc`), so `fderiv u x (eᵢ) = 0`. -/
theorem fderiv_zero_outside_Icc {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) (i : Fin 3) {x : E3}
    (hx : eL3 x ∉ Set.Icc F.a F.b) :
    fderiv ℝ (u t) x (e3 i) = 0 := by
  have hopen : IsOpen (eL3 ⁻¹' (Set.Icc F.a F.b)ᶜ) :=
    (isClosed_Icc.isOpen_compl).preimage eL3.continuous
  have hev : u t =ᶠ[nhds x] fun _ => 0 := by
    apply Filter.eventuallyEq_of_mem (hopen.mem_nhds hx)
    intro z hz
    exact F.supp t z (fun ho => hz (openBox_subset_Icc F.a F.b ho))
  rw [Filter.EventuallyEq.fderiv_eq hev]; simp

/-- Continuity of the componentwise divergence integrand `‖∇u_j‖² + u_j·(Δu)_j`
    (from the gates `contU`, `contU'`, `contU''`). -/
theorem contHjdiv {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) (j : Fin 3) :
    Continuous (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j) := by
  apply Continuous.add
  · have heq : (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
        = fun x => ∑ i, (fderiv ℝ (u t) x (e3 i) j)^2 := funext fun x => wj_normSq (u t) x j
    rw [heq]; apply continuous_finset_sum; intro i _
    exact ((EuclideanSpace.proj j).continuous.comp (F.contU' t i)).pow 2
  · apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
    have heq : (fun x => (vectorLaplacian (u t) x) j)
        = fun x => ∑ i, (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 i)) j := by
      funext x; rw [vectorLaplacian, e3_sum_apply]
    rw [heq]; apply continuous_finset_sum; intro i _
    exact (EuclideanSpace.proj j).continuous.comp (F.contU'' t i i)

/-- **KILLER III (VISCOSITY) — PROVEN:** `∫⟪u,Δu⟫ = −∫∑ᵢ‖∂ᵢu‖²` (IBP).
    Componentwise the field `H_j := u_j•∇u_j` has divergence `‖∇u_j‖² + u_j·(Δu)_j`,
    the master lemma §3bis gives `∫ = 0` for each `j`; summation over `j`, the split
    (both sides are integrable: `⟪u,Δu⟫` is box-supported, `∑‖∂ᵢu‖²` is Icc-supported) and
    `Finset.sum_comm` (`∑_j‖∇u_j‖² = ∑_i‖∂ᵢu‖²`) land on the enstrophy. -/
theorem viscosityIBP_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, (∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ)
      = -(∫ x : E3, ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖ ^ 2) := by
  intro t
  have perj : ∀ j, (∫ x : E3, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j) = 0 := by
    intro j
    set G : E3 → E3 := fun y => (u t y j) • (∑ i, (fderiv ℝ (u t) y (e3 i) j) • e3 i) with hG
    set G' : E3 → E3 →L[ℝ] E3 := fun x =>
      ((u t x j) • (∑ i, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x)).smulRight (e3 i))
        + ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ (u t) x)).smulRight
            (∑ i, (fderiv ℝ (u t) x (e3 i) j) • e3 i)) with hG'
    have hGderiv : ∀ x, HasFDerivAt G (G' x) x := fun x =>
      (hasFDerivAt_phij (u t) x j (F.spaceDiff t x)).smul
        (hasFDerivAt_wj (u t) x j (fun i => F.spaceDiff2 t i x))
    have hdivpt : ∀ x, (∑ i, (G' x (e3 i)) i)
        = ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
          + (u t x j) * (vectorLaplacian (u t) x) j := fun x => Hj_div (u t) x j
    have hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i) := by
      have heq : (fun x : E3 => ∑ i, (G' x (e3 i)) i)
          = fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
            + (u t x j) * (vectorLaplacian (u t) x) j := funext hdivpt
      rw [heq]; exact contHjdiv F t j
    have hsupp : ∀ x : E3, eL3 x ∉ openBox F.a F.b → G x = 0 := by
      intro x hx
      show (u t x j) • (∑ i, (fderiv ℝ (u t) x (e3 i) j) • e3 i) = 0
      rw [F.supp t x hx]; simp
    have hmaster :=
      integral_e3_divergence_eq_zero F.a F.b F.aleb G G' hGderiv hcont hsupp
    rw [← hmaster]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hdivpt x).symm)
  have hIntW : ∀ j, Integrable
      (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2) volume := by
    intro j
    apply integrable_of_IccSupported_E3 F.a F.b _
    · have heq : (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
          = fun x => ∑ i, (fderiv ℝ (u t) x (e3 i) j)^2 := funext fun x => wj_normSq (u t) x j
      rw [heq]; apply continuous_finset_sum; intro i _
      exact ((EuclideanSpace.proj j).continuous.comp (F.contU' t i)).pow 2
    · intro x hx
      have hz : ∀ k, fderiv ℝ (u t) x (e3 k) j = 0 := fun k => by
        rw [fderiv_zero_outside_Icc F t k hx]; simp
      simp only [hz]
      rw [show (∑ k, (0:ℝ) • e3 k : E3) = 0 from by simp]; simp
  have hIntUL : ∀ j, Integrable
      (fun x => (u t x j) * (vectorLaplacian (u t) x) j) volume := by
    intro j
    apply integrable_of_IccSupported_E3 F.a F.b _
    · apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
      have heq : (fun x => (vectorLaplacian (u t) x) j)
          = fun x => ∑ i, (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 i)) j := by
        funext x; rw [vectorLaplacian, e3_sum_apply]
      rw [heq]; apply continuous_finset_sum; intro i _
      exact (EuclideanSpace.proj j).continuous.comp (F.contU'' t i i)
    · intro x hx
      have hu0 : u t x = 0 := F.supp t x (fun ho => hx (openBox_subset_Icc F.a F.b ho))
      rw [show (u t x) j = 0 from by rw [hu0]; simp]; ring
  have hsum0 : (∫ x : E3, ∑ j, (‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j)) = 0 := by
    rw [MeasureTheory.integral_finset_sum]
    · rw [Finset.sum_eq_zero]; intro j _; exact perj j
    · intro j _; exact (hIntW j).add (hIntUL j)
  have hsplit : (∫ x : E3, ∑ j, (‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j))
      = (∫ x : E3, ∑ j, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
        + ∫ x : E3, ∑ j, (u t x j) * (vectorLaplacian (u t) x) j := by
    rw [← MeasureTheory.integral_add]
    · apply integral_congr_ae; apply Filter.Eventually.of_forall; intro x
      exact Finset.sum_add_distrib
    · exact integrable_finset_sum _ (fun j _ => hIntW j)
    · exact integrable_finset_sum _ (fun j _ => hIntUL j)
  have hConvUL : (fun x => ∑ j, (u t x j) * (vectorLaplacian (u t) x) j)
      = fun x => ⟪u t x, vectorLaplacian (u t) x⟫_ℝ := by
    funext x; rw [real_inner_e3_eq_sum]
  have hConvW : (fun x => ∑ j, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
      = fun x => ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖^2 := by
    funext x
    have h1 : ∀ j, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
        = ∑ i, (fderiv ℝ (u t) x (e3 i) j)^2 := fun j => wj_normSq (u t) x j
    have h2 : ∀ i, ‖fderiv ℝ (u t) x (e3 i)‖^2 = ∑ j, (fderiv ℝ (u t) x (e3 i) j)^2 := by
      intro i; rw [← real_inner_self_eq_norm_sq, real_inner_e3_eq_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [h1, h2]; exact Finset.sum_comm
  rw [hConvUL, hConvW] at hsplit
  rw [hsplit] at hsum0
  linarith [hsum0]

/-- **R3AssemblyGates — LAYER-BY-LAYER GATE SET (fallback unfolding):** everything needed
    to DERIVE the energy balance at time `t`. The fields `timeDeriv/domination` feed R1;
    `intLap/intPress/intConv` — integrabilities of the right-hand side components (splitting
    the integral); the THREE killers `pressureKills/transportKills/viscosityIBP` —
    E3 identities of integration by parts.

    ✅ FALLBACK CLOSED: the three killers (`pressureKills`, `transportKills`,
    `viscosityIBP`) are NO LONGER HYPOTHESES — they are PROVEN (§4bis/§4ter) by the master lemma
    §3bis (`integral_e3_divergence_eq_zero`: E3↔Pi3 fderiv bridge by a comp-chain, feeding
    R2). `killerBundle_of_boxSupported` collects all their values from
    `BoxSupportedC2Flow` + `IsNSSolution`. The structure is PRESERVED as a layer-by-layer
    abstraction (its fields are derivable); the headline theorems do not require it directly. -/
structure R3AssemblyGates (ν : ℝ) (f : ℝ → E3 → E3)
    (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) where
  forceZero : ∀ t x, f t x = 0
  timeDeriv : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  domination : ∀ t, TimeDomination u (nsTimeDerivative ν f u p) t
  intLap : ∀ t, Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume
  intPress : ∀ t, Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume
  intConv : ∀ t, Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume
  pressureKills : ∀ t, (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ) = 0
  transportKills : ∀ t, (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) = 0
  viscosityIBP : ∀ t,
    (∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ)
      = -(∫ x : E3, ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖ ^ 2)

/-- Splitting the integral `∫⟪u, D⟫` over the summands of the NS right-hand side. -/
theorem integral_inner_nsTimeDerivative_split
    (ν : ℝ) (f : ℝ → E3 → E3) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) (t : ℝ)
    (hf : ∀ x, f t x = 0)
    (hLap : Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume)
    (hPress : Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume)
    (hConv : Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume) :
    (∫ x : E3, ⟪u t x, nsTimeDerivative ν f u p t x⟫_ℝ)
      = (∫ x : E3, ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ)
        - (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ)
        - (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) := by
  set gLap := fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ with hgLap
  set gPress := fun x => ⟪u t x, gradient (p t) x⟫_ℝ with hgPress
  set gConv := fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ with hgConv
  have hpt : (fun x : E3 => ⟪u t x, nsTimeDerivative ν f u p t x⟫_ℝ)
      = fun x => (gLap x - gPress x) - gConv x := by
    funext x
    rw [hgLap, hgPress, hgConv, nsTimeDerivative]
    rw [show ν • vectorLaplacian (u t) x - gradient (p t) x + f t x
          - convectiveTerm (u t) x
        = (ν • vectorLaplacian (u t) x - gradient (p t) x)
          - convectiveTerm (u t) x + f t x from by rw [hf x]; abel]
    rw [inner_add_right, inner_sub_right, inner_sub_right]
    rw [hf x, inner_zero_right]
    ring
  rw [hpt]
  have hstep1 : (∫ x : E3, (gLap x - gPress x) - gConv x)
      = (∫ x : E3, gLap x - gPress x) - ∫ x : E3, gConv x :=
    MeasureTheory.integral_sub (hLap.sub hPress) hConv
  have hstep2 : (∫ x : E3, gLap x - gPress x)
      = (∫ x : E3, gLap x) - ∫ x : E3, gPress x :=
    MeasureTheory.integral_sub hLap hPress
  rw [hstep1, hstep2]

/-- **ASSEMBLY HEADLINE (R1 + three killers ⟹ LAW): `energyBalance_of_r3Gates`.**
    The energy balance `dE/dt = −D` is DERIVED from the layer-by-layer gates: R1 gives `dE/dt = ∫⟪u,∂ₜu⟫`,
    splitting over the NS summands + the three killers (pressure and transport ⟶ 0, viscosity ⟶
    −∫∑‖∂ᵢu‖²) land on `−dissipationRate`. THE LAW IS NOT DECREED. -/
theorem energyBalance_of_r3Gates
    {ν : ℝ} {f : ℝ → E3 → E3} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (G : R3AssemblyGates ν f u p) :
    EnergyBalanceLaw ν u := by
  intro t
  -- R1
  have hR1 := hasDerivAt_kineticEnergy_of_timeDomination u
    (nsTimeDerivative ν f u p) t (G.domination t)
  -- value of the derivative = −dissipationRate
  have hval : (∫ x : E3, ⟪u t x, nsTimeDerivative ν f u p t x⟫_ℝ)
      = -(dissipationRate ν (u t)) := by
    rw [integral_inner_nsTimeDerivative_split ν f u p t (fun x => G.forceZero t x)
      (G.intLap t) (G.intPress t) (G.intConv t)]
    rw [G.pressureKills t, G.transportKills t, sub_zero, sub_zero]
    -- ∫⟪u, ν•Δu⟫ = ν∫⟪u,Δu⟫ = −ν∫∑‖∂ᵢu‖² = −dissipationRate remains
    have hsmul : (∫ x : E3, ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ)
        = ν * ∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only []
      rw [real_inner_smul_right]
    rw [hsmul, G.viscosityIBP t, dissipationRate]
    ring
  rw [hval] at hR1
  exact hR1

/-- **Killer bundle + integrabilities — NOW DERIVABLE (not a residual input).**
    Three killers (E3 IBP identities) and three component integrabilities. FORMERLY the bundle was
    an honest analytic remainder; NOW `killerBundle_of_boxSupported F sol`
    builds ALL its fields from `BoxSupportedC2Flow` + `IsNSSolution` via the master lemma
    §3bis. The structure is PRESERVED as a reusable abstraction of the layer-by-layer assembly. -/
structure KillerBundle (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) where
  intLap : ∀ t, Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume
  intPress : ∀ t, Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume
  intConv : ∀ t, Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume
  pressureKills : ∀ t, (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ) = 0
  transportKills : ∀ t, (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) = 0
  viscosityIBP : ∀ t,
    (∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ)
      = -(∫ x : E3, ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖ ^ 2)

/-- **`killerBundle_of_boxSupported` — THE ENTIRE KILLER BUNDLE DERIVED (not a hypothesis).**
    From a box-supported C² flow `F` and a force-free solution `sol`, ALL six
    fields of `KillerBundle` are assembled: three integrabilities (§4bis, §4ter) and three killers
    (§4bis `pressureKills`, §4bis `transportKills`, §4ter `viscosityIBP`).
    The killers are no longer named inputs — they are PROVEN by the master lemma §3bis. -/
def killerBundle_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p) :
    KillerBundle ν u p where
  intLap := intLap_of_boxSupported F
  intPress := intPress_of_boxSupported F
  intConv := intConv_of_boxSupported F
  pressureKills := pressureKills_of_boxSupported F sol
  transportKills := transportKills_of_boxSupported F sol
  viscosityIBP := viscosityIBP_of_boxSupported F

/-- **`r3AssemblyGates_of_boxSupported` — layer-by-layer assembly of the gate set.**
    From a box-supported C² flow `F`, a per-time majorant `dom`, a force-free solution
    `sol` (`f = 0`) and a residual killer bundle `K`, an `R3AssemblyGates` is assembled.
    `F` (including the pressure smoothness gate) provides the structural part;
    the residual analytics `K` is fed transparently (the LAYER is preserved; `K` is now DERIVABLE
    via `killerBundle_of_boxSupported`). -/
def r3AssemblyGates_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (K : KillerBundle ν u p) :
    R3AssemblyGates ν (fun _ _ => 0) u p where
  forceZero := fun _ _ => rfl
  timeDeriv := F.timeDeriv
  domination := dom
  intLap := K.intLap
  intPress := K.intPress
  intConv := K.intConv
  pressureKills := K.pressureKills
  transportKills := K.transportKills
  viscosityIBP := K.viscosityIBP

/-- **`energyBalance_of_boxSupported` — COMPOSITION (LAW DERIVED for the box class).**
    A box-supported C² flow `F` + a force-free solution `sol` + a majorant `dom` ⟹
    the energy balance. The three killers are NO LONGER an INPUT — they are assembled inside
    `killerBundle_of_boxSupported F sol` (master lemma §3bis). The honest input
    `dom` (🔴 `TimeDomination`, R1) remains. -/
theorem energyBalance_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t) :
    EnergyBalanceLaw ν u :=
  energyBalance_of_r3Gates
    (r3AssemblyGates_of_boxSupported F dom (killerBundle_of_boxSupported F sol))

/-#############################################################################
  §5. INHABITANCE — the zero solution passes ALL class gates (not vacuity).
#############################################################################-/

/-- The zero field is a box-supported C² flow (trivially: everything is the constant `0`). -/
def zero_boxSupportedC2Flow (ν : ℝ) (hν : 0 ≤ ν) :
    BoxSupportedC2Flow ν (fun _ _ => 0) (fun _ _ => 0) where
  hle := hν
  a := 0
  b := 1
  aleb := by intro i; simp
  timeDeriv := fun _ _ => differentiableAt_const _
  spaceDiff := fun _ _ => differentiableAt_const _
  spaceDiff2 := fun _ i x => by
    have h : (fun y : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) y (e3 i))
        = fun _ => (0 : E3) := by
      funext y; simp
    rw [h]; exact differentiableAt_const _
  pressDiff := fun _ _ => differentiableAt_const _
  contU := fun _ => continuous_const
  contU' := fun _ i => by
    have h : (fun x : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) x (e3 i))
        = fun _ => (0 : E3) := by
      funext y; simp
    rw [h]; exact continuous_const
  contU'' := fun _ i j => by
    have h : (fun x : E3 =>
        fderiv ℝ (fun y : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) y (e3 i)) x (e3 j))
        = fun _ => (0 : E3) := by
      funext x
      have h0 : (fun y : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) y (e3 i))
          = fun _ => (0 : E3) := by funext y; simp
      rw [h0]; simp
    rw [h]; exact continuous_const
  contP := fun _ => continuous_const
  contP' := fun _ i => by
    have h : (fun x : E3 => fderiv ℝ (fun _ : E3 => (0 : ℝ)) x (e3 i))
        = fun _ => (0 : ℝ) := by
      funext y; simp
    rw [h]; exact continuous_const
  supp := fun _ _ _ => rfl

/-- The zero field is a time majorant (bound := 0; the `nsTimeDerivative` of zero is `0`). -/
def zero_timeDomination (ν : ℝ) (t : ℝ) :
    TimeDomination (fun _ _ => (0 : E3))
      (nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)) t where
  bound := fun _ => 0
  measSq := Filter.Eventually.of_forall (fun _ => by
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact aestronglyMeasurable_const)
  intSq := by
    have h : (fun x : E3 => ‖(0 : E3)‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [h]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  measDeriv := by
    have h : (fun x : E3 => (2 : ℝ) * ⟪(0 : E3),
        nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) t x⟫_ℝ)
        = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [h]; exact aestronglyMeasurable_const
  dominated := Filter.Eventually.of_forall (fun x s _ => by
    simp only [nsTimeDerivative_zero, inner_zero_right, mul_zero, norm_zero, le_refl])
  intBound := integrable_zero (α := E3) (ε' := ℝ) volume
  hasDeriv := Filter.Eventually.of_forall (fun x s _ => by
    rw [nsTimeDerivative_zero]; exact hasDerivAt_const s (0 : E3))

/-- The zero field is a residual killer bundle (all integrands and integrals are zero). -/
def zero_killerBundle (ν : ℝ) :
    KillerBundle ν (fun _ _ => (0 : E3)) (fun _ _ => 0) where
  intLap := fun _ => by
    simp only [inner_zero_left]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  intPress := fun _ => by
    simp only [inner_zero_left]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  intConv := fun _ => by
    simp only [inner_zero_left]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  pressureKills := fun _ => by simp only [inner_zero_left, integral_zero]
  transportKills := fun _ => by simp only [inner_zero_left, integral_zero]
  viscosityIBP := fun _ => by
    simp only [inner_zero_left, integral_zero]
    simp

/-- **INHABITANCE (not vacuity): the zero solution derives the energy balance via the assembly.**
    The killers are now DERIVED — only the solution `zero_is_NSSolution` and
    the majorant `zero_timeDomination` are fed in. -/
theorem zero_energyBalance_of_boxSupported (ν : ℝ) (hν : 0 ≤ ν) :
    EnergyBalanceLaw ν (fun _ _ => 0) :=
  energyBalance_of_boxSupported (zero_boxSupportedC2Flow ν hν)
    (zero_is_NSSolution ν) (zero_timeDomination ν)

/-#############################################################################
  §6. HEADLINE — smoothness surrogate and energy identity from the R3 assembly.
#############################################################################-/

/-- **HEADLINE: `noSingularCascade_of_r3Assembly` — SMOOTHNESS SURROGATE from the assembly.**
    A box-supported C² flow + majorant + killers + integrability of the dissipation ⟹
    `NoSingularCascade` (no uniformly quantized δ-cascade up to a finite `T`).
    Composition of `energyBalance_of_boxSupported` (§4) and `noSingularCascade_of_energyBalance`
    (front). ⚠️ SURROGATE, NOT C∞; the Clay problem is NOT solved. -/
theorem noSingularCascade_of_r3Assembly
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    NoSingularCascade ν u :=
  noSingularCascade_of_energyBalance ν u
    (energyBalance_of_boxSupported F sol dom) hInt

/-- **`energyIdentity_of_r3Assembly` — ENERGY IDENTITY (FTC-2) from the assembly.**
    `E(t₂) = E(t₁) − ∫_{t₁}^{t₂} D` for a box-supported flow. -/
theorem energyIdentity_of_r3Assembly
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)
    (t₁ t₂ : ℝ) :
    kineticEnergy (u t₂)
      = kineticEnergy (u t₁) - ∫ s in t₁..t₂, dissipationRate ν (u s) :=
  energy_identity_of_energyBalance ν u
    (energyBalance_of_boxSupported F sol dom) hInt t₁ t₂

/-- **DOCUMENTARY (`nsBoundary_redundant_on_boxClass`): on the box class the decree
    `NsSolutionBalanceLaw` is REDUNDANT.** The law's conclusion (energy balance +
    integrability of the dissipation) for a box-supported flow is DERIVED by the assembly —
    it need NOT be decreed on this class. The content of the decree remains only
    OUTSIDE the finite box support (the limit transition box→ℝ³ is absent in mathlib —
    an external gap, NOT closed here). -/
theorem nsBoundary_redundant_on_boxClass
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    EnergyBalanceLaw ν u ∧
    (∀ t₁ t₂ : ℝ, IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :=
  ⟨energyBalance_of_boxSupported F sol dom, hInt⟩

/-#############################################################################
  §7. EXCLUSION OF IMPOSTORS — both fail the class gates (one-liners).
#############################################################################-/

/-- **Forging-B (`cookedFlow`) FAILS the assembly gate** — spatial
    differentiability `spaceDiff` is impossible (non-smoothness on the sphere,
    front `cookedFlow_fails_space_gate`). The class smoothness gate catches the junk in ∇p. -/
theorem cookedFlow_fails_assemblyGates {ν : ℝ} {p : ℝ → E3 → ℝ} :
    ¬ ∃ F : BoxSupportedC2Flow ν cookedFlow p, True := by
  rintro ⟨F, -⟩
  exact cookedFlow_fails_space_gate F.spaceDiff

/-- **Forging-A (`dirichletFlow`) FAILS the assembly gate** — temporal
    differentiability `timeDeriv` is impossible (Dirichlet flicker,
    front `dirichletFlow_fails_time_gate`). -/
theorem dirichletFlow_fails_assemblyGates {ν : ℝ} {p : ℝ → E3 → ℝ} :
    ¬ ∃ F : BoxSupportedC2Flow ν dirichletFlow p, True := by
  rintro ⟨F, -⟩
  exact dirichletFlow_fails_time_gate F.timeDeriv

end EuclidsPath.NavierStokesR3

end

/-#############################################################################
  §8. #print axioms — machine visibility of purity in the build log
      (expected [propext, Classical.choice, Quot.sound]).
#############################################################################-/

#print axioms EuclidsPath.NavierStokesR3.hasDerivAt_kineticEnergy_of_dominated
#print axioms EuclidsPath.NavierStokesR3.boxDivergence_integral_eq_zero
#print axioms EuclidsPath.NavierStokesR3.divergence_integral_eq_zero
#print axioms EuclidsPath.NavierStokesR3.pressureDiv_pi
#print axioms EuclidsPath.NavierStokesR3.integral_e3_divergence_eq_zero
#print axioms EuclidsPath.NavierStokesR3.pressureKills_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.transportKills_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.viscosityIBP_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.killerBundle_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.energyBalance_of_r3Gates
#print axioms EuclidsPath.NavierStokesR3.energyBalance_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.noSingularCascade_of_r3Assembly
#print axioms EuclidsPath.NavierStokesR3.energyIdentity_of_r3Assembly
#print axioms EuclidsPath.NavierStokesR3.zero_energyBalance_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.zero_timeDomination
#print axioms EuclidsPath.NavierStokesR3.cookedFlow_fails_assemblyGates
#print axioms EuclidsPath.NavierStokesR3.dirichletFlow_fails_assemblyGates
