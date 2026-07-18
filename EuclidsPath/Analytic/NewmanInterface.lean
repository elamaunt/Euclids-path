/-
  Analytic/NewmanInterface — STAGE P-A0 of the Tauberian campaign: the
  Newman interface in MELLIN NORMAL FORM, and its immediate discharge.

  ARCHITECTURE NOTE (deviation from the approved plan, in the honest
  direction).  The plan staged this interface as a named `Prop` so that
  the plumbing could be built green-conditionally BEFORE the analytic
  core landed.  The core landed FIRST (stage N complete:
  `Tauberian.newman_tauberian_mellin`), so the interface `Prop` is
  DISCHARGED IN THIS SAME MODULE (`newmanMellin_proved`) — the repo
  gains ZERO open `Prop`s from this stage, and every downstream
  consumer is unconditionally green.  The planned `NewmanLaplace` Prop
  is NOT declared: no consumer needs the Laplace form.

  The interface shape: `S` measurable and uniformly bounded on `[1,∞)`,
  `g` holomorphic on an open `U ⊇ {Re ≥ 0}` with
  `g(z) = ∫_1^∞ S(t)·t^{−z−1} dt` on `Re z > 0`; conclusion
  `∫_1^X S(t)/t dt → g(0)`.  This is the pole-free unshifted form: the
  three arithmetic consumers (ψ-type sums, ψ in progressions, λ-sums)
  subtract their pole BEFORE applying it.

  DISCLOSURES.
    * Pure analysis: no arithmetic content, no face of the parity wall is
      touched, and no §110 event is claimed.
    * The `Prop` below is a DOCUMENTED INTERFACE — introduced and
      discharged in the same file; nothing in the repo assumes it.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Tauberian.NewmanMellin

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex MeasureTheory Metric Set Filter intervalIntegral
open scoped Interval Real

/-- **Newman's theorem, Mellin normal form** — the single interface
consumed by the plumbing stage.  Discharged below (`newmanMellin_proved`);
kept as a named statement so consumers can be read against a fixed
normal form. -/
def NewmanMellin : Prop :=
  ∀ (S : ℝ → ℂ) (g : ℂ → ℂ) (U : Set ℂ) (C : ℝ),
    Measurable S →
    (∀ t : ℝ, 1 ≤ t → ‖S t‖ ≤ C) →
    IsOpen U → {z : ℂ | 0 ≤ z.re} ⊆ U →
    DifferentiableOn ℂ g U →
    (∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (1 : ℝ), S t * (t : ℂ) ^ (-z - 1)) →
    Tendsto (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X, S t / t)
      atTop (nhds (g 0))

/-- **THE DISCHARGE**: the interface holds — instantiate the stage-N core
(`newman_tauberian_mellin`) at `A := S·t`, `c := 0`, `G := g ∘ (· − 1)`. -/
theorem newmanMellin_proved : NewmanMellin := by
  intro S g U C hS_meas hS_bdd hU_open hU_mem hg hrep
  have hA_meas : Measurable (fun t : ℝ => S t * (t : ℂ)) :=
    hS_meas.mul (Complex.measurable_ofReal.comp measurable_id)
  have hA_bdd : ∀ t ∈ Set.Ioi (1 : ℝ), ‖S t * (t : ℂ)‖ ≤ C * t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < t)]
    exact mul_le_mul_of_nonneg_right (hS_bdd t ht1.le) (by linarith)
  have hU'_open : IsOpen ((fun s : ℂ => s - 1) ⁻¹' U) :=
    hU_open.preimage (by fun_prop)
  have hU'_mem : {s : ℂ | 1 ≤ s.re} ⊆ (fun s : ℂ => s - 1) ⁻¹' U := by
    intro s hs
    apply hU_mem
    simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
    have h1 : 1 ≤ s.re := hs
    linarith
  have hG : DifferentiableOn ℂ (fun s => g (s - 1))
      ((fun s : ℂ => s - 1) ⁻¹' U) := by
    intro s hs
    exact ((hg _ hs).comp s
      ((differentiable_id.sub_const 1) s).differentiableWithinAt
      (fun w hw => hw))
  have hrep' : ∀ s : ℂ, 1 < s.re →
      (fun s => g (s - 1)) s
        = (∫ t in Set.Ioi (1 : ℝ), (S t * (t : ℂ)) * (t : ℂ) ^ (-s - 1))
          - 0 / (s - 1) := by
    intro s hs
    simp only [zero_div, sub_zero]
    have hz : 0 < (s - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    rw [hrep (s - 1) hz]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (t : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      linarith
    have hexp : (-(s - 1) - 1 : ℂ) = (-s - 1) + 1 := by ring
    rw [hexp, Complex.cpow_add _ _ ht0, Complex.cpow_one]
    ring
  have hmain := Tauberian.newman_tauberian_mellin hA_meas hA_bdd
    hU'_open hU'_mem hG hrep'
  rw [show (1 : ℂ) - 1 = 0 by ring] at hmain
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  rw [intervalIntegral.integral_of_le hX]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have ht0 : (t : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith [ht.1]
  field_simp
  ring

/-- The real-valued consumption corollary: for real `S` the conclusion
descends to a real limit `(g 0).re` — the only form the arithmetic
chains use. -/
theorem NewmanMellin.real_of (hN : NewmanMellin) {S : ℝ → ℝ} {g : ℂ → ℂ}
    {U : Set ℂ} {C : ℝ} (h₁ : Measurable S) (h₂ : ∀ t : ℝ, 1 ≤ t → |S t| ≤ C)
    (h₃ : IsOpen U) (h₄ : {z : ℂ | 0 ≤ z.re} ⊆ U)
    (h₅ : DifferentiableOn ℂ g U)
    (h₆ : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (1 : ℝ), (S t : ℂ) * (t : ℂ) ^ (-z - 1)) :
    Tendsto (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X, S t / t)
      atTop (nhds ((g 0).re)) := by
  have hc := hN (fun t => (S t : ℂ)) g U C
    (Complex.measurable_ofReal.comp h₁)
    (fun t ht => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact h₂ t ht)
    h₃ h₄ h₅ h₆
  have hre := (Complex.continuous_re.tendsto (g 0)).comp hc
  refine hre.congr fun X => ?_
  simp only [Function.comp_apply]
  have hcast : ∫ t in Set.Ioc (1 : ℝ) X, (S t : ℂ) / (t : ℂ)
      = ((∫ t in Set.Ioc (1 : ℝ) X, S t / t : ℝ) : ℂ) := by
    rw [← _root_.integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

end Analytic
end EuclidsPath
