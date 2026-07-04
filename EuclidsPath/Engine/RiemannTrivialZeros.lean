/-
  RiemannTrivialZeros — GATE #1 OF THE RH BRANCH IS CLOSED.
  Prose: prose/30_RiemannBranch.md.

  PROVED HERE (mathlib, std axioms, no sorry):
    * trivialBelowZeroClassification — classification of zeros at Re ≤ 0:
      every zero ζ with Re s ≤ 0 is −2(n+1). Route: s=0 is excluded
      (riemannZeta_zero = −1/2); for s ≠ 0 the functional equation
      riemannZeta_one_sub at w := 1−s (Re w ≥ 1), non-trivial factors
      are nonzero (riemannZeta_ne_zero_of_one_le_re, Gamma_ne_zero_of_re_pos,
      cpow_ne_zero), hence cos(π(1−s)/2) = 0 ⟹ s = −2k, k ≥ 1.
    * _proved / _branch_proved — exact Props of RiemannEngine and RiemannBranch;
    * UNCONDITIONAL CONSEQUENCES: localization of a non-trivial zero to the strip
      is no longer a gate; RH is now conditional ONLY on EngineBridge (or TwoTransportBridge).

  The former "analytic gate" turned out to be derivable: mathlib supplied the values
  of trivial zeros, and the reverse classification follows from mathlib itself.
  Discovered by workflow agent (xhigh), verified manually, integrated.
-/
import Mathlib
import EuclidsPath.Engine.RiemannEngine
import EuclidsPath.Engine.RiemannBranch

set_option autoImplicit false

namespace EuclidsPath.TrivialZeros

open Complex
open scoped Real

/-- **Classification of zeta zeros in the closed left half-plane.**
Every zero of `riemannZeta` with `Re s ≤ 0` is a trivial zero `-2(n+1)`. -/
theorem trivialBelowZeroClassification :
    ∀ s : ℂ, riemannZeta s = 0 → s.re ≤ 0 → ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  intro s hzero hre
  -- `s ≠ 0`, since `ζ(0) = -1/2`.
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  -- The reflected point `1 - s` lies in `Re ≥ 1`.
  have hw_re : 1 ≤ (1 - s).re := by
    have h : (1 - s).re = 1 - s.re := by simp
    rw [h]; linarith
  have hw_pos : 0 < (1 - s).re := lt_of_lt_of_le one_pos hw_re
  -- `1 - s` is not a non-positive integer.
  have hw_ne : ∀ n : ℕ, (1 : ℂ) - s ≠ -(n : ℂ) := by
    intro n hn
    have h1 : (1 - s).re = ((-(n : ℂ)).re : ℝ) := by rw [hn]
    have h2 : (-(n : ℂ)).re = -(n : ℝ) := by simp
    rw [h2] at h1
    have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [h1] at hw_re
    linarith
  -- `1 - s ≠ 1` (since `s ≠ 0`).
  have hw_ne_one : (1 : ℂ) - s ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
  -- Functional equation at `1 - s` : expresses `ζ(s)` via `ζ(1 - s)`.
  have hfe := riemannZeta_one_sub (s := 1 - s) hw_ne hw_ne_one
  have hss : (1 : ℂ) - (1 - s) = s := by ring
  rw [hss, hzero] at hfe
  -- All non-trigonometric factors are nonzero.
  have hzeta_ne : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hGamma_ne : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw_pos
  have hpow_ne : (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  -- Extract vanishing of the cosine factor.
  have hcos : Complex.cos ((π : ℂ) * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp hfe.symm with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd h4 two_ne_zero
          · exact absurd h4 hpow_ne
        · exact absurd h3 hGamma_ne
      · exact h2
    · exact absurd h1 hzeta_ne
  -- Classify: `π (1-s)/2 = (2k+1) π / 2` for some integer `k`, hence `s = -2k`.
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : (π : ℂ) * (1 - s) = (π : ℂ) * (2 * (k : ℂ) + 1) := by
    linear_combination 2 * hk
  have h2 : (1 : ℂ) - s = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi_ne h1
  have hs_eq : s = -2 * (k : ℂ) := by linear_combination -h2
  -- Pin down the integer via the cast through ℤ.
  have hs_eq' : s = ((-2 * k : ℤ) : ℂ) := by rw [hs_eq]; push_cast; ring
  have hre_eq : s.re = ((-2 * k : ℤ) : ℝ) := by
    rw [hs_eq']
    simp
  -- `Re s ≤ 0` gives `0 ≤ k`; `s ≠ 0` gives `k ≠ 0`; hence `1 ≤ k`.
  have hk_nonneg : (0 : ℤ) ≤ k := by
    have h_le : ((-2 * k : ℤ) : ℝ) ≤ 0 := hre_eq ▸ hre
    have h_le' : (-2 * k : ℤ) ≤ 0 := by exact_mod_cast h_le
    omega
  have hk_ne : k ≠ 0 := by
    rintro rfl
    apply hs0
    rw [hs_eq']
    norm_num
  have hk_one : 1 ≤ k := by omega
  -- Produce the natural number `n = k - 1`.
  refine ⟨(k - 1).toNat, ?_⟩
  have hn : (((k - 1).toNat : ℤ)) = k - 1 := Int.toNat_of_nonneg (by omega)
  have hcast : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
    rw [← Int.cast_natCast (R := ℂ), hn]
    push_cast
    ring
  rw [hs_eq, hcast]
  ring

/-- The analytic input of `EuclidsPath.RiemannEngine` is now a theorem. -/
theorem trivialBelowZeroClassification_proved :
    EuclidsPath.RiemannEngine.TrivialBelowZeroClassification :=
  trivialBelowZeroClassification

/-- The analytic input of `EuclidsPath.RiemannBranch` is now a theorem. -/
theorem trivialBelowZeroClassification_branch_proved :
    EuclidsPath.RiemannBranch.TrivialBelowZeroClassification :=
  trivialBelowZeroClassification

#print axioms trivialBelowZeroClassification
#print axioms trivialBelowZeroClassification_proved
#print axioms trivialBelowZeroClassification_branch_proved


/-! Unconditional consequences: what was closed along with the gate -/

/-- **Localization to the strip — now a THEOREM** (was conditional on the gate):
    a non-trivial zero lies strictly in 0 < Re ρ < 1. -/
theorem nontrivialZero_in_strip_unconditional {ρ : ℂ}
    (hρ : EuclidsPath.RiemannBranch.NontrivialZeroM ρ) :
    0 < ρ.re ∧ ρ.re < 1 :=
  EuclidsPath.RiemannBranch.nontrivialZero_in_strip
    trivialBelowZeroClassification_branch_proved hρ

/-- **RH is conditional ONLY on EngineBridge** (the classification gate is lifted). -/
theorem riemannHypothesis_of_engineBridge_only
    (H : EuclidsPath.RiemannBranch.EngineBridge) : RiemannHypothesis :=
  EuclidsPath.RiemannBranch.riemannHypothesis_of_engine_bridge
    trivialBelowZeroClassification_branch_proved H

/-- **RH is conditional ONLY on TwoTransportBridge** (second route, gate lifted). -/
theorem riemannHypothesis_of_twoTransportBridge_only
    (bridge : EuclidsPath.RiemannBranch.TwoTransportBridge) : RiemannHypothesis :=
  EuclidsPath.RiemannBranch.riemannHypothesis_of_two_transport
    trivialBelowZeroClassification_branch_proved bridge

end EuclidsPath.TrivialZeros
