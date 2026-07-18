/-
  Analytic/ZeroFreeNbhd — STAGE P-B2 of the Tauberian campaign: the OPEN
  ZERO-FREE NEIGHBORHOOD of the closed half-plane `Re ≥ 1`, uniformly in
  the modulus — WITHOUT zeta-zero discreteness.

  DESIGN.  Every denominator of the campaign comes from
  `LFunctionTrivChar₁ q` (ENTIRE, the pole multiplied away, nonzero at 1)
  or `LFunction χ` for `χ ≠ 1` (entire).  So the set
  `zeroFreeSet q := {L₁ ≠ 0} ∩ ⋂_{χ ≠ 1} {L(χ) ≠ 0}` is OPEN (preimages
  of `{0}ᶜ` under continuous entire functions, finite intersection) and
  CONTAINS `{Re ≥ 1}` (the pin's nonvanishing).  Discreteness of zeros
  (`ZetaZeros`) is never needed: the pole is already cancelled.

  On this set the residue-class auxiliary function of the pin
  (`vonMangoldt.LFunctionResidueClassAux`) is HOLOMORPHIC (the pin only
  states continuity; the proof skeleton is identical with
  `ContinuousOn.*` replaced by `DifferentiableOn.*`), and the holomorphic
  inverse `LFunctionInv` continues `1/L(χ,·)` across the trivial pole.

  DISCLOSURES.
    * Pure analytic infrastructure over the pin's L-function frame: no
      face of the parity wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex DirichletCharacter ArithmeticFunction Set
open scoped LSeries.notation

variable (q : ℕ) [NeZero q]

/-- The uniform open zero-free set: where the pole-cancelled trivial
L-function and all nontrivial L-functions are simultaneously nonzero. -/
noncomputable def zeroFreeSet : Set ℂ :=
  {s : ℂ | LFunctionTrivChar₁ q s ≠ 0} ∩
    ⋂ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
      {s : ℂ | LFunction χ s ≠ 0}

theorem isOpen_zeroFreeSet : IsOpen (zeroFreeSet q) := by
  unfold zeroFreeSet
  refine IsOpen.inter ?_ (isOpen_biInter_finset fun χ hχ => ?_)
  · exact isOpen_ne.preimage (differentiable_LFunctionTrivChar₁ q).continuous
  · have hχ1 : χ ≠ 1 := by
      simpa [Finset.mem_compl, Finset.mem_singleton] using hχ
    exact isOpen_ne.preimage (differentiable_LFunction hχ1).continuous

theorem closedHalfPlane_subset_zeroFreeSet :
    {s : ℂ | 1 ≤ s.re} ⊆ zeroFreeSet q := by
  intro s hs
  have hs1 : 1 ≤ s.re := hs
  constructor
  · rcases eq_or_ne s 1 with rfl | hne
    · exact LFunctionTrivChar₁_apply_one_ne_zero q
    · show LFunctionTrivChar₁ q s ≠ 0
      rw [LFunctionTrivChar₁, Function.update_of_ne hne]
      exact mul_ne_zero (sub_ne_zero_of_ne hne)
        (LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q)
          (Or.inr hne) hs1)
  · rw [Set.mem_iInter₂]
    intro χ hχ
    have hχ1 : χ ≠ 1 := by
      simpa [Finset.mem_compl, Finset.mem_singleton] using hχ
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hs1

variable {q}

/-- Membership unfolding: the trivial component. -/
theorem zeroFreeSet_triv_ne_zero {s : ℂ} (hs : s ∈ zeroFreeSet q) :
    LFunctionTrivChar₁ q s ≠ 0 := hs.1

/-- Membership unfolding: the nontrivial components. -/
theorem zeroFreeSet_ne_zero {s : ℂ} (hs : s ∈ zeroFreeSet q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : LFunction χ s ≠ 0 := by
  have h2 := hs.2
  rw [Set.mem_iInter₂] at h2
  exact h2 χ (by simpa [Finset.mem_compl, Finset.mem_singleton] using hχ)

variable (q)

/-- **The residue-class auxiliary function is HOLOMORPHIC on the zero-free
set** — the differentiable strengthening of the pin's
`continuousOn_LFunctionResidueClassAux`. -/
theorem differentiableOn_LFunctionResidueClassAux (a : ZMod q) :
    DifferentiableOn ℂ (vonMangoldt.LFunctionResidueClassAux a)
      (zeroFreeSet q) := by
  have h1 : Differentiable ℂ (LFunctionTrivChar₁ q) :=
    differentiable_LFunctionTrivChar₁ q
  have h1d : Differentiable ℂ (deriv (LFunctionTrivChar₁ q)) :=
    h1.contDiff.differentiable_deriv_two
  refine DifferentiableOn.const_mul ?_ _
  refine DifferentiableOn.sub ?_ ?_
  · exact (h1d.neg.differentiableOn.div h1.differentiableOn
      fun s hs => zeroFreeSet_triv_ne_zero hs)
  · refine DifferentiableOn.fun_sum fun χ hχ => ?_
    have hχ1 : χ ≠ 1 := by
      simpa [Finset.mem_compl, Finset.mem_singleton] using hχ
    have h2 : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ1
    have h2d : Differentiable ℂ (deriv (LFunction χ)) :=
      h2.contDiff.differentiable_deriv_two
    exact ((h2d.differentiableOn.const_mul _).div h2.differentiableOn
      fun s hs => zeroFreeSet_ne_zero hs hχ1)

variable {q}

/-- The holomorphic continuation of `1/L(χ,·)` across the trivial pole:
`(s−1)/L₁` for the trivial character, the plain inverse otherwise. -/
noncomputable def LFunctionInv (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then fun s => (s - 1) / LFunctionTrivChar₁ q s
  else fun s => (LFunction χ s)⁻¹

theorem differentiableOn_LFunctionInv (χ : DirichletCharacter ℂ q) :
    DifferentiableOn ℂ (LFunctionInv χ) (zeroFreeSet q) := by
  unfold LFunctionInv
  split_ifs with hχ
  · exact (differentiable_id.sub_const 1).differentiableOn.div
      (differentiable_LFunctionTrivChar₁ q).differentiableOn
      fun s hs => zeroFreeSet_triv_ne_zero hs
  · exact ((differentiable_LFunction hχ).differentiableOn).inv
      fun s hs => zeroFreeSet_ne_zero hs hχ

/-- On `Re s > 1` the continuation IS the inverse. -/
theorem LFunctionInv_eq_inv {χ : DirichletCharacter ℂ q} {s : ℂ}
    (hs : 1 < s.re) : LFunctionInv χ s = (LFunction χ s)⁻¹ := by
  unfold LFunctionInv
  split_ifs with hχ
  · subst hχ
    have hne : s ≠ 1 := by
      intro h
      rw [h] at hs
      simp at hs
    show (s - 1) / LFunctionTrivChar₁ q s
        = (LFunction (1 : DirichletCharacter ℂ q) s)⁻¹
    rw [LFunctionTrivChar₁, Function.update_of_ne hne]
    have hL : LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 :=
      LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q)
        (Or.inr hne) hs.le
    have hsub : s - 1 ≠ 0 := sub_ne_zero_of_ne hne
    rw [show LFunctionTrivChar q s
        = LFunction (1 : DirichletCharacter ℂ q) s from rfl]
    field_simp
  · rfl

end Analytic
end EuclidsPath
