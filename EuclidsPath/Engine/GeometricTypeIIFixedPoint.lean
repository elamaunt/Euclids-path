/-
  GeometricTypeIIFixedPoint — the one-defect fixed point: no finite even moment breaks the wall.

  ORIGIN (parity_wall Prime-Chaos session dossier §26 / §27 / §28). Locally the character
  eigenvalues are `λ(1) = 1`, `λ(χ) = −1/m` (`χ ≠ 1`), with `m + 1 = p − 1` characters.  For any
  moment order and any nontrivial shift `θ`, the "one-defect" contraction
  `B_{k,p}(θ) = Σ_χ λ(χ)^{2k−1} λ(χθ)` collapses EXACTLY to `−(1/m) A_{k,p}` where
  `A_{k,p} = Σ_χ |λ(χ)|^{2k}` — i.e. every finite even moment reproduces the SAME parity eigenvalue
  `−1/m = −1/(p−2)`.  Hence `S₄, S₆, S₈, …` by themselves do NOT break the wall.

  We formalize abstractly: `ι` finite of card `m+1`, a two-valued `f` (`f i₀ = 1`, `f i = −1/m`
  off `i₀`), and a permutation `σ` with `σ i₀ ≠ i₀` (the nontrivial shift).  The whole content is
  a finite delta-decomposition of the product `f(χ)^{2j+1} f(σχ)`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `A_moment` — `Σ_χ f(χ)^{2j+2} = 1 + (m)·v^{2j+2}` (the even moment, `v = −1/m`);
    * `one_defect_fixed_point` — `Σ_χ f(χ)^{2j+1} f(σχ) = (−1/m)·Σ_χ f(χ)^{2j+2}` (the wall
      eigenvalue reproduced at every order).

  DISCLOSURE. This is a no-go: the eigenvalue `−1/(p−2)` is a fixed point of every even moment, so
  higher moments alone cannot break the parity wall (§59). twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## Two elementary finite-sum facts -/

private theorem sum_ite_const {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (A B : ℝ) :
    ∑ χ : ι, (if χ = i₀ then A else B) = A + ((Fintype.card ι : ℝ) - 1) * B := by
  have h : ∀ χ : ι, (if χ = i₀ then A else B) = B + (if χ = i₀ then A - B else 0) := by
    intro χ; by_cases hχ : χ = i₀ <;> simp [hχ]
  rw [Finset.sum_congr rfl (fun χ _ => h χ), Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ i₀), Finset.card_univ, nsmul_eq_mul]
  ring

private theorem sum_indicator_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ∑ χ : ι, (if χ = a then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]

/-! ## The even moment and the one-defect fixed point (§27) -/

/-- **Even moment (§27).** `Σ_χ f(χ)^{2j+2} = 1 + m·v^{2j+2}`, `v = −1/m`. -/
theorem A_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (m : ℕ) (hm : Fintype.card ι = m + 1) (j : ℕ)
    (f : ι → ℝ) (hf0 : f i₀ = 1) (hf1 : ∀ i, i ≠ i₀ → f i = -1 / (m : ℝ)) :
    ∑ χ, (f χ) ^ (2 * j + 2) = 1 + (m : ℝ) * (-1 / (m : ℝ)) ^ (2 * j + 2) := by
  have hcard : (Fintype.card ι : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  have hpt : ∀ χ : ι, (f χ) ^ (2 * j + 2)
      = if χ = i₀ then (1 : ℝ) else (-1 / (m : ℝ)) ^ (2 * j + 2) := by
    intro χ; by_cases h : χ = i₀
    · rw [if_pos h, h, hf0, one_pow]
    · rw [if_neg h, hf1 χ h]
  rw [Finset.sum_congr rfl (fun χ _ => hpt χ), sum_ite_const i₀ 1 _, hcard]
  ring

/-- **One-defect fixed point (§27).** For any moment order `j` and any nontrivial shift `σ`, the
    contraction `Σ_χ f(χ)^{2j+1} f(σχ)` equals `(−1/m)` times the even moment — the parity
    eigenvalue `−1/(p−2)` is reproduced at every order.  Higher moments alone do not break the wall. -/
theorem one_defect_fixed_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) (j : ℕ)
    (f : ι → ℝ) (hf0 : f i₀ = 1) (hf1 : ∀ i, i ≠ i₀ → f i = -1 / (m : ℝ))
    (σ : Equiv.Perm ι) (hσ : σ i₀ ≠ i₀) :
    ∑ χ, (f χ) ^ (2 * j + 1) * f (σ χ) = (-1 / (m : ℝ)) * ∑ χ, (f χ) ^ (2 * j + 2) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcard : (Fintype.card ι : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  set v : ℝ := -1 / (m : ℝ) with hv
  set w : ℝ := v ^ (2 * j + 1) with hw
  have hi₀ne : i₀ ≠ σ⁻¹ i₀ := by
    intro h
    apply hσ
    have h2 : σ (σ⁻¹ i₀) = i₀ := by simp
    rw [← h] at h2
    exact h2
  -- pointwise forms
  have hBodd : ∀ χ : ι, (f χ) ^ (2 * j + 1) = if χ = i₀ then (1 : ℝ) else w := by
    intro χ; by_cases h : χ = i₀
    · rw [if_pos h, h, hf0, one_pow]
    · rw [if_neg h, hf1 χ h, hw]
  have hBsig : ∀ χ : ι, f (σ χ) = if χ = σ⁻¹ i₀ then (1 : ℝ) else v := by
    intro χ; by_cases h : χ = σ⁻¹ i₀
    · rw [if_pos h, h, show σ (σ⁻¹ i₀) = i₀ from by simp, hf0]
    · rw [if_neg h]; apply hf1; intro hc; apply h; rw [← hc]; simp
  have hdecomp : ∀ χ : ι, (f χ) ^ (2 * j + 1) * f (σ χ)
      = w * v + (1 - w) * v * (if χ = i₀ then (1 : ℝ) else 0)
          + w * (1 - v) * (if χ = σ⁻¹ i₀ then (1 : ℝ) else 0) := by
    intro χ
    rw [hBodd, hBsig]
    by_cases hA : χ = i₀
    · subst hA
      rw [if_pos rfl, if_neg hi₀ne, if_pos rfl, if_neg hi₀ne]; ring
    · by_cases hB : χ = σ⁻¹ i₀
      · subst hB
        rw [if_neg hA, if_pos rfl, if_neg hA, if_pos rfl]; ring
      · rw [if_neg hA, if_neg hB, if_neg hA, if_neg hB]; ring
  have hB : ∑ χ, (f χ) ^ (2 * j + 1) * f (σ χ)
      = w * v * (Fintype.card ι : ℝ) + (1 - w) * v + w * (1 - v) := by
    rw [Finset.sum_congr rfl (fun χ _ => hdecomp χ), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum,
      sum_indicator_eq_one i₀, sum_indicator_eq_one (σ⁻¹ i₀)]
    ring
  have hA : ∑ χ, (f χ) ^ (2 * j + 2) = 1 + (m : ℝ) * v ^ (2 * j + 2) := by
    have := A_moment i₀ m hm j f hf0 hf1
    rw [← hv] at this
    exact this
  have hvw : v ^ (2 * j + 2) = w * v := by rw [hw, ← pow_succ]
  rw [hB, hA, hcard, hvw, hv]
  field_simp
  ring

end TypeII
end Geometric
end EuclidsPath
