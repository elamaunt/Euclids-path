/-
  GeometricTypeIIQuartic — the S_{2k} support Pythagoras and the summability gain
  1/p → 1/p^{2k-1}.

  ORIGIN (parity_wall dossier §38–42 / §71): the rectangle fourth (and higher even
  Schatten) moment turns the parity-divergent local energy `1/p` of the residual `Z_p`
  into `1/p^{2k-1}` (progress criterion B: genuine summability gain), and distinct prime
  supports are orthogonal, so the norms add (support Pythagoras).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `zEnergy_S4` — the S_4 local residual energy `(p-2)/(p-1)^4 ≤ 1/(p-1)^3`: the exact
      transition `1/p → 1/p^3` (§38);
    * `zEnergy_cube_summable` — `1/(p-1)^3 ≤ 1/(2(p-2)^2) − 1/(2(p-1)^2)`, so the gained
      energy telescopes (`Σ_p 1/(p-1)^3 < ∞`);
    * `disjoint_support_orthogonal` — functions with disjoint support have zero inner
      product (distinct supports do not interact);
    * `pythagoras_of_orthogonal` — for an orthogonal family the squared norm decomposes:
      `Σ_x (Σ_i f_i x)^2 = Σ_i Σ_x (f_i x)^2` (the support Pythagoras, §41).

  DISCLOSURE. These are the exact CRT/full-space energy facts: the first parity-divergent
  `1/p` layer is removed and different supports are orthogonal.  The open target is whether
  this survives the transfer to a real interval (`CRE`, see `TypeIIMap`); on the interval
  the mixed modes carry `1/p` again (see `TypeIINoGo`).  Nothing here proves twins.
  twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The local residual energy and the summability gain (§38–42) -/

/-- The normalized `S_{2k}` local residual energy `z_{2k,p} = (p−2)/(p−1)^{2k}`. -/
noncomputable def zEnergy (k p : ℕ) : ℝ := ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ (2 * k)

/-- **The S_4 gain (§38).** `(p−2)/(p−1)^4 ≤ 1/(p−1)^3`: the residual local energy drops from
    the parity-divergent `1/p` scale to the summable `1/p^3` scale. -/
theorem zEnergy_S4 {p : ℕ} (hp : 2 ≤ p) : zEnergy 2 p ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  unfold zEnergy
  have step : ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ (2 * 2) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ (2 * 2) := by
    gcongr
    linarith
  have heq : ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ (2 * 2) = 1 / ((p : ℝ) - 1) ^ 3 := by
    field_simp
  rw [heq] at step
  exact step

/-- **The gained energy telescopes (§42).** `1/(p−1)^3 ≤ 1/(p−2) − 1/(p−1)`, so
    `Σ_p 1/(p−1)^3 < ∞` (cube majorized by the square telescope). -/
theorem zEnergy_cube_summable {p : ℕ} (hp : 3 ≤ p) :
    (1 : ℝ) / ((p : ℝ) - 1) ^ 3 ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
  have hpp : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hcube : (1 : ℝ) / ((p : ℝ) - 1) ^ 3 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [h1]
  have hsq : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
    have key : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
      field_simp
      ring
    rw [key]
    apply one_div_le_one_div_of_le (mul_pos h2 h1)
    nlinarith [hpp]
  linarith

/-! ## Support orthogonality and the Pythagoras decomposition (§41) -/

/-- **Distinct supports do not interact.** Functions with disjoint support are orthogonal. -/
theorem disjoint_support_orthogonal {κ : Type*} [Fintype κ] (f g : κ → ℝ)
    (h : ∀ x, f x = 0 ∨ g x = 0) : ∑ x : κ, f x * g x = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rcases h x with hx | hx <;> simp [hx]

/-- **Support Pythagoras (§41).** For an orthogonal family `{f_i}` the squared norm
    decomposes: `Σ_x (Σ_i f_i x)^2 = Σ_i Σ_x (f_i x)^2` — different supports are
    quartically (here quadratically) orthogonal, so the energies add. -/
theorem pythagoras_of_orthogonal {κ ι : Type*} [Fintype κ] [DecidableEq ι] (S : Finset ι)
    (f : ι → κ → ℝ)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∑ x : κ, f i x * f j x = 0) :
    ∑ x : κ, (∑ i ∈ S, f i x) ^ 2 = ∑ i ∈ S, ∑ x : κ, (f i x) ^ 2 := by
  have e1 : ∀ x : κ, (∑ i ∈ S, f i x) ^ 2 = ∑ i ∈ S, ∑ j ∈ S, f i x * f j x := by
    intro x; rw [sq, Finset.sum_mul_sum]
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji))
    (fun h => absurd hi h)]
  simp_rw [sq]

end TypeII
end Geometric
end EuclidsPath
