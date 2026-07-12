/-
  GeometricSegreDefect — the connected-defect (Segre) upgrade of the four-corner law.

  ORIGIN (user's geometric program, §XII / §XVII / §XXIV of
  `geometric_twin_prime_program_full.md`): the four-state layer PP / PS / SP / SS of a
  twin center carries a two-variable state polynomial whose ONLY connected content is a
  single determinant Δ = TQ − UV.  Projectively this is a Segre quadric, and the
  connected defect is an exact energy (a double sum of squared pair-differences), a
  cross-ratio, and a Hilbert projective distance.

  RELATION TO THE REPO.  `EuclidsPath.N33_le_N00_of_four_corner` (Engine/FourCorner) and
  `EuclidsPath.real_four_corner_decomp` (Engine/RealFourCorner) record the four-corner
  INEQUALITY and the exact real = model + remainder split.  This module adds the
  CONNECTED (Segre) refinement those files do not carry: the exact decomposition
  A·P = L·R + Δ·(1−x)(1−y), the covariance identity Cov = Δ/A², the exterior-algebra
  energy form of Δ, and the projective distance from independence.  It is pure ring /
  finite-sum algebra over an arbitrary commutative field (instantiated at ℝ for the
  metric statements).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `segre_decomposition` — A·P(x,y) = L(x)·R(y) + Δ·(1−x)(1−y) (the Segre split);
    * `cov_eq_delta_div_Asq` — the four-state covariance equals Δ/A² (A ≠ 0);
    * `exterior_algebra_identity` — AS − M₋M₊ = ½ Σ_{k,ℓ} w_k w_ℓ (x_k−x_ℓ)(y_k−y_ℓ)
      (the connected defect is an exact connected energy — purely-left or purely-right
      deformations are tangent to the Segre quadric);
    * `crossRatio` / `hilbertDist` and `hilbertDist_eq_zero_iff_segre` — the projective
      separation from rank one vanishes exactly on the independence locus AS = M₋M₊.

  DISCLOSURE.  This is the four-corner gap in CONNECTED/energy form — the same single
  wall, seen projectively.  Nothing here feeds the wall: Δ is the exact model defect,
  and the open input remains remainder control (`real_four_corner_of_remainder`).
  twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace Segre

/-! ## The four-state state polynomial and its Segre decomposition (§17) -/

variable {R : Type*} [CommRing R]

/-- The four-state state polynomial `P(x,y) = T + U·y + V·x + Q·x·y`
    (counts `T=#PP, U=#PS, V=#SP, Q=#SS`). -/
def statePoly (T U V Q x y : R) : R := T + U * y + V * x + Q * x * y

/-- The total mass `A = T + U + V + Q`. -/
def Adet (T U V Q : R) : R := T + U + V + Q

/-- Left marginal factor `L(x) = (T+U) + (V+Q)·x`. -/
def Lfac (T U V Q x : R) : R := (T + U) + (V + Q) * x

/-- Right marginal factor `R(y) = (T+V) + (U+Q)·y`. -/
def Rfac (T U V Q y : R) : R := (T + V) + (U + Q) * y

/-- The connected defect (Segre determinant) `Δ = TQ − UV`. -/
def segreDelta (T U V Q : R) : R := T * Q - U * V

/-- **Segre decomposition (§17).** `A·P(x,y) = L(x)·R(y) + Δ·(1−x)(1−y)`: the state
    polynomial splits into a rank-one product part and the connected determinant. -/
theorem segre_decomposition (T U V Q x y : R) :
    Adet T U V Q * statePoly T U V Q x y
      = Lfac T U V Q x * Rfac T U V Q y
        + segreDelta T U V Q * (1 - x) * (1 - y) := by
  simp only [Adet, statePoly, Lfac, Rfac, segreDelta]; ring

/-! ## The covariance identity and the exterior-algebra energy (§17, §33) -/

/-- **Covariance identity (§17).** For a nonzero total mass `A`, the covariance of the
    two side-indicators equals `Δ/A²`: `Q/A − (V+Q)/A · (U+Q)/A = (TQ−UV)/A²`. -/
theorem cov_eq_delta_div_Asq {F : Type*} [Field F] (T U V Q : F)
    (hA : T + U + V + Q ≠ 0) :
    Q / (T + U + V + Q)
        - ((V + Q) / (T + U + V + Q)) * ((U + Q) / (T + U + V + Q))
      = (T * Q - U * V) / (T + U + V + Q) ^ 2 := by
  field_simp
  ring

/-- **Exterior-algebra identity (§33).** The connected defect `AS − M₋M₊`, doubled, is an
    exact connected energy — the sum over ordered pairs of `w_k w_ℓ (x_k−x_ℓ)(y_k−y_ℓ)`
    (equivalently `AS − M₋M₊ = ½ Σ_{k,ℓ} …`). Consequently only JOINT variation of the two
    sides sees the determinant; purely-left or purely-right deformations are tangent to the
    Segre quadric. Stated in doubled form to hold over an arbitrary commutative ring. -/
theorem exterior_algebra_identity {ι : Type*} (s : Finset ι) (w x y : ι → R) :
    2 * ((∑ k ∈ s, w k) * (∑ k ∈ s, w k * x k * y k)
          - (∑ k ∈ s, w k * x k) * (∑ k ∈ s, w k * y k))
      = ∑ k ∈ s, ∑ l ∈ s, w k * w l * (x k - x l) * (y k - y l) := by
  have hexp : ∀ k l : ι,
      w k * w l * (x k - x l) * (y k - y l)
        = (w k * x k * y k) * w l - (w k * x k) * (w l * y l)
          - (w k * y k) * (w l * x l) + w k * (w l * x l * y l) := by
    intro k l; ring
  simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul_sum]
  ring

/-! ## Projective separation from independence (§34–35) -/

/-- The cross-ratio `R = AS / (M₋M₊)` (invariant under independent row/column
    rescalings). -/
noncomputable def crossRatio (A S Mm Mp : ℝ) : ℝ := (A * S) / (Mm * Mp)

/-- The Hilbert projective distance from rank one, `d_H = |log R|`. -/
noncomputable def hilbertDist (A S Mm Mp : ℝ) : ℝ := |Real.log (crossRatio A S Mm Mp)|

/-- **Projective independence locus (§35).** With positive column norms, the projective
    distance from rank one vanishes exactly on the Segre independence locus
    `AS = M₋M₊`. -/
theorem hilbertDist_eq_zero_iff_segre {A S Mm Mp : ℝ}
    (hAS : 0 < A * S) (hM : 0 < Mm * Mp) :
    hilbertDist A S Mm Mp = 0 ↔ A * S = Mm * Mp := by
  have hMne : Mm * Mp ≠ 0 := ne_of_gt hM
  have hr : 0 < crossRatio A S Mm Mp := div_pos hAS hM
  constructor
  · intro h
    rw [hilbertDist, abs_eq_zero] at h
    have hcr : crossRatio A S Mm Mp = 1 := by
      have hx := Real.exp_log hr
      rw [h, Real.exp_zero] at hx
      exact hx.symm
    rw [crossRatio, div_eq_one_iff_eq hMne] at hcr
    exact hcr
  · intro h
    rw [hilbertDist, crossRatio, h, div_self hMne, Real.log_one, abs_zero]

end Segre
end Geometric
end EuclidsPath
