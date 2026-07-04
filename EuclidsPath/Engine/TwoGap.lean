/-
  The "two" axis: exact identities that carry the +2 gap (twin-gap) along the descent.
  Prose: prose/17_TwoGap.md (written after the green Lean).
  Source of laws: catalogue from the source files (det law abv−qrs=−2; collapse u₂r₁−u₁r₂=2K;
  euclidean descent qΔ−vΞ=2; small collapse B₂Q₁−B₁Q₂=12h; abstract form Cb−Dr=−2).

  All statements are ELEMENTARY algebra (no analysis / distribution / sieve). mathlib is used
  only for basic ring arithmetic (`ring`, `linear_combination`, `omega`, `mul_left_cancel₀`).
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

/-- **Determinant law rank-(3,3).** From `6m−1=abv`, `6m+1=qrs` (with `m≥1`) it follows that `qrs = abv + 2`. -/
theorem det_law_rank33 {m a b v q r s : ℕ} (hm : 1 ≤ m)
    (h1 : 6 * m - 1 = a * b * v) (h2 : 6 * m + 1 = q * r * s) :
    q * r * s = a * b * v + 2 := by
  omega

/-- **Abstract form** `Cb − Dr = −2` (over ℤ): if `Cb = 6m−1` and `Dr = 6m+1`, then `Cb − Dr = −2`. -/
theorem det_law_CD {m C D b r : ℤ} (h1 : C * b = 6 * m - 1) (h2 : D * r = 6 * m + 1) :
    C * b - D * r = -2 := by
  linear_combination h1 - h2

/--
  **Determinant collapse** `u₂r₁ − u₁r₂ = 2K`.
  If two points of the ray satisfy `uᵢv + 2 = rᵢs` and the step is `u₂ − u₁ = sK`, then (with `s ≠ 0`)
  `u₂r₁ − u₁r₂ = 2K`. This is the "carry of the two" in ray coordinates.
-/
theorem det_collapse {u1 u2 r1 r2 v s K : ℤ}
    (h1 : u1 * v + 2 = r1 * s) (h2 : u2 * v + 2 = r2 * s)
    (hK : u2 - u1 = s * K) (hs : s ≠ 0) : u2 * r1 - u1 * r2 = 2 * K := by
  have a1 : r1 * s = u1 * v + 2 := h1.symm
  have a2 : r2 * s = u2 * v + 2 := h2.symm
  have key : s * (u2 * r1 - u1 * r2) = s * (2 * K) := by
    have step : s * (u2 * r1 - u1 * r2) = u2 * (r1 * s) - u1 * (r2 * s) := by ring
    rw [step, a1, a2]
    linear_combination 2 * hK
  exact mul_left_cancel₀ hs key

/--
  **Exact Euclidean descent identity** `qΔ − vΞ = 2`.
  From the rank-one equation `abv + 2 = qP` with decompositions `P = v² + Δ`, `ab = qv + Ξ`.
  This is the diagonal kernel of the self-similar descent.
-/
theorem euclid_descent_identity {a b v q P Δ Ξ : ℤ}
    (h1 : a * b * v + 2 = q * P) (h2 : P = v ^ 2 + Δ) (h3 : a * b = q * v + Ξ) :
    q * Δ - v * Ξ = 2 := by
  linear_combination -h1 - q * h2 + v * h3

/--
  **Small determinant collapse for a repeated atom** `B₂Q₁ − B₁Q₂ = 12h`.
  From the bridge equation `a·Bᵢ = qs·Qᵢ − 2` and the shift `B₂ − B₁ = 6·qs·h` (with `a ≠ 0`, `qs ≠ 0`).
-/
theorem small_det_collapse {a q s B1 B2 Q1 Q2 h : ℤ}
    (e1 : a * B1 = q * s * Q1 - 2) (e2 : a * B2 = q * s * Q2 - 2)
    (hsh : B2 - B1 = 6 * (q * s) * h) (ha : a ≠ 0) (hqs : q * s ≠ 0) :
    B2 * Q1 - B1 * Q2 = 12 * h := by
  have hQ : Q2 - Q1 = 6 * a * h := by
    have hmul : q * s * (Q2 - Q1) = q * s * (6 * a * h) := by
      linear_combination e1 - e2 + a * hsh
    exact mul_left_cancel₀ hqs hmul
  have key : a * (B2 * Q1 - B1 * Q2) = a * (12 * h) := by
    linear_combination Q1 * e2 - Q2 * e1 + 2 * hQ
  exact mul_left_cancel₀ ha key

end EuclidsPath.Engine
