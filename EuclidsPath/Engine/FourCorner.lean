/-
  Symmetry transition: four-corner ⟹ N₃₃ < N₀₀ (algebra).
  Prose: prose/19_FourCorner.md (after green Lean).

  Context (intuition "it's all about symmetry"): in the CRT model the four-corner inequality
      N₀₀·N₃₃ ≤ N₀₃·N₃₀
  is proved via Maclaurin's inequality on elementary symmetric polynomials
  (R_CRT = 20·e₆/e₃² ≤ 20·C(s,6)/C(s,3)² < 1). This is a purely SYMMETRY fact.
  Together with side-corner `N₀₃·N₃₀ ≤ N₀₀²` it yields `N₃₃ ≤ N₀₀` (strict — `N₃₃ < N₀₀`, i.e. B₅>0).

  What is formalised here is the ALGEBRA of the transition (elementary). The two inequalities for REAL counts
  remain open (model→reality — the locus of the parity problem; see prose/19). ± symmetry
  of the sides gives `N₀₃ = N₃₀`, simplifying side-corner to `N₀₃ ≤ N₀₀`.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/--
  **Four-corner transition (non-strict).** If `N₀₀ > 0`, four-corner `N₀₀·N₃₃ ≤ N₀₃·N₃₀`
  and side-corner `N₀₃·N₃₀ ≤ N₀₀²`, then `N₃₃ ≤ N₀₀`.
-/
theorem N33_le_N00_of_four_corner {N00 N03 N30 N33 : ℕ} (hpos : 0 < N00)
    (hfc : N00 * N33 ≤ N03 * N30) (hsc : N03 * N30 ≤ N00 * N00) : N33 ≤ N00 := by
  have h : N00 * N33 ≤ N00 * N00 := le_trans hfc hsc
  exact Nat.le_of_mul_le_mul_left h hpos

/--
  **Four-corner transition (strict) ⟹ B₅ > 0.** If `N₀₀ > 0`, strict four-corner
  `N₀₀·N₃₃ < N₀₃·N₃₀` and side-corner `N₀₃·N₃₀ ≤ N₀₀²`, then `N₃₃ < N₀₀`.
-/
theorem N33_lt_N00_of_four_corner {N00 N03 N30 N33 : ℕ} (_hpos : 0 < N00)
    (hfc : N00 * N33 < N03 * N30) (hsc : N03 * N30 ≤ N00 * N00) : N33 < N00 := by
  have h : N00 * N33 < N00 * N00 := lt_of_lt_of_le hfc hsc
  exact lt_of_mul_lt_mul_left h (Nat.zero_le N00)

/--
  **± symmetry simplifies side-corner.** When `N₀₃ = N₃₀` it suffices to have `N₀₃ ≤ N₀₀` to obtain
  side-corner `N₀₃·N₃₀ ≤ N₀₀²`.
-/
theorem side_corner_of_le {N00 N03 N30 : ℕ} (hsymm : N03 = N30) (h : N03 ≤ N00) :
    N03 * N30 ≤ N00 * N00 := by
  subst hsymm; exact Nat.mul_le_mul h h

end EuclidsPath
