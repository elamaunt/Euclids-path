/-
  Self-similarity / squeeze. Prose: prose/20_Squeeze.md (after the green Lean).
  Source: catalogue §23 (cubic squeeze of a repeated atom): h(1+6h) < A/12 ⟹ h < √(A/72).
  We take the honest integer form (without √): from 12(h+6h²) < A it follows that 72h² < A.
  Elementary (linear arithmetic over the atom h²).
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

/-- **Cubic squeeze.** `12·(h + 6h²) < A ⟹ 72h² < A` (equivalent to `h < √(A/72)`). -/
theorem cubic_squeeze {A h : ℕ} (hsq : 12 * (h + 6 * h ^ 2) < A) : 72 * h ^ 2 < A := by
  omega

/-- Corollary: a repeated atom is extremely short — `h² < A` (and therefore `h < A`). -/
theorem cubic_squeeze_sq_lt {A h : ℕ} (hsq : 12 * (h + 6 * h ^ 2) < A) : h ^ 2 < A := by
  have := cubic_squeeze hsq; omega

end EuclidsPath.Engine
