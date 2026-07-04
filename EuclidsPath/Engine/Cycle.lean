/-
  Acyclicity (rigidity of repetitions). Prose: prose/21_Cycle.md (after green Lean).
  Source: catalogue §31/§58 (fuel-law / factor-repeat rigidity): a large factor on a linear
  train cannot repeat more often than the step allows. This forbids "infinite repetition" and,
  together with EPMI, gives acyclicity of the descent forest.
  Elementary (divisibility + coprimality).
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

/--
  **Factor-repeat rigidity.** If `ℓ` divides `N₀ + q·n₁` and `N₀ + q·n₂` on a linear train, and
  `(ℓ, q) = 1`, then `ℓ ∣ (n₂ − n₁)`. A large divisor "anchors" the repetition to the step — repetitions are few.
-/
theorem factor_repeat_rigidity {ℓ q N0 n1 n2 : ℤ}
    (h1 : ℓ ∣ N0 + q * n1) (h2 : ℓ ∣ N0 + q * n2) (hcop : IsCoprime ℓ q) :
    ℓ ∣ (n2 - n1) := by
  have hd : ℓ ∣ q * (n2 - n1) := by
    have hsub := dvd_sub h2 h1
    have e : (N0 + q * n2) - (N0 + q * n1) = q * (n2 - n1) := by ring
    rwa [e] at hsub
  exact hcop.dvd_of_dvd_mul_left hd

/--
  **Fuel-law (transfer of the two between sides).** If `p ∣ B_α` and `p ∣ R_β` on opposite
  sides of the star rectangle (`a·B_α = …`, see det-form), then `p ∣ 2 + a·q·(β − α)`.
  Here — pure divisibility form: from `p ∣ aα + c` and `p ∣ aβ + c − 2` it follows that `p ∣ a(β−α) − 2`.
-/
theorem cross_side_fuel {p a c α β : ℤ}
    (h1 : p ∣ a * α + c) (h2 : p ∣ a * β + c - 2) :
    p ∣ (a * (β - α) - 2) := by
  have hsub := dvd_sub h2 h1
  have e : (a * β + c - 2) - (a * α + c) = a * (β - α) - 2 := by ring
  rwa [e] at hsub

end EuclidsPath.Engine
