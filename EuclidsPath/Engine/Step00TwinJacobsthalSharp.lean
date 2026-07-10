import EuclidsPath.Engine.Step00WitnessChainKernel

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The sharp (two-regime) wall — a SECOND named hypothesis, never a decree

The exact gap data (ledger L30, all ten scales machine- or solver-exact) shows a genuine
two-regime split: `G(A) ≤ ⌊A²/14⌋` holds at EVERY exactly known scale `A ≥ 11`
(11: 7≤8, 13: 11≤12, 17: 18≤20, **19: 25 = ⌊361/14⌋ TIGHT**, 23: 34≤37, 29: 43≤60,
31: 58≤68, 37: 88≤97) and FAILS at both small scales (`⌊25/14⌋ = 1 < 2 = G(5)`,
`⌊49/14⌋ = 3 < 5 = G(7)`) — the regime boundary sits exactly at 11.

Honest status: `TwinJacobsthalBoundSharp` is a HYPOTHESIS strictly stronger per-scale than
the load-bearing wall `TwinJacobsthalBound` (which KEEPS the constant 1/7 — the escalation
only ever needs `A² > 42·M0`, so sharper constants buy a factor ~2 in `A`, nothing
qualitative).  The Sharp wall's value is falsifiability: it is TIGHT at `A = 19`, so the
very next solver scales (41, 43) can refute it by a couple of units — unlike the 1/7 wall
whose corridor sits at ratio ≤ 0.5 for `A ≥ 11`.  Universal Sharp = EXACT-CANDIDATE in the
ledger; the per-scale INSTANCES below are theorems.  Instances at `A ≥ 17` require the true
gaps (`CleanGapBound 17 18`, `19 25`, …) — they land with the phase-cover kernel
certificates, NOT from the witness chains (whose bounds 41/51 are chain steps; see the
honesty corrections in `Step00ExtremalGapGeometry`/`Step00WitnessChainKernel`).
-/

namespace EuclidsPath
namespace TwinJacobsthalSharp

open EuclidsPath.TwinJacobsthalWall
open EuclidsPath.Residuals

/-- **The sharp wall (named hypothesis, regime `A ≥ 11`)**: the gap bound at window `⌊A²/14⌋`. -/
def TwinJacobsthalBoundSharp : Prop :=
  ∀ A : ℕ, A.Prime → 11 ≤ A → CleanGapBound A (A ^ 2 / 14)

/-- The weakest sufficient form: cofinally many sharp scales. -/
def TwinJacobsthalBoundSharpCofinal : Prop :=
  ∀ A0 : ℕ, ∃ A : ℕ, A0 ≤ A ∧ A.Prime ∧ CleanGapBound A (A ^ 2 / 14)

/-- Sharp cofinal scales serve the ordinary wall's cofinal form (`⌊A²/14⌋ ≤ ⌊A²/7⌋`). -/
theorem twinJacobsthalCofinal_of_sharpCofinal (H : TwinJacobsthalBoundSharpCofinal) :
    TwinJacobsthalBoundCofinal := by
  intro A0
  obtain ⟨A, hge, hp, hbound⟩ := H A0
  exact ⟨A, hge, hp, cleanGapBound_mono hbound (Nat.div_le_div_left (by norm_num) (by norm_num))⟩

/-- The full sharp wall implies the full ordinary wall (small scales 5, 7 from their own
    kernel instances; `A ≥ 11` by widening the window). -/
theorem twinJacobsthal_of_sharp (H : TwinJacobsthalBoundSharp) : TwinJacobsthalBound := by
  intro A hp h5
  rcases Nat.lt_or_ge A 11 with h11 | h11
  · interval_cases A
    · exact twinJacobsthal_at_5
    · exact absurd hp (by norm_num)
    · exact twinJacobsthal_at_7
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  · exact cleanGapBound_mono (H A hp h11) (Nat.div_le_div_left (by norm_num) (by norm_num))

/-- The sharp wall reaches the goal through the existing escalation. -/
theorem twinLowersInfinite_of_sharpCofinal (H : TwinJacobsthalBoundSharpCofinal) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_twinJacobsthalCofinal (twinJacobsthalCofinal_of_sharpCofinal H)

/-- Sharp instance at 11: `⌊121/14⌋ = 8 ≥ 7 = G(11)`. -/
theorem twinJacobsthalSharp_at_11 : CleanGapBound 11 (11 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_11 (by norm_num)

/-- Sharp instance at 13: `⌊169/14⌋ = 12 ≥ 11 = G(13)`. -/
theorem twinJacobsthalSharp_at_13 : CleanGapBound 13 (13 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_13 (by norm_num)

/-! ### The margin ledger (exact integer checks) and the regime breakers -/

example : 14 * 7 ≤ 11 ^ 2 := by norm_num
example : 14 * 11 ≤ 13 ^ 2 := by norm_num
example : 14 * 18 ≤ 17 ^ 2 := by norm_num
example : 14 * 25 ≤ 19 ^ 2 ∧ 19 ^ 2 < 14 * 26 := by norm_num  -- TIGHT at 19
example : 14 * 34 ≤ 23 ^ 2 := by norm_num
example : 14 * 43 ≤ 29 ^ 2 := by norm_num
example : 14 * 58 ≤ 31 ^ 2 := by norm_num
example : 14 * 88 ≤ 37 ^ 2 := by norm_num
/-- Regime breakers: the sharp constant FAILS at the small scales (why `11 ≤ A`). -/
example : ¬ (14 * 2 ≤ 5 ^ 2) := by norm_num   -- G(5) = 2
example : ¬ (14 * 5 ≤ 7 ^ 2) := by norm_num   -- G(7) = 5

end TwinJacobsthalSharp
end EuclidsPath
