/-
  Separating scale: ¬ProductHall on the legal carrier layer. Formalisation of the author's file.
  Source: step00_producthall_bridge_separating_scale_ru_2026-07-01.md. Prose: prose/30_SeparatingScale.md.

  Idea (bypasses the trilemma UniqueLegalLift): if the primorial `P_A > 6X_A+1`, then on the legal-domain
  `a < P_A`, so `a ↦ a mod P_A` is INJECTIVE there — the coarse passport is automatically fine. Then
  two legal active factors with `a₁ ≡ a₂ (mod P_A)` are EQUAL, contradicting `a₁ ≠ a₂` in ProductHall.
  Hence `¬ProductHall` on the legal layer. This is PURE ARITHMETIC — no EPMI, no payment, no steering.

  Here — complete arithmetic (WITHOUT sorry). Critical compatibility check with pigeonhole — separate.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.SeparatingScale

/--
  **Separating congruence (Lemma 3.1) — FULLY PROVEN.** If `0 < a₁`, `0 < a₂`, both `< P`,
  and `a₁ ≡ a₂ (mod P)`, then `a₁ = a₂`. (The difference is a multiple of `P`, but `|a₁−a₂| < P` ⟹ the difference is 0.) -/
theorem eq_of_modEq_of_lt {P a₁ a₂ : ℕ} (h1 : a₁ < P) (h2 : a₂ < P)
    (hcong : a₁ ≡ a₂ [MOD P]) : a₁ = a₂ := by
  -- a₁ % P = a₁ and a₂ % P = a₂ (since < P); ModEq ⟹ equal
  rwa [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hcong

/--
  **Legal lift bound (BoundedLegalLift §2) — proven.** If `a ∣ N` (`a > 0`), `N ≤ 6·X_A+1`,
  and separating scale `6·X_A+1 < P_A`, then `a < P_A`. (`a ≤ N ≤ 6X_A+1 < P_A`.) -/
theorem legal_lift_lt_primorial {a N X_A P_A : ℕ}
    (hsep : 6 * X_A + 1 < P_A) (hN : N ≤ 6 * X_A + 1) (hdvd : a ∣ N) (_hpos : 0 < a) (hNpos : 0 < N) :
    a < P_A := by
  have haN : a ≤ N := Nat.le_of_dvd hNpos hdvd
  omega

/-- ProductHall on the legal layer (abstractly): two DISTINCT legal active factors `a₁ ≠ a₂` over one
    base, congruent modulo `P_A`, both bounded by the carrier (`aᵢ ∣ Nᵢ ≤ 6X_A+1`, `aᵢ > 0`). -/
structure LegalProductHall (X_A P_A : ℕ) where
  a₁ : ℕ
  a₂ : ℕ
  N₁ : ℕ
  N₂ : ℕ
  hne : a₁ ≠ a₂
  hcong : a₁ ≡ a₂ [MOD P_A]
  hdvd₁ : a₁ ∣ N₁
  hdvd₂ : a₂ ∣ N₂
  hpos₁ : 0 < a₁
  hpos₂ : 0 < a₂
  hN₁ : 0 < N₁ ∧ N₁ ≤ 6 * X_A + 1
  hN₂ : 0 < N₂ ∧ N₂ ≤ 6 * X_A + 1

/--
  **NoProductHall (Theorem 5.1) — FULLY PROVEN.** Under separating scale `P_A > 6X_A+1`
  a legal ProductHall is IMPOSSIBLE: both factors `< P_A`, congruent ⟹ equal ⟹ contradiction with `a₁ ≠ a₂`.
  This closes the `ProductHall` node on the legal layer by pure arithmetic. -/
theorem no_productHall {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A)
    (PH : LegalProductHall X_A P_A) : False := by
  have h1 : PH.a₁ < P_A :=
    legal_lift_lt_primorial hsep PH.hN₁.2 PH.hdvd₁ PH.hpos₁ PH.hN₁.1
  have h2 : PH.a₂ < P_A :=
    legal_lift_lt_primorial hsep PH.hN₂.2 PH.hdvd₂ PH.hpos₂ PH.hN₂.1
  exact PH.hne (eq_of_modEq_of_lt h1 h2 PH.hcong)

/--
  **ProductHallBridge via vacuity (§7).** `ProductHall ⟹ anything` (`HeightEngine`/`Engine`)
  by `False.elim`, since a legal ProductHall is impossible under the separating scale. -/
theorem productHall_bridge {X_A P_A : ℕ} {Engine : Prop} (hsep : 6 * X_A + 1 < P_A)
    (PH : LegalProductHall X_A P_A) : Engine :=
  False.elim (no_productHall hsep PH)

/-! ### Where the difficulty moved (honestly): the trichotomy narrows, but new nodes are open -/

/--
  **Trichotomy after ¬ProductHall (§8).** If `¬ProductHall` (proven above), then the energy-defect
  trichotomy `LowerRankCollision ∨ ProductHall` reduces to the SINGLE branch `LowerRankCollision`.
  Here — a logical reduction: `(L ∨ PH) ∧ ¬PH ⟹ L`. (`energy_defect_trichotomy` itself is an open node.) -/
theorem trichotomy_collapses {L PH : Prop} (htri : L ∨ PH) (hno : ¬ PH) : L :=
  htri.resolve_right hno

/--
  **Bounded rank descent (§8) — skeleton.** If every energy-defect at rank `r > 1` yields
  `LowerRankCollision` (rank `r−1`), and rank-1 closes (SNOL), then the descent `r → … → 1` is finite.
  Here — a well-founded skeleton for `r ≤ 4`; `lower_step` and `rank1_closes` are OPEN nodes. -/
theorem rank_descent_terminates {Engine : Prop}
    (lower_step : ∀ r, 1 < r → r ≤ 4 → (∃ r', r' = r - 1) )  -- rank reduction (open: the real one)
    (rank1_closes : Engine)                                   -- rank-1 ⟹ Engine (SNOL, open here)
    : Engine :=
  rank1_closes

end EuclidsPath.SeparatingScale
