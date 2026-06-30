/-
  Separating scale: ¬ProductHall на legal carrier layer. Формализация авторского файла.
  Источник: step00_producthall_bridge_separating_scale_ru_2026-07-01.md. Проза: prose/30_SeparatingScale.md.

  Идея (обходит трилемму UniqueLegalLift): если primorial `P_A > 6X_A+1`, то на legal-domain
  `a < P_A`, значит `a ↦ a mod P_A` ИНЪЕКТИВНО там — coarse-паспорт автоматически fine. Тогда
  два legal active factor с `a₁ ≡ a₂ (mod P_A)` РАВНЫ, что противоречит `a₁ ≠ a₂` в ProductHall.
  Значит `¬ProductHall` на legal layer. Это ЧИСТАЯ АРИФМЕТИКА — не EPMI, не payment, не steering.

  Здесь — полная арифметика (БЕЗ sorry). Критическая проверка совместимости с pigeonhole — отдельно.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.SeparatingScale

/--
  **Separating congruence (Lemma 3.1) — ПОЛНОСТЬЮ доказано.** Если `0 < a₁`, `0 < a₂`, оба `< P`,
  и `a₁ ≡ a₂ (mod P)`, то `a₁ = a₂`. (Разность кратна `P`, но `|a₁−a₂| < P` ⟹ разность 0.) -/
theorem eq_of_modEq_of_lt {P a₁ a₂ : ℕ} (h1 : a₁ < P) (h2 : a₂ < P)
    (hcong : a₁ ≡ a₂ [MOD P]) : a₁ = a₂ := by
  -- a₁ % P = a₁ и a₂ % P = a₂ (т.к. < P); ModEq ⟹ равны
  rwa [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hcong

/--
  **Legal lift bound (BoundedLegalLift §2) — доказано.** Если `a ∣ N` (`a > 0`), `N ≤ 6·X_A+1`,
  и separating scale `6·X_A+1 < P_A`, то `a < P_A`. (`a ≤ N ≤ 6X_A+1 < P_A`.) -/
theorem legal_lift_lt_primorial {a N X_A P_A : ℕ}
    (hsep : 6 * X_A + 1 < P_A) (hN : N ≤ 6 * X_A + 1) (hdvd : a ∣ N) (_hpos : 0 < a) (hNpos : 0 < N) :
    a < P_A := by
  have haN : a ≤ N := Nat.le_of_dvd hNpos hdvd
  omega

/-- ProductHall на legal layer (абстрактно): два РАЗНЫХ legal active factor `a₁ ≠ a₂` над одним
    base, сравнимых по модулю `P_A`, оба ограниченных carrier'ом (`aᵢ ∣ Nᵢ ≤ 6X_A+1`, `aᵢ > 0`). -/
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
  **NoProductHall (Theorem 5.1) — ПОЛНОСТЬЮ доказано.** При separating scale `P_A > 6X_A+1`
  legal ProductHall НЕВОЗМОЖЕН: оба фактора `< P_A`, сравнимы ⟹ равны ⟹ противоречие с `a₁ ≠ a₂`.
  Это закрывает узел `ProductHall` на legal layer чистой арифметикой. -/
theorem no_productHall {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A)
    (PH : LegalProductHall X_A P_A) : False := by
  have h1 : PH.a₁ < P_A :=
    legal_lift_lt_primorial hsep PH.hN₁.2 PH.hdvd₁ PH.hpos₁ PH.hN₁.1
  have h2 : PH.a₂ < P_A :=
    legal_lift_lt_primorial hsep PH.hN₂.2 PH.hdvd₂ PH.hpos₂ PH.hN₂.1
  exact PH.hne (eq_of_modEq_of_lt h1 h2 PH.hcong)

/--
  **ProductHallBridge через пустоту (§7).** `ProductHall ⟹ что угодно` (`HeightEngine`/`Engine`)
  по `False.elim`, т.к. legal ProductHall невозможен при separating scale. -/
theorem productHall_bridge {X_A P_A : ℕ} {Engine : Prop} (hsep : 6 * X_A + 1 < P_A)
    (PH : LegalProductHall X_A P_A) : Engine :=
  False.elim (no_productHall hsep PH)

/-! ### Куда переехала трудность (честно): трихотомия сужается, но новые узлы открыты -/

/--
  **Трихотомия после ¬ProductHall (§8).** Если `¬ProductHall` (доказано выше), то energy-defect
  трихотомия `LowerRankCollision ∨ ProductHall` сводится к ОДНОЙ ветви `LowerRankCollision`.
  Здесь — логическая редукция: `(L ∨ PH) ∧ ¬PH ⟹ L`. (Сам `energy_defect_trichotomy` — открытый узел.) -/
theorem trichotomy_collapses {L PH : Prop} (htri : L ∨ PH) (hno : ¬ PH) : L :=
  htri.resolve_right hno

/--
  **Bounded rank descent (§8) — скелет.** Если каждый energy-defect на ранге `r > 1` даёт
  `LowerRankCollision` (rank `r−1`), а rank-1 закрывается (SNOL), то descent `r → … → 1` конечен.
  Здесь — well-founded скелет на `r ≤ 4`; `lower_step` и `rank1_closes` — ОТКРЫТЫЕ узлы. -/
theorem rank_descent_terminates {Engine : Prop}
    (lower_step : ∀ r, 1 < r → r ≤ 4 → (∃ r', r' = r - 1) )  -- редукция ранга (открыто: реальная)
    (rank1_closes : Engine)                                   -- rank-1 ⟹ Engine (SNOL, открыто здесь)
    : Engine :=
  rank1_closes

end EuclidsPath.SeparatingScale
