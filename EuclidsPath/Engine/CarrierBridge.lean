/-
  Последнее звено: построение CarrierData из бесконечности carrier. Проза: prose/33_CarrierBridge.md.

  ProductCore.product_core_engine_of_carrier берёт carrier-данные:
    бесконечное S стартов + node:ι→RankNode r (InjOn) + AmbientLegal ⟹ Engine.
  Здесь это строится из УЖЕ ДОКАЗАННОГО `Residuals.carrier_nonempty_above` (clean центр выше любого N
  ⟹ carrier бесконечен).

  Доказуемо здесь:
    • carrier бесконечен (из carrier_nonempty_above);
    • distinct centers ⟹ distinct cores (через значение 6m+σ).
  Единственный реальный вход (factorization): каждый legal `6m+σ` раскладывается в `RankNode r`
  (простые факторы >A, фиксированный r после pigeonhole по рангу). Это существование разложения —
  его даёт carrier/сито, не аксиома двигателя. Выделен явно как `FactorizationData`.
-/
import Mathlib
import EuclidsPath.Engine.ProductCore
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.CarrierBridge

open EuclidsPath.ProductCore EuclidsPath.Residuals

/-! ### Carrier бесконечен (из carrier_nonempty_above) -/

/-- Множество clean-центров (ℕ) при заданном `A`. -/
def CleanCenters (A : ℕ) : Set ℕ := {m | CleanZ A (m : ℤ)}

/--
  **Carrier бесконечен — ДОКАЗАНО.** `carrier_nonempty_above` даёт clean-центр выше любого `N`,
  значит `CleanCenters A` не ограничено сверху ⟹ бесконечно. -/
theorem cleanCenters_infinite (A : ℕ) : (CleanCenters A).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨m, hmN, hclean⟩ := carrier_nonempty_above A N
  exact ⟨m, hclean, hmN⟩

/-! ### Factorization data — единственный реальный вход (от carrier/сита) -/

/--
  **FactorizationData** — структурный вход: для бесконечного подмножества clean-центров одного
  ранга `r` (`1≤r≤4`), каждый центр `m` даёт `RankNode r` (факторы — простые `>A` стороны `6m+σ`),
  с AmbientLegal (факторы делят `6m+σ ≤ 6X_A+1`), и разные центры ⟹ разные node.

  Это НЕ аксиома двигателя — это существование факторизации + pigeonhole по рангу, которое даёт
  carrier (сито/арифметика, `rank≤4` проверен численно). Выделено явно как единственный остаток. -/
structure FactorizationData (A X_A : ℕ) where
  r : ℕ
  hr : 1 ≤ r ∧ r ≤ 4
  S : Set ℕ
  hS : S.Infinite
  node : ℕ → RankNode r
  hinj : Set.InjOn node S
  hamb : ∀ m ∈ S, AmbientLegal X_A (node m).factors

/--
  **ПОСЛЕДНЕЕ ЗВЕНО: CarrierData ⟹ Engine.** Если carrier даёт `FactorizationData` (бесконечно
  много стартов фиксированного ранга, факторизованных в AmbientLegal-RankNode, инъективно), то при
  separating scale — `Engine`. Это `product_core_engine_of_carrier`, подставленный данными carrier.
  Вся pump-машина (descent, база, pigeonhole) доказана; вход — только `FactorizationData`. -/
theorem engine_of_factorization {A X_A P_A : ℕ} {Engine : Prop} [NeZero P_A]
    (hsep : 6 * X_A + 1 < P_A) (F : FactorizationData A X_A) : Engine :=
  product_core_engine_of_carrier hsep F.hr F.S F.hS F.node F.hinj F.hamb

end EuclidsPath.CarrierBridge
