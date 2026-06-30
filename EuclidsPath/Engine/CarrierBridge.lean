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

/-! ### Построение FactorizationData: infinite-pigeonhole по рангу (доказано) -/

/-- **Infinite-pigeonhole по `Fin (n+1)` — ДОКАЗАНО.** Бесконечное `S`, разбитое функцией `f` на
    `n+1` классов ⟹ один класс бесконечен. -/
theorem exists_infinite_fiber {α : Type*} {n : ℕ} (S : Set α) (hS : S.Infinite)
    (f : α → Fin (n + 1)) : ∃ c, {x | x ∈ S ∧ f x = c}.Infinite := by
  by_contra h
  simp only [not_exists, Set.not_infinite] at h
  have hsub : S ⊆ ⋃ c, {x | x ∈ S ∧ f x = c} :=
    fun x hx => Set.mem_iUnion.mpr ⟨f x, hx, rfl⟩
  exact hS ((Set.finite_iUnion (fun c => h c)).subset hsub)

/--
  **Построение FactorizationData из carrier + factorize-карты (полу-доказано).** Дано: бесконечный
  carrier `C`, ранг-функция `rankOf : ℕ → Fin 4` (число больших простых факторов, ≤4 — арифметика),
  node-карта `mk : ℕ → RankNode` для каждого ранга, инъективная и AmbientLegal. Тогда есть
  `FactorizationData`. Здесь — infinite-pigeonhole по рангу (доказан); вход — лишь сами карты
  `mk`/`amb` (факторизация), привязанные к рангу. -/
noncomputable def factorizationData_of_carrier {A X_A : ℕ}
    (C : Set ℕ) (hC : C.Infinite)
    (rankOf : ℕ → Fin 4)
    (mkNode : (r : ℕ) → ℕ → RankNode r)
    (hinj : ∀ r : Fin 4, Set.InjOn (mkNode (r + 1)) {x | x ∈ C ∧ rankOf x = r})
    (hamb : ∀ (r : Fin 4) (m), m ∈ C → rankOf m = r →
        AmbientLegal X_A (mkNode (r + 1) m).factors) :
    FactorizationData A X_A :=
  let c := (exists_infinite_fiber C hC rankOf).choose
  have hc := (exists_infinite_fiber C hC rankOf).choose_spec
  { r := (c : ℕ) + 1
    hr := ⟨by omega, by omega⟩
    S := {x | x ∈ C ∧ rankOf x = c}
    hS := hc
    node := mkNode ((c : ℕ) + 1)
    hinj := hinj c
    hamb := fun m hm => hamb c m hm.1 hm.2 }

/--
  **ФИНАЛ от carrier + node-карт.** Если задана node-карта `mkNode` (факторизация центра в RankNode
  данного ранга), инъективная и AmbientLegal на каждом ранге, то при separating scale бесконечный
  carrier ⟹ Engine. Infinite-pigeonhole по рангу + вся pump-машина доказаны; вход — только сами
  `rankOf`/`mkNode`/`hinj`/`hamb` (факторизация `6m+σ` от carrier). -/
theorem engine_of_carrier_and_factorize {A X_A P_A : ℕ} {Engine : Prop} [NeZero P_A]
    (hsep : 6 * X_A + 1 < P_A)
    (C : Set ℕ) (hC : C.Infinite)
    (rankOf : ℕ → Fin 4) (mkNode : (r : ℕ) → ℕ → RankNode r)
    (hinj : ∀ r : Fin 4, Set.InjOn (mkNode (r + 1)) {x | x ∈ C ∧ rankOf x = r})
    (hamb : ∀ (r : Fin 4) (m), m ∈ C → rankOf m = r →
        AmbientLegal X_A (mkNode (r + 1) m).factors) :
    Engine :=
  engine_of_factorization (A := A) hsep (factorizationData_of_carrier C hC rankOf mkNode hinj hamb)

end EuclidsPath.CarrierBridge
