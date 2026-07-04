/-
  The final link: constructing CarrierData from the infinitude of the carrier. Prose: prose/33_CarrierBridge.md.

  ProductCore.product_core_engine_of_carrier takes carrier data:
    infinite S of starts + node:ι→RankNode r (InjOn) + AmbientLegal ⟹ Engine.
  Here this is built from the ALREADY PROVEN `Residuals.carrier_nonempty_above` (a clean center above any N
  ⟹ the carrier is infinite).

  Provable here:
    • the carrier is infinite (from carrier_nonempty_above);
    • distinct centers ⟹ distinct cores (via the value 6m+σ).
  The sole real input (factorization): every legal `6m+σ` factors into a `RankNode r`
  (prime factors >A, fixed r after pigeonhole by rank). This is the existence of the factorization —
  it comes from the carrier/sieve, not from the engine axiom. Isolated explicitly as `FactorizationData`.
-/
import Mathlib
import EuclidsPath.Engine.ProductCore
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.CarrierBridge

open EuclidsPath.ProductCore EuclidsPath.Residuals

/-! ### Carrier is infinite (from carrier_nonempty_above) -/

/-- The set of clean centers (ℕ) for a given `A`. -/
def CleanCenters (A : ℕ) : Set ℕ := {m | CleanZ A (m : ℤ)}

/--
  **Carrier is infinite — PROVEN.** `carrier_nonempty_above` gives a clean center above any `N`,
  so `CleanCenters A` is unbounded above ⟹ infinite. -/
theorem cleanCenters_infinite (A : ℕ) : (CleanCenters A).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨m, hmN, hclean⟩ := carrier_nonempty_above A N
  exact ⟨m, hclean, hmN⟩

/-! ### Factorization data — the sole real input (from the carrier/sieve) -/

/--
  **FactorizationData** — the structural input: for an infinite subset of clean centers of a single
  rank `r` (`1≤r≤4`), each center `m` yields a `RankNode r` (factors are primes `>A` on the sides of `6m+σ`),
  with AmbientLegal (factors divide `6m+σ ≤ 6X_A+1`), and distinct centers ⟹ distinct nodes.

  This is NOT the engine axiom — it is the existence of the factorization + pigeonhole by rank, which gives the
  carrier (sieve/arithmetic, `rank≤4` verified numerically). Isolated explicitly as the sole remaining input. -/
structure FactorizationData (A X_A : ℕ) where
  r : ℕ
  hr : 1 ≤ r ∧ r ≤ 4
  S : Set ℕ
  hS : S.Infinite
  node : ℕ → RankNode r
  hinj : Set.InjOn node S
  hamb : ∀ m ∈ S, AmbientLegal X_A (node m).factors

/--
  **THE FINAL LINK: CarrierData ⟹ Engine.** If the carrier yields `FactorizationData` (infinitely
  many starts of fixed rank, factored into AmbientLegal-RankNode, injectively), then at
  separating scale — `Engine`. This is `product_core_engine_of_carrier` instantiated with the carrier data.
  The entire pump machine (descent, base, pigeonhole) is proven; the only input is `FactorizationData`. -/
theorem engine_of_factorization {A X_A P_A : ℕ} {Engine : Prop} [NeZero P_A]
    (hsep : 6 * X_A + 1 < P_A) (F : FactorizationData A X_A) : Engine :=
  product_core_engine_of_carrier hsep F.hr F.S F.hS F.node F.hinj F.hamb

/-! ### Building FactorizationData: infinite pigeonhole by rank (proven) -/

/-- **Infinite pigeonhole on `Fin (n+1)` — PROVEN.** An infinite `S` partitioned by a function `f` into
    `n+1` classes ⟹ one class is infinite. -/
theorem exists_infinite_fiber {α : Type*} {n : ℕ} (S : Set α) (hS : S.Infinite)
    (f : α → Fin (n + 1)) : ∃ c, {x | x ∈ S ∧ f x = c}.Infinite := by
  by_contra h
  simp only [not_exists, Set.not_infinite] at h
  have hsub : S ⊆ ⋃ c, {x | x ∈ S ∧ f x = c} :=
    fun x hx => Set.mem_iUnion.mpr ⟨f x, hx, rfl⟩
  exact hS ((Set.finite_iUnion (fun c => h c)).subset hsub)

/--
  **Building FactorizationData from the carrier + factorize maps (partially proven).** Given: an infinite
  carrier `C`, a rank function `rankOf : ℕ → Fin 4` (number of large prime factors, ≤4 — arithmetic),
  a node map `mk : ℕ → RankNode` for each rank, injective and AmbientLegal. Then there exists
  `FactorizationData`. Here — infinite pigeonhole by rank (proven); the only input is the maps
  `mk`/`amb` (factorization) tied to rank. -/
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
  **FINALE from carrier + node maps.** Given a node map `mkNode` (factorization of a center into a RankNode
  of the given rank), injective and AmbientLegal at every rank, then at separating scale an infinite
  carrier ⟹ Engine. Infinite pigeonhole by rank + the entire pump machine are proven; the only input is
  `rankOf`/`mkNode`/`hinj`/`hamb` (factorization of `6m+σ` from the carrier). -/
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
