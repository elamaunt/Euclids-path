/-
  ProductHall / SteeringEngine — a strict local pump WITHOUT circular payment.
  Source: step00_producthall_steering_pump_strict_ru_2026-07-01.md. Prose: prose/29_ProductHall.md.

  Substantial improvement over previous pumps: does NOT use "same key ⟹ payment by definition"
  (§9 explicitly rejects this — eliminating the circularity found by the audit). Instead — a
  4-case dichotomy of Legal/Forbidden zones with genuine logical content.

  PROVABLE CORE (here): zone-dichotomy + steering-constructors + `productHall_engine` (case logic).
  Open nodes (explicit hypotheses): `UniqueLegalLift` (passport normality) and
  `SteeringEngine ⟹ EuclideanEngine` (new EPMI on steering). They are NOT proven — but these are
  STRUCTURAL nodes, not circular definitions.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.ProductHall

variable {EngineState : Type*}

/-- Configuration of the local engine: zones, step, passport. All fields are abstract predicates/functions;
    their concrete implementation (product-state `6m+σ`, residue-passport) is an input. -/
structure HallConfig (EngineState : Type*) (Passport : Type*) where
  Legal : EngineState → Prop
  Forbidden : EngineState → Prop
  RigidStep : EngineState → EngineState → Prop
  pass : EngineState → Passport
  EuclideanEngine : Prop
  /-- zone dichotomy (§1): every state is either legal or forbidden -/
  zone_cases : ∀ X, Legal X ∨ Forbidden X
  /-- **UniqueLegalLift (UL, §4) — OPEN NODE.** Two legal-lifts of the same passport over the same base
      coincide. (Should follow from the passport as the normal form of a legal-state; §13.) -/
  uniqueLegalLift : ∀ X₁ X₂ Y, RigidStep X₁ Y → RigidStep X₂ Y →
      pass X₁ = pass X₂ → Legal X₁ → Legal X₂ → X₁ = X₂
  /-- **SteeringEngine ⟹ EuclideanEngine (§6) — OPEN NODE (new EPMI).** Any steering
      configuration (intersection of legal/forbidden boundary) yields a forbidden engine. -/
  steering_is_euclidean : ∀ X₁ X₂ Y, X₁ ≠ X₂ → pass X₁ = pass X₂ →
      RigidStep X₁ Y → RigidStep X₂ Y →
      ((Legal X₁ ∧ Forbidden X₂) ∨ (Forbidden X₁ ∧ Legal X₂) ∨
       (Forbidden X₁ ∧ Legal Y) ∨ (Forbidden X₂ ∧ Legal Y)) →
      EuclideanEngine

variable {Passport : Type*}

/--
  **ProductHall ⟹ EuclideanEngine (Lemma 8.1) — PROVEN by 4 cases.** Local fan-in
  `X₁→Y`, `X₂→Y` with `X₁≠X₂`, the same passport, and `Legal Y`. Case analysis on zones `X₁,X₂`:
  - both legal ⟹ `uniqueLegalLift` gives `X₁=X₂`, contradiction;
  - mixed ⟹ steering;
  - both forbidden ⟹ forbidden-inflow into legal Y ⟹ steering.
  In all cases — `EuclideanEngine`. This is PURE LOGIC (non-circular), on two open nodes. -/
theorem productHall_engine (C : HallConfig EngineState Passport)
    (X₁ X₂ Y : EngineState) (hne : X₁ ≠ X₂) (hp : C.pass X₁ = C.pass X₂)
    (h1 : C.RigidStep X₁ Y) (h2 : C.RigidStep X₂ Y) (hYlegal : C.Legal Y) :
    C.EuclideanEngine := by
  rcases C.zone_cases X₁ with hX1L | hX1F
  · rcases C.zone_cases X₂ with hX2L | hX2F
    · -- both legal ⟹ X₁=X₂, contradiction
      exact absurd (C.uniqueLegalLift X₁ X₂ Y h1 h2 hp hX1L hX2L) hne
    · -- legal/forbidden ⟹ steering
      exact C.steering_is_euclidean X₁ X₂ Y hne hp h1 h2 (Or.inl ⟨hX1L, hX2F⟩)
  · rcases C.zone_cases X₂ with hX2L | hX2F
    · -- forbidden/legal ⟹ steering
      exact C.steering_is_euclidean X₁ X₂ Y hne hp h1 h2 (Or.inr (Or.inl ⟨hX1F, hX2L⟩))
    · -- both forbidden, Y legal ⟹ forbidden-inflow ⟹ steering
      exact C.steering_is_euclidean X₁ X₂ Y hne hp h1 h2 (Or.inr (Or.inr (Or.inl ⟨hX1F, hYlegal⟩)))

/--
  **Why this is NOT a renaming of payment (§9).** There is no "same key ⟹ payment" here. The content
  lies in `uniqueLegalLift` (normality) and the zone-dichotomy: a passport collision is resolved EITHER
  by coincidence (UL) OR by steering. These are distinct logical branches, not a baked-in conclusion. -/
theorem productHall_noncircular (C : HallConfig EngineState Passport)
    (X₁ X₂ Y : EngineState) (h1 : C.RigidStep X₁ Y) (h2 : C.RigidStep X₂ Y)
    (hp : C.pass X₁ = C.pass X₂) (hX1L : C.Legal X₁) (hX2L : C.Legal X₂) :
    X₁ = X₂ :=
  C.uniqueLegalLift X₁ X₂ Y h1 h2 hp hX1L hX2L

end EuclidsPath.ProductHall
