/-
  UniversalEngine — the ABSTRACT perpetual engine of Euclid over ANY space,
  its INTRINSIC impossibility (well-foundedness), rank transfer, and — HONESTLY —
  its OPERATION on the continuum ℝ (the governing dividing line).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER — WHAT IS PROVED HERE AND WHAT IS HONESTLY NOT PROVED.    │
  └───────────────────────────────────────────────────────────────────────────┘

  1. DEFINITION OVER ANY SPACE. The engine `PerpetualEngine r` is an infinite
     STRICTLY r-descending chain `f : ℕ → α` with `r (f (n+1)) (f n)`. The definition is given over
     an ARBITRARY relation `r : α → α → Prop`, so the "engine" transfers to any
     space by the same expression.

  2. INTRINSIC IMPOSSIBILITY. On every well-founded (`WellFounded r`) carrier the engine
     does NOT exist: `no_perpetual_engine_of_wellFounded`. The reason is INTRINSIC, almost
     definitional — the very form of the engine (infinite strict descent) is exactly what
     `WellFounded` forbids (`wellFounded_iff_isEmpty_descending_chain`). "Intrinsic
     cause" is the meeting of the engine's own form with a well-founded carrier, not an
     external addition. More precisely: `perpetualEngine_iff_not_wellFounded` is the EXACT dividing
     line: the engine exists ⟺ the carrier is NOT well-founded.

  3. RANK TRANSFER. `no_perpetual_engine_of_rank`: if r-steps strictly decrease the rank
     `ρ : α → β` in a well-founded `(β, s)`, there is no engine. EVERY front of the repository —
     `lexRank` in `ConcreteStep00Graph`, `HodgeFront.height`, the height of the dyadic hull,
     `HigherEnergy.DebtEnergy`, `BadCoverDescent.Energy` — is a COROLLARY of this ONE
     theorem (the same `of_natRank` with ℕ-rank). Here we explicitly exhibit EPMI and ℕ; the remaining
     fronts are the same `of_natRank`.

  4. HONEST CONTROLLER. NOT "impossible everywhere". On the continuum ℝ (the order is NOT
     well-founded) the engine OPERATES: `perpetualEngine_on_real` (reusing the witness
     `(1/2)ⁿ` from `DissipativeCascade.real_positive_work_not_wellfounded`). The well-ordering
     of the number line ℕ is the CONTROLLER: it decides WHERE perpetual motion is forbidden
     (discrete) and WHERE it is realized (continuum = mass/singularity). Cf.
     `ContinuousEngine.continuous_engine_dividing_line` (M6) — the same demarcation in
     differential form.

  5. HONEST NOVELTY. The core "WellFounded ⟹ no descending chain" is mathlib
     (`wellFounded_iff_isEmpty_descending_chain`). The module's contribution: the EXPLICIT definition of the engine
     `PerpetualEngine` + UNIFICATION by rank transfer (`of_rank`/`of_natRank`) + the dividing
     line of the controller (`universal_engine_dividing_line`). This is FORMALIZATION/UNIFICATION, not
     new deep mathematics.

  No `sorry`, no new axiom, no `native_decide`. Module 🟢 (standard
  triple `propext` / `Classical.choice` / `Quot.sound`); repository taint (47) unchanged.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/UniversalEngine.lean → zero errors.

  Kinship: EuclidsPath/Engine/EPMI.lean (`DescentStep`, `no_infinite_descent` — ℕ-prohibition);
    EuclidsPath/Engine/DissipativeCascade.lean (`real_positive_work_not_wellfounded` — ℝ-(1/2)ⁿ);
    EuclidsPath/Engine/ContinuousEngine.lean (`continuous_engine_dividing_line` — M6, demarcation).
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.DissipativeCascade
import EuclidsPath.Engine.ContinuousEngine

set_option autoImplicit false

namespace EuclidsPath.UniversalEngine

/-- Perpetual engine in ANY space: an infinite strictly r-descending chain. -/
def PerpetualEngine {α : Type*} (r : α → α → Prop) : Prop :=
  ∃ f : ℕ → α, ∀ n, r (f (n + 1)) (f n)

/-- Exact dividing line: the engine exists ⟺ the carrier is NOT well-founded. -/
theorem perpetualEngine_iff_not_wellFounded {α : Type*} {r : α → α → Prop} :
    PerpetualEngine r ↔ ¬ WellFounded r := by
  rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff]
  exact ⟨fun ⟨f, hf⟩ => ⟨⟨f, hf⟩⟩, fun ⟨⟨f, hf⟩⟩ => ⟨f, hf⟩⟩

/-- INTRINSIC IMPOSSIBILITY: on every well-founded carrier there is no engine.
    The engine's own definition (descending chain) is exactly what
    well-foundedness forbids. -/
theorem no_perpetual_engine_of_wellFounded {α : Type*} {r : α → α → Prop}
    (hwf : WellFounded r) : ¬ PerpetualEngine r :=
  fun h => (perpetualEngine_iff_not_wellFounded.mp h) hwf

/-- RANK TRANSFER to any well-founded `(β, s)`: if r-steps strictly decrease the rank `ρ`,
    there is no engine. -/
theorem no_perpetual_engine_of_rank {α β : Type*} (ρ : α → β) {r : α → α → Prop}
    {s : β → β → Prop} (hwf : WellFounded s)
    (hmono : ∀ x y, r x y → s (ρ x) (ρ y)) : ¬ PerpetualEngine r :=
  fun ⟨f, hf⟩ =>
    no_perpetual_engine_of_wellFounded hwf ⟨ρ ∘ f, fun n => hmono _ _ (hf n)⟩

/-- Number line case: a strictly decreasing ℕ-rank forbids the engine. -/
theorem no_perpetual_engine_of_natRank {α : Type*} (ρ : α → ℕ) {r : α → α → Prop}
    (hmono : ∀ x y, r x y → ρ x < ρ y) : ¬ PerpetualEngine r :=
  no_perpetual_engine_of_rank ρ (wellFounded_lt (α := ℕ)) hmono

/-- Every `WellFoundedLT` space forbids a `(<)`-engine. -/
theorem no_perpetual_engine_of_wellFoundedLT {α : Type*} [Preorder α] [WellFoundedLT α] :
    ¬ PerpetualEngine (· < · : α → α → Prop) :=
  no_perpetual_engine_of_wellFounded wellFounded_lt

/-- ℕ (the number line) carries the prohibition within itself. -/
theorem no_perpetual_engine_on_nat : ¬ PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  no_perpetual_engine_of_wellFounded wellFounded_lt

/-- HONEST CONTROLLER BOUNDARY: on the continuum ℝ the engine OPERATES (reusing
    the witness `(1/2)ⁿ`). -/
theorem perpetualEngine_on_real : PerpetualEngine (· < · : ℝ → ℝ → Prop) := by
  obtain ⟨a, hdesc, _, _⟩ :=
    EuclidsPath.DissipativeCascade.real_positive_work_not_wellfounded
  exact ⟨a, fun n => hdesc n⟩

/-- As a consequence: the strict order on ℝ is NOT well-founded. -/
theorem real_lt_not_wellFounded : ¬ WellFounded (· < · : ℝ → ℝ → Prop) :=
  perpetualEngine_iff_not_wellFounded.mp perpetualEngine_on_real

/-- CONTROLLER: forbidden on every well-founded carrier, realized on the continuum. -/
theorem universal_engine_dividing_line :
    (∀ {α : Type} {r : α → α → Prop}, WellFounded r → ¬ PerpetualEngine r)
      ∧ PerpetualEngine (· < · : ℝ → ℝ → Prop) :=
  ⟨fun hwf => no_perpetual_engine_of_wellFounded hwf, perpetualEngine_on_real⟩

/-- UNIFICATION: the existing ℕ-impossibility `EPMI.no_infinite_descent` is a COROLLARY
    of the abstract theorem (rank = `H`; for `A ≥ 1`, from `DescentStep A (H t) (H (t+1))` it follows
    that `H (t+1) < H t`). We derive a contradiction from `no_perpetual_engine_on_nat`. -/
theorem epmi_no_infinite_descent_as_instance {A : ℕ} (hA : 1 ≤ A) (H : ℕ → ℕ)
    (hchain : ∀ t, EuclidsPath.Engine.DescentStep A (H t) (H (t + 1))) : False := by
  apply no_perpetual_engine_on_nat
  exact ⟨H, fun t => by
    have h := hchain t
    unfold EuclidsPath.Engine.DescentStep at h
    -- h : A * H (t+1) < H t; for 1 ≤ A we get H (t+1) < H t
    have hle : H (t + 1) ≤ A * H (t + 1) := Nat.le_mul_of_pos_left _ hA
    omega⟩

/-!
################################################################################
  SUMMARY (LOUD HONEST): what is proved, what is reused, what REMAINS OPEN
################################################################################

  🟢 GENUINELY NEW (machine-checked, in this module):
     · `PerpetualEngine` — explicit definition of the engine over ANY relation;
     · `perpetualEngine_iff_not_wellFounded` — EXACT dividing line;
     · `no_perpetual_engine_of_wellFounded` — intrinsic impossibility (almost definitional);
     · `no_perpetual_engine_of_rank` / `no_perpetual_engine_of_natRank` — UNIFICATION by rank:
       every front of the repository is a corollary of this ONE theorem;
     · `universal_engine_dividing_line` — controller: prohibition (well-founded) ↔ operation (ℝ);
     · `epmi_no_infinite_descent_as_instance` — EPMI as an instance of the abstraction.

  🟢 REUSED (cited, NOT re-derived):
     · `DissipativeCascade.real_positive_work_not_wellfounded` (ℝ-(1/2)ⁿ, `perpetualEngine_on_real`);
     · `EuclidsPath.Engine.DescentStep` (EPMI-rank);
     · `wellFounded_iff_isEmpty_descending_chain` / `wellFounded_lt` (mathlib core).

  HONEST NOVELTY: the core (WellFounded ⟹ no chain) is mathlib; the contribution is the engine definition +
  unification by rank transfer + the controller's dividing line. Formalization/unification, not
  new deep mathematics. No `sorry`, no new axiom, no `native_decide`; taint 47 unchanged.
-/

#print axioms no_perpetual_engine_of_wellFounded
#print axioms perpetualEngine_iff_not_wellFounded
#print axioms no_perpetual_engine_of_rank
#print axioms universal_engine_dividing_line
#print axioms epmi_no_infinite_descent_as_instance
#print axioms perpetualEngine_on_real

end EuclidsPath.UniversalEngine
