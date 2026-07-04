/-
  Pump Lemma — the final node Step00, formalisation of the author's file.
  Source: step00_final_pump_payment_complete_normsig_ru_2026-06-30.md. Prose: prose/26_Pump.md.

  Author's goal: `γ₁≠γ₂ ∧ key γ₁ = key γ₂ ⟹ EuclideanEngine` (closes GlobalAbsorberNode).
  Via: collision ⟹ CertifiedPayment ⟹ rigid self-loop ⟹ engine.

  HONEST BOUNDARY (the file itself acknowledges §15–16): `pump` is trivial LOGIC given three inputs:
    (1) PaymentCompleteKey: key-collision ⟹ CertifiedPayment  — NOT proven (the heart);
    (2) rigid_payment_step: CertifiedPayment ⟹ RigidStep self-loop — NOT proven;
    (3) engine_of_self_loop: RigidStep S S ⟹ engine — depends on the DEFINITION of engine.

  CRITICAL: our proven EPMI (`no_infinite_engine_descent`) forbids an infinite STRICTLY
  DESCENDING height descent. Self-loop `LedgerState K → LedgerState K` does NOT change height — this is NOT a strict
  descent. Hence `engine_of_self_loop` does NOT follow from our EPMI: "engine = self-loop" is a DIFFERENT
  notion from "engine = infinite descent". This gap is marked explicitly.

  Here pump is formalised as a CONDITIONAL theorem: all three inputs are explicit hypotheses. `#print axioms`
  will show that the entire burden lies in them.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.PumpFinal

variable {Genealogy AbsKey RigidState : Type*}

/-- `pump` (Theorem 12.1) — PURE LOGIC given three explicit inputs. -/
theorem pump
    (key : Genealogy → AbsKey)
    (LedgerState : AbsKey → RigidState)
    (RigidStep : RigidState → RigidState → Prop)
    (EuclideanEngine : Prop)
    -- (1) payment-completeness (NOT proven — the heart of the node):
    (same_key_payment : ∀ γ₁ γ₂ : Genealogy, γ₁ ≠ γ₂ → key γ₁ = key γ₂ →
        RigidStep (LedgerState (key γ₁)) (LedgerState (key γ₁)))
    -- (2) self-loop ⟹ engine (depends on the definition of engine; does NOT follow from our EPMI):
    (engine_of_self_loop : ∀ S : RigidState, RigidStep S S → EuclideanEngine)
    {γ₁ γ₂ : Genealogy} (hne : γ₁ ≠ γ₂) (hkey : key γ₁ = key γ₂) :
    EuclideanEngine :=
  engine_of_self_loop (LedgerState (key γ₁)) (same_key_payment γ₁ γ₂ hne hkey)

/--
  **EPMI gap (explicit).** Our `no_infinite_engine_descent` (Irreversibility) forbids an infinite
  STRICTLY descending height descent. Self-loop preserves height (`h S = h S`), so the constant chain
  `z = fun _ => S` is NOT `StrictAnti` ⟹ EPMI does NOT apply to it. Therefore "self-loop ⟹ ⊥" does NOT
  follow from our EPMI: closing the gap requires EXTENDING EPMI to lossless-ledger-cycles (§15.3), and that is NOT proven. -/
theorem self_loop_height_preserved {RigidState : Type*} (h : RigidState → ℕ) (S : RigidState) :
    h S = h S ∧ ¬ (h S < h S) := ⟨rfl, lt_irrefl _⟩

end EuclidsPath.PumpFinal
