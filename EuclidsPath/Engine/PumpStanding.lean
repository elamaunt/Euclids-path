/-
  Pump Lemma v2 — concrete two-token standing engine. Formalisation of the author's file.
  Source: step00_pump_standing_engine_strict_proof_ru_2026-06-30.md. Prose: prose/27_PumpStanding.md.

  Fix over the previous version: instead of the quotient self-loop `K→K` (which could be an infinite
  shift, not a cycle — a real gap) — a concrete 2-cycle `D₁→D₂→D₁` between DISTINCT debt-tokens.
  Logically cleaner.

  pump v2: `γ₁≠γ₂ ∧ key γ₁ = key γ₂ ⟹ EuclideanEngine` via:
    same_key_payment + debtToken_ne + standing_engine_of_two_cycle.

  HONEST BOUNDARY (the file acknowledges §14–15): three inputs are NOT proved:
    (1) same_key_payment — key collision ⟹ PaymentStep (the heart = former Hall node);
    (2) debtToken_ne — distinct genealogies ⟹ distinct tokens (distinguishability);
    (3) standing_engine_of_two_cycle — 2-cycle of tokens ⟹ engine (= new EPMI on standing cycles).

  Here pump is formalised as a CONDITIONAL theorem; #print axioms will show the load in the three inputs.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.PumpStanding

variable {Genealogy DebtToken : Type*}

/-- `pump` v2 (Theorem 10.1) — PURE LOGIC with three explicit inputs. -/
theorem pump
    {Key : Type*} (key : Genealogy → Key)
    (debt : Genealogy → DebtToken)
    (PaymentStep : DebtToken → DebtToken → Prop)
    (EuclideanEngine : Prop)
    -- (1) payment-completeness (NOT proved — the heart):
    (same_key_payment : ∀ a b : Genealogy, a ≠ b → key a = key b →
        PaymentStep (debt a) (debt b))
    -- (2) token distinguishability (NOT proved):
    (debtToken_ne : ∀ a b : Genealogy, a ≠ b → debt a ≠ debt b)
    -- (3) standing 2-cycle ⟹ engine (NOT proved — new EPMI on standing cycles):
    (standing_engine_of_two_cycle : ∀ D₁ D₂ : DebtToken, D₁ ≠ D₂ →
        PaymentStep D₁ D₂ → PaymentStep D₂ D₁ → EuclideanEngine)
    {γ₁ γ₂ : Genealogy} (hne : γ₁ ≠ γ₂) (hkey : key γ₁ = key γ₂) :
    EuclideanEngine :=
  standing_engine_of_two_cycle (debt γ₁) (debt γ₂)
    (debtToken_ne γ₁ γ₂ hne)
    (same_key_payment γ₁ γ₂ hne hkey)
    (same_key_payment γ₂ γ₁ (Ne.symm hne) hkey.symm)

/--
  **The two-cycle DOES fix the self-loop gap (in one sense).** The concrete 2-cycle `D₁→D₂→D₁`
  with `D₁ ≠ D₂` is a genuine directed cycle of length 2 in the `PaymentStep` graph, not a
  quotient artefact. Unlike a self-loop, it contains TWO distinct vertices ⟹ it is a real cycle.
  (Cycle logic.) -/
theorem two_cycle_is_real_cycle {DebtToken : Type*}
    (PaymentStep : DebtToken → DebtToken → Prop) (D₁ D₂ : DebtToken)
    (hne : D₁ ≠ D₂) (h12 : PaymentStep D₁ D₂) (h21 : PaymentStep D₂ D₁) :
    D₁ ≠ D₂ ∧ PaymentStep D₁ D₂ ∧ PaymentStep D₂ D₁ :=
  ⟨hne, h12, h21⟩

/--
  **BUT the EPMI gap REMAINS (height does not drop in a cycle).** The standing 2-cycle `D₁→D₂→D₁`
  RETURNS to `D₁` — so any "height" `h` on it does NOT strictly decrease (`h D₁ = h D₁` after
  traversal). Our proved EPMI (`no_infinite_engine_descent`) forbids a strictly DECREASING descent —
  but a standing cycle PRESERVES height. Therefore `standing_engine_of_two_cycle ⟹ ⊥` does NOT
  follow from our height-based EPMI: a NEW EPMI on lossless standing cycles (§14.3) is needed,
  which is NOT proved. -/
theorem standing_cycle_preserves_height {DebtToken : Type*}
    (h : DebtToken → ℕ) (D₁ D₂ : DebtToken) :
    h D₁ = h D₁ ∧ ¬ (h D₁ < h D₁) :=
  ⟨rfl, lt_irrefl _⟩

end EuclidsPath.PumpStanding
