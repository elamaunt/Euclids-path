/-
  Side branch: the Riemann Hypothesis (RH) by CONTRADICTION via the Euclid engine.
  Prose: prose/28_RiemannBranch.md.

  HONEST FRAME (important): RH does NOT follow logically from the infinitude of twin primes directly — these
  are independent statements. Here we build a CORRECT contrapositive through the MECHANISM (the engine),
  the same one that closes the twin-prime branch.

  EXTERNAL = FROM MATHLIB. `RiemannHypothesis` is taken from mathlib (NOT a homemade def): the official
  formulation via zeros of `riemannZeta`, excluding trivial zeros `-2(n+1)` and `s = 1`. The location
  of zeros is also from mathlib: `riemannZeta_ne_zero_of_one_le_re` (no zeros when `Re ≥ 1`).

  What is proved / what is a named input:
    • `Re ρ ≥ 1` is impossible for a zero — PROVED via mathlib (`riemannZeta_ne_zero_of_one_le_re`);
    • `Re ρ ≤ 0` ⟹ ρ is trivial (`-2(n+1)`) — ANALYTIC NAMED INPUT `TrivialBelowZeroClassification`
      (functional equation; mathlib gives values of trivial zeros but not the classification
      "all zeros with Re ≤ 0 are trivial" — this is an explicit labelled named input);
    • strip `0 < Re ρ < 1` with `Re ≠ 1/2` ⟹ perpetual engine — gate `EngineBridge` (open, like `pump`);
    • no perpetual engine — PROVED (`no_infinite_descent`).
  The RH branch is conditional on `EngineBridge` + `TrivialBelowZeroClassification`. Both are explicit named inputs, not axioms.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.TwoGap

set_option autoImplicit false

namespace EuclidsPath.RiemannBranch

open Complex EuclidsPath.Engine

/-- Nontrivial zero of the zeta function in the mathlib-RH sense: `ζ ρ = 0`, ρ is not a trivial zero, `ρ ≠ 1`. -/
def NontrivialZeroM (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1

/--
  **`no_zero_of_one_le_re` — CLOSED BY mathlib ANALYTICS (not the engine core).** The zeta function has no zeros
  with `Re ρ ≥ 1`, so every zero satisfies `Re ρ < 1`.

  ⚠️ HONEST CAVEAT (per audit result): "proved" here means "derivable from mathlib", NOT
  "derivable from our core". The single step is the imported lemma `riemannZeta_ne_zero_of_one_le_re`,
  i.e., non-vanishing of zeta on `Re ≥ 1` — **an analytic result at PNT level**, proved in mathlib,
  not by us. It merely RESTRICTS the strip (`Re < 1`); it does NOT place a zero on `Re = 1/2` and does NOT close any
  open gate. This is not an RH leak, but it is also not a self-contained part of the engine. -/
theorem no_zero_of_one_le_re {ρ : ℂ} (hz : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  push_neg at h
  exact riemannZeta_ne_zero_of_one_le_re h hz

/--
  **Analytic named input `TrivialBelowZeroClassification`.** Every zero with `Re ρ ≤ 0` is trivial
  (`ρ = -2(n+1)`). This is classical (functional equation), but mathlib only provides the VALUES of trivial
  zeros (`riemannZeta_neg_two_mul_nat_add_one`), NOT the converse classification. Hence — an explicit named input,
  NOT a homemade RH. -/
def TrivialBelowZeroClassification : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 0 → ∃ n : ℕ, ρ = -2 * (n + 1)

/--
  **`nontrivialZero_in_strip` — LOCALISATION TO THE STRIP (mathlib analytics `Re<1` + named input for `Re≤0`).**
  A nontrivial zero lies strictly in the critical strip `0 < Re ρ < 1`.

  ⚠️ Both bounds are NOT from the engine core: the upper bound (`Re < 1`) rests on mathlib analytics at PNT level
  (see `no_zero_of_one_le_re`), the lower bound (`Re > 0`) rests on the explicit analytic named input
  `TrivialBelowZeroClassification`. Neither one places the zero on `1/2`. -/
theorem nontrivialZero_in_strip (hClass : TrivialBelowZeroClassification)
    {ρ : ℂ} (hρ : NontrivialZeroM ρ) : 0 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨hz, hnt, _⟩ := hρ
  refine ⟨?_, no_zero_of_one_le_re hz⟩
  by_contra h
  push_neg at h                    -- ρ.re ≤ 0
  exact hnt (hClass ρ hz h)

/--
  **Engine gate (H_RH) — open node of the branch.** A zero in the strip with `Re ≠ 1/2` ⟹ perpetual engine:
  the asymmetry yields an infinite clean chain of strictly decreasing height. NOT proved — analytic named input. -/
def EngineBridge : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (A : ℕ) (H : ℕ → ℕ), 1 ≤ A ∧ ∀ t, DescentStep A (H t) (H (t + 1))

/--
  **RH (mathlib) from two explicit named inputs (conditional theorem).** Given the gate `EngineBridge` and the classification
  `TrivialBelowZeroClassification`, the mathlib `RiemannHypothesis` holds: every nontrivial
  zero has `Re = 1/2`. Mechanism: a zero in the strip (proved) with `Re ≠ 1/2` would yield an engine, which does not exist
  (`no_infinite_descent`). All analytics is isolated in the two named inputs; the engine itself is the proved core. -/
theorem riemannHypothesis_of_engine_bridge
    (hClass : TrivialBelowZeroClassification) (H_RH : EngineBridge) :
    RiemannHypothesis := by
  intro ρ hz htriv hne1
  -- assemble nontriviality in the sense of our predicate
  have hρ : NontrivialZeroM ρ := ⟨hz, htriv, hne1⟩
  obtain ⟨hpos, hlt⟩ := nontrivialZero_in_strip hClass hρ
  by_contra hne
  obtain ⟨A, Hgt, hA, hchain⟩ := H_RH ρ hz hpos hlt hne
  exact no_infinite_descent hA Hgt hchain

/--
  **Contrapositive: ¬RH ⟹ engine ⟹ ⊥.** If both named inputs are given and mathlib-RH is false, then there exists
  a perpetual engine — a contradiction with the core. -/
theorem not_RH_gives_engine
    (hClass : TrivialBelowZeroClassification) (H_RH : EngineBridge) (hnotRH : ¬ RiemannHypothesis) :
    ∃ (A : ℕ) (H : ℕ → ℕ), 1 ≤ A ∧ ∀ t, DescentStep A (H t) (H (t + 1)) := by
  exact absurd (riemannHypothesis_of_engine_bridge hClass H_RH) hnotRH

/-! ### Connection to twin primes: one shared node instead of two -/

/--
  **Two-transport law (abstract form).** "The two-transport core holds" — ALREADY proved by the identities in
  `Engine/TwoGap`. Here it appears as an abstract premise. -/
def TwoTransportLaw : Prop :=
  ∀ m a b v q r s : ℕ, 1 ≤ m → 6 * m - 1 = a * b * v → 6 * m + 1 = q * r * s →
    q * r * s = a * b * v + 2

/-- The two-transport law is PROVED (this is `det_law_rank33`). Not an axiom. -/
theorem twoTransportLaw_holds : TwoTransportLaw :=
  fun _ _ _ _ _ _ _ hm h1 h2 => det_law_rank33 hm h1 h2

/--
  **Linking node `TwoTransportBridge`.** Implication: two-transport law ⟹ EngineBridge. A zero of ζ outside
  `1/2` breaks the two-transport and spawns a perpetual engine. If THIS (+ the classification) is proved, RH
  follows from the ALREADY proved core (`TwoGap` + EPMI). -/
def TwoTransportBridge : Prop := TwoTransportLaw → EngineBridge

/--
  **RH (mathlib) from the proved core + two linking nodes.** Given `TwoTransportBridge` and the classification,
  RH follows: `TwoTransportLaw` is ALREADY proved, EPMI is ALREADY proved. EXACTLY `TwoTransportBridge` and
  `TrivialBelowZeroClassification` remain open — both explicit, not axioms. -/
theorem riemannHypothesis_of_two_transport
    (hClass : TrivialBelowZeroClassification) (bridge : TwoTransportBridge) :
    RiemannHypothesis :=
  riemannHypothesis_of_engine_bridge hClass (bridge twoTransportLaw_holds)

end EuclidsPath.RiemannBranch
