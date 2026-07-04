/-
  RiemannEngine — RH by contradiction to the perpetual engine, clean form: `¬RH → OffCriticalZero → Engine`.
  Source: EuclidsPath_boundary_..._patch (RH-to-engine brick).
  Prose: prose/30_RiemannBranch.md (section «RH → OffCriticalZero → Engine, clean form»).

  IDEA. Split the contrapositive into a PURE part (`¬RH → OffCriticalZero`, only negation of
  the mathlib-RH definition) and a BRIDGE (`OffCriticalZero → Engine`, analytic named input). Localisation of the zero into
  the strip: upper boundary (`Re < 1`) — from mathlib (`riemannZeta_ne_zero_of_one_le_re`, PNT-level, IMPORT, not
  core), lower boundary (`Re > 0`) — from the explicit named input `TrivialBelowZeroClassification`.

  PROVED HERE (pure logic + one mathlib-lemma, std axioms, no sorry):
    * `offCriticalZero_of_not_RH` / `not_RH_of_offCriticalZero` / `not_RH_iff_nonempty_offCriticalZero`
      — equivalence `¬RH ⟺ ∃ off-critical zero` (only push_neg on mathlib-RH);
    * `offCriticalZero_re_lt_one` (mathlib), `offCriticalZero_re_pos` (named input), localisation into the strip;
    * `engine_of_not_RH(_in_strip)` and `RH_of_no_engine(_in_strip)` — contrapositive both directions.

  HONEST BOUNDARY. RH is NOT proved: `RH_of_no_engine` requires the bridge `EngineBridge` AND `¬Engine`. Bridges
  (`EngineBridge`, `CriticalStripEngineBridge`) and `TrivialBelowZeroClassification` are unproved named inputs.
  `Engine` is a parameter (not a free leak: `Engine := True` gives `¬Engine = False`, RH does NOT come for free).
  `Step00` remains `sorry`.
-/
import Mathlib
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option autoImplicit false

namespace EuclidsPath.RiemannEngine

open Complex

/-- Nontrivial zero in the sense of mathlib-RH: `ζ s = 0`, not trivial (`≠ -2(n+1)`), `s ≠ 1`. -/
structure NontrivialZetaZero where
  s : ℂ
  zero : riemannZeta s = 0
  nontrivial : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)
  not_one : s ≠ 1

/-- Counterexample to RH (in the sense of mathlib): a nontrivial zero off the critical line. -/
structure OffCriticalZero extends NontrivialZetaZero where
  off_line : s.re ≠ (1 / 2 : ℝ)

/-- Counterexample additionally localised into the critical strip. -/
structure CriticalStripOffLineZero extends OffCriticalZero where
  re_pos : 0 < s.re
  re_lt_one : s.re < 1

/-- **Analytic named input.** Every zero with `Re ≤ 0` is trivial (`-2(n+1)`). Functional equation;
    mathlib gives only the VALUES of the trivial zeros, not this classification. NOT proved here. -/
def TrivialBelowZeroClassification : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → s.re ≤ 0 → ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

/-! ## Pure logic: `¬RH` yields an off-critical zero -/

/-- **`offCriticalZero_of_not_RH` — PROVED (pure push_neg on mathlib-RH).** -/
theorem offCriticalZero_of_not_RH (hNotRH : ¬ RiemannHypothesis) :
    Nonempty OffCriticalZero := by
  classical
  unfold RiemannHypothesis at hNotRH
  push_neg at hNotRH
  rcases hNotRH with ⟨s, hzero, hnontrivial, hnot_one, hoff⟩
  -- push_neg yields hnontrivial : ∀ n, s ≠ -2*(n+1); the field expects ¬∃. Bridge:
  refine ⟨{ s := s, zero := hzero, nontrivial := ?_, not_one := hnot_one, off_line := hoff }⟩
  rintro ⟨n, hn⟩; exact hnontrivial n hn

/-- **`not_RH_of_offCriticalZero` — PROVED.** An off-critical zero refutes RH. -/
theorem not_RH_of_offCriticalZero (Z : OffCriticalZero) : ¬ RiemannHypothesis := by
  intro hRH
  exact Z.off_line (hRH Z.s Z.zero Z.nontrivial Z.not_one)

/-- **`not_RH_iff_nonempty_offCriticalZero` — PROVED (equivalence).** -/
theorem not_RH_iff_nonempty_offCriticalZero :
    ¬ RiemannHypothesis ↔ Nonempty OffCriticalZero := by
  constructor
  · exact offCriticalZero_of_not_RH
  · intro h; rcases h with ⟨Z⟩; exact not_RH_of_offCriticalZero Z

/-! ## Localisation into the critical strip -/

/-- **`offCriticalZero_re_pos` — PROVED (from the classification named input).** Nontrivial zero: `Re > 0`. -/
theorem offCriticalZero_re_pos (hBelow : TrivialBelowZeroClassification) (Z : OffCriticalZero) :
    0 < Z.s.re := by
  have hnot_le : ¬ Z.s.re ≤ 0 := fun hle => Z.nontrivial (hBelow Z.s Z.zero hle)
  exact lt_of_not_ge hnot_le

/-- **`offCriticalZero_re_lt_one` — CLOSED BY mathlib-ANALYTICS (not core).** `Re < 1` from
    `riemannZeta_ne_zero_of_one_le_re` (non-vanishing of zeta on `Re ≥ 1` — PNT-level, IMPORT). -/
theorem offCriticalZero_re_lt_one (Z : OffCriticalZero) : Z.s.re < 1 := by
  have hnot_le : ¬ 1 ≤ Z.s.re := fun hle => (riemannZeta_ne_zero_of_one_le_re hle) Z.zero
  exact lt_of_not_ge hnot_le

/-- Upgrade of an off-critical zero to a zero-in-strip (given the `Re ≤ 0` classification). -/
def criticalStripOffLineZero_of_offCriticalZero
    (hBelow : TrivialBelowZeroClassification) (Z : OffCriticalZero) : CriticalStripOffLineZero :=
{ s := Z.s, zero := Z.zero, nontrivial := Z.nontrivial, not_one := Z.not_one,
  off_line := Z.off_line, re_pos := offCriticalZero_re_pos hBelow Z,
  re_lt_one := offCriticalZero_re_lt_one Z }

/-- **`criticalStripOffLineZero_of_not_RH` — PROVED.** `¬RH` + classification ⟹ counterexample in the strip. -/
theorem criticalStripOffLineZero_of_not_RH
    (hBelow : TrivialBelowZeroClassification) (hNotRH : ¬ RiemannHypothesis) :
    Nonempty CriticalStripOffLineZero := by
  rcases offCriticalZero_of_not_RH hNotRH with ⟨Z⟩
  exact ⟨criticalStripOffLineZero_of_offCriticalZero hBelow Z⟩

/-! ## Bridges to the engine (named inputs) -/

variable (Engine : Prop)

/-- **Bridge (named input):** off-critical zero ⟹ engine. NOT proved. -/
def EngineBridge : Prop := OffCriticalZero → Engine

/-- **Strip bridge (named input):** off-critical zero IN THE STRIP ⟹ engine. NOT proved. -/
def CriticalStripEngineBridge : Prop := CriticalStripOffLineZero → Engine

/-- **`engine_of_not_RH` — PROVED (given the bridge).** `¬RH → Engine`. -/
theorem engine_of_not_RH (bridge : EngineBridge Engine) (hNotRH : ¬ RiemannHypothesis) : Engine := by
  rcases offCriticalZero_of_not_RH hNotRH with ⟨Z⟩; exact bridge Z

/-- **`engine_of_not_RH_in_strip` — PROVED (given strip bridge + classification).** -/
theorem engine_of_not_RH_in_strip (hBelow : TrivialBelowZeroClassification)
    (bridge : CriticalStripEngineBridge Engine) (hNotRH : ¬ RiemannHypothesis) : Engine := by
  rcases criticalStripOffLineZero_of_not_RH hBelow hNotRH with ⟨Z⟩; exact bridge Z

/-- **`RH_of_no_engine` — PROVED (conditional RH).** Bridge + `¬Engine` ⟹ mathlib-RH. -/
theorem RH_of_no_engine (bridge : EngineBridge Engine) (hNoEngine : ¬ Engine) : RiemannHypothesis := by
  by_contra hNotRH; exact hNoEngine (engine_of_not_RH Engine bridge hNotRH)

/-- **`RH_of_no_engine_in_strip` — PROVED (conditional RH, strip).** -/
theorem RH_of_no_engine_in_strip (hBelow : TrivialBelowZeroClassification)
    (bridge : CriticalStripEngineBridge Engine) (hNoEngine : ¬ Engine) : RiemannHypothesis := by
  by_contra hNotRH; exact hNoEngine (engine_of_not_RH_in_strip Engine hBelow bridge hNotRH)

end EuclidsPath.RiemannEngine
