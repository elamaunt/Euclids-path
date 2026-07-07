/-
  PoincareRecurrence — the reversibility dividing line.

  The perpetual-engine prohibition is about IRREVERSIBILITY: on a well-founded
  carrier no strictly descending chain exists, so nothing returns
  (`no_perpetual_engine_of_wellFounded`). Its exact contrary is Poincaré
  recurrence: a MEASURE-PRESERVING (reversible) map on a finite measure space is
  conservative, and then almost every point RETURNS to any set infinitely often.

  This module pairs the two — mathlib's `Conservative.ae_mem_imp_frequently_image_mem`
  against the engine core — as a dividing line mirroring `universal_engine_dividing_line`:
  reversible ⇒ recurrence, strict descent ⇒ no return. It is isolated from the rest
  of the Engine line because it pulls in measure theory.

  Green (standard triple). The recurrence half is imported mathlib; the no-return
  half is the engine. This is a contrast, not a claim to subsume recurrence.
-/
import EuclidsPath.Engine.UniversalEngine
import Mathlib.Dynamics.Ergodic.Conservative

set_option autoImplicit false

namespace EuclidsPath.PoincareRecurrence

open EuclidsPath.UniversalEngine
open MeasureTheory Filter

/-- **The reversibility dividing line.** On one side, every well-founded relation
    forbids the perpetual engine — a strictly descending chain, hence any return
    (the irreversible side). On the other, a conservative (e.g. finite-measure
    measure-preserving, reversible) map satisfies Poincaré recurrence: almost every
    point of a set returns to it infinitely often. The two halves are the exact
    contraries the engine's `universal_engine_dividing_line` names on ℝ, here on a
    measure space: strict descent never returns, reversibility always does. -/
theorem poincare_dividing_line {α : Type*} [MeasurableSpace α]
    (f : α → α) (μ : Measure α) :
    (∀ r : α → α → Prop, WellFounded r → ¬ PerpetualEngine r)
      ∧ (Conservative f μ → ∀ s : Set α, NullMeasurableSet s μ →
          ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s) :=
  ⟨fun _ hwf => no_perpetual_engine_of_wellFounded hwf,
   fun hc s hs => hc.ae_mem_imp_frequently_image_mem hs⟩

/-- Finite-measure measure-preserving maps land on the recurrence side: they are
    conservative, so Poincaré recurrence holds — the reversible counterpart of the
    engine's no-return. -/
theorem measurePreserving_recurs {α : Type*} [MeasurableSpace α]
    {f : α → α} {μ : Measure α} [IsFiniteMeasure μ] (h : MeasurePreserving f μ μ)
    {s : Set α} (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s :=
  h.conservative.ae_mem_imp_frequently_image_mem hs

#print axioms poincare_dividing_line
#print axioms measurePreserving_recurs

end EuclidsPath.PoincareRecurrence
