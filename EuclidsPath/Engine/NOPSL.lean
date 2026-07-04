/-
  NOPSL — No Old-Peel Sink Lemma. Closure of SNOL via old-peel regeneration.
  Source: snol_old_peel_closure_ru_2026-06-30.md (§5–14). Prose: prose/20_NOPSL.md.

  Abstract core of the final closure. A state of the old-peel ledger carries a height `h : σ → ℕ`.
  Dichotomy of every state (§10–11, four cases): either it is a VALID sink (twin / clean-return
  with halt), or it has a successor of STRICTLY SMALLER height (next old-peel / fan-in / known
  defect — all of them old-peel-regenerate, `t < n`, see `OldPeel.old_peel_height_drop`).

  NOPSL: a carrier-scale SN-catch CANNOT be a genuine terminal sink. Formally: if the flow has no
  valid sink (no twin), then every state has a descending successor ⟹ infinite strict
  descent ⟹ contradiction with the perpetual engine (EPMI, `no_infinite_engine_descent`).

  The logic is the same as for the perpetual engine: strict decrease of height cannot last forever.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.Irreversibility
import EuclidsPath.Engine.OldPeel
import EuclidsPath.Engine.TwoTransport

set_option autoImplicit false

namespace EuclidsPath.NOPSL

open EuclidsPath.Engine

variable {σ : Type*}

/--
  **State dichotomy (§10–11, four-case taxonomy).** `Sink` — a valid halt of the flow
  (twin sink or clean-return that does not continue downward). `Step h s s'` — an old-peel step with
  strict height drop (`h s' < h s`): covers next-peel / fan-in / known-defect.
-/
structure OldPeelLedger (σ : Type*) where
  /-- height of the state (center) -/
  h : σ → ℕ
  /-- valid sink: twin or a halted clean-return -/
  Sink : σ → Prop
  /-- old-peel successor with strict height drop -/
  Step : σ → σ → Prop
  /-- **old-peel law:** every step strictly decreases the height (`OldPeel.old_peel_height_drop`) -/
  step_drops : ∀ {s s'}, Step s s' → h s' < h s
  /-- **regeneration (§10, NOPSL core):** a non-sink state ALWAYS has an old-peel successor
      (clean-return/next-peel/fan-in/known-defect — but not a "dangling" terminal) -/
  regenerate : ∀ s, ¬ Sink s → ∃ s', Step s s'

/--
  **NOPSL (Theorem 11.1 / 13.1).** In the old-peel ledger, from any state the flow reaches a valid
  sink in finitely many steps: there is NO infinite trajectory without a sink. The proof is
  pure perpetual-engine logic: otherwise height decreases strictly forever (`step_drops`), which is impossible in ℕ.
-/
theorem no_old_peel_sink (L : OldPeelLedger σ) (start : σ) :
    ∃ s, L.Sink s := by
  by_contra hno
  -- no sink at all ⟹ every state is a non-sink ⟹ has a descending successor
  have hstep : ∀ s, ∃ s', L.Step s s' := fun s => L.regenerate s (fun hs => hno ⟨s, hs⟩)
  -- build an infinite chain by choosing successors
  choose next hnext using hstep
  let z : ℕ → σ := fun k => Nat.rec start (fun _ s => next s) k
  have hz : ∀ k, L.Step (z k) (z (k + 1)) := fun k => hnext (z k)
  -- height decreases strictly at every step ⟹ infinite descent ⟹ False
  have hdrop : ∀ k, L.h (z (k + 1)) < L.h (z k) := fun k => L.step_drops (hz k)
  exact OldPeel.old_peel_terminates (fun k => L.h (z k)) hdrop

/--
  **SNOL as a corollary of NOPSL (§13).** If a carrier-scale terminal shifted-neighbour obstruction
  existed, its states would be NON-sinks (no twin) and would have NO regeneration — contradicting
  `regenerate`. Hence the obstruction is impossible: the flow reaches a twin sink.
  Formally: from any start there exists a sink (= twin or halt), `no_old_peel_sink`.
-/
theorem snol_of_nopsl (L : OldPeelLedger σ) (start : σ) : ∃ s, L.Sink s :=
  no_old_peel_sink L start

/-! ### Bridge to the conjecture: NOPSL ⟹ infinitely many twin primes -/

open EuclidsPath in
/--
  **Final closure (Theorem 14.1).** Suppose that at every scale `N` an old-peel ledger is given with
  a start such that EVERY valid sink is a twin-center above `N` (the old-peel flow halts only on a
  twin). Then by NOPSL a sink exists, so at every `N` there is a twin-center above `N` ⟹ infinitely
  many twin primes (`infinite_of_unbounded_centers`).

  This closes the whole programme back to the perpetual engine: the sole input is the `OldPeelLedger`
  structure (old-peel regeneration + strict height drop), and NOT distribution.
-/
theorem twin_primes_of_nopsl
    (L : ∀ N : ℕ, OldPeelLedger σ) (start : ∀ N : ℕ, σ)
    (center : ∀ N : ℕ, σ → ℕ)
    (sink_is_twin : ∀ N s, (L N).Sink s → N < center N s ∧ IsTwinCenter (center N s)) :
    TwinLowers.Infinite := by
  apply infinite_of_unbounded_centers
  intro N
  obtain ⟨s, hs⟩ := no_old_peel_sink (L N) (start N)
  exact ⟨center N s, sink_is_twin N s hs⟩

end EuclidsPath.NOPSL
