/-
  Step00 clean/boundary split — fixing the «sink-is-clean» gap.
  Source: step00_clean_graph_boundary_exit_fix_ru_2026-06-30.md. Prose: prose/24_CleanGraph.md.

  The gap (RESULTS_descent_gap): descent from a clean start jumps to an unclean small twin (18 →
  (107,109)), to which `clean_twin_above` does not apply. Author's fix: a sink is defined
  ONLY in the clean graph. Descent to `n ∉ Ω_A` is a BoundaryExit (not a sink); it goes into defect/old-peel.

  Formalised here is the PROVABLE clean part:
    • active_edge_clean_or_boundary — every active edge is either clean or boundary;
    • clean_sink_is_twin — clean-sink (no clean active edge, and a non-twin yields an active edge) ⟹ twin;
    • clean_center_outcome — clean center: twin / clean-edge / boundary / sink.
  This correctly excludes unclean small twins from sinks.

  Honest boundary (RESULTS_clean_graph figures: 59% of clean centers have ALL edges in boundary):
  the clean graph is NOT self-sufficient ⟹ all load goes into `BoundaryExit` ⟹ the only open
  entry point is `boundary_exit_regenerates` (boundary-state regenerates / yields engine). Here it is an explicit
  hypothesis, NOT proved.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false

namespace EuclidsPath.CleanGraph

open EuclidsPath.Residuals

variable {A : ℕ}
set_option linter.unusedVariables false

/-- `Clean A m`: no prime `q ≤ A` divides either side `6m−1`, `6m+1` (in ℕ). -/
def Clean (A m : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1))

/-- `ActiveEdge A m n`: there is an active edge `m→n` (abstractly — existence of a smaller target center). -/
def ActiveEdge (A m n : ℕ) : Prop := True ∧ n < m  -- carrier: the smaller center (details in OldPeel/cofactor)

/-- Clean edge: `m,n` are both clean. -/
def CleanActiveEdge (A m n : ℕ) : Prop := Clean A m ∧ Clean A n ∧ ActiveEdge A m n

/-- Boundary-exit: `m` clean, `n` NOT clean. This is NOT a sink — entry into the defect ledger. -/
def BoundaryExit (A m n : ℕ) : Prop := Clean A m ∧ ActiveEdge A m n ∧ ¬ Clean A n

/--
  **Every active edge from a clean center is clean or boundary (§2).** Full dichotomy on `Clean A n`.
-/
theorem active_edge_clean_or_boundary {m n : ℕ}
    (hclean : Clean A m) (hedge : ActiveEdge A m n) :
    CleanActiveEdge A m n ∨ BoundaryExit A m n := by
  by_cases hn : Clean A n
  · exact Or.inl ⟨hclean, hn, hedge⟩
  · exact Or.inr ⟨hclean, hedge, hn⟩

/-- Clean-sink: a clean center with no active edge at all (an unclean target does NOT count as a sink). -/
def CleanSink (A m : ℕ) : Prop := Clean A m ∧ ¬ ∃ n, ActiveEdge A m n

/--
  **Clean-sink ⟹ twin (Lemma 3.1, corrected).** If `m` is clean, both sides `≥2`, `<A²`, and
  `m` has no active edge (no composite side ⟹ both are prime), then `m` is a twin. Uses
  `sink_is_twin` (old-free + `<A²` ⟹ prime). -/
theorem clean_sink_is_twin {m : ℕ}
    (hlo : 2 ≤ 6 * m - 1) (hhi : 2 ≤ 6 * m + 1)
    (hlo2 : 6 * m - 1 < A * A) (hhi2 : 6 * m + 1 < A * A)
    (hsink : CleanSink A m) : TwinCenterZ m := by
  -- clean + < A² ⟹ both sides are prime (sink_is_twin); the active edge is not used directly
  apply sink_is_twin hlo hhi hlo2 hhi2
  intro q hq hqA hd
  exact hsink.1 q hq hqA hd

/--
  **Outcome of a clean center (§5).** A clean center is `twin` ∨ clean-edge ∨ boundary-exit ∨ clean-sink.
  An unclean small twin (18) falls into boundary, NOT into twin. -/
theorem clean_center_outcome {m : ℕ} (hclean : Clean A m) :
    TwinCenterZ m
    ∨ (∃ n, CleanActiveEdge A m n)
    ∨ (∃ n, BoundaryExit A m n)
    ∨ CleanSink A m := by
  by_cases htwin : TwinCenterZ m
  · exact Or.inl htwin
  · by_cases hedge : ∃ n, ActiveEdge A m n
    · obtain ⟨n, hn⟩ := hedge
      rcases active_edge_clean_or_boundary hclean hn with hc | hb
      · exact Or.inr (Or.inl ⟨n, hc⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨n, hb⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hclean, hedge⟩))

/--
  **Clean-sink above M₀ (§4, via `clean_twin_above`).** If `6M₀+1 < A`, `m` is clean and twin, then
  `m > M₀`. This is already proved in `Residuals.clean_twin_above` — this is a bridge. -/
theorem clean_sink_above {M0 m : ℕ} (hA : 6 * M0 + 1 < A) (hm : 1 ≤ m)
    (hcl : Clean A m) (htwin : TwinCenterZ m) : M0 < m := by
  apply Residuals.clean_twin_above hA hm _ htwin
  -- bridge: ℕ-divisibility → ℤ-divisibility of sides
  intro q hq hqA hd
  refine hcl q hq hqA ?_
  have h1 : ((6 * m - 1 : ℕ) : ℤ) = 6 * (m : ℤ) - 1 := by
    have : 1 ≤ 6 * m := by omega
    push_cast [Nat.cast_sub this]; ring
  have h2 : ((6 * m + 1 : ℕ) : ℤ) = 6 * (m : ℤ) + 1 := by push_cast; ring
  rcases hd with h | h
  · exact Or.inl (by rw [← h1] at h; exact_mod_cast h)
  · exact Or.inr (by rw [← h2] at h; exact_mod_cast h)

end EuclidsPath.CleanGraph
