/-
  Step00 clean/boundary split — исправление разрыва «sink-is-clean».
  Источник: step00_clean_graph_boundary_exit_fix_ru_2026-06-30.md. Проза: prose/24_CleanGraph.md.

  Разрыв (RESULTS_descent_gap): спуск из clean-старта проскакивает к unclean малому twin (18 →
  (107,109)), к которому `clean_twin_above` неприменима. Исправление автора: sink определяется
  ТОЛЬКО в clean-графе. Спуск к `n ∉ Ω_A` — это BoundaryExit (не sink), идёт в defect/old-peel.

  Здесь формализована ДОКАЗУЕМАЯ clean-часть:
    • active_edge_clean_or_boundary — любое active-ребро либо clean, либо boundary;
    • clean_sink_is_twin — clean-sink (нет clean-active-ребра, и не-twin даёт active) ⟹ twin;
    • clean_center_outcome — clean центр: twin / clean-edge / boundary / sink.
  Это корректно отсекает unclean малые twin от sink.

  Честная граница (числа RESULTS_clean_graph: 59% clean центров имеют ВСЕ рёбра в boundary):
  clean-граф НЕ самодостаточен ⟹ вся нагрузка уходит в `BoundaryExit` ⟹ единственный открытый
  вход — `boundary_exit_regenerates` (boundary-state регенерирует / даёт engine). Здесь он — явная
  гипотеза, НЕ доказан.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false

namespace EuclidsPath.CleanGraph

open EuclidsPath.Residuals

variable {A : ℕ}
set_option linter.unusedVariables false

/-- `Clean A m`: ни один простой `q ≤ A` не делит ни одну сторону `6m−1`, `6m+1` (в ℕ). -/
def Clean (A m : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1))

/-- `ActiveEdge A m n`: есть active-ребро `m→n` (абстрактно — существование меньшего центра-цели). -/
def ActiveEdge (A m n : ℕ) : Prop := True ∧ n < m  -- носитель: меньший центр (детали — в OldPeel/cofactor)

/-- Clean-ребро: `m,n` оба clean. -/
def CleanActiveEdge (A m n : ℕ) : Prop := Clean A m ∧ Clean A n ∧ ActiveEdge A m n

/-- Boundary-exit: `m` clean, `n` НЕ clean. Это НЕ sink — вход в defect-ledger. -/
def BoundaryExit (A m n : ℕ) : Prop := Clean A m ∧ ActiveEdge A m n ∧ ¬ Clean A n

/--
  **Любое active-ребро из clean-центра — clean или boundary (§2).** Полная дихотомия по `Clean A n`.
-/
theorem active_edge_clean_or_boundary {m n : ℕ}
    (hclean : Clean A m) (hedge : ActiveEdge A m n) :
    CleanActiveEdge A m n ∨ BoundaryExit A m n := by
  by_cases hn : Clean A n
  · exact Or.inl ⟨hclean, hn, hedge⟩
  · exact Or.inr ⟨hclean, hedge, hn⟩

/-- Clean-sink: clean центр без active-ребра вообще (unclean-цель НЕ считается sink). -/
def CleanSink (A m : ℕ) : Prop := Clean A m ∧ ¬ ∃ n, ActiveEdge A m n

/--
  **Clean-sink ⟹ twin (Лемма 3.1, исправленная).** Если `m` clean, обе стороны `≥2`, `<A²`, и
  у `m` нет active-ребра (нет составной стороны ⟹ обе простые), то `m` — twin. Использует
  `sink_is_twin` (old-free + `<A²` ⟹ простое). -/
theorem clean_sink_is_twin {m : ℕ}
    (hlo : 2 ≤ 6 * m - 1) (hhi : 2 ≤ 6 * m + 1)
    (hlo2 : 6 * m - 1 < A * A) (hhi2 : 6 * m + 1 < A * A)
    (hsink : CleanSink A m) : TwinCenterZ m := by
  -- clean + < A² ⟹ обе стороны простые (sink_is_twin); active-ребро не используется напрямую
  apply sink_is_twin hlo hhi hlo2 hhi2
  intro q hq hqA hd
  exact hsink.1 q hq hqA hd

/--
  **Исход clean-центра (§5).** Clean центр — это `twin` ∨ clean-edge ∨ boundary-exit ∨ clean-sink.
  Unclean малый twin (18) попадает в boundary, НЕ в twin. -/
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
  **Clean-sink выше M₀ (§4, через `clean_twin_above`).** Если `6M₀+1 < A`, `m` clean и twin, то
  `m > M₀`. Это уже доказано в `Residuals.clean_twin_above` — здесь мост. -/
theorem clean_sink_above {M0 m : ℕ} (hA : 6 * M0 + 1 < A) (hm : 1 ≤ m)
    (hcl : Clean A m) (htwin : TwinCenterZ m) : M0 < m := by
  apply Residuals.clean_twin_above hA hm _ htwin
  -- мост ℕ-делимость → ℤ-делимость сторон
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
