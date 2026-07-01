/-
  RiemannImpossibleEngine — ИСПРАВЛЕННОЕ ядро (Parts I–VII).
  Три починки против оригинального кирпича:
    (1) push_neg даёт ∀n, s≠… — мостик к полю ¬∃ (как в RiemannEngine.lean);
    (2) nextU: .choose вместо rcases (Prop→Type элиминация запрещена в noncomputable def);
    (3) ПЕРЕИСПОЛЬЗУЕМ реповый ClosedUniverse.ClosedPaidDynamics / no_infinite_closed_paid_run
        вместо дублирования (кирпич определял свою копию).
-/
import EuclidsPath.Engine.ClosedUniverse
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option autoImplicit false

namespace EuclidsPath.RiemannImpossibleEngine

open Complex EuclidsPath.ClosedUniverse

/-! ## RH counterexample objects -/

structure NontrivialZetaZero where
  s : ℂ
  zero : riemannZeta s = 0
  nontrivial : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)
  not_one : s ≠ 1

structure OffCriticalZero extends NontrivialZetaZero where
  off_line : s.re ≠ (1 / 2 : ℝ)

structure CriticalStripOffLineZero extends OffCriticalZero where
  re_pos : 0 < s.re
  re_lt_one : s.re < 1

def TrivialBelowZeroClassification : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → s.re ≤ 0 → ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

/-! ## Pure logic: ¬RH gives off-critical zero -/

theorem offCriticalZero_of_not_RH (hNotRH : ¬ RiemannHypothesis) :
    Nonempty OffCriticalZero := by
  classical
  unfold RiemannHypothesis at hNotRH
  push_neg at hNotRH
  rcases hNotRH with ⟨s, hzero, hnontrivial, hnot_one, hoff⟩
  refine ⟨{ s := s, zero := hzero, nontrivial := ?_, not_one := hnot_one, off_line := hoff }⟩
  rintro ⟨n, hn⟩; exact hnontrivial n hn

theorem not_RH_of_offCriticalZero (Z : OffCriticalZero) : ¬ RiemannHypothesis := by
  intro hRH; exact Z.off_line (hRH Z.s Z.zero Z.nontrivial Z.not_one)

theorem not_RH_iff_nonempty_offCriticalZero :
    ¬ RiemannHypothesis ↔ Nonempty OffCriticalZero :=
  ⟨offCriticalZero_of_not_RH, fun ⟨Z⟩ => not_RH_of_offCriticalZero Z⟩

/-! ## Localization to the critical strip -/

theorem offCriticalZero_re_pos (hBelow : TrivialBelowZeroClassification) (Z : OffCriticalZero) :
    0 < Z.s.re :=
  lt_of_not_ge (fun hle => Z.nontrivial (hBelow Z.s Z.zero hle))

theorem offCriticalZero_re_lt_one (Z : OffCriticalZero) : Z.s.re < 1 :=
  lt_of_not_ge (fun hle => (riemannZeta_ne_zero_of_one_le_re hle) Z.zero)

def criticalStripOffLineZero_of_offCriticalZero
    (hBelow : TrivialBelowZeroClassification) (Z : OffCriticalZero) : CriticalStripOffLineZero :=
{ s := Z.s, zero := Z.zero, nontrivial := Z.nontrivial, not_one := Z.not_one,
  off_line := Z.off_line, re_pos := offCriticalZero_re_pos hBelow Z,
  re_lt_one := offCriticalZero_re_lt_one Z }

theorem criticalStripOffLineZero_of_not_RH
    (hBelow : TrivialBelowZeroClassification) (hNotRH : ¬ RiemannHypothesis) :
    Nonempty CriticalStripOffLineZero := by
  rcases offCriticalZero_of_not_RH hNotRH with ⟨Z⟩
  exact ⟨criticalStripOffLineZero_of_offCriticalZero hBelow Z⟩

/-! ## Eternal Riemann engine (переиспользует реповый ClosedPaidDynamics) -/

structure EternalRiemannEngine (Z : CriticalStripOffLineZero) where
  State : Type
  Step : State → State → Prop
  dyn : ClosedPaidDynamics State Step
  path : ℕ → State
  start_in_universe : dyn.Universe (path 0)
  step : ∀ k, Step (path k) (path (k + 1))

/-- **`no_eternalRiemannEngine` — ДОКАЗАНА безусловно** через реповый `no_infinite_closed_paid_run`. -/
theorem no_eternalRiemannEngine (Z : CriticalStripOffLineZero) :
    ¬ Nonempty (EternalRiemannEngine Z) := by
  rintro ⟨E⟩
  exact no_infinite_closed_paid_run E.dyn ⟨E.path, E.start_in_universe, E.step⟩

/-! ## RiemannEngineFactory -/

structure RiemannEngineFactory (Z : CriticalStripOffLineZero) where
  State : Type
  Step : State → State → Prop
  dyn : ClosedPaidDynamics State Step
  seed : State
  seed_in_universe : dyn.Universe seed
  next : ∀ x, dyn.Universe x → ∃ y, Step x y

/-- Успешный шаг на legal-подтипе (ИСПРАВЛЕНО: `.choose`, не `rcases`). -/
noncomputable def RiemannEngineFactory.nextU {Z : CriticalStripOffLineZero}
    (F : RiemannEngineFactory Z) (x : {s : F.State // F.dyn.Universe s}) :
    {y : {s : F.State // F.dyn.Universe s} // F.Step x.1 y.1} :=
  let hy : F.Step x.1 (F.next x.1 x.2).choose := (F.next x.1 x.2).choose_spec
  ⟨⟨(F.next x.1 x.2).choose, F.dyn.closed x.2 hy⟩, hy⟩

noncomputable def RiemannEngineFactory.pathU {Z : CriticalStripOffLineZero}
    (F : RiemannEngineFactory Z) : ℕ → {s : F.State // F.dyn.Universe s}
  | 0 => ⟨F.seed, F.seed_in_universe⟩
  | n + 1 => (F.nextU (F.pathU n)).1

theorem RiemannEngineFactory.pathU_step {Z : CriticalStripOffLineZero}
    (F : RiemannEngineFactory Z) :
    ∀ n, F.Step (F.pathU n).1 (F.pathU (n + 1)).1 :=
  fun n => (F.nextU (F.pathU n)).2

noncomputable def eternalEngine_of_factory {Z : CriticalStripOffLineZero}
    (F : RiemannEngineFactory Z) : EternalRiemannEngine Z :=
{ State := F.State, Step := F.Step, dyn := F.dyn,
  path := fun n => (F.pathU n).1,
  start_in_universe := (F.pathU 0).2,
  step := F.pathU_step }

/-- **`no_riemannEngineFactory` — ДОКАЗАНА безусловно.** Off-critical zero в полосе НЕ может породить
    factory невозможного closed-paid двигателя. -/
theorem no_riemannEngineFactory (Z : CriticalStripOffLineZero) :
    ¬ Nonempty (RiemannEngineFactory Z) := by
  rintro ⟨F⟩
  exact no_eternalRiemannEngine Z ⟨eternalEngine_of_factory F⟩

/-! ## The Riemann bridge -/

/-- **Мост (вход):** каждый off-critical zero в полосе порождает factory. НЕ доказан. -/
def CriticalStripRiemannEngineBridge : Prop :=
  ∀ Z : CriticalStripOffLineZero, Nonempty (RiemannEngineFactory Z)

/-- **`RH_of_criticalStripRiemannEngineBridge` — ДОКАЗАНА (главная теорема, условная RH).**
    Классификация + мост ⟹ mathlib-RH. Без отдельного `¬Engine` входа: `no_riemannEngineFactory`
    безусловна. -/
theorem RH_of_criticalStripRiemannEngineBridge
    (hBelow : TrivialBelowZeroClassification) (bridge : CriticalStripRiemannEngineBridge) :
    RiemannHypothesis := by
  by_contra hNotRH
  rcases criticalStripOffLineZero_of_not_RH hBelow hNotRH with ⟨Z⟩
  exact no_riemannEngineFactory Z (bridge Z)

end EuclidsPath.RiemannImpossibleEngine
