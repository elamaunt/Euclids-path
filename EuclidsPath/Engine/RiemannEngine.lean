/-
  RiemannEngine — RH от противного к двигателю, аккуратная форма: `¬RH → OffCriticalZero → Engine`.
  Источник: EuclidsPath_boundary_..._patch (RH-to-engine brick).
  Проза: prose/30_RiemannBranch.md (раздел «RH → OffCriticalZero → Engine, чистая форма»).

  ИДЕЯ. Разделить контрапозицию на ЧИСТУЮ часть (`¬RH → OffCriticalZero`, только отрицание
  определения mathlib-RH) и МОСТ (`OffCriticalZero → Engine`, аналитический вход). Локализация нуля в
  полосу: верх (`Re < 1`) — из mathlib (`riemannZeta_ne_zero_of_one_le_re`, PNT-уровень, ИМПОРТ, не
  ядро), низ (`Re > 0`) — из явного входа `TrivialBelowZeroClassification`.

  ЗДЕСЬ ДОКАЗАНО (чистая логика + один mathlib-lemma, std аксиомы, без sorry):
    * `offCriticalZero_of_not_RH` / `not_RH_of_offCriticalZero` / `not_RH_iff_nonempty_offCriticalZero`
      — эквивалентность `¬RH ⟺ ∃ off-critical нуль` (только push_neg на mathlib-RH);
    * `offCriticalZero_re_lt_one` (mathlib), `offCriticalZero_re_pos` (вход), локализация в полосу;
    * `engine_of_not_RH(_in_strip)` и `RH_of_no_engine(_in_strip)` — контрапозиция обе стороны.

  ЧЕСТНАЯ ГРАНИЦА. RH НЕ доказана: `RH_of_no_engine` требует мост `EngineBridge` И `¬Engine`. Мосты
  (`EngineBridge`, `CriticalStripEngineBridge`) и `TrivialBelowZeroClassification` — недоказанные входы.
  `Engine` — параметр (не свободная утечка: `Engine := True` даёт `¬Engine = False`, RH бесплатно НЕ
  выходит). `Step00` остаётся `sorry`.
-/
import Mathlib
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option autoImplicit false

namespace EuclidsPath.RiemannEngine

open Complex

/-- Нетривиальный нуль в смысле mathlib-RH: `ζ s = 0`, не тривиальный (`≠ -2(n+1)`), `s ≠ 1`. -/
structure NontrivialZetaZero where
  s : ℂ
  zero : riemannZeta s = 0
  nontrivial : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)
  not_one : s ≠ 1

/-- Контрпример к RH (в смысле mathlib): нетривиальный нуль вне критической прямой. -/
structure OffCriticalZero extends NontrivialZetaZero where
  off_line : s.re ≠ (1 / 2 : ℝ)

/-- Контрпример, дополнительно локализованный в критическую полосу. -/
structure CriticalStripOffLineZero extends OffCriticalZero where
  re_pos : 0 < s.re
  re_lt_one : s.re < 1

/-- **Аналитический вход.** Всякий нуль с `Re ≤ 0` тривиален (`-2(n+1)`). Функциональное уравнение;
    mathlib даёт лишь ЗНАЧЕНИЯ тривиальных нулей, не эту классификацию. НЕ доказано здесь. -/
def TrivialBelowZeroClassification : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → s.re ≤ 0 → ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

/-! ## Чистая логика: `¬RH` даёт off-critical нуль -/

/-- **`offCriticalZero_of_not_RH` — ДОКАЗАНА (чистый push_neg на mathlib-RH).** -/
theorem offCriticalZero_of_not_RH (hNotRH : ¬ RiemannHypothesis) :
    Nonempty OffCriticalZero := by
  classical
  unfold RiemannHypothesis at hNotRH
  push_neg at hNotRH
  rcases hNotRH with ⟨s, hzero, hnontrivial, hnot_one, hoff⟩
  -- push_neg даёт hnontrivial : ∀ n, s ≠ -2*(n+1); поле ждёт ¬∃. Мостик:
  refine ⟨{ s := s, zero := hzero, nontrivial := ?_, not_one := hnot_one, off_line := hoff }⟩
  rintro ⟨n, hn⟩; exact hnontrivial n hn

/-- **`not_RH_of_offCriticalZero` — ДОКАЗАНА.** Off-critical нуль опровергает RH. -/
theorem not_RH_of_offCriticalZero (Z : OffCriticalZero) : ¬ RiemannHypothesis := by
  intro hRH
  exact Z.off_line (hRH Z.s Z.zero Z.nontrivial Z.not_one)

/-- **`not_RH_iff_nonempty_offCriticalZero` — ДОКАЗАНА (эквивалентность).** -/
theorem not_RH_iff_nonempty_offCriticalZero :
    ¬ RiemannHypothesis ↔ Nonempty OffCriticalZero := by
  constructor
  · exact offCriticalZero_of_not_RH
  · intro h; rcases h with ⟨Z⟩; exact not_RH_of_offCriticalZero Z

/-! ## Локализация в критическую полосу -/

/-- **`offCriticalZero_re_pos` — ДОКАЗАНА (из входа-классификации).** Нетривиальный нуль: `Re > 0`. -/
theorem offCriticalZero_re_pos (hBelow : TrivialBelowZeroClassification) (Z : OffCriticalZero) :
    0 < Z.s.re := by
  have hnot_le : ¬ Z.s.re ≤ 0 := fun hle => Z.nontrivial (hBelow Z.s Z.zero hle)
  exact lt_of_not_ge hnot_le

/-- **`offCriticalZero_re_lt_one` — ЗАМЫКАЕТСЯ mathlib-АНАЛИТИКОЙ (не ядром).** `Re < 1` из
    `riemannZeta_ne_zero_of_one_le_re` (неисчезание дзеты на `Re ≥ 1` — PNT-уровень, ИМПОРТ). -/
theorem offCriticalZero_re_lt_one (Z : OffCriticalZero) : Z.s.re < 1 := by
  have hnot_le : ¬ 1 ≤ Z.s.re := fun hle => (riemannZeta_ne_zero_of_one_le_re hle) Z.zero
  exact lt_of_not_ge hnot_le

/-- Апгрейд off-critical нуля до нуля-в-полосе (при классификации `Re ≤ 0`). -/
def criticalStripOffLineZero_of_offCriticalZero
    (hBelow : TrivialBelowZeroClassification) (Z : OffCriticalZero) : CriticalStripOffLineZero :=
{ s := Z.s, zero := Z.zero, nontrivial := Z.nontrivial, not_one := Z.not_one,
  off_line := Z.off_line, re_pos := offCriticalZero_re_pos hBelow Z,
  re_lt_one := offCriticalZero_re_lt_one Z }

/-- **`criticalStripOffLineZero_of_not_RH` — ДОКАЗАНА.** `¬RH` + классификация ⟹ контрпример в полосе. -/
theorem criticalStripOffLineZero_of_not_RH
    (hBelow : TrivialBelowZeroClassification) (hNotRH : ¬ RiemannHypothesis) :
    Nonempty CriticalStripOffLineZero := by
  rcases offCriticalZero_of_not_RH hNotRH with ⟨Z⟩
  exact ⟨criticalStripOffLineZero_of_offCriticalZero hBelow Z⟩

/-! ## Мосты к двигателю (входы) -/

variable (Engine : Prop)

/-- **Мост (вход):** off-critical нуль ⟹ двигатель. НЕ доказан. -/
def EngineBridge : Prop := OffCriticalZero → Engine

/-- **Strip-мост (вход):** off-critical нуль В ПОЛОСЕ ⟹ двигатель. НЕ доказан. -/
def CriticalStripEngineBridge : Prop := CriticalStripOffLineZero → Engine

/-- **`engine_of_not_RH` — ДОКАЗАНА (при мосту).** `¬RH → Engine`. -/
theorem engine_of_not_RH (bridge : EngineBridge Engine) (hNotRH : ¬ RiemannHypothesis) : Engine := by
  rcases offCriticalZero_of_not_RH hNotRH with ⟨Z⟩; exact bridge Z

/-- **`engine_of_not_RH_in_strip` — ДОКАЗАНА (при strip-мосту + классификации).** -/
theorem engine_of_not_RH_in_strip (hBelow : TrivialBelowZeroClassification)
    (bridge : CriticalStripEngineBridge Engine) (hNotRH : ¬ RiemannHypothesis) : Engine := by
  rcases criticalStripOffLineZero_of_not_RH hBelow hNotRH with ⟨Z⟩; exact bridge Z

/-- **`RH_of_no_engine` — ДОКАЗАНА (условная RH).** Мост + `¬Engine` ⟹ mathlib-RH. -/
theorem RH_of_no_engine (bridge : EngineBridge Engine) (hNoEngine : ¬ Engine) : RiemannHypothesis := by
  by_contra hNotRH; exact hNoEngine (engine_of_not_RH Engine bridge hNotRH)

/-- **`RH_of_no_engine_in_strip` — ДОКАЗАНА (условная RH, strip).** -/
theorem RH_of_no_engine_in_strip (hBelow : TrivialBelowZeroClassification)
    (bridge : CriticalStripEngineBridge Engine) (hNoEngine : ¬ Engine) : RiemannHypothesis := by
  by_contra hNotRH; exact hNoEngine (engine_of_not_RH_in_strip Engine hBelow bridge hNotRH)

end EuclidsPath.RiemannEngine
