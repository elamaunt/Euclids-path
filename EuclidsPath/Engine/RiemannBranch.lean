/-
  Побочная ветка: гипотеза Римана (RH) ОТ ПРОТИВНОГО через двигатель Евклида.
  Проза: prose/28_RiemannBranch.md.

  ЧЕСТНАЯ РАМКА (важно): RH НЕ следует логически из бесконечности близнецов напрямую — это
  независимые утверждения. Здесь строится КОРРЕКТНАЯ контрапозиция через МЕХАНИЗМ (двигатель),
  тот же, что замыкает близнецов.

  ВНЕШНЕЕ = ИЗ MATHLIB. `RiemannHypothesis` берётся из mathlib (НЕ самодельный def): официальная
  формулировка через нули `riemannZeta`, исключая тривиальные нули `-2(n+1)` и `s = 1`. Расположение
  нулей тоже из mathlib: `riemannZeta_ne_zero_of_one_le_re` (нет нулей при `Re ≥ 1`).

  Что доказано / что вход:
    • `Re ρ ≥ 1` невозможно для нуля — ДОКАЗАНО через mathlib (`riemannZeta_ne_zero_of_one_le_re`);
    • `Re ρ ≤ 0` ⟹ ρ тривиальный (`-2(n+1)`) — АНАЛИТИЧЕСКИЙ ВХОД `TrivialBelowZeroClassification`
      (функциональное уравнение; mathlib даёт значения тривиальных нулей, но не классификацию
      «все нули с Re ≤ 0 тривиальны» — это явный помеченный вход);
    • полоса `0 < Re ρ < 1` с `Re ≠ 1/2` ⟹ вечный двигатель — мост `EngineBridge` (открыт, как `pump`);
    • вечного двигателя нет — ДОКАЗАНО (`no_infinite_descent`).
  RH-ветка условна на `EngineBridge` + `TrivialBelowZeroClassification`. Оба — явные входы, не аксиомы.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.TwoGap

set_option autoImplicit false

namespace EuclidsPath.RiemannBranch

open Complex EuclidsPath.Engine

/-- Нетривиальный нуль дзеты в смысле mathlib-RH: `ζ ρ = 0`, ρ не тривиальный нуль, `ρ ≠ 1`. -/
def NontrivialZeroM (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1

/--
  **`no_zero_of_one_le_re` — ЗАМЫКАЕТСЯ mathlib-АНАЛИТИКОЙ (не ядром двигателя).** У дзеты нет нулей
  с `Re ρ ≥ 1`, значит любой нуль имеет `Re ρ < 1`.

  ⚠️ ЧЕСТНАЯ ОГОВОРКА (по результату аудита): «доказано» здесь означает «выводимо из mathlib», а НЕ
  «выводимо из нашего ядра». Единственный шаг — импортированная лемма `riemannZeta_ne_zero_of_one_le_re`,
  то есть неисчезание дзеты на `Re ≥ 1` — **аналитический результат PNT-уровня**, доказанный в mathlib,
  а не нами. Он лишь ОГРАНИЧИВАЕТ полосу (`Re < 1`); он НЕ помещает нуль на `Re = 1/2` и НЕ закрывает ни
  один открытый мост. Это не утечка RH, но и не самодостаточная часть двигателя. -/
theorem no_zero_of_one_le_re {ρ : ℂ} (hz : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  push_neg at h
  exact riemannZeta_ne_zero_of_one_le_re h hz

/--
  **Аналитический вход `TrivialBelowZeroClassification`.** Всякий нуль с `Re ρ ≤ 0` тривиален
  (`ρ = -2(n+1)`). Это классика (функциональное уравнение), но mathlib даёт лишь ЗНАЧЕНИЯ тривиальных
  нулей (`riemannZeta_neg_two_mul_nat_add_one`), а НЕ обратную классификацию. Поэтому — явный вход,
  а НЕ самодельная RH. -/
def TrivialBelowZeroClassification : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 0 → ∃ n : ℕ, ρ = -2 * (n + 1)

/--
  **`nontrivialZero_in_strip` — ЛОКАЛИЗАЦИЯ В ПОЛОСУ (mathlib-аналитика `Re<1` + вход по `Re≤0`).**
  Нетривиальный нуль лежит строго в критической полосе `0 < Re ρ < 1`.

  ⚠️ Обе границы — НЕ из ядра двигателя: верхняя (`Re < 1`) держится на mathlib-аналитике PNT-уровня
  (см. `no_zero_of_one_le_re`), нижняя (`Re > 0`) — на явном аналитическом входе
  `TrivialBelowZeroClassification`. Ни та, ни другая не помещает нуль на `1/2`. -/
theorem nontrivialZero_in_strip (hClass : TrivialBelowZeroClassification)
    {ρ : ℂ} (hρ : NontrivialZeroM ρ) : 0 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨hz, hnt, _⟩ := hρ
  refine ⟨?_, no_zero_of_one_le_re hz⟩
  by_contra h
  push_neg at h                    -- ρ.re ≤ 0
  exact hnt (hClass ρ hz h)

/--
  **Мост двигателя (H_RH) — открытый узел ветки.** Нуль в полосе с `Re ≠ 1/2` ⟹ вечный двигатель:
  асимметрия даёт бесконечную clean-цепь строго убывающей высоты. НЕ доказан — аналитический вход. -/
def EngineBridge : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (A : ℕ) (H : ℕ → ℕ), 1 ≤ A ∧ ∀ t, DescentStep A (H t) (H (t + 1))

/--
  **RH (mathlib) из двух явных входов (условная теорема).** Если мост `EngineBridge` и классификация
  `TrivialBelowZeroClassification` даны, то выполняется mathlib-`RiemannHypothesis`: любой нетривиальный
  нуль имеет `Re = 1/2`. Механизм: нуль в полосе (доказано) с `Re ≠ 1/2` дал бы двигатель, которого нет
  (`no_infinite_descent`). Вся аналитика изолирована в двух входах; сам двигатель — доказанное ядро. -/
theorem riemannHypothesis_of_engine_bridge
    (hClass : TrivialBelowZeroClassification) (H_RH : EngineBridge) :
    RiemannHypothesis := by
  intro ρ hz htriv hne1
  -- собрать нетривиальность в смысле нашего предиката
  have hρ : NontrivialZeroM ρ := ⟨hz, htriv, hne1⟩
  obtain ⟨hpos, hlt⟩ := nontrivialZero_in_strip hClass hρ
  by_contra hne
  obtain ⟨A, Hgt, hA, hchain⟩ := H_RH ρ hz hpos hlt hne
  exact no_infinite_descent hA Hgt hchain

/--
  **Контрапозиция: ¬RH ⟹ двигатель ⟹ ⊥.** Если оба входа даны и mathlib-RH ложна, то существует
  вечный двигатель — противоречие с ядром. -/
theorem not_RH_gives_engine
    (hClass : TrivialBelowZeroClassification) (H_RH : EngineBridge) (hnotRH : ¬ RiemannHypothesis) :
    ∃ (A : ℕ) (H : ℕ → ℕ), 1 ≤ A ∧ ∀ t, DescentStep A (H t) (H (t + 1)) := by
  exact absurd (riemannHypothesis_of_engine_bridge hClass H_RH) hnotRH

/-! ### Связка с близнецами: один общий узел вместо двух -/

/--
  **Закон переноса двойки (абстрактно).** «Ядро переноса двойки держится» — УЖЕ доказано тождествами
  `Engine/TwoGap`. Здесь — абстрактная форма как посылка. -/
def TwoTransportLaw : Prop :=
  ∀ m a b v q r s : ℕ, 1 ≤ m → 6 * m - 1 = a * b * v → 6 * m + 1 = q * r * s →
    q * r * s = a * b * v + 2

/-- Закон переноса двойки ДОКАЗАН (это `det_law_rank33`). Не аксиома. -/
theorem twoTransportLaw_holds : TwoTransportLaw :=
  fun _ _ _ _ _ _ _ hm h1 h2 => det_law_rank33 hm h1 h2

/--
  **Узел-связка `TwoTransportBridge`.** Импликация: закон переноса двойки ⟹ EngineBridge. Нуль ζ вне
  `1/2` ломает перенос двойки и порождает вечный двигатель. Если ЭТО (+ классификация) доказано, RH
  следует из УЖЕ доказанного ядра (`TwoGap` + EPMI). -/
def TwoTransportBridge : Prop := TwoTransportLaw → EngineBridge

/--
  **RH (mathlib) из доказанного ядра + двух связок.** Если `TwoTransportBridge` и классификация даны,
  RH следует: `TwoTransportLaw` УЖЕ доказан, EPMI УЖЕ доказан. Открыты РОВНО `TwoTransportBridge` и
  `TrivialBelowZeroClassification` — обе явные, не аксиомы. -/
theorem riemannHypothesis_of_two_transport
    (hClass : TrivialBelowZeroClassification) (bridge : TwoTransportBridge) :
    RiemannHypothesis :=
  riemannHypothesis_of_engine_bridge hClass (bridge twoTransportLaw_holds)

end EuclidsPath.RiemannBranch
