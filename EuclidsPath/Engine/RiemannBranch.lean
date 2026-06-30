/-
  Побочная ветка: гипотеза Римана (RH) ОТ ПРОТИВНОГО через двигатель Евклида.
  Проза: prose/28_RiemannBranch.md.

  ЧЕСТНАЯ РАМКА (важно): RH НЕ следует логически из бесконечности близнецов напрямую — это
  независимые утверждения. Здесь строится КОРРЕКТНАЯ контрапозиция через МЕХАНИЗМ (двигатель),
  тот же, что замыкает близнецов:

    ¬RH  ⟺  ∃ нетривиальный нуль ρ с Re(ρ) ≠ 1/2
         ⟹  [мост H_RH, НЕ доказан]  нарушение переноса двойки / вечный двигатель
         ⟹  противоречие с `no_infinite_descent` (двигатель невозможен, ДОКАЗАНО)
    ∴ RH.

  Логическая форма ровно как у близнецов: `(¬P ⟹ Engine) ∧ ¬Engine ⟹ P`.

  Здесь RH формализована как УСЛОВНАЯ теорема на явном мосту `H_RH` (помечен открытым, как `pump`).
  `riemannZeta` — из mathlib. Мост — единственный открытый узел этой ветки.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.TwoGap

set_option autoImplicit false

namespace EuclidsPath.RiemannBranch

open Complex EuclidsPath.Engine

/-- Нетривиальный нуль дзеты: `ζ ρ = 0` в критической полосе `0 < Re ρ < 1`. -/
def NontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- Гипотеза Римана: каждый нетривиальный нуль лежит на критической прямой `Re = 1/2`. -/
def RiemannHypothesis : Prop := ∀ ρ : ℂ, NontrivialZero ρ → ρ.re = 1 / 2

/--
  **Мост двигателя (H_RH) — ЕДИНСТВЕННЫЙ открытый узел ветки.** Если существует нетривиальный нуль
  с `Re ≠ 1/2`, то возникает вечный двигатель Евклида: асимметрия `Re ≠ 1/2` даёт «бесплатное»
  направленное перекачивание массы вдоль descent (нарушение переноса двойки), т.е. бесконечную
  clean-цепь строго убывающей высоты, не достигающую дна.

  Формально (абстрактно): нуль вне `1/2` ⟹ существует `A ≥ 1` и `H : ℕ → ℕ` с `DescentStep A (H t)
  (H (t+1))` для всех `t` (вечный двигатель). Это НЕ доказано — это содержательный аналитический мост,
  который должен следовать из тех же законов (перенос двойки / RH-связь), что замыкают близнецов. -/
def EngineBridge : Prop :=
  ∀ ρ : ℂ, NontrivialZero ρ → ρ.re ≠ 1 / 2 →
    ∃ (A : ℕ) (H : ℕ → ℕ), 1 ≤ A ∧ ∀ t, DescentStep A (H t) (H (t + 1))

/--
  **RH от противного (условная теорема).** Если мост `EngineBridge` верен, то RH истинна:
  нуль вне `1/2` дал бы вечный двигатель, что невозможно (`no_infinite_descent`). Значит каждый
  нетривиальный нуль на `Re = 1/2`. Вся аналитика изолирована в `EngineBridge`. -/
theorem riemann_of_engine_bridge (H_RH : EngineBridge) : RiemannHypothesis := by
  intro ρ hρ
  by_contra hne
  -- нуль вне 1/2 ⟹ вечный двигатель (мост)
  obtain ⟨A, Hgt, hA, hchain⟩ := H_RH ρ hρ hne
  -- но вечного двигателя нет (доказано)
  exact no_infinite_descent hA Hgt hchain

/--
  **Контрапозиция явно: ¬RH ⟹ двигатель ⟹ ⊥.** Тот же EPMI-механизм, что у близнецов.
  Если мост верен и RH ложна, то существует вечный двигатель — противоречие. -/
theorem not_RH_gives_engine (H_RH : EngineBridge) (hnotRH : ¬ RiemannHypothesis) :
    ∃ (A : ℕ) (H : ℕ → ℕ), 1 ≤ A ∧ ∀ t, DescentStep A (H t) (H (t + 1)) := by
  -- ¬RH ⟹ есть нуль вне 1/2
  rw [RiemannHypothesis] at hnotRH
  simp only [not_forall] at hnotRH
  obtain ⟨ρ, hρ, hne⟩ := hnotRH
  exact H_RH ρ hρ hne

/-! ### Связка с близнецами: один общий узел вместо двух -/

/--
  **Закон переноса двойки (абстрактно).** Пропозиция «ядро переноса двойки держится» — она УЖЕ
  доказана конкретными тождествами `Engine/TwoGap` (`det_law_rank33`, `det_law_CD`, `det_collapse`,
  …). Здесь — её абстрактная форма как посылки (свидетель — любое из тождеств). -/
def TwoTransportLaw : Prop :=
  ∀ m a b v q r s : ℕ, 1 ≤ m → 6 * m - 1 = a * b * v → 6 * m + 1 = q * r * s →
    q * r * s = a * b * v + 2

/-- Закон переноса двойки ДОКАЗАН (это `det_law_rank33`). Не аксиома. -/
theorem twoTransportLaw_holds : TwoTransportLaw :=
  fun _ _ _ _ _ _ _ hm h1 h2 => det_law_rank33 hm h1 h2

/--
  **Узел-связка `TwoTransportBridge` — ЕДИНСТВЕННОЕ, что надо доказать для «одновременности».**
  Импликация (НЕ эквивалентность гипотез!): закон переноса двойки ⟹ EngineBridge. То есть нуль `ζ`
  вне `1/2` ломает перенос двойки и порождает вечный двигатель. Если ЭТО доказано, RH следует из
  УЖЕ доказанного ядра (`TwoGap` + EPMI), не дожидаясь близнецов. -/
def TwoTransportBridge : Prop := TwoTransportLaw → EngineBridge

/--
  **RH из доказанного ядра + одной связки (структура «одновременности» явно).** Если узел-связка
  `TwoTransportBridge` верен, то RH следует — потому что `TwoTransportLaw` УЖЕ доказан
  (`twoTransportLaw_holds`) и EPMI УЖЕ доказан. Открытым остаётся РОВНО `TwoTransportBridge`
  (импликация перенос-двойки ⟹ мост), а НЕ отдельная аналитика и НЕ эквивалентность гипотез. -/
theorem riemann_of_two_transport (bridge : TwoTransportBridge) : RiemannHypothesis :=
  riemann_of_engine_bridge (bridge twoTransportLaw_holds)

end EuclidsPath.RiemannBranch
