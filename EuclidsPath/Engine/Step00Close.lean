/-
  Step00 closure attempt — сборка конкретного графа над центрами.
  Цель: построить HeightGraph над ℕ-центрами, доказать Regenerates целиком, и попытаться закрыть
  `Step00.twin_prime_conjecture`.

  Архитектурная проверка (честно): `reaches_twin` спускает высоту ⟹ найденный twin НИЖЕ старта.
  Для бесконечности нужен twin ВЫШЕ каждого N. Здесь это вскрывается явно.

  ВЕРДИКТ (3 независимых аудита + числа, tools/RESULTS_descent_gap.md): СБОРКА НЕ ЗАМЫКАЕТСЯ.
  Несущая дыра — `sink-is-clean`: `Twin` здесь = `TwinCenterZ` БЕЗ конъюнкта `CleanZ`, а `Step` —
  абстрактное `t'<t` без сертификата clean-ности и без `<A²`. Поэтому `clean_twin_above` к стоку
  НЕприменима (нет предпосылки «sink clean»), и спуск может финишировать на МАЛОМ twin ≤ M₀
  (контрпример: центр 166698 → 18 → стороны (107,109), не-clean при A=200; в пределе m=1 ↔ (5,7)).
  Это совместимо с «M₀ — последний twin» ⟹ противоречия НЕТ. Недостающее звено — инвариант
  «Step сохраняет CleanZ A вдоль спуска» — по сложности равно самой гипотезе. `Step00` НЕ закрыт.
-/
import Mathlib
import EuclidsPath.Engine.RigidClose
import EuclidsPath.Engine.Residuals
import EuclidsPath.Engine.Regeneration

set_option autoImplicit false

namespace EuclidsPath.Step00Close

open EuclidsPath.RigidClose EuclidsPath.Residuals EuclidsPath.Regeneration

/--
  **Состояние:** центр `t` со знаком стороны `η` (направление текущего old-peel/active шага).
  Высота = центр. -/
structure CState where
  t : ℕ
  η : ℤ

/--
  **Граф спуска над центрами.** `Twin` = twin-центр; `Step` = переход к строго меньшему центру
  `t' < t` (old-peel/active через `cofactor_is_center`). Высота = центр `t`. -/
def descentGraph : HeightGraph CState where
  height := fun s => s.t
  Twin := fun s => TwinCenterZ s.t
  Step := fun s s' => s'.t < s.t   -- абстрактное «спуск к меньшему центру» (конкретное ребро строит cofactor)
  step_drops := fun {s s'} h => h

/--
  **Regenerates для descentGraph — ЧЕСТНАЯ проверка.** Не-twin центр должен иметь нисходящего
  преемника. Из дихотомии (`regeneration_dichotomy`) + `cofactor_is_center` мы умеем строить
  меньший центр КОГДА у стороны есть делитель `q ≥ 5`. Но `Step` здесь — `s'.t < s.t`, и чтобы
  его дать, нужен КОНКРЕТНЫЙ меньший центр `t' < t`.

  Тонкость: для `t = 0` или малых `t` делитель/кофактор может не дать `t' < t` строго. Поэтому
  `Regenerates descentGraph` в чистом виде НЕ универсальна — нужна нижняя граница (carrier scale).
  Это и есть оставшийся вход. -/
theorem regenerates_iff_has_smaller (hbuild : ∀ s : CState, ¬ TwinCenterZ s.t → ∃ t' : ℕ, t' < s.t) :
    Regenerates descentGraph := by
  intro s hs
  obtain ⟨t', ht'⟩ := hbuild s hs
  exact ⟨⟨t', 1⟩, ht'⟩

/--
  **Архитектурный разрыв (вскрыт явно).** `reaches_twin descentGraph` даёт twin С НЕКОТОРОЙ высотой
  `≤ height(start)` — то есть twin НИЖЕ старта. Для бесконечности (twin выше каждого `N`) спуск
  «вниз» не годится: нужно либо (а) стартовать достаточно высоко и показать, что twin-сток всё ещё
  `> N`, либо (б) сменить направление (восходящий поиск). Это РЕАЛЬНЫЙ открытый пункт сборки.
-/
theorem reaches_some_twin (hregen : Regenerates descentGraph) (s₀ : CState) :
    ∃ s : CState, TwinCenterZ s.t :=
  reaches_twin descentGraph hregen s₀

end EuclidsPath.Step00Close
