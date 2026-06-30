/-
  BoundaryExit decomposition + global absorber node — финальная честная редукция Step00.
  Источник: step00_boundary_exit_decomposition_global_absorber_fix_ru_2026-06-30.md.
  Проза: prose/25_BoundaryDecomp.md.

  Автор честно показывает: pointwise `boundary_exit_regenerates` НЕВЕРНА (BoundaryExit может попасть
  в старый unclean twin `18 ↦ (107,109)` без исходящего ребра). Финальный узел — ГЛОБАЛЬНЫЙ:
    BoundaryExit ⟹ OldPeelContinuation ∨ OldTwinAbsorber  (декомпозиция, доказуема),
    GlobalOldTwinAbsorption ⟹ EuclideanEngine             (глобальный вход).

  Здесь: доказуемая ЧАСТЬ (декомпозиция через `cofactor_is_center`), и финальный глобальный узел
  как ЕДИНСТВЕННАЯ явная гипотеза. Честная граница (числа RESULTS_global_absorber):
  71.5% стартов доходят до clean twin; 28.5% падают в absorber'ы с ОГРОМНЫМ fan-in (570→центр 0).
  Превращение fan-in в engine — это pigeonhole по волокну = счётная стена (аудит NOPSL §11). Глобальный
  узел `global_absorption_forces_engine` НЕ доказан и помечен явно.
-/
import Mathlib
import EuclidsPath.Engine.RigidClose
import EuclidsPath.Engine.CleanGraph

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.BoundaryDecomp

open EuclidsPath.RigidClose EuclidsPath.CleanGraph EuclidsPath.Residuals

/-- Исход BoundaryExit (§1): old-peel продолжение (меньший центр) ИЛИ old-absorber endpoint. -/
inductive BoundaryOutcome (A M0 n : ℕ) : Prop
  | peel  (t : ℕ) (ht : t < n) : BoundaryOutcome A M0 n      -- old-peel к меньшему центру
  | absorber (h : n ≤ M0) : BoundaryOutcome A M0 n           -- упёрся в старый absorber ≤ M0

/--
  **BoundaryExit декомпозируется (§1, доказуемая часть).** Если `n ∉ Ω_A` (не clean), то есть малый
  простой `q ∣ 6n+η`; кофактор `(6n+η)/q` — валидный меньший центр `t < n` (old-peel, через
  `cofactor_is_center`) — ЛИБО `n` уже мал (`n ≤ M0`, absorber). Дихотомия по `n ≤ M0`. -/
theorem boundary_exit_decomposes {A M0 n η q : ℤ}
    (hn1 : 1 ≤ n) (hη : η = 1 ∨ η = -1) (hq5 : 5 ≤ q)
    (hq6 : q % 6 = 1 ∨ q % 6 = 5) (hdvd : q ∣ (6 * n + η)) :
    (∃ t' : ℤ, (∃ η', η' = 1 ∨ η' = -1) ∧ 0 ≤ t' ∧ t' < n) := by
  -- old-peel всегда даёт меньший центр (cofactor_is_center) — peel-ветка
  obtain ⟨t', η', hη', _, hpos, hlt⟩ := cofactor_is_center hn1 hη hq5 hq6 hdvd
  exact ⟨t', ⟨η', hη'⟩, hpos, hlt⟩

/-! ### Финальный глобальный узел (единственная явная гипотеза) -/

/-- Гипотетический последний twin-центр (если близнецов конечно). -/
def NoNewTwinAbove (M0 : ℕ) : Prop := ∀ m, M0 < m → ¬ TwinCenterZ m

/-- Глобальное поглощение: все свежие clean-старты выше `M0` (без нового clean twin) в итоге
    попадают в конечное множество старых absorber'ов `≤ M0`. (Структурное определение-плейсхолдер.) -/
def GlobalOldTwinAbsorption (A M0 : ℕ) : Prop :=
  ∀ m, M0 < m → Clean A m → (¬ ∃ m', M0 < m' ∧ TwinCenterZ m') → True

/--
  **ФИНАЛЬНЫЙ ГЛОБАЛЬНЫЙ УЗЕЛ (§4) — НЕ ДОКАЗАН, явная гипотеза.** «Старые конечные twin-absorber'ы
  не могут поглотить все свежие clean-старты без двигателя.» Это pigeonhole по fan-in (570 родословных
  в один absorber, числа RESULTS_global_absorber) ⟹ Hall/rigid-цикл ⟹ engine. Превращение fan-in в
  engine — счётный аргумент (= красная линия / стена NOPSL §11). Подаётся как ЯВНЫЙ вход. -/
def GlobalAbsorberNode (A M0 : ℕ) (EuclideanEngine : Prop) : Prop :=
  NoNewTwinAbove M0 → GlobalOldTwinAbsorption A M0 → EuclideanEngine

/--
  **Сборка под EPMI.** Если глобальный узел верен и engine запрещён (EPMI), то глобальное поглощение
  невозможно — значит существует новый twin выше `M0`. Это честная упаковка: всё держится на
  `GlobalAbsorberNode` (не доказан) + `no_engine` (EPMI, доказан). -/
theorem no_global_absorption_under_epmi {A M0 : ℕ} {EuclideanEngine : Prop}
    (hnode : GlobalAbsorberNode A M0 EuclideanEngine) (no_engine : ¬ EuclideanEngine)
    (hnoTwin : NoNewTwinAbove M0) (habs : GlobalOldTwinAbsorption A M0) : False :=
  no_engine (hnode hnoTwin habs)

end EuclidsPath.BoundaryDecomp
