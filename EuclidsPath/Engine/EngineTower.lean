/-
  EngineTower — башенная формализация БЕЗ traversal: inverse-limit через компактность конечных префиксов.
  Источник: engine_tower_without_traversal_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «EngineTower без traversal»).

  ГЛАВНЫЙ СДВИГ (правильный). Не доказывать, что конечный движок ПРОЕЗЖАЕТ бесконечную башню (это
  orientation-стена = вечный двигатель), а: NoTwinAbove ⟹ все конечные префиксы уровней ⟹ (компактность)
  EngineTower ⟹ RecurrentCenter ∨ CrossLevelCollision. RecurrentCenter невозможен (центр clean на
  неограниченных уровнях), CrossLevelCollision даёт Close, оба под NoEngine/NoTwin запрещены.

  ЗДЕСЬ ДОКАЗАНО (реальная арифметика + честная сборка, std аксиомы, без sorry):
    * `unboundedClean_forces_side_le_one` — центр clean на НЕОГРАНИЧЕННЫХ уровнях не может иметь сторону
      `≥ 2` (взять `B = q`); это ключевой не-counting факт;
    * `no_recurrentEngineTower` — рекуррентный центр невозможен;
    * `engineTower_recurrent_or_escapes` — дихотомия (классическая);
    * `no_engineTower_of_crossLevel_collision`, `twin_above_of_engineTower_contradiction` — сборка.

  ЧЕСТНАЯ ГРАНИЦА (ключевая, вскрыта при формализации — та же ловушка, что HigherTower). Кирпич
  НАДЕЯЛСЯ, что recurrence (центр на неограниченных уровнях) СЛАБЕЕ fixed-center clean-forever и потому
  НЕ вакуумна. Это НЕ так: для простого делителя `p` стороны взять `B = p`, получить `A ≥ p` с
  `CleanZ A m`, и `p ≤ A` ⟹ cleanness запрещает `p ∣ side`. Значит unbounded-clean ТОЖЕ запрещает ЛЮБОЙ
  простой делитель ⟹ side ≤ 1. Поэтому `no_recurrentEngineTower` ВАКУУМЕН так же, как `no_badTower`:
  противоречие «recurrent ⟹ side ≤ 1», а НЕ «recurrent ⟹ twin»; поле `bad` не используется.

  ВЫВОД: recurrence-ветка вакуумна и twin-содержания НЕ несёт. ВСЁ содержание маршрута — в escape/
  CrossLevelCollision ветке (входы C/D/E кирпича: `hRepeat` = pigeonhole по конечной подписи, `hSig`
  = recurrence-or-collision, `hCollisionClose` = cross-level labelled-fan-in). По прежним аудитам это
  та же counting/pigeonhole + labelled-fan-in стена. Компактность-мост тоже требует finite branching
  = counting. Здесь C/D/E — входы. `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.EngineTower

open EuclidsPath.Residuals

/-! ### §3. Арифметика: clean на неограниченных уровнях ⟹ side ≤ 1 (тот же не-counting факт)

Кирпич хотел `clean_for_unbounded_A_implies_twin` как не-вакуумную замену fixed-center. Но гипотеза
ОДИНАКОВО невыполнима: unbounded-clean запрещает любой простой делитель. -/

/--
  **`unboundedClean_forces_no_prime_divisor` — ДОКАЗАНА.** Если `m` clean на неограниченных уровнях
  (`∀ B, ∃ A ≥ B, CleanZ A m`), то НИ ОДИН простой `q` не делит `6m+1`: взять `B = q`, получить `A ≥ q`
  с `CleanZ A m`; `q ≤ A` ⟹ запрет. То же, что fixed-center — recurrence НЕ слабее. -/
theorem unboundedClean_forces_no_prime_divisor {m : ℕ}
    (hUnb : ∀ B, ∃ A, B ≤ A ∧ CleanZ A (m : ℤ)) :
    ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ (6 * (m : ℤ) + 1) := by
  intro q hq hdvd
  obtain ⟨A, hqA, hClean⟩ := hUnb q
  exact hClean q hq hqA (Or.inr hdvd)

/--
  **`unboundedClean_forces_side_le_one` — ДОКАЗАНА (вскрывает вакуумность recurrence-ветки).** Если
  `m` clean на неограниченных уровнях, то `6m+1 ≤ 1` (сторона НЕ `≥ 2`): `minFac` был бы запрещённым
  простым делителем. Значит recurrence + side ≥ 2 несовместимы — ТАК ЖЕ, как fixed-center. -/
theorem unboundedClean_forces_side_le_one {m : ℕ}
    (hUnb : ∀ B, ∃ A, B ≤ A ∧ CleanZ A (m : ℤ)) : ¬ (2 ≤ 6 * m + 1) := by
  intro hge
  have hp : (6 * m + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hd : (6 * m + 1).minFac ∣ (6 * m + 1) := Nat.minFac_dvd _
  have hdZ : ((6 * m + 1).minFac : ℤ) ∣ (6 * (m : ℤ) + 1) := by
    have hcast : ((6 * m + 1 : ℕ) : ℤ) = 6 * (m : ℤ) + 1 := by push_cast; ring
    rw [← hcast]; exact_mod_cast hd
  exact unboundedClean_forces_no_prime_divisor hUnb _ hp hdZ

/-! ### §4–6. EngineShadow и EngineTower (moving-center inverse limit)

`EngineShadow A` — конечная тень движка на уровне `A`, дошедшая до bad-terminal: центр clean на `A`,
стороны `≥ 2`, не twin. Абстрактно фиксируем ТОЛЬКО арифметические поля (реальные restriction maps —
проектный интерфейс, здесь не нужны для recurrence-ветки). Центр МОЖЕТ меняться между уровнями. -/

/-- Тень движка на уровне `A`: центр clean на `A`, стороны `≥ 2`, не twin. -/
structure EngineShadow (A : ℕ) where
  center : ℕ
  clean : CleanZ A (center : ℤ)
  side_hi : 2 ≤ 6 * center + 1
  bad : ¬ TwinCenterZ center

/-- EngineTower: тень на каждом уровне (moving-center; совместимость — проектный интерфейс, для
    recurrence-ветки достаточно самих теней). -/
structure EngineTower where
  shadow : ∀ A, EngineShadow A

/-! ### §10–11. Recurrence: дихотомия + невозможность рекуррентного центра (ВАКУУМНО) -/

/-- Центр `m` рекуррентен: повторяется на неограниченных уровнях. -/
def CenterRecursUnbounded (T : EngineTower) (m : ℕ) : Prop :=
  ∀ B, ∃ A, B ≤ A ∧ (T.shadow A).center = m

/-- Башня имеет рекуррентный центр. -/
def HasRecurrentCenter (T : EngineTower) : Prop := ∃ m, CenterRecursUnbounded T m

/-- Башня «убегает»: у каждого центра ограниченный уровень появления. -/
def NoRecurrentCenter (T : EngineTower) : Prop :=
  ∀ m, ∃ B, ∀ A, B ≤ A → (T.shadow A).center ≠ m

/-- **`engineTower_recurrent_or_escapes` — ДОКАЗАНА (классическая дихотомия).** -/
theorem engineTower_recurrent_or_escapes (T : EngineTower) :
    HasRecurrentCenter T ∨ NoRecurrentCenter T := by
  by_cases h : HasRecurrentCenter T
  · exact Or.inl h
  · refine Or.inr (fun m => ?_)
    by_contra hNoBound
    push_neg at hNoBound
    exact h ⟨m, fun B => hNoBound B⟩

/-- Рекуррентный центр clean на неограниченных уровнях. -/
theorem recurrent_unboundedClean (T : EngineTower) {m : ℕ}
    (hRec : CenterRecursUnbounded T m) : ∀ B, ∃ A, B ≤ A ∧ CleanZ A (m : ℤ) := by
  intro B
  obtain ⟨A, hBA, hCenter⟩ := hRec B
  exact ⟨A, hBA, hCenter ▸ (T.shadow A).clean⟩

/-- Рекуррентный центр имеет сторону `≥ 2`. -/
theorem recurrent_side_hi (T : EngineTower) {m : ℕ}
    (hRec : CenterRecursUnbounded T m) : 2 ≤ 6 * m + 1 := by
  obtain ⟨A, _, hCenter⟩ := hRec 0
  exact hCenter ▸ (T.shadow A).side_hi

/--
  **`no_recurrentEngineTower` — ДОКАЗАНА, но ВАКУУМНО (честная пометка).** Рекуррентный центр
  невозможен. ПРИЧИНА (вырожденная, как в `HigherTower.no_badTower`): recurrence даёт clean на
  неограниченных уровнях (`recurrent_unboundedClean`), что запрещает стороне быть `≥ 2`
  (`unboundedClean_forces_side_le_one`) — против `recurrent_side_hi`. Противоречие «recurrent ⟹
  side ≤ 1», НЕ «recurrent ⟹ twin»; поле `bad` НЕ используется. Кирпич надеялся, что recurrence
  слабее fixed-center — но нет. Так что recurrence-ветка twin-содержания НЕ несёт. -/
theorem no_recurrentEngineTower (T : EngineTower) (hHasRec : HasRecurrentCenter T) : False := by
  obtain ⟨m, hRec⟩ := hHasRec
  exact unboundedClean_forces_side_le_one (recurrent_unboundedClean T hRec) (recurrent_side_hi T hRec)

/-! ### §15, §17. Сборка: башня + collision-вход ⟹ Close; финальная теорема

Recurrence-ветка закрыта (вакуумно). Escape-ветка требует ВХОДОВ C/D/E (cross-level collision), которые
кирпич сам называет: `hRepeat` (∞ уровней с одной подписью — pigeonhole), `hSig` (recurrence-or-collision),
`hCollisionClose` (collision ⟹ Close = cross-level labelled-fan-in). Это та же counting/labelled-fan-in
стена; здесь — входы. -/

/-- Абстрактный `Close` и `CrossLevelCollision` (проектный тип). -/
def CloseAt (Engine : ℕ → Prop) (N : ℕ) : Prop := (∃ A, Engine A) ∨ ∃ t, N < t ∧ TwinCenterZ t

/--
  **`no_engineTower_of_crossLevel_collision` — ДОКАЗАНА (сборка §15).** Если башня всегда даёт
  бесконечно-повторную подпись (`hRepeat`), подпись ⟹ recurrence ∨ collision (`hSig`), collision ⟹
  Close (`hCollisionClose`), а Close запрещён (`hNoClose`), то башни нет. Recurrence бьётся
  `no_recurrentEngineTower` (вакуумно), collision — `hCollisionClose` + `hNoClose`.

  ВСЁ содержание — в `hSig`/`hRepeat`/`hCollisionClose` (входы = counting/labelled-fan-in стена). -/
theorem no_engineTower_of_crossLevel_collision {Sig : Type*} {Engine : ℕ → Prop} {N : ℕ}
    {CrossLevelCollision : EngineTower → Prop}
    (hNoClose : ¬ CloseAt Engine N)
    (hRepeat : ∀ T : EngineTower, HasRecurrentCenter T ∨ CrossLevelCollision T)
    (hCollisionClose : ∀ T : EngineTower, CrossLevelCollision T → CloseAt Engine N) :
    ¬ Nonempty EngineTower := by
  rintro ⟨T⟩
  rcases hRepeat T with hRec | hCol
  · exact no_recurrentEngineTower T hRec
  · exact hNoClose (hCollisionClose T hCol)

/--
  **`twin_above_of_engineTower_contradiction` — ДОКАЗАНА (финальная сборка §17).** Под `¬Engine` и
  `¬(twin выше N)`: если NoTwin форсирует башню (`hForce`, через префиксы+компактность — вход), а
  башня невозможна (recurrence вакуумна + collision закрывает), то `∃ twin > N`.

  ЧЕСТНО: recurrence-ветка вакуумна (0 содержания). Реальная нагрузка — `hForce` (A+B: prefix force +
  compactness, требует finite branching = counting) и collision-входы (C/D/E = labelled-fan-in стена).
  Никакого traversal/orientation-стены здесь нет — это выигрыш формы; но counting/collision стена
  осталась. -/
theorem twin_above_of_engineTower_contradiction {Engine : ℕ → Prop} {N : ℕ}
    {CrossLevelCollision : EngineTower → Prop}
    (hNoEngine : ¬ ∃ A, Engine A)
    (hForce : ¬ (∃ t, N < t ∧ TwinCenterZ t) → Nonempty EngineTower)
    (hRepeat : ∀ T : EngineTower, HasRecurrentCenter T ∨ CrossLevelCollision T)
    (hCollisionClose : ∀ T : EngineTower, CrossLevelCollision T → CloseAt Engine N) :
    ∃ t, N < t ∧ TwinCenterZ t := by
  by_contra hNoTwin
  have hNoClose : ¬ CloseAt Engine N := by
    rintro (hE | hT)
    · exact hNoEngine hE
    · exact hNoTwin hT
  exact no_engineTower_of_crossLevel_collision (Sig := Unit) hNoClose hRepeat hCollisionClose
    (hForce hNoTwin)

end EuclidsPath.EngineTower
