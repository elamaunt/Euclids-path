/-
  AboveConflict — противоречие в слове «Above» (порядковый конфликт), а не в «Twin» (хвост).
  Источник: above_structure_order_conflict_formal_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Above-конфликт порядков»).

  ИДЕЯ. Искать противоречие не в хвосте `NoTwinAbove(max T)`, а в ПОРЯДКОВОМ КОНФЛИКТЕ: engine-порядок
  `T₁ <_eng T₂ <_eng T₃`, но натуральный порядок центров `center T₁ < center T₃ < center T₂` («Twin #3
  оказался между Twin #1 и Twin #2»). Если это внутренние настоящие twin'ы, а engine-порядок независим —
  это не-хвостовое противоречие.

  ЗДЕСЬ ДОКАЗАНО (чистая логика порядка, std аксиомы, без sorry):
    * `no_above_conflict` — sound above-порядок не может дать конфликт (§7);
    * `no_order_crossing` (§8), `contradiction_of_twin_order_conflict` (§9);
    * `twinGap_not_pierced`, `contradiction_of_gap_piercing` (§3);
    * `no_twin_between_consecutive` (§2), `no_third_between_first_second` (§5 order);
    * `contradiction_of_finiteTwinOrderAttack` (§10).

  ЧЕСТНАЯ ГРАНИЦА (§14, §17, §19 кирпича — вскрыта и МАШИННО зафиксирована). Все теоремы выше —
  ТРИВИАЛЬНАЯ логика порядка (следствие `above_sound`). Единственный содержательный вход —
  `step00_forces_above_conflict` (finite twins ⟹ конфликт), и он в ЛОВУШКЕ:
    * если `Step00Above := center X < center Y` (definitional), конфликт ПОСТРОИТЬ НЕЛЬЗЯ
      (`definitional_above_conflict_impossible` — машинно), маршрут мёртв;
    * если `above` — независимый sound-порядок, `no_above_conflict` всё равно запрещает конфликт;
    значит `step00_forces_above_conflict` требует построить конфликт, которого при sound-порядке НЕ
    существует — то есть он либо ложен, либо предъявляет новый twin между двумя (= `TwinAbove`
    внутреннего интервала, что и есть цель). Кирпич сам это признаёт (§17). Здесь этот вход НЕ
    предъявлен. `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.AboveConflict

open EuclidsPath.Residuals

/-! ### §6–8. AboveStructure и order-конфликт (чистая логика) -/

/-- Абстрактная above-структура: объекты с центром, порядок `above`, монотонный по центру, транзитивный. -/
structure AboveStructure where
  Obj : Type
  center : Obj → ℕ
  above : Obj → Obj → Prop
  above_sound : ∀ X Y, above X Y → center X < center Y
  trans : ∀ X Y Z, above X Y → above Y Z → above X Z

/--
  **`no_above_conflict` — ДОКАЗАНА (ядро order-противоречия §7).** Не может быть `above X Y`,
  `above Y Z` при `center X < center Z < center Y`: из `above Y Z` следует `center Y < center Z`, что
  против `center Z < center Y`. Чистая логика порядка — но вся сила в `above_sound`. -/
theorem no_above_conflict (S : AboveStructure) (X Y Z : S.Obj)
    (hXY : S.above X Y) (hYZ : S.above Y Z)
    (hbetween : S.center X < S.center Z ∧ S.center Z < S.center Y) : False := by
  have := S.above_sound Y Z hYZ
  omega

/-- **`no_order_crossing` — ДОКАЗАНА (§8).** То же для явного two-order crossing. -/
theorem no_order_crossing (S : AboveStructure) (X Y Z : S.Obj)
    (hXY : S.above X Y) (hYZ : S.above Y Z)
    (hnatXZ : S.center X < S.center Z) (hnatZY : S.center Z < S.center Y) : False := by
  have := S.above_sound Y Z hYZ
  omega

/-! ### §2–3. TwinGap: интервал между последовательными twin'ами -/

/-- Gap между двумя twin-центрами без twin внутри. -/
structure TwinGap where
  left : ℕ
  right : ℕ
  hLeftTwin : TwinCenterZ left
  hRightTwin : TwinCenterZ right
  hlt : left < right
  noTwinBetween : ∀ m, left < m → m < right → ¬ TwinCenterZ m

/-- **`twinGap_not_pierced` — ДОКАЗАНА (§3).** Gap нельзя проколоть twin'ом внутри. -/
theorem twinGap_not_pierced (G : TwinGap) :
    ¬ ∃ m, G.left < m ∧ m < G.right ∧ TwinCenterZ m := by
  rintro ⟨m, hlm, hmr, hT⟩
  exact G.noTwinBetween m hlm hmr hT

/-- **`contradiction_of_gap_piercing` — ДОКАЗАНА (§3).** Прокол gap ⟹ False. -/
theorem contradiction_of_gap_piercing (G : TwinGap)
    (hPierce : ∃ m, G.left < m ∧ m < G.right ∧ TwinCenterZ m) : False :=
  twinGap_not_pierced G hPierce

/-- **`no_twin_between_consecutive` — ДОКАЗАНА (§2).** У последовательных twin'ов нет twin внутри. -/
theorem no_twin_between_consecutive {a b : ℕ}
    (haTwin : TwinCenterZ a) (hbTwin : TwinCenterZ b) (hab : a < b)
    (hNoBetween : ∀ c, a < c → c < b → ¬ TwinCenterZ c) :
    ¬ ∃ c, a < c ∧ c < b ∧ TwinCenterZ c := by
  rintro ⟨c, hac, hcb, hT⟩
  exact hNoBetween c hac hcb hT

/-! ### §9. TwinOrderConflict — специализация к twin-блокам -/

/-- Блок-близнец (центр). -/
structure TwinBlock where
  center : ℕ

/-- `IsTwin` блока = twin-центр. -/
def TwinBlock.IsTwin (B : TwinBlock) : Prop := TwinCenterZ B.center

/-- Order-конфликт трёх twin'ов: engine-порядок `T₁→T₂→T₃`, но `center T₁ < center T₃ < center T₂`. -/
structure TwinOrderConflict where
  T1 : TwinBlock
  T2 : TwinBlock
  T3 : TwinBlock
  hTwin1 : T1.IsTwin
  hTwin2 : T2.IsTwin
  hTwin3 : T3.IsTwin
  EngineBefore : TwinBlock → TwinBlock → Prop
  engine_before_12 : EngineBefore T1 T2
  engine_before_23 : EngineBefore T2 T3
  engine_before_sound : ∀ X Y, EngineBefore X Y → X.center < Y.center
  natural_between : T1.center < T3.center ∧ T3.center < T2.center

/--
  **`contradiction_of_twin_order_conflict` — ДОКАЗАНА (§9).** «Twin #3 между Twin #1 и Twin #2»
  невозможен: из `EngineBefore T2 T3` следует `center T2 < center T3`, против `center T3 < center T2`. -/
theorem contradiction_of_twin_order_conflict (C : TwinOrderConflict) : False := by
  have := C.engine_before_sound C.T2 C.T3 C.engine_before_23
  have := C.natural_between.2
  omega

/-! ### §5. Nth-twin порядок (пример; сама монотонность ранга — отдельный факт) -/

/-- **`no_third_between_of_order` — ДОКАЗАНА (§5, чистый порядок).** Если nth-twin монотонен
    (`b < c` из рангов), то `c < b` невозможно. Сама монотонность ранга — вход, здесь не нужна. -/
theorem no_third_between_of_order {b c : ℕ} (hbc : b < c) (hcb : c < b) : False := by omega

/-! ### §10. FiniteTwinOrderAttack -/

/-- Атака: полный список twin'ов + внутренний gap + его прокол. -/
structure FiniteTwinOrderAttack where
  T : Finset ℕ
  complete : ∀ m, TwinCenterZ m → m ∈ T
  gap : TwinGap
  pierce : ∃ m, gap.left < m ∧ m < gap.right ∧ TwinCenterZ m

/-- **`contradiction_of_finiteTwinOrderAttack` — ДОКАЗАНА (§10).** -/
theorem contradiction_of_finiteTwinOrderAttack (A : FiniteTwinOrderAttack) : False :=
  twinGap_not_pierced A.gap A.pierce

/-! ### §14, §17. МАШИННЫЙ ДИАГНОЗ ЛОВУШКИ: почему это не новый маршрут сам по себе

Все теоремы выше тривиальны (следствие `above_sound`). Единственный содержательный вход —
`step00_forces_above_conflict`. Покажем машинно, что он в ловушке. -/

/--
  **`definitional_above_conflict_impossible` — ДОКАЗАНА (диагноз ловушки §14).** Если above-порядок
  ОПРЕДЕЛЁН как `center X < center Y` (definitional), то `AboveConflict` ПОСТРОИТЬ НЕЛЬЗЯ: `above X Y`,
  `above Y Z` дают `center X < center Y < center Z`, а `center Z < center Y` противоречит. Значит при
  definitional above маршрут мёртв (конфликт не существует). -/
theorem definitional_above_conflict_impossible (center : ℕ → ℕ) (X Y Z : ℕ)
    (hXY : center X < center Y) (hYZ : center Y < center Z)
    (hbetween : center X < center Z ∧ center Z < center Y) : False := by omega

/--
  **`above_conflict_route_is_trapped` — ДОКАЗАНА (итог диагноза).** Для ЛЮБОЙ sound above-структуры
  `AboveConflict` невозможен (`no_above_conflict`). Значит `step00_forces_above_conflict` (finite twins
  ⟹ конфликт) требует построить несуществующий объект — он ЛИБО ложен, ЛИБО его «конфликт» на деле
  предъявляет новый twin внутри интервала (= `TwinAbove` внутреннего gap = цель). В обоих случаях это
  НЕ обход, а переформулировка. Формально: конфликт ⟹ False, поэтому вход-форс эквивалентен `¬finite`
  лишь через уже-невозможность, а не через новый ресурс. -/
theorem above_conflict_route_is_trapped (S : AboveStructure)
    (hConflict : ∃ X Y Z : S.Obj, S.above X Y ∧ S.above Y Z ∧
      S.center X < S.center Z ∧ S.center Z < S.center Y) : False := by
  obtain ⟨X, Y, Z, hXY, hYZ, h1, h2⟩ := hConflict
  exact no_above_conflict S X Y Z hXY hYZ ⟨h1, h2⟩

end EuclidsPath.AboveConflict
