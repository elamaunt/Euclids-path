# RESULTS: аудит product-rank descent (3 агента) — Step00 НЕ закрыт, 3 дефекта

## Доказано (логика верна)
- rank_step_descent (БЕЗ аксиом), product_rank_pump (propext/Quot.sound): excluded-middle + сильная
  индукция r→…→1→Engine. При формализации пойман реальный off-by-one (collision-rank vs state-rank), исправлен.

## Три дефекта (Step00 НЕ закрыт)
1. no_mismatch_state_eq — ТРИЛЕММА ВОЗРОДИЛАСЬ (extensionality-gap): ProdSig должна экстенсионально
   определять состояние, но absorber/tail = 570→1 many-to-one (BoundaryDecomp). Паспорт нужен
   fine (для леммы) И coarse (для pigeonhole) — та же трилемма UniqueLegalLift, на ранг выше.
2. Граница a<P_A НЕ сохраняется на residual рангах: legal_lift_lt_primorial только top-level;
   no_PH не передоказывает a<P_A для residual на каждом ранге 1..4.
3. ProdSig НЕ конечна: (ℤ/P_A)^r имеет размер P_A^r→∞ (P_A примориал ~A/ln10). Pigeonhole §14 хочет
   фиксированный A; separating scale хочет A→∞. «ProdSig конечен» заявлено, не доказано.
+ скелет вакуумен: нет RankSetup-инстанса; все содержательные поля — гипотезы.

## Что реально улучшено
SeparatingScale.no_productHall закрыл ОДИН узел чистой арифметикой (держится). Rank-descent логика
корректна как логика. Counting wall рефакторен в меньшие коробки, одна опустошена.

## Вывод
Несущий узел no_mismatch_state_eq = та же трилемма (fine vs coarse), теперь на rank-уровне.
Плюс новые: несохранение границы на residual + неконечность ProdSig vs pigeonhole. Step00 = sorry.
