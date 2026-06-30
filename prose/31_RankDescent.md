# 31. energy_defect_trichotomy + конечный product-rank descent

> Источник: step00_energy_defect_trichotomy_rank_descent_ru_2026-07-01.md. Lean:
> `Engine/RankDescent.lean`. Аудит: tools/RESULTS_rankdescent_audit.md.

## Что доказано (логика)

После закрытого `no_productHall` (separating scale):
- `rank_step_descent` (**без аксиом**): equal-rank `>1` collision + `¬ProductHall` ⟹ collision ранга `r-1`;
- `product_rank_pump` (propext/Quot.sound): сильная индукция по рангу `r→…→1→Engine` (база — rank-1 SNOL).

Логика **верна** (excluded middle `R₁=R₂ ∨ R₁≠R₂` + well-founded по рангу). При формализации я **поймал
реальный off-by-one** в индукции (collision-rank vs state-rank) — исправлен.

## Вердикт аудита (3 агента): Step00 НЕ закрыт — 3 дефекта

**1. `no_mismatch_state_eq` — ТРИЛЕММА ВОЗРОДИЛАСЬ (extensionality-gap).** Для «нет mismatch ⟹
`X₁=X₂`» `ProdSig` должна экстенсионально определять состояние. Separating scale даёт инъективность
`a mod P_A` только на legal-слое, а absorber/tail — **570→1 many-to-one** (BoundaryDecomp). Паспорт
нужен fine (для леммы) И coarse (для pigeonhole) — та же трилемма UniqueLegalLift, на ранг выше.

**2. Граница `a<P_A` НЕ сохраняется на residual рангах.** `legal_lift_lt_primorial` — только top-level.
`no_PH` (абстрактное поле) не передоказывает `a<P_A` для residual состояний на каждом ранге 1..4.

**3. `ProdSig` НЕ конечна — pigeonhole §14 под угрозой.** Residue-пространство `(ℤ/P_A)^r` имеет размер
`P_A^r→∞` (P_A примориал ~ `A/ln10`). Pigeonhole хочет фиксированный A; separating scale хочет A→∞.
`«ProdSig конечен»` — заявлено, не доказано. Прямое напряжение, не разрешено.

**+ скелет вакуумен:** ни одного `RankSetup`-инстанса в репо; все содержательные поля — гипотезы.

## Вывод

Реальный прогресс: один узел (ProductHall) закрыт, rank-descent логика корректна. Но три дефекта —
extensionality (трилемма на ранг выше), несохранение границы на residual, неконечность `ProdSig` vs
pigeonhole. `Step00` = `sorry`. Стена не снята — рефакторена точнее и частью опустошена, но
несущий узел `no_mismatch_state_eq` остаётся той же трилеммой.
