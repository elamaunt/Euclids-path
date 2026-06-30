# 30. Separating scale: ¬ProductHall чистой арифметикой (узел закрыт)

> Источник: step00_producthall_bridge_separating_scale_ru_2026-07-01.md. Lean:
> `Engine/SeparatingScale.lean` (минимальные аксиомы, без `sorry`). Числа: tools/RESULTS_separating_scale.md.

## Прорыв этого файла: впервые узел закрыт ДОКАЗАТЕЛЬСТВОМ

Прошлые pump-файлы переименовывали стену (payment / UniqueLegalLift / steering). Этот —
**закрывает `ProductHall` чистой арифметикой**, обходя трилемму UniqueLegalLift честно.

**Идея — separating scale `P_A > 6X_A + 1`:** на legal carrier layer активный фактор `a ∣ N`,
`N = 6m+σ ≤ 6X_A+1 < P_A`, значит `a < P_A`. Тогда `a ↦ a mod P_A` **инъективно на legal-domain** —
coarse-паспорт автоматически становится exact. Два legal-фактора с `a₁ ≡ a₂ (mod P_A)` **равны**,
что противоречит `a₁ ≠ a₂` в ProductHall. Значит **`¬ProductHall`**.

## Доказано (Lean, без `sorry`)

| теорема | аксиомы |
|---|---|
| `eq_of_modEq_of_lt` (`<P`, `≡` ⟹ `=`) | `propext` |
| `legal_lift_lt_primorial` (`a < P_A`) | `propext, Quot.sound` |
| **`no_productHall`** (¬ProductHall) | `propext, Quot.sound` |

Минимальные аксиомы, **без `Classical.choice`** — конструктивная арифметика. Трилемма обойдена:
паспорт coarse (`a mod P_A`), но на legal-domain `a < P_A` ⟹ это уже exact.

## Separating scale достижим (с огромным запасом)

`log P_A ~ A/ln10` (Чебышёв) обгоняет `4.5·log A` уже при `A ≈ 50`: `P_A > 6·A^4.5` легко
(A=200: `log P_A=81` vs `11`). Условие реалистично.

## Куда переехала трудность (честно)

`¬ProductHall` **сужает** трихотомию `LowerRankCollision ∨ ProductHall` до одной ветви
`LowerRankCollision` (`trichotomy_collapses`, доказано). Но нагрузка переехала в НОВЫЕ узлы (§8–9,
открыты):
1. `energy_defect_trichotomy` (ProdSig-коллизия + mismatch ⟹ LowerRankCollision ∨ ProductHall);
2. rank-1 SNOL closure (есть, отдельный блок);
3. bounded rank induction `r ≤ 4`.

Глобальный pigeonhole (бесконечно родословных → конечный key) теперь должен давать
`LowerRankCollision` на каждом ранге — тот же fan-in аргумент, на ранг ниже.

## Вывод

**Реальный прогресс, не переименование:** один узел (ProductHall) закрыт чистой арифметикой,
трилемма обойдена честно, separating scale достижим. Дыра не исчезла — переехала в
`energy_defect_trichotomy` + rank-induction. Но это **настоящее сужение**: counting wall теперь
на rank-уровне и должен быть предъявлен явно. `Step00` = `sorry`, но узлов стало меньше и они точнее.
