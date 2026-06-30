# RESULTS: separating scale — ¬ProductHall чистой арифметикой

## Главное: узел ProductHall ЗАКРЫТ (доказательством, не переименованием)

`Engine/SeparatingScale.lean` (минимальные аксиомы propext/Quot.sound, БЕЗ Classical.choice, БЕЗ sorry):
- `eq_of_modEq_of_lt`: a₁,a₂ < P, a₁≡a₂ (mod P) ⟹ a₁=a₂;
- `legal_lift_lt_primorial`: separating scale ⟹ legal factor a < P_A;
- **`no_productHall`**: при P_A>6X_A+1 legal ProductHall НЕВОЗМОЖЕН (a₁=a₂ ⟂ a₁≠a₂).

Это ВПЕРВЫЕ закрывает pump-узел настоящим доказательством. Трилемма UniqueLegalLift ОБОЙДЕНА:
паспорт coarse (a mod P_A), но на legal-domain a<P_A ⟹ это уже exact data ⟹ инъективно.

## Separating scale достижим (с запасом)

log P_A растёт как ~A/ln10 (Чебышёв), обгоняет 4.5·log10(A) уже при A≈50:
| A | log10 P_A | log10(6·A^4.5) | P_A>6X_A |
|---|---|---|---|
| 50 | 17.0 | 8.4 | ✓ |
| 200 | 81.1 | 11.1 | ✓ |
| 1000 | 414.5 | 14.3 | ✓ |

## Куда переехала трудность (честно)

¬ProductHall сужает трихотомию `LowerRankCollision ∨ ProductHall` до ОДНОЙ ветви
`LowerRankCollision` (доказано: `trichotomy_collapses`). Но теперь нагрузка в НОВЫХ узлах
(§8-9, все открыты):
1. `energy_defect_trichotomy` (ProdSig-коллизия + mismatch ⟹ LowerRankCollision ∨ ProductHall);
2. rank-1 SNOL closure;
3. bounded rank induction r≤4.
Глобальный pigeonhole (inf родословных → конечный key) теперь должен давать LowerRankCollision на
каждом ранге — тот же fan-in аргумент, на ранг ниже.

## Вывод

РЕАЛЬНЫЙ прогресс: один узел (ProductHall) закрыт чистой арифметикой, трилемма обойдена честно.
Дыра НЕ исчезла — переехала в energy_defect_trichotomy + rank-induction. Но это сужение настоящее:
counting wall теперь на rank-уровне, и его ещё надо предъявить. Step00 = sorry.
