# RESULTS: финальная дыра Step00 — честный диагноз (попытка прямой склейки)

## Что доказано (вся машина, std axioms, без sorry)

separating scale ⟹ ¬ProductHall; product-core (extensionality, AmbientLegal bound, CoreSig finite);
core_step (descent); rank-1 база (арифметика); pigeonhole; **mkNode** (RankNode из составной стороны,
factor_rank_le_four, prime_factor_gt_A — всё арифметика); carrier бесконечен; engine_of_carrier.
EPMI. Все прежние стены (parity, трилемма, steering, payment, 3 дефекта) — сняты.

## Попытка закрыть последнюю дыру прямой склейкой — НЕ РАБОТАЕТ

Идея: `cleanCenters_infinite` (∞ clean) + `NoNewTwin ⟹ non-twin ⟹ composite side ⟹ mkNode` ⟹
`Infinite {nodeable}`. **Ловушка (проверено):**

- `NodeableCenter` требует `m ≤ X_A` (carrier — КОНЕЧНЫЙ отрезок [1, A^κ]);
- `cleanCenters_infinite` даёт бесконечность по `m → ∞` (центры УХОДЯТ выше X_A);
- на фиксированном [1, X_A] — КОНЕЧНО центров ⟹ `Infinite {nodeable в carrier}` НЕВОЗМОЖНО;
- pigeonhole требует бесконечность ВНУТРИ конечного отрезка — противоречие.

Значит прямая склейка ложна. Бесконечность для pigeonhole приходит НЕ из стартового отрезка.

## Несводимый узел: GlobalOldAbsorption

Бесконечность «fresh starts» (§9) — это РОДОСЛОВНЫЕ/genealogies на растущем масштабе спуска
(спускающиеся в absorber), НЕ центры в фиксированном [1, X_A]. Это РОВНО `GlobalOldAbsorption` —
placeholder (тело True в BoundaryDecomp), помеченный как counting wall (fan-in 570→1).

## Честный итог

Вся product-core / mkNode машина — реальный прогресс (множество узлов закрыто арифметикой,
все прежние стены сняты). НО финальная дыра `GlobalOldAbsorption ⟹ InfiniteNodeableCenters`
НЕ сводится к прямой склейке и остаётся несводимым узлом = исходный absorber/fan-in.
Step00 = sorry. Программа: честная редукция к ОДНОМУ узлу (GlobalOldAbsorption), всё остальное доказано.
