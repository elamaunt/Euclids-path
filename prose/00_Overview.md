# Ход доказательства: карта пути (от идей к финальному узлу)

> Этот файл — навигатор по всему репозиторию: видимый ход доказательства, какие идеи изучались
> по пути, что доказано машинно, и где единственный открытый узел. Парная проза — `prose/NN_*.md`,
> Lean — `EuclidsPath/Engine/*.lean`, числа — `tools/RESULTS_*.md`. Старая аналитическая линия —
> `archive/` (изучена, обойдена).

## Краткая суть

Гипотеза близнецов сведена машинно-проверенной цепью к **одному** открытому узлу. По пути изучены
несколько линий-атак на ключевую оценку — все они честно картографированы (включая упор в стену
чётности), а финальная редукция (rank descent → rank-1 → **SNOL**) даёт единственный оставшийся,
**не-счётный** узел.

## Ход (в порядке доказательства)

### Основания
- **00 Overview** — цель (`TwinLowers.Infinite`), центровая форма `6m±1`, `IsTwinCenter`.
  [`Step00_Overview.lean`]

### I. Двигатель Евклида и его законы (атомарные, доказаны без `sorry`)
- **EPMI** — невозможность вечного двигателя (`no_infinite_descent`). [prose 06, `Engine/EPMI`]
- **Carrier** — носитель двойки: `shared gcd ∣ 2`. [`Engine/Carrier`]
- **TwoGap** — 1-й закон: сохранение двойки `XY−ZW=2`. [prose 05, `Engine/TwoGap`]
- **Descent** — строгий спуск + boundary-law `p∣bv−2ε`. [`Engine/Descent`]
- **Irreversibility** — 2-й закон: не повернёт назад, асимметрия (вверх ∞ / вниз конечно), turn⇒halt.
  [prose 24, `Engine/Irreversibility`]
- **NoBackward** — диагональ исчезает (эксклюзивность ⇒ нет хода назад на двух точках). [`Engine/NoBackward`]
- **Squeeze / BK / Cycle** — короткий train, ограниченные циклы, factor-repeat rigidity.

### II. Редукция к близнецам (мост)
- **NonCover** — `survivor ⇒ twin`; `infinite_of_unbounded_centers`. [`Engine/NonCover`]
- **TwoTransport** — `twin_prime_conjecture_of_blocks`: гипотеза ⟸ блочное ядро. [`Engine/TwoTransport`]

### III. Линии-атаки на оценку (изучены по пути — все упёрлись в одну стену чётности)
- **FourCorner / ModelFourCorner / RealFourCorner** — отрицательная ассоциация; модельный four-corner
  `20·C(n,6) < C(n,3)²` доказан; перенос модель→реальность открыт. [prose 20, `Engine/*FourCorner`]
- **ToTwins** — `twin_primes_of_four_corner` (условно на входе `H` = реальный four-corner). [prose 21, `Engine/ToTwins`]
- **FiniteContradiction** — от противного: `finite ∧ H ⇒ False`; 3 независимых маршрута (counting/EPMI/
  four-corner) сводятся к одной стене. [prose 25, `Engine/FiniteContradiction`]
- **PaymentLedger** — закон оплаты: channel `p−2`, tax `(q−3)/(q−2)`, shifted-primorial, порог `Y_A`.
  [prose 26, `Engine/PaymentLedger`]

  > Числа (`tools/RESULTS_*`): margin `1−R_fc→0` (knife-edge), remainder ~4× модели, tax ~1/lnA
  > (Мертенс). Все эти линии упираются в распределение/чётность — это честно зафиксировано.

### IV. Финальный узел (единственный открытый)
- **SNOL** — rank descent (4→3→2→1) сводит всё к rank-1 shifted-neighbour obstruction `p∣a−2ε`.
  `twin_primes_of_SNOL`, `finite_contradicts_SNOL` доказаны; **SNOL — единственный вход**. [prose 27,
  `Engine/SNOL`]

  > Ключевое (числа `RESULTS_snol`): SNOL **не следует из CRT-ёмкости** (62–78% соседей пойманы) ⟹
  > она требует Euclidean-родословную `a`, а не распределение. Это **не та же стена** — счёт здесь
  > запрещён по построению.

## Что изучалось по пути и обойдено (archive/)

Старая **аналитическая линия** (PMKLS / Kloosterman / large-sieve / DASC / G2 / O4C) — `archive/lean/`
(Step01–16) и `archive/prose/`. Она была первой попыткой; почти вся в `sorry`; **обойдена**
структурной Engine-линией (Multi-Rank Non-Cover + двигатель). Сохранена, чтобы был виден ход мысли.

## Статус (честно)

- **Доказано машинно (без `sorry`, стандартные аксиомы):** весь двигатель и его законы; редукция к
  блочному ядру; модельный four-corner; алгебра оплаты; финальная редукция к SNOL.
- **Единственная открытая цель:** `Step00.twin_prime_conjecture` = финальный узел **SNOL**.
- **Единственный вход к закрытию:** `SNOL.SNOLInput` (структурный, не-счётный).
