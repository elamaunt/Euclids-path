# Euclids-path

Консолидация доказательной программы гипотезы **простых-близнецов**, выстроенной вокруг
**вечного двигателя Евклида** (невозможность бесконечного «чистого» спуска — версия бесконечного
спуска Ферма).

Это **не завершённое доказательство**. Это машинно-проверяемая сборка, в которой гипотеза сведена
к **одному** открытому узлу, а весь ход — от законов двигателя до финальной редукции — виден по
пронумерованным файлам.

> **Карта хода доказательства:** [`prose/00_Overview.md`](prose/00_Overview.md) — главный навигатор.
> **Источник истины:** первичные записи в `f:/Primes/*.md`/`*.csv` (не редактируются). При расхождении
> первичны исходники.

---

## Структура

- **`EuclidsPath/Engine/*.lean`** — основная (доказанная) линия: двигатель и его законы → редукция к
  близнецам → линии-атаки → финальный узел. Импортируются корневым `EuclidsPath.lean` **в порядке
  хода доказательства**.
- **`prose/NN_*.md`** — парная проза, та же сквозная нумерация 00→32 (+ приложение `A`), единый
  академический нарратив от двигателя до Римана.
- **`tools/`** — числовые харнессы (`*_harness.py`) и результаты (`RESULTS_*.md`).
- **`archive/`** — первая **аналитическая** линия (PMKLS/DASC/G2/O4C, `B₅=N₀₀−N₃₃`), изученная и
  **обойдённая**. Сохранена ради видимого хода мысли (см. `archive/README.md`).

## Ход (проза ↔ Lean)

| № | Тема | Проза | Lean | Статус |
|---|---|---|---|---|
| 00 | Цель, карта хода, определения | [00](prose/00_Overview.md) | `Step00_Overview` | 🔴 цель |
| 01 | Невозможность двигателя (EPMI) | [01](prose/01_EPMI.md) | `Engine/EPMI` | 🟢 |
| 02 | Носитель двойки `gcd∣2` | [02](prose/02_Carrier.md) | `Engine/Carrier` | 🟢 |
| 03 | Сохранение двойки `XY−ZW=2` | [03](prose/03_TwoGap.md) | `Engine/TwoGap` | 🟢 |
| 04 | Спуск + boundary-law | [04](prose/04_Descent.md) | `Engine/Descent` | 🟢 |
| 05 | Необратимость / 2 закона | [05](prose/05_Irreversibility.md) | `Engine/Irreversibility` | 🟢 |
| 06 | Нет хода назад (эксклюзивность) | [06](prose/06_NoBackward.md) | `Engine/NoBackward` | 🟢 |
| 07 | Короткий train (squeeze) | [07](prose/07_Squeeze.md) | `Engine/Squeeze` | 🟢 |
| 08 | Ограниченный цикл | [08](prose/08_BK.md) | `Engine/BK` | 🟢 |
| 09 | Factor-repeat rigidity | [09](prose/09_Cycle.md) | `Engine/Cycle` | 🟢 |
| 10 | survivor ⇒ twin; мост ∞ | [10](prose/10_NonCover.md) | `Engine/NonCover` | 🟢 |
| 11 | Гипотеза ⟸ блочное ядро | [11](prose/11_TwoTransport.md) | `Engine/TwoTransport` | 🟢 |
| 12 | Four-corner (отриц. ассоциация) | [12](prose/12_FourCorner.md) | `Engine/FourCorner` | 🟢 |
| 13 | Фрактальный слой / модель | [13](prose/13_FractalLayer.md) | `Engine/ModelFourCorner` | 🟢 |
| 14 | Декомпозиция остатка | [14](prose/14_RealFourCorner.md) | `Engine/RealFourCorner` | 🟢 |
| 15 | Цепь к близнецам (условно `H`) | [15](prose/15_ToTwins.md) | `Engine/ToTwins` | 🟢 |
| 16 | От противного: finite∧H⇒False | [16](prose/16_FiniteContradiction.md) | `Engine/FiniteContradiction` | 🟢 |
| 17 | Закон оплаты (ledger) | [17](prose/17_PaymentLedger.md) | `Engine/PaymentLedger` | 🟢 |
| 18 | SNOL — shifted-neighbour узел | [18](prose/18_SNOL.md) | `Engine/SNOL` | 🟢 |
| 19 | Old-peel: catch как шаг спуска | [19](prose/19_OldPeel.md) | `Engine/OldPeel` | 🟢 |
| 20 | NOPSL: нет old-peel sink | [20](prose/20_NOPSL.md) | `Engine/NOPSL` | 🟢 |
| 21 | Дихотомия регенерации (Ω_A) | [21](prose/21_Regeneration.md) | `Engine/Regeneration` | 🟢 |
| 22 | Residuals: старт, sink⇒twin | [22](prose/22_Residuals.md) | `Engine/Residuals` | 🟢 |
| 23 | Clean/boundary граф | [23](prose/23_CleanGraph.md) | `Engine/CleanGraph` | 🟢 |
| 24 | Boundary-декомпозиция + глоб. узел | [24](prose/24_BoundaryDecomp.md) | `Engine/BoundaryDecomp`, `Engine/LabelledFanIn`, `Engine/AtomicSNOL`, `Engine/ConcreteComponents`, `Engine/BadCoverDescent`, `Engine/ObstructionClosure`, `Engine/ManyUnresolved`, `Engine/HigherEnergy`, `Engine/HigherTower`, `Engine/EngineTower` | 🟢 деком.; 🔴 узел |
| 25 | Rigid-замыкание (reaches_twin) | [25](prose/25_RigidClose.md) | `Engine/RigidClose` | 🟢 |
| 26 | Separating scale ⟹ ¬ProductHall | [26](prose/26_SeparatingScale.md) | `Engine/SeparatingScale` | 🟢 |
| 27 | Product-core: вся машина | [27](prose/27_ProductCore.md) | `Engine/ProductCore` | 🟢 |
| 28 | Факторизация → RankNode | [28](prose/28_MkNode.md) | `Engine/MkNode` | 🟢 |
| 29 | **Последнее звено + граница** | [29](prose/29_CarrierBridge.md) | `Engine/CarrierBridge` | 🔴 единственный узел |
| 30 | Риман: контрапозиция (двигатель) | [30](prose/30_RiemannBranch.md) | `Engine/RiemannBranch` | 🔴 вход RH |
| 31 | Риман через Лиувилля (λ=(−1)^rank) | [31](prose/31_RiemannLiouville.md) | `Engine/RiemannLiouville` | 🔴 вход RH |
| 32 | Единый rank-parity узел (эпилог) | [32](prose/32_RankParityUnity.md) | — (синтез) | 🔴 гипотеза единства |
| A | Численные данные | [A](prose/A_NumericalEvidence.md) | `tools/RESULTS_*` | — |

🟢 = машинно проверено, без `sorry` (стандартные аксиомы). 🔴 = открытый узел / вход.

## Статус (честно)

- **Доказано (без `sorry`, стандартные аксиомы):** весь двигатель и его законы (EPMI); редукция
  гипотезы к блочному ядру; модельный four-corner; алгебра оплаты; раскрытие SNOL в old-peel-спуск
  (sign law, height drop, замыкание на двигатель); дихотомия регенерации; separating scale ⟹
  `¬ProductHall` **чистой арифметикой**; **вся product-core машина** (экстенсиональность, rank-descent
  4→1, база rank-1, pigeonhole); факторизация `RankNode` из составной стороны; бесконечность carrier.
  Все прежние стены (parity, трилемма `UniqueLegalLift`, steering-self-loop, циркулярный payment,
  три дефекта rank-descent) **сняты**.
- **Единственный открытый узел:** `GlobalOldAbsorption` ([29](prose/29_CarrierBridge.md),
  `tools/RESULTS_final_gap.md`) — бесконечно много поглощаемых родословных на **растущем** масштабе
  спуска (fan-in `570 → 1`), а не в фиксированном отрезке `[1, X_A]`. `Step00.twin_prime_conjecture`
  остаётся `sorry` до его закрытия. Это **честная редукция**, а не доказательство.
- **Побочная ветвь (Риман):** независимая контрапозиция через двигатель
  ([30](prose/30_RiemannBranch.md)) и через функцию Лиувилля `λ(n)=(−1)^{rank(n)}`
  ([31](prose/31_RiemannLiouville.md), тождество и флип **доказаны**); открытый вход — оценка
  `LiouvilleBound` `|L(x)|=O(√x·x^ε)`. Единый rank-parity узел ([32](prose/32_RankParityUnity.md))
  показывает, что оставшийся узел близнецов и узел RH — **одна и та же** стена контроля чётности ранга
  (гипотеза единства, не редукция).
- `sorry` подделать нельзя: «зелёный» модуль = реально проверенная часть.

## Сборка

```sh
lake exe cache get    # прекомпилированные oleans mathlib (v4.31.0)
lake build            # вся Engine-линия; exit 0 = проверено
lake env lean EuclidsPath/Engine/EPMI.lean   # быстрый чек ядра двигателя
```

`archive/` не входит в основную сборку (исторический контекст).
