# 00. Пролог: двигатель Евклида, близнецы, Риман и классические фронты — одна rank-parity программа

> Это входной файл всей программы — пролог и главный навигатор. Дальше идут пронумерованные главы
> `prose/NN_*.md` (парная проза, 00→38) и модули `EuclidsPath/Engine/*.lean` (машинная проверка).
> Здесь мы вводим объект, объявляем стратегию, чертим карту частей I–VIII и — главное — честно
> фиксируем, что именно доказано машинно, что условно на единственную аксиому, а что открыто.
>
> **Легенда статусов:** 🟢 — доказано машинно при стандартных аксиомах Lean/mathlib;
> 🟡 — **AXIOM-TAINTED**: условно на единственную аксиому репозитория `step00FirstCause`
> (первопричина `0 → 1` с двумя границами — twin-узел и римановский закон манифестации; карантин
> `Engine/CausalClosureAxiom.lean`, ровно 31 такая декларация, утечек нет — верификатор
> отслеживает каждую); 🔴 — открытый узел / цель.
> Сама цель `twin_prime_conjecture` остаётся `sorry`. Ничего сильнее машинных фактов здесь нет.

## ★ Главная теорема программы

**`higherEnergyIncompatibility_main`** (`Engine/FiniteKnowledgeBarrier`) — **высшая энергетическая
несовместимость**, пять граней одной несовместимости, ядро целиком 🟢 (аксиомо-свободно):

1. внутреннее знание первопричины **строит** вечный двигатель (`knowledge_builds_perpetualEngine`);
2. потому первопричина непознаваема изнутри — `cause_unknowable` (двигателей нет, `lexRank`);
3. конечный просеивающий вид знает близнеца только целиком чистым классом — близнец со смешанным
   классом принципиально невидим (`mixed_class_twin_unknowable`);
4. при хвостовом смешении классов бесконечность близнецов изнутри неудостоверима
   (`infinitude_unknowable_of_eventually_mixed`);
5. несущая грань: сама несовместимость (нет двигателей = непознаваемость) + принятая причинная
   граница ⟹ близнецы бесконечны (`twins_infinite_of_noEngine_and_boundary`).

Читается это так: **знание изнутри стоит вечного двигателя, которого нет; бесконечность близнецов —
внешнее знание, оплачиваемое первопричиной.** Обе стены — одна природа (`two_walls_one_nature`, 🟢).
Следствие **`higherEnergyIncompatibility_twins`** — `TwinLowers.Infinite` — 🟡 AXIOM-TAINTED:
грань 5 инстанциирована декретом `step00FirstCause`. Это условный вывод, **не** доказательство
гипотезы близнецов.

## 1. Объект: двигатель Евклида как well-founded мультипликативный спуск

Всё здание стоит на одном элементарном объекте: «состояние» евклидова процесса разложения сводится
к его **высоте** — индексу $m$ центра пары $(6m-1,\,6m+1)$; чистый шаг спуска уменьшает высоту
**мультипликативно**: $\mathrm{DescentStep}(A,h,h') :\Leftrightarrow A\cdot h' < h$ (`DescentStep`,
`Engine/EPMI`). Двигатель Евклида — гипотетическая бесконечная последовательность высот, в которой
каждый шаг таков. Её не существует: $H(t)+t$ не возрастает, а строго убывающая цепь натуральных
высот обрывается — это бесконечный спуск Ферма, переписанный мультипликативно.

**Теорема (невозможность вечного двигателя).** `no_infinite_descent`, структурная форма
`no_perpetual_engine`, дихотомия шага `boundary_dichotomy` — все 🟢, без `sorry`, на голом ядре
Lean 4 (даже без mathlib). Это самый твёрдый камень фундамента: любая конструкция, предъявленная
как вечный двигатель, автоматически ложна.

## 2. Стратегия: контрапозиция через двигатель

Для каждой цели $P$ (бесконечность близнецов; Риман; фронты) строится мост
$\neg P \Rightarrow \mathsf{Engine}$ и замыкается доказанным EPMI:
$(\neg P \Rightarrow \mathsf{Engine}) \land \neg\,\mathsf{Engine} \Rightarrow P$. Для близнецов:
конечность близнецов (`NoNewTwinAbove M0`) загоняет бесконечный поток чистых стартов в конечное
множество старых поглотителей — rigid-цикл, двигатель, противоречие. Для Римана: нуль вне
критической прямой даёт бесплатную направленную перекачку массы — снова двигатель. Мы **не** пишем
`twins ⟹ RH`: общее у ветвей не следствие, а механизм — один EPMI, одна контрапозиция и, как
покажет §4, один rank-parity инвариант.

## 3. Карта частей I–VIII

**I. Двигатель и его законы (гл. 01–09, 🟢).** Ядро невозможности (`Engine/EPMI`, гл. 01);
носитель двойки `no_large_shared_divisor` (`Engine/Carrier`, гл. 02); 1-й закон $XY-ZW=2$ —
`det_law_rank33` (`Engine/TwoGap`, гл. 03); спуск и boundary-law (`Engine/Descent`, гл. 04);
необратимость, `turn ⇒ halt` (`Engine/Irreversibility`, гл. 05); исчезновение диагонали
(`Engine/NoBackward`, гл. 06); squeeze, ограниченный цикл, factor-repeat rigidity
(`Engine/Squeeze`, `Engine/BK`, `Engine/Cycle`, гл. 07–09).

**II. Редукция к близнецам (гл. 10–11, 🟢).** `infinite_of_unbounded_centers` (`Engine/NonCover`,
гл. 10); `twin_prime_conjecture_of_blocks` (`Engine/TwoTransport`, гл. 11).

**III. Линии-атаки и стена чётности (гл. 12–17, 🟢 условно/модельно).** Four-corner
(`Engine/FourCorner`, гл. 12); модельный слой (`Engine/ModelFourCorner`, гл. 13); декомпозиция
остатка (`Engine/RealFourCorner`, гл. 14); цепь к близнецам (`Engine/ToTwins`, гл. 15);
`finite ∧ H ⇒ False` (`Engine/FiniteContradiction`, гл. 16); ledger (`Engine/PaymentLedger`, гл. 17).

**IV. Финальная редукция twin-линии (гл. 18–25, 🟢 + 🔴 узел).** `twin_primes_of_SNOL`
(`Engine/SNOL`, гл. 18); old-peel (`Engine/OldPeel`, гл. 19); NOPSL (гл. 20);
`regeneration_dichotomy` (`Engine/Regeneration`, гл. 21); residuals/clean-graph (гл. 22–23);
boundary-декомпозиция и **финальный узел близнецов** `TheLastStep00Obligation`
(`Engine/BoundaryDecomp`, `Engine/ConcreteStep00Graph` и свита, гл. 24); rigid-замыкание
`reaches_twin` (`Engine/RigidClose`, гл. 25).

**V. Product-core rank descent (гл. 26–29, 🟢 + 🔴 узел).** `no_productHall`
(`Engine/SeparatingScale`, гл. 26); `product_core_engine_of_carrier` (`Engine/ProductCore`, гл. 27);
`factor_rank_le_four` (`Engine/MkNode`, гл. 28); `cleanCenters_infinite`,
`engine_of_factorization` (`Engine/CarrierBridge`, гл. 29).

**VI. Риманова ветка и rank-parity мост (гл. 30–32).** `riemann_of_engine_bridge`,
`not_RH_gives_engine` (`Engine/RiemannBranch`, `Engine/RiemannEngine`,
`Engine/RiemannImpossibleEngine(-Off)`, `Engine/RankJumpBridge`, гл. 30);
`liouville_eq_neg_one_pow_rank`, `riemann_of_liouville_bound` (`Engine/RiemannLiouville`, гл. 31);
единый rank-parity узел — эпилог-гипотеза (гл. 32).

**VII. Первопричина и барьер конечного знания (гл. 33, пишется параллельно).** Карантинная аксиома
`step00FirstCause` и её теоремная свита: `step00CausalClosure` (теперь теорема из первопричины),
честность `step00FirstCause_iff_causalClosure` (маркеры несут `True`, вся сила в границе),
эквивалентность остатка `nonAxiomaticRemainingObligation_iff_lastStep00Obligation`
(`Engine/CausalClosureAxiom`); эпистемика — `cause_unknowable`, `two_walls_one_nature` и **главная
теорема** `higherEnergyIncompatibility_main` (`Engine/FiniteKnowledgeBarrier`) — см. блок ★ выше.

**VIII. Классические фронты (гл. 34–37, пишутся параллельно).**
— *Мерсенн (гл. 34):* тождество $M_p = 6c+1$ — `mersenne_eq_sixCenter_add_one`, условный мост
`twinLowersInfinite_of_mersenneTwins`, честный гейт `noTwinsToMersenneImplicationClaimed`
(`Engine/MersenneBranch`); платёжный конфликт — `soundness_forbids_mersennePrimePaymentConflict`,
`twinLowersInfinite_of_infiniteMersenneSupply` (`Engine/MersennePaymentConflict`); peel-давление —
`mersenneCenter_base4PeelStep`, `absence_forces_peelCoverage_or_paymentLaw_defect`
(`Engine/MersennePeelPressure`); форвард-фронт из 34 кирпичей (`Engine/MersenneForwardFront`) —
⚠️ поздние noEngine-пакеты **необитаемы** (вакуумность №3, см. §5).
— *P vs NP, локально (гл. 35):* `verificationEasy_always`,
`localPSuccess_iff_semanticFlowLedgerCollisionResolves`, `localP_success_detects_twin`,
безусловная несжимаемость малого масштаба `concrete_localSearchIncompressible_smallScale`
(`Engine/LocalPNPNode`); классический мост — `genealogyLanguage_in_NP`,
`classicalSeparation_of_localIncompressible`, гейт области `bridgeScopeGuard_ok`
(`Engine/ClassicalPNPBridge`); каноническая самозедукция — `extracts_local_success_of_selfReduction`,
антивакуумный гейт `trivialFrame_not_faithful` (`Engine/CanonicalSelfReduction`); маршруты фронта —
`extracts_local_success_of_bitwiseEncoding` (`Engine/ClassicalFrontierRoutes`); дисциплина ранга —
`no_rankBoundaryEngine`, `taxonomyExpansion_not_strictProgress` (`Engine/RankClosureFront`).
— *Навье–Стокс (гл. 36):* `ns_no_infinite_dissipative_cascade`,
`ns_no_infinite_dissipative_cascade_of_balance`, `kineticEnergy_nonneg` (`Engine/NavierStokes`,
каркас каскада — `Engine/DissipativeCascade`) — структурное «нет бесконечного диссипативного
каскада», **не** задача регулярности Клэя.
— *Риман-фронты (гл. 37):* вход закрыт — `trivialBelowZeroClassification` 🟢
(`Engine/RiemannTrivialZeros`, функциональное уравнение mathlib): RH условна **только** на
`EngineBridge` (`riemannHypothesis_of_engineBridge_only`) или `TwoTransportBridge`; rank-projection
маршрут и его вскрытие (`Engine/RiemannRankProjection`, `Engine/RiemannRankProjectionAudit` —
вакуумность №2, см. §5); two-transport форма и её честность `coherentTwoTransportBridge_iff_RH`
(`Engine/RiemannTwoTransportFront`); арифметический атом $+2$ —
`riemannHypothesis_of_arithmeticTwoTransport` (`Engine/RiemannArithmeticTwoTransport`);
спектральные аудиты — `front_pair_iff_RH`, `no_single_atom_anchors_two_distinct_invariants`
(`Engine/RiemannSpectralAnchorAudit`), origin-blind firewall
`no_identity_with_residues_555_111_plus_two` (`Engine/RiemannLayerBoxFront`), терминальный
rank-фронт — `no_free_origin_for_distinct_zeros`, чек-лист 66 линий / 11 балансов
(`Engine/RiemannTerminalRankFront`).

## 4. Единый rank-parity узел

Обе исходные гипотезы редуцируются к одному инварианту — чётности ранга
$\mathrm{rank}(n)=\Omega(n)$. Twin-сторона: эксклюзивность двойки (`no_large_shared_divisor`)
запрещает перекрёстный член $xy$ в производящей функции рангов и форсирует четырёхугольное
неравенство $N_{00}N_{33}\le N_{03}N_{30}$ (`N33_lt_N00_of_four_corner`, `Engine/FourCorner`) —
баланс близнецов есть баланс rank-parity. Риман-сторона: $\lambda(n)=(-1)^{\mathrm{rank}(n)}$
(`liouville_eq_neg_one_pow_rank`), `deleteFactor` флипает знак (`liouville_flip_of_mul_prime`),
а RH — малость $L(x)=\sum_{n\le x}(-1)^{\mathrm{rank}(n)}$ (`LiouvilleBound`). Один инвариант,
один оператор, одна стена чётности — потому мы говорим об **одном rank-parity узле**. Фронты
части VIII — попытки обойти эту стену с разных сторон; их аудиты (гл. 37) машинно показывают,
где обход подлинный, а где — переупаковка RH.

## 5. Честный статус по веткам

**Близнецы — 🔴 один узел, максимально сужен.** Вся ветка машинно сведена к
`TheLastStep00Obligation` (`Engine/ConcreteStep00Graph`):
`twinLowersInfinite_of_lastStep00Obligation` 🟢. Узел — twin-детектор: `twin_above_of_resolves`
(вход на масштабе `M0` сам предъявляет twin выше `M0` — он не слабее цели помасштабно); вся семья
из ~15 эквивалентных форм (energy / nested / seam / gauge / compression …) машинно ⟺ ему.
⚠️ **Сужение (адверсариальный probe):** ветвь `A ≤ 4` **опровергнута** — 5-адическая цепь
$c(k{+}1)=5c(k)+1$ даёт бесконечно много admissible-генеалогий без twin-гипотез
(`smallScale_branch_of_lastStep00Obligation_refuted`); `∃A` живёт только при `A ≥ 5`
(`lastStep00Obligation_forces_scale_ge_five`). ⚠️ **Вакуумность №1 (вскрыта, починена):**
дегенеративный peel `p = p·1` делал узел опровержимым; заплата `properDiv` + `targetPos` — теперь
twin-гипотеза несущая, выполнимость при `A ≥ 5` подлинно открыта. Условное замыкание через
первопричину (`higherEnergyIncompatibility_twins` и родня) — 🟡. `Step00.twin_prime_conjecture`
остаётся `sorry`.

**Риман — 🔴 входы фронтов, 🟡 через расширенный декрет.** 🟢: `trivialBelowZeroClassification`
(всякий нуль с `Re ≤ 0` тривиален) — RH условна только на
`EngineBridge`/`TwoTransportBridge`/`LiouvilleBound`.
⚠️ **Вакуумность №2 (вскрыта, не приукрашена):** цель rank-jump-маршрута не привязана — полный
пакет `LiouvilleToTwinLocalization` обитаем с нулевым входом (`fullLocalization_noInput`),
честная стена — ровно `¬LiouvilleViolation` (`wall_global`) = RH-силы; window-бухгалтерия при этом
закрыта честно (`relevantViolation_gives_window`). Машинная честность мостов:
`offCriticalBridge_iff_RH`, `coherentTwoTransportBridge_iff_RH`, `no_coherent_twoTransportLaw` —
декомпозиции суть карты обязательств, не некруговой путь.
✳️ **Через первопричину (глава 38):** RH проведена той же ранговой машиной, что близнецы — нуль
вне прямой = неоплаченное отклонение; закон манифестации (вторая граница декрета) + зелёная
невозможность поставки на разрешённых масштабах ⟹ `riemannHypothesis_from_firstCause` 🟡.
НЕ доказательство RH; цена раскрыта: `riemannManifestation_asserts_RH` — при границе закон ⟺ RH.

**P vs NP — локальная архитектура, не классическая теорема.** 🟢: верификация легка всегда
(`verificationEasy_always`), локальный успех ⟺ семантический узел близнецов
(`localPSuccess_iff_semanticFlowLedgerCollisionResolves`), на малом масштабе `A ≤ 4`
несжимаемость безусловна (`concrete_localSearchIncompressible_smallScale`). Классическое
разделение (`classicalSeparation_of_localIncompressible`) условно на `remainingBridgeObligation` —
гейт `localPNP_is_architecture_local` фиксирует явно: это **не** доказательство P ≠ NP.

**Навье–Стокс — структурный результат, не Клэй.** 🟢: `ns_no_infinite_dissipative_cascade` —
при энергетическом балансе бесконечный диссипативный каскад невозможен (тот же well-founded
механизм EPMI в $\mathbb{R}_{\ge0}$). О глобальной регулярности гладких решений ничего не заявлено.

**Мерсенн — условные мосты + вакуумность №3.** 🟢: арифметика центров, условный экспорт
`twinLowersInfinite_of_mersenneTwins` и платёжно-peel'ные дихотомии дефектов. ⚠️ **Вакуумность №3
(вскрыта, зафиксирована в шапке модуля):** в `Engine/MersenneForwardFront` поздние
noEngine-пакеты (`NoForbiddenPrimePaymentEngine`-семейство и родня) **необитаемы** — токены несут
свободное поле `witness : Prop`, «двигатель» строится тривиально, headline-выводы этих кирпичей
вакуумны; маршруты в этой форме неинстанциируемы. Безусловных сильных выводов в ветке нет.

**Первопричина — 🟡 карантин, две границы.** Единственная аксиома `step00FirstCause` несёт
twin-узел (`causalBoundary`) и римановский закон манифестации (`riemannBoundary`, глава 38);
ровно 31 AXIOM-TAINTED декларация (30 в карантинном модуле + задокументированное следствие
`higherEnergyIncompatibility_twins`), верификатор репортит каждую. Непротиворечивость расширенной
теории ⟺ неопровержимость узла и RH в базе (растяжки — узел / off-critical нуль / ¬RH / закон);
интернализация первопричины невозможна — двигатель
(`no_internalSelfDerivation_step00CausalClosure`, 🟢).

**Итог честно.** 🟢-корпус — реально проверенная машина: двигатель, редукции, аудиты, главная
теорема (ядро). 🟡-слой — ровно то, что оплачено первопричиной, и он отделён карантином.
🔴 — `TheLastStep00Obligation` при `A ≥ 5`, входы RH, классические фронты. Редукция — не
доказательство; `sorry` подделать нельзя.

## Где мы и куда дальше

Мы ввели объект (`no_infinite_descent`), объявили стратегию (контрапозиция через двигатель),
расчертили части I–VIII и поставили в вершину карты `higherEnergyIncompatibility_main`: знание
изнутри стоит вечного двигателя, которого нет. Следующая глава [01. EPMI] строит фундамент
буквально — на голом ядре Lean; главы 33–38 разворачивают первопричину (теперь с двумя
границами — близнецы и Риман) и классические фронты.
