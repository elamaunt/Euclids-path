# 35. P/NP: локальный узел и классический мост

<!--navtop-->
[← 34. Ветка Мерсенна](34_MersenneBranch.md) · [Оглавление](00_Overview.md) · [36. Навье–Стокс: уравнение →](36_NavierStokes.md)
<!--/navtop-->



> Lean: `Engine/LocalPNPNode.lean` (абстрактный узел + конкретная инстанциация),
> `Engine/ClassicalPNPBridge.lean` (классический фрейм, мост, extraction-слой),
> `Engine/CanonicalSelfReduction.lean` (faithful-фреймы, fuel-протокол, генерическое закрытие run),
> `Engine/RankClosureFront.lean` (rank-closure серия, 6 кирпичей),
> `Engine/ClassicalFrontierRoutes.lean` (классический фронт, 42 кирпича одной сборкой),
> §12/§12bis `PvsNPAnalogy` в `Engine/ConcreteStep00Graph.lean`.
> Проза-предшественник: [24. BoundaryDecomp](24_BoundaryDecomp.md), раздел «Структурная аналогия P/NP».
> В этой главе *нет* жёлтых деклараций: аксиома `step00FirstCause` нигде не используется;
> всё либо 🟢 доказано при стандартных аксиомах, либо 🔴 открыто.

В [24](24_BoundaryDecomp.md) мы заметили, что стена близнецов имеет узнаваемую вычислительную анатомию: прямой ход
двигателя дёшево проверяется, а обратный поиск генеалогии не сжимается в конечный ключ. Тогда это
было наблюдение внутри одного файла.

Настоящая глава разбирает, во что оно выросло: асимметрия
стала теоремой конкретного графа (и на малых масштабах — безусловной), финальный узел близнецов
получил точную P/NP-форму, вокруг него построен абстрактный локальный узел, а от узла — честный
условный мост к классическим классам сложности.

Сразу зафиксируем рамку, чтобы не создавать ложных
ожиданий: **ничего о настоящих P и NP здесь не доказывается** — ни машин Тьюринга, ни кодировок,
ни теоремы «P ≠ NP» в репозитории нет, и это оформлено машинно (`localPNP_scopeGuard`,
`bridgeScopeGuard`, см. финальный раздел).

## Асимметрия как теорема конкретного графа

На графе `6m±1` обе стороны аналогии доказаны (🟢, `PvsNPAnalogy` в `ConcreteStep00Graph.lean`).
P-сторона: любой forward-путь длины $n$ из состояния $X$ имеет
$n \le \mathrm{lexRank}(X)$, поэтому каждая генеалогия «проверяется дёшево» (`VerificationEasy`,
`verificationEasy_always` — свойство *всех* потоков, не гипотеза).

**Теорема 35.1** (`pathN_len_le_lexRank`). Для любых $A, M_0 \in \mathbb{N}$ и любого forward-пути
длины $n$ по шагу `RealStep` $A\,M_0$, ведущего из $X$ в $Y$, выполнено $n \le \mathrm{lexRank}(X)$.
Ранг строго убывает на каждом шаге, поэтому его начальное значение ограничивает длину любой
генеалогии — проверка линейна по рангу.

NP-сторона:
`search_not_compressible_of_infinite` — на бесконечной семье состояний конечный ключ проекции
теряет информацию (`finite_key_cannot_determine_state_on_infinite`), то есть обратный поиск не
сжимается в конечный сертификат. Обе стороны разом даёт следующая теорема.

**Теорема 35.2** (`verify_easy_but_search_not_compressible`). Для любых $A, M_0$, любой
семантической проекции $\mathrm{proj}$ и любого бесконечного множества состояний $S$ выполнено
одновременно: (i) $\forall F,\ \mathrm{VerificationEasy}(F)$ — *каждый* порождённый поток
проверяется дёшево; и (ii) $\mathrm{SearchNotCompressible}(\mathrm{proj}, S)$ — обратный поиск на
$S$ не сжимается в конечный ключ. Асимметрия «проверка легка / поиск несжимаем» здесь не лозунг, а
конъюнкция двух машинных фактов.

Более того, на малых масштабах несжимаемость **безусловна**.

**Теорема 35.3** (`concrete_localSearchIncompressible_smallScale`). При $A \le 4$ конкретная задача
`concreteProblem` $A\,1$ удовлетворяет $\mathrm{LocalSearchIncompressible}$: не существует
конечноключевого резолвера. Доказательство (🟢, `LocalPNPNode.lean`): бесконечная 5-адическая цепь
потоков (`fiveAdicChainFlow`) пиджонхолом (конечный ключ не может инъективно пометить бесконечное
семейство, см. [словарь](GLOSSARY.md)) создаёт same-key коллизию, а обе резолюционные альтернативы
при $A \le 4$ уже опровергнуты (`no_extendedFlowResolutionAlternative`).

Ирония, которую надо проговорить честно: это та самая
5-адическая цепь, что в [24](24_BoundaryDecomp.md) сузила финальный узел близнецов до $A \ge 5$. Безусловная теорема
несжимаемости живёт ровно на той шкале, которая для близнецов *мертва*; на живой шкале $A \ge 5$
вопрос открыт 🔴.

## Узел близнецов — это P/NP-узел

§12bis фиксирует связку.

**Теорема 35.4** (`twin_reduction_is_pnp_node`). `TheLastStep00Obligation` («конечный сертификат
разрешения коллизий генеалогий достаточен») влечёт `TwinLowers.Infinite` (бесконечность семьи
близнецовых понижений): формально $\mathrm{TheLastStep00Obligation} \Rightarrow
\mathrm{TwinLowers.Infinite}$ (🟢).

Это переформулировка уже известной `twinLowersInfinite_of_lastStep00Obligation`, но она даёт узлу
имя на новом языке: единственный оставшийся вход всей близнецовой ветки (вход, или гейт, — честно
названное красное утверждение, которого не хватает до цели, см. [словарь](GLOSSARY.md)) — вопрос «достаточен ли
полиномиальный сертификат обратного пути», то есть `PolyCertificateSuffices` =
`SemanticFlowLedgerCollisionResolves` в P/NP-одежде.

Условная сторона тоже доказана:
`branch_closes_if_polyCertificateSuffices` — если сертификат достаточен И семья генеалогий
бесконечна, ветка схлопывается. Сам узел не предъявлен и не опровергнут (🔴), и Теорема 35.2
(`verify_easy_but_search_not_compressible`) объясняет, почему он не даётся даром: сертификат теряет
информацию, значит «сертификата
достаточно» — дополнительная арифметика fan-in, а не следствие сжатия.

## Локальный узел: абстракция и её обитаемость

`LocalPNPNode.lean` вынимает эту структуру в абстрактный кирпич: `RankedForwardGraph` (ранг строго
падает на шаге), сертификаты-генеалогии с доказанной P-стороной (`PathN.len_le_lexRank`,
`GenealogyCertificate.verificationEasy_always`), пиджонхол-принцип `FiniteKeyCollisionPrinciple`.

К этому — локальный P-успех `LocalPSuccess` и его отрицание `LocalSearchIncompressible`, twin-детектор
(`localP_success_detects_twin`, `twinBound_forces_localSearchIncompressible`) и семантический
интерфейс `localPSuccess_iff_semanticFlowLedgerCollisionResolves`. Итоговый пакет —
`localPNP_status_slogan` (🟢).

Ключевой вопрос к любой такой абстракции — обитаема ли она. Здесь да, и не игрушечно: граф
инстанциации — **сам** Step00-граф репо (`concreteGraph` = `State`/`RealStep`/`lexRank`),
сертификаты инъективны (`concreteCertificate_injective` — данные-поля плюс proof irrelevance).

Дальше по списку: локальный P-успех эквивалентен существованию резолвящей проекции репо
(`concreteSemanticInterface`), детектор — `twin_above_of_resolves` из [24](24_BoundaryDecomp.md)
(`concreteTwinDetector`). При $A \le 4$ собран полный статус-пакет
`concreteLocalPNPStatus_smallScale` (🟢), где collision principle — безусловная теорема
(`concrete_collisionPrinciple_smallScale`), а не параметр.

## Классический фрейм: честность прежде моста

`ClassicalPNPBridge.lean` вводит `ClassicalComplexityFrame`: предикаты `InP`/`InNP` на языках плюс
замыкание P под poly-прообразами. И здесь модуль сам вскрывает свою главную слабость: **InP и InNP
абстрактны**.

**Теорема 35.5** (`trivialFrame_separates_for_free`). Тривиальный фрейм с `InP := False`,
`InNP := True` удовлетворяет `ClassesSeparate` (🟢, намеренная анти-теорема): существует язык в NP,
но не в P, — свидетелем служит любой язык, поскольку `InP` тождественно ложно. Иначе говоря,
$\mathrm{ClassesSeparate}$ относительно произвольного фрейма не стоит ничего.

Петля честности замыкается в `CanonicalSelfReduction.lean`: `FaithfulPFrame` требует конкретных
decider'ов за `InP` и принадлежности `TrueLanguage`/`FalseLanguage` классу P.

**Теорема 35.6** (`trivialFrame_not_faithful`). Не существует `FaithfulPFrame` над тривиальным
фреймом: любой такой объект даёт `False` (🟢) — из `InP := False` немедленно следует противоречие с
требуемой принадлежностью `TrueLanguage` классу P. Дегенеративный фрейм честности не удовлетворяет.
Дегенерация отсечена машинно, но
обратная сторона медали обязательна к произнесению: пока `FaithfulClassicalFrame` не инстанциирован
реальной моделью машин, ни одно `ClassesSeparate` в этих файлах не говорит о настоящих P/NP.

## Мост и его несущее поле

Сам мост — `Step00ToClassicalBridge`: кодирование локального узла как классического языка, где
NP-сторона (`verifier_yields_NP`) — лёгкая половина, а несущее поле —
**`P_decider_extracts_local_success`**: любой P-решатель кодированного языка обязан выдавать
локальный резолвер.

При этом поле условные теоремы доказаны (🟢):
`classicalSeparation_of_localIncompressible`, `classicalSeparation_under_twinBound`,
`classicalSeparation_at_smallScale` — несжимаемость узла плюс мост дают разделяющий язык
(относительно фрейма!). Остаток честно назван: `RemainingClassicalBridgeObligation`.

Extraction-слой раскрывает несущее поле в конструкцию: `PDecider` (sound/complete решатель),
`ConcretePAccess` (из абстрактного `InP` — реальный решатель), `LocalResolverTarget`,
`CanonicalResolverReconstruction`, и `PDeciderExtractionField.extracts_local_success` (🟢) собирает
из них ровно недостающее `C.InP L → N.LocalPSuccess`.

Дальше `CanonicalSelfReduction.lean` делает
реконструкцию алгоритмом: ограниченный адаптивный протокол запросов
(`BoundedAdaptiveQueryProtocol`, fuel строго падает на шаге), терминальный декодер
(`TerminalResolverDecoder`), и — важный генерический факт — терминация fuel-исполнителя
**доказана**.

**Теорема 35.7** (`runSteps_done_of_fuel`). Для любого протокола $P$ и любого решателя $D$: если
$P.\mathrm{fuel}(s) \le n$, то $P.\mathrm{done}(\mathrm{runSteps}\,P\,D\,n\,s)$ (🟢). Иначе говоря,
исполнитель, стартовавший с запасом fuel не меньше остатка, гарантированно завершается: строгое
падение fuel на каждом шаге плюс спуск в $\mathbb{N}$ дают терминацию. Поэтому поля
`run`/`run_done` закрываются конструктором `selfReduction_of_protocol_and_decoder` раз и навсегда.

Живой остаток фронта — `FaithfulSelfReductionFront`: протокол + декодер + верный фрейм +
несжимаемость узла; всё это 🔴 не инстанциировано на живой шкале.

## Фронт v2–v8 и его аудит

Дальше репозиторий разворачивает широкий фронт маршрутов. `RankClosureFront.lean`: все
False-выводы гипотезо-зависимы, а «P-neq-NP-образное» `rankLocalClasses_do_not_coincide` условно
на `RankSeparationWitness`, **который нигде не построен** — и сам является renamed-conclusion
входом («inNP + unbounded» подано на вход); по-домовому это переименование цели — «закон»,
равносильный самой цели (см. [словарь](GLOSSARY.md)).

`ClassicalFrontierRoutes.lean` (42 кирпича:
frontier-манифесты v2–v8, circuit ladder, proof complexity, FP/FNP, bitwise decision-to-search)
прошёл сборочный аудит с явными флагами в заголовке: удалён `falseDecider` — кирпич заявлял
решатель любого языка константой false и был ложен как сформулирован; исключён дубликат;
два Prop-как-доказательство дефекта починены усилением входов.

Далее по флагам: около 30 slogan-abbrev — буквально
`Prop := True` (маркеры, не теоремы), аудит-гейты `gate/gate_proof` повсеместно инстанциируемы
`True` (то же честно показано и для моста: `PDeciderExtraction.regateReconstruction`);
renamed-conclusion входы (`BitwiseClassicalBridgeFront` и родня) несут `local_incompressible`
готовым полем — их `ClassesSeparate` есть переупаковка гипотезы. Итог аудита: **безусловных
`ClassesSeparate`/`False` во фронте нет; `sorry`/`axiom` нет.**

## Scope и место в общем ходе

Границы утверждений оформлены как теоремы: `localPNP_is_architecture_local` и `bridgeScopeGuard_ok`
(🟢, тривиальны по построению — и это честно: они документируют отсутствие заявки, а не доказывают
её невозможность). В репозитории нет модели машин Тьюринга, нет кодировок и полиномиальных оценок
времени; слова «P» и «NP» всюду означают Step00-локальные роли «rank-ограниченная проверка» и
«несжимаемый обратный поиск».

Что глава добавляет к общему ходу программы: стена близнецов теперь
не только арифметический факт ([24](24_BoundaryDecomp.md)) и энергетический (energy-ledger-формы там же), но и вычислительный —
единственный вход `TheLastStep00Obligation` изоморфен вопросу «достаточен ли конечный сертификат
против ветвящегося поиска», причём на опровергнутой шкале $A \le 4$ ответ машинно «нет». Если
когда-нибудь узел падёт при $A \ge 5$, мост немедленно превратит это в разделение классов — но
лишь относительно фрейма, который ещё предстоит сделать верным.

**Вывод.** До тех пор: аналогия — теорема,
мост — условность, классические P/NP — не тронуты. `twin_prime_conjecture` остаётся `sorry`.

## Постскриптум (глава 39, вакуумность №4)

Адверсариальный аудит главы 39 вскрыл о фронтах *этой* главы: `PDecider` не несёт
complexity-содержания и классически строится для любого языка
(`classicalPDecider` 🟢), поэтому decider-gated extraction-фронты
(`FaithfulSelfReductionFront`, `CurrentExtractionFront`), связывающие
реконструкцию с несжимаемостью, *классически пусты* (`IsEmpty` — теоремы) —
их `gives_classicalSeparation` вакуумны, то есть выполняются даром, ничего не
утверждая (вакуумность — см. [словарь](GLOSSARY.md)). Это **вакуумность №4** программы.

InP-gated мост (`Step00ToClassicalBridge`) не затронут — `InP` абстрактен;
но слой фреймов пластичен в обе стороны (`allPFrame` faithful и совпадает даром,
`constantsFrame` faithful и разделяет даром). Само же неравенство в ранговой
модели — 🟢 теорема: см. [39_PNPRankPayment.md](39_PNPRankPayment.md)
(«NP = полная оплата сертификатов ранга» — `concrete_localPSuccess_iff_fullPayment`;
сепарация — `pnp_rank_separation_smallScale`; трилемма — декретный обход
невозможен машинно).

<!--navbot-->

---

[← 34. Ветка Мерсенна](34_MersenneBranch.md) · [Оглавление](00_Overview.md) · [36. Навье–Стокс: уравнение →](36_NavierStokes.md)
<!--/navbot-->
