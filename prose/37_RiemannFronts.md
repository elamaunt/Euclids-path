# 37. Римановы фронты сессии

<!--navtop-->
[← 36. Навье–Стокс: уравнение](36_NavierStokes.md) · [Оглавление](00_Overview.md) · [38. Риман через первопричину →](38_RiemannFirstCause.md)
<!--/navtop-->



> Lean: `Engine/RiemannTrivialZeros.lean` (вход №1 закрыт — 🟢), `Engine/RiemannRankProjection.lean` +
> `Engine/RiemannRankProjectionAudit.lean` (эпизод вакуумности №2), `Engine/RiemannTwoTransportFront.lean`,
> `Engine/RiemannArithmeticTwoTransport.lean`, `Engine/RiemannSpectralAnchorAudit.lean`,
> `Engine/RiemannLayerBoxFront.lean` (25 кирпичей), `Engine/RiemannTerminalRankFront.lean` (18 кирпичей).
> Проза-контекст: [30. Гипотеза Римана](30_RiemannBranch.md), [24](24_BoundaryDecomp.md) (диссипативный cascade). Все процитированные теоремы —
> 🟢 при стандартных аксиомах, без `step00FirstCause`; сама RH — 🔴 открыта, и ниже это не смягчается.

Риманова ветка репозитория — контрапозиция через двигатель: нетривиальный нуль вне критической прямой
должен был бы питать вечную платную динамику, которой не бывает (`no_riemannEngineFactoryOff`). Вся
аналитика при этом жила в двух входах — напомним, вход (гейт) — это честно названное красное
утверждение, которого не хватает до цели (см. [словарь](GLOSSARY.md)): классификация нулей в левой полуплоскости
(вход №1) и мост «нуль ⟹ двигатель» (`EngineBridge`, вход №2 со свитой).

Эта глава — хроника одной сессии: один вход
закрыт по-настоящему, одна обёртка вскрыта как пустая, один маршрут доказанно циркулярен, один
критерий честности доказанно неправилен — и в остатке два живых входа.

## Вход №1 закрыт: тривиальные нули

**Теорема 37.1** (`trivialBelowZeroClassification`) 🟢. Всякий нуль $\zeta$ с $\mathrm{Re}\,s \le 0$ есть тривиальный нуль:
$$\forall s \in \mathbb{C},\quad \zeta(s) = 0 \wedge \mathrm{Re}\,s \le 0 \;\Rightarrow\; \exists n \in \mathbb{N},\; s = -2(n+1). \tag{37.1}$$
Маршрут целиком из mathlib: $s=0$ исключён (`riemannZeta_zero` $= -1/2$); для $s \ne 0$ функциональное
уравнение `riemannZeta_one_sub` в точке $w = 1-s$ (где $\mathrm{Re}\,w \ge 1$), нетривиальные факторы
не нули (`riemannZeta_ne_zero_of_one_le_re`, `Gamma_ne_zero_of_re_pos`, `cpow_ne_zero`), значит
обнулился косинус: $\cos(\pi(1-s)/2)=0 \Rightarrow s = -2k$, $k \ge 1$.

Бывший «аналитический вход»
оказался выводимым: mathlib давал значения тривиальных нулей, и обратная классификация из него же и
следует.

Адаптеры `trivialBelowZeroClassification_proved` / `_branch_proved` втыкают теорему в точные
Prop'ы `RiemannEngine`/`RiemannBranch`; безусловные следствия: `nontrivialZero_in_strip_unconditional`
(локализация в полосу $0<\mathrm{Re}\,\rho<1$ — теперь теорема) и пара
`riemannHypothesis_of_engineBridge_only` / `riemannHypothesis_of_twoTransportBridge_only` — RH условна
*только* на мосте.

**Вывод.** Это честное закрытие: вход снят, нагрузка не переехала, а исчезла.

## Вакуумность №2: rank-jump цель непривязана

Симметричный по жанру, противоположный по знаку результат — эпизод вакуумности: так мы называем
ситуацию, когда кандидат-цель выполняется даром, свидетелем-заглушкой (см. [словарь](GLOSSARY.md)).
Маршрут №8 декомпозировал мост через
Лиувилля: нарушение RH-bound'а $|L(X)| \le C\,X^{1/2+\varepsilon}$ ⟹ переполнение релевантной части
⟹ непарный носитель ⟹ rank-jump.

Кирпичи `RiemannRankProjection` доказаны честно:
`rankProjectionSoundness`, дискретная first-crossing лемма `exists_firstOverflowCrossing` (Nat.find),
сборка `gradualOverflow_forces_rankJump`. Кусок (A) тоже честен:
`relevantViolation_gives_window` — конкретный ledger (mass $=|L_{\mathrm{relevant}}|$, capacity
$=\lceil X^{1/2+\varepsilon}\rceil$) с настоящим окном переполнения.

Но адверсариальный probe (`RiemannRankProjectionAudit`) вскрыл цель. `TwinCarrierEnergyJump` — голое
`Nonempty (RankEnergyJump …)` без привязки к нарушению: для естественной системы (rank $=\Omega$,
sign $=\lambda$) он — *безусловная теорема* `liouvilleRankSystem_has_jump` (состояния 1 и 2 уже
прыгают), откуда `localizationTarget_trivial_for_natural_system` — центральный узел тривиален.

Хуже:
`fullLocalization_noInput` — полный пакет `LiouvilleToTwinLocalization` обитаем с **нулевым
аналитическим входом** (partition «всё релевантно», `irrelevantCancellation_trivial`,
`paired := False`); поле `paired` инертно (`unpaired_gives_jump` его не упоминает), а rank-видимость
дискаржится даром (`trivialVisibility`: пара $\langle 0,1\rangle$ для любого носителя). Декомпозиция
«cancellation + pairing» была ложной: pairing-сторона веса не несла.

Честный остаток —

**Теорема 37.2** (`wall_relevant` / `wall_global`) 🟢. Для любой jump-free системы $S$ (нет twin-carrier прыжка) с pairing'ом $P$ отсутствует нарушение Лиувилля:
$$\lnot\,\mathrm{TwinCarrierEnergyJump}(S) \wedge \mathrm{TwinCarrierPairing}(P,S) \;\Rightarrow\; \lnot\,\mathrm{LiouvilleViolation}. \tag{37.2}$$

То есть для любой системы, пригодной downstream (jump-free),
pairing — это ровно $\lnot$`LiouvilleViolation`, т.е. стена маршрута №8 — сам RH-силы bound на $L$.
Ничего не потеряно, кроме иллюзии: RH не доказана, обёртка вскрыта, цель требует переформулировки
с привязкой к нарушению.

## Two-transport: циркулярность наследуется

Живой вход №1 (мост) декомпозирован в `TwoTransportLaw` — non-opaque замену `EngineBridge`, где все
paid-dynamics обязательства выставлены полями. Машинная честность конкретного слоя беспощадна:
**Теорема 37.3** (`no_coherent_twoTransportLaw`) 🟢. Для любого off-critical нуля $Z$ когерентный закон невозможен (`CoherentLaw`: вселенная закона совпадает со вселенной его платной динамики):
$$\forall Z,\; \forall\, T : \mathrm{TwoTransportLaw}(Z),\quad \mathrm{CoherentLaw}(T) \;\Rightarrow\; \bot, \tag{37.3}$$
ибо $T$ строил бы фабрику, а фабрика безусловно пуста (engine-killer).

И главное,

**Теорема 37.4** (`coherentTwoTransportBridge_iff_RH`) 🟢. Когерентный two-transport мост эквивалентен RH *дословно*:
$$\mathrm{CoherentTwoTransportBridge} \;\Longleftrightarrow\; \mathrm{RiemannHypothesis}. \tag{37.4}$$ Декомпозиция — карта обязательств, а не некруговой путь;
аудит-гейты `zero_anchored`/`non_circular` свободны (`regateTrivially` перегейтирует их в `True`) —
маркеры, не проверки.

## Арифметический атом и полярный коллапс

Ответ на коллапс — не-двигательная цель: `ArithmeticTransportAtom`, шесть положительных параметров с
тождеством twin-слоя $qrs = abv + 2$ (`natGap_eq_two`: зазор ровно 2).

Но интеграционный аудит
показал, что и тут привязка к нулю пока не несущая: `trivialAtom` ($3 = 1 + 2$) существует даром, и
**Теорема 37.5** (`law_iff_admissibleAtom`) 🟢. Обитаемость арифметического two-transport закона при данном $Z$ эквивалентна $Z$-*независимому* вопросу `AdmissibleAtomExists`:
$$\forall Z,\quad \mathrm{Nonempty}\big(\mathrm{ArithmeticTwoTransportLaw}(Z)\big) \;\Longleftrightarrow\; \mathrm{AdmissibleAtomExists}. \tag{37.5}$$

Оба входа фронта — `bridge_iff` и `impossible_iff` — один и тот же
арифметический вопрос, разведённый по полярности под гипотезой нуля, и

**Теорема 37.6** (`front_pair_iff_no_zero`) 🟢. Пара входов (мост и невозможность) совместно выполнима тогда и только тогда, когда нулей нет:
$$\big(\mathrm{ArithmeticTwoTransportBridge} \wedge \mathrm{ArithmeticTwoTransportImpossible}\big) \;\Longleftrightarrow\; \lnot\,\mathrm{Nonempty}(\mathrm{OffCriticalZero}). \tag{37.6}$$ Циркулярность
сохраняется, пока anchor свободен. Сборка с настоящим извлечением репо
(`RH_of_concreteArithmeticFront`) готова — но кормить её пока нечем.

## Исправленный фронт: невакуумность живёт на уровне данных

Следующий слой (`RiemannSpectralAnchorAudit`) формализует сам вскрытый коллапс (`FreeLawCollapse`;
стыковка `concrete_freeLawCollapse`: моя `law_iff_admissibleAtom` и есть free-коллапс конкретного
маршрута) и доказывает тонкий негативный результат:
**Теорема 37.7** (`propLevel_nonvacuity_incompatible_with_bridge`) 🟢. Prop-уровневый критерий «закон никогда не коллапсирует в $Z$-независимое утверждение» несовместим с самим мостом:
$$\big(\forall P : \mathrm{Prop},\; \lnot\,\mathrm{PropFreeCollapse}(\mathrm{Law}, P)\big) \wedge \mathrm{PropBridge}(\mathrm{Law}) \;\Rightarrow\; \bot, \tag{37.7}$$
ибо доказанный мост коллапсирует закон в `True`.

Критерий честности обязан жить на уровне *данных* — то есть быть data-anchor'ом, якорем в данных:
реальным объектом, привязывающим пропозициональный закон к настоящей задаче
(см. [словарь](GLOSSARY.md)).

Отсюда `DataAnchoredLaw`
(Admissible + Anchor), экстрактор атомов из нулей, `SpectralInvariantAnchor` с полем `respects`
(инвариант заякоренного атома = инвариант нуля) и `NonVacuousDataAnchor` (два нуля с разными
инвариантами) — тогда `nonVacuousDataAnchor_forbids_freeOriginSupply` и
`extractor_not_constant_under_nonVacuousDataAnchor` 🟢 запрещают free-origin поставку и константные
экстракторы. Исправленное обязательство упаковано в `SpectralAnchorStrictFront`.

## Партия layerbox/terminal: что реально доказано в 43 кирпичах

Серии `RiemannLayerBoxFront` (25 кирпичей) и `RiemannTerminalRankFront` (18) — самая массовая
поставка сессии, и флаги сборочного аудита тут важнее объёма.

Реально доказанная арифметика —
mod-6 residue-факты:

**Теорема 37.8** (`no_identity_with_residues_555_111_plus_two`) 🟢. Полярность $q,r,s \equiv 5$, $a,b,v \equiv 1 \pmod 6$ несовместима с тождеством twin-слоя:
$$q,r,s \equiv 5 \pmod 6 \;\wedge\; a,b,v \equiv 1 \pmod 6 \;\wedge\; qrs = abv + 2 \;\Rightarrow\; \bot \tag{37.8}$$
(слева вычет $qrs \equiv 5$, справа $abv+2 \equiv 3 \pmod 6$),
`tuple555_111_unbalanced_mod6`, `tuple511_511_balanced_mod6` (kernel-checked `decide`;
`native_decide` из кирпичей выброшен — доверие `ofReduceBool` не введено), плюс генерические
well-founded descent / finite-cover сборки.

Остальное — каркасы обязательств, и честность требует
сказать это прямо: *каждый* closure-сертификат terminal-серии несёт поле
`target_of_noZeros : (нулей нет) → Target` — RH-образный вывод является *входом*, а сама
no-zeros-часть приходит из assumption-полей (`contradiction : False` в
`LayerPressure`/`DeterminantPressure` — неинстанциируемые слоты, не доказательства); гейты типа
`NonEngineCoherenceFirewall` и Prop-леджеры инертны.

**Итог раздела.** Партия дала язык и таблицы, не мосты.

## Итог: два живых входа

Дихотомия сессии, зафиксированная terminal-слоем: двигательно-когерентные маршруты пусты или
циркулярны (⟺ RH); free-origin арифметика — не мост, а внешняя $0\to 1$ поставка (поставка — то,
чем отклонение расплачивается; см. [словарь](GLOSSARY.md)); Лиувилль-маршрут —
эквивалентность целевой силы ($\lnot$`LiouvilleViolation`).

Живыми остаются два входа: (1) **несущая
спектральная привязка** — data-anchor со спектральным инвариантом и zero-indexed экстрактором
(`SpectralAnchorStrictFront`, конечный LayerBox-транскрипт как последняя нетривиальная форма), и
(2) **`AdmissibleAtomExists`** как самостоятельный арифметический вопрос — интересный сам по себе,
но пока его решение в любую сторону не разъякорено от полярного коллапса.

RH — 🔴; закрыт по-честному
только вход №1, и ровно поэтому этой главе есть что предъявить: отрицательные и вскрывающие теоремы
здесь такие же машинные, как положительные.

## Постскриптум (глава 38)

После этой главы Риман проведён через первопричину: закон манифестации отклонений стал **второй
границей единственного декрета**, и `riemannHypothesis_from_firstCause` 🟡 выводит RH из
расширенной аксиомы той же ранговой машиной, что и близнецов — с машинно раскрытой ценой
(`riemannManifestation_asserts_RH`: при границе закон ⟺ RH). Оба живых входа этой главы остаются
🔴 и нетронутыми: фронты — карты обязательств для безаксиомного пути, декрет — намеренный обход по
цене, объявленной вслух. См. [38_RiemannFirstCause.md](38_RiemannFirstCause.md).

<!--navbot-->

---

[← 36. Навье–Стокс: уравнение](36_NavierStokes.md) · [Оглавление](00_Overview.md) · [38. Риман через первопричину →](38_RiemannFirstCause.md)
<!--/navbot-->
