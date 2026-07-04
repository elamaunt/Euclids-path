/-
  Корневой модуль `Euclids-path`. Импорты идут В ПОРЯДКЕ ХОДА ДОКАЗАТЕЛЬСТВА
  (двигатель Евклида → его законы → редукция к близнецам → линии-атаки → финальный узел SNOL).

  Карта хода: prose/00_ProofPath.md. Парная проза к каждому модулю — prose/NN_*.md.
  Старая аналитическая линия (PMKLS/DASC/G2/O4C) — изучена и обойдена, см. archive/.

  Легенда статуса:
    * доказанные модули — без `sorry` (стандартные аксиомы);
    * единственная открытая цель — `Step00.twin_prime_conjecture` (= финальный узел SNOL);
    * единственный явный вход к закрытию — `SNOL.SNOLInput` (он же `ToTwins`-`H`).
  `sorry` подделать нельзя: «зелёный» файл = реально проверенная часть.
-/

-- 00. Основания: цель и базовые определения (TwinLowers, IsTwinCenter)
import EuclidsPath.Step00_Overview

-- I. Двигатель Евклида и его законы (атомарные, доказанные)
import EuclidsPath.Engine.EPMI              -- невозможность вечного двигателя
import EuclidsPath.Engine.Carrier           -- shared gcd ∣ 2 (носитель двойки)
import EuclidsPath.Engine.TwoGap            -- XY−ZW=2 (сохранение двойки, 1-й закон)
import EuclidsPath.Engine.Descent           -- строгий спуск + boundary-law
import EuclidsPath.Engine.Irreversibility   -- не повернёт назад / асимметрия / turn⇒halt (2-й закон)
import EuclidsPath.Engine.NoBackward        -- диагональ исчезает (эксклюзивность)
import EuclidsPath.Engine.Squeeze           -- cubic squeeze (короткий train)
import EuclidsPath.Engine.BK                -- bounded additive cycle
import EuclidsPath.Engine.Cycle             -- factor-repeat rigidity, cross-side fuel

-- II. Редукция гипотезы близнецов к блочному ядру
import EuclidsPath.Engine.NonCover          -- survivor ⇒ twin; infinite_of_unbounded_centers
import EuclidsPath.Engine.TwoTransport      -- twin_prime_conjecture_of_blocks

-- III. Линии-атаки на оценку (изучены по пути; упираются в стену чётности)
import EuclidsPath.Engine.FourCorner        -- N₃₃<N₀₀ из four-corner + side-corner
import EuclidsPath.Engine.ModelFourCorner   -- 20·C(n,6) ≤/< C(n,3)² (модельный, строгий)
import EuclidsPath.Engine.RealFourCorner    -- точная декомпозиция остатка
import EuclidsPath.Engine.ToTwins           -- twin_primes_of_four_corner (условно на H)
import EuclidsPath.Engine.FiniteContradiction -- finite ∧ H ⇒ False (3 маршрута от противного)
import EuclidsPath.Engine.PaymentLedger     -- channel/tax/shifted-primorial/Y_A (закон оплаты)

-- IV. Финальный узел: единственная открытая лемма
import EuclidsPath.Engine.SNOL              -- rank descent → rank-1 → shifted-neighbour (SNOL)
import EuclidsPath.Engine.OldPeel           -- SNOL раскрывается в old-peel ⇒ EPMI-противоречие
import EuclidsPath.Engine.NOPSL             -- NOPSL: нет old-peel sink ⇒ twin sink (замыкание)
import EuclidsPath.Engine.Regeneration      -- Old-Peel Regeneration: дихотомия Ω_A (случаи 1–3)
import EuclidsPath.Engine.Residuals         -- Step00-остатки: start (primorial), sink⇒twin, height
import EuclidsPath.Engine.RigidClose        -- rigid-замыкание: reaches_twin без цикла + cofactor_is_center
import EuclidsPath.Engine.CleanGraph        -- clean/boundary split: clean-sink ⟹ twin выше M₀ (исправление)
import EuclidsPath.Engine.BoundaryDecomp    -- BoundaryExit декомпозиция + глобальный absorber-узел
import EuclidsPath.Engine.PumpFinal         -- pump (условно) + разрыв EPMI на self-loop
import EuclidsPath.Engine.PumpStanding      -- pump v2 (two-token standing cycle) + EPMI-разрыв остаётся
import EuclidsPath.Engine.RiemannBranch     -- побочная ветка: RH от противного через двигатель (условно)
import EuclidsPath.Engine.RiemannLiouville  -- RH через Liouville-эквивалентность (λ=(−1)^rank)
import EuclidsPath.Engine.ProductHall       -- ProductHall/Steering pump (4-случайная логика, без циркулярного payment)
import EuclidsPath.Engine.SeparatingScale   -- separating scale: ¬ProductHall чистой арифметикой (закрыт узел)
import EuclidsPath.Engine.RankDescent       -- energy-defect trichotomy + конечный product-rank descent
import EuclidsPath.Engine.ProductCore       -- исправленный product-core: 3 дефекта закрыты теоремами
import EuclidsPath.Engine.CarrierBridge     -- последнее звено: carrier бесконечен; вход = FactorizationData
import EuclidsPath.Engine.MkNode            -- mkNode: RankNode из составной стороны (арифметика, доказано)
import EuclidsPath.Engine.LabelledFanIn     -- labelled fan-in: König ДОКАЗАН, SNOL сведён (v2→v4)
import EuclidsPath.Engine.AtomicSNOL         -- post-audit: legal subtype (нет hAll) + SNOL-free atomic + SNOLDeriv (R8 = красная линия)
import EuclidsPath.Engine.ConcreteComponents -- discharge active/old-peel компоненты из separating scale; локализация counting-стены
import EuclidsPath.Engine.BadCoverDescent    -- обход counting-стены: bad-cover finite descent (условная редукция, R3 = новая красная линия)
import EuclidsPath.Engine.ObstructionClosure -- абстрактный well-founded obstruction-двигатель; входы НЕинстанциируемы (SNOL.bad — counting)
import EuclidsPath.Engine.ManyUnresolved     -- маршрут many-unresolved collision: комбинаторика доказана, U4-терминал циркулярен
import EuclidsPath.Engine.HigherEnergy       -- weighted debt energy: реальный well-founded движок; вход = step00_promotion_is_weightedDebtReplacement
import EuclidsPath.Engine.HigherTower        -- Euclidean Tower: fixed-center BadTower ВАКУУМЕН; moving tower = orientation стена
import EuclidsPath.Engine.EngineTower        -- EngineTower без traversal: recurrence-ветка ТОЖЕ вакуумна; escape/collision = counting стена
import EuclidsPath.Engine.ParityBarrier       -- стена чётности как ТЕОРЕМА: finite-sieve не сертифицирует twin; пересечение требует cofinal
import EuclidsPath.Engine.ReverseTower        -- reverse engine: дерево предков + barrier (абстрактный no-go); Step00-мосты = стена
import EuclidsPath.Engine.AboveConflict       -- конфликт в «Above»: order-логика тривиальна; step00_forces_above_conflict в ловушке (машинно)
import EuclidsPath.Engine.JumpBarrier          -- jump/cut-barrier: paid jump + cofinal cut-пиджонхол (доказано); force-ray/barrier = входы (стена)
import EuclidsPath.Engine.PaidDynamics         -- платная динамика: no free inertia/acceleration/cloning (доказано); regeneration-to-close = SNOL стена
import EuclidsPath.Engine.ClosedUniverse       -- двигатель не покидает вселенную: universe-preservation + closed-paid no-run (доказано); promotion_paid_or_closes = стена
import EuclidsPath.Engine.BoundaryDefectPayment -- boundary-дефект: извлечение SmallPrimeDefect + невозможность no-tax оплаты (доказано); вход = дихотомия цикл∨оплата
import EuclidsPath.Engine.BoundaryLedgerCollision -- ledger-коллизия: пиджонхол + сжигание оплаты ⟹ цикл (доказано); вход = collision-resolve
import EuclidsPath.Engine.ConcreteStep00Graph  -- КОНКРЕТНЫЙ граф 6m±1 (не абстрактный σ); lexRank высота ДОКАЗАНА (падает на absorb); остаток = ledger/семья/resolve
import EuclidsPath.Engine.TwinNodeEpistemic -- 🟢 эпистемический комплемент УЗЛА: опровержение близнецов = безусловная поставка (twinBound_carries_unbounded_supply) ⟹ двигатель в стабильной вселенной; strict-сужение узла к A ≥ 5; twinNode_unknowable; таинт не растёт
import EuclidsPath.Engine.TwinScaleAdvances -- 🟢 масштабные продвижения узла: малый масштаб A ≤ 4 мёртв при ВСЕХ базах M0 ≥ 1 (no_projection_resolves_at_smallScale_allM0, 5-адика+пижонхол); растущий разделяющий масштаб (exists_growing_separating_scale, Бертран+примориал, шаг (1) плана §29.6); барьер §29.5 машинно виден (fixedWindow_factorization_impossible_at_separating_scale); мост скелетов BoundaryDecomp↔CarrierBridge; таинт не растёт
import EuclidsPath.Engine.RiemannEngine        -- RH→OffCriticalZero→Engine (чистая форма); мосты = входы; RH не доказана
import EuclidsPath.Engine.RiemannImpossibleEngine -- RH через невозможный closed-paid двигатель: no_riemannEngineFactory БЕЗУСЛОВНА; вход = strip-bridge
import EuclidsPath.Engine.RiemannImpossibleEngineOff -- OffCritical версия: убирает TrivialBelowZeroClassification; ЕДИНСТВЕННЫЙ вход = OffCriticalRiemannEngineBridge
import EuclidsPath.Engine.RankJumpBridge        -- rank/parity мост (Лиувилль λ=(−1)^Ω ↔ factory): всё ВОКРУГ узла доказано; §4 запрет читинга; вход = RankJumpLocalization
import EuclidsPath.Engine.DichotomyEngine       -- УНИФИКАЦИЯ: Close∨paid-step ⟹ Close неизбежен (close_forced); все режимы читинга поглощены; вход = локальная дихотомия
import EuclidsPath.Engine.DissipativeCascade    -- cascade-сертификат (Step00/RH/NS-аналогия): capacity/overflow декомпозиция Лиувилль-узла; ℝ vs ℕ warning
import EuclidsPath.Engine.NavierStokes          -- САМО уравнение НС (PDE-предикат, mathlib fderiv/gradient/∫): momentum+incompressible; ноль-решение; каскад-связка
import EuclidsPath.Engine.RiemannRankProjection -- живой узел №8 RH-ветки: строгая+градуальная декомпозиция unpaired_gives_jump (first-crossing ДОКАЗАНА); стыковка с TwinCarrierPairing
import EuclidsPath.Engine.RiemannTrivialZeros -- ВХОД №1 ЗАКРЫТ: классификация нулей Re≤0 ДОКАЗАНА (функц. уравнение); RH теперь условна ТОЛЬКО на EngineBridge
import EuclidsPath.Engine.RiemannRankProjectionAudit -- ⚠️ вакуумность №2: цель маршрута №8 не привязана; честная стена = ¬LiouvilleViolation; window-бухгалтерия закрыта
import EuclidsPath.Engine.RiemannTwoTransportFront -- вход №1 в two-transport форме: split+realization+builder; ЧЕСТНОСТЬ: когерентный мост ⟺ RH (циркулярность наследуется)
import EuclidsPath.Engine.RiemannArithmeticTwoTransport -- НЕ-двигательная цель: qrs = abv + 2 (зазор 2 доказан); ЧЕСТНОСТЬ: при свободном anchor оба входа = один вопрос AdmissibleAtomExists
import EuclidsPath.Engine.RiemannSpectralAnchorAudit -- аудит коллапса формализован; Prop-невакуумность — неправильный критерий (доказано); исправленный фронт = data-anchor со спектральным инвариантом
import EuclidsPath.Engine.MersenneBranch -- Мерсенн: вложение 2^p−1 = 6m_p+1 + twin-критерий; ЧЕСТНО: Мерсенн-близнецы ⟹ близнецы (НЕ наоборот!)
import EuclidsPath.Engine.MersennePaymentConflict -- платёжный маршрут: sound-леджер + давление ⟹ ∞ Мерсенн-близнецов ⟹ TwinLowers.Infinite; ЧЕСТНОСТЬ: для канонич. леджера pressure = вывод
import EuclidsPath.Engine.MersennePeelPressure -- расщепление давления: coverage+payment-law, затем debt+realization; цепи до TwinLowers.Infinite; канонический коллапс = честность
-- КОЛЛАТЦ (заземлён на ту же первопричину; граница = ЧЕТВЁРТОЕ поле step00FirstCause, §18):
import EuclidsPath.Engine.CollatzEngine     -- Коллатц: строгий закон НАРУШЕН (нечётный шаг поднимает высоту, нет Ляпунова); even_marginal/odd_accel_ascends/not_descent_on_odd 🟢
import EuclidsPath.Engine.CollatzFuel       -- Коллатц: топливо конечно В СРЕДНЕМ (дрейф ×0.864), но монотонной высоты НЕТ (k=1 при n≡1 mod 4 растит); no_monotone_height 🟢
import EuclidsPath.Engine.CollatzTugOfWar   -- Коллатц: канат vs двигатель, window_budget ⟹ спуск при перевесе; ГЕРОЙ reaches_one_of_countingLaw (per-n, условный); универсальный закон каната ОПРОВЕРГНУТ 🟢 (not_ropeCountingLaw_27, ropeLaw_universal_refuted — свидетель n=27); опровержение гипотезы=вечный двигатель 🟢
import EuclidsPath.Engine.CollatzFirstCause -- 🟢 ПОСТ-МОРТЕМ декрета: четвёртая граница ВЗЯТА И СНЯТА (растяжка сработала — закон ложен, декрет переплатил до лжи); трилемма закрыта кованым опровержением (как ЯМ); эпистемика уцелела (collatzCause_unknowable, collatz_open_status); гипотеза Коллатца 🔴 открыта
import EuclidsPath.Engine.LocalPNPNode -- строгий локальный P/NP-узел + конкретная инстанциация (при A≤4 несжимаемость БЕЗУСЛОВНА); scope guard: НЕ классические P/NP
import EuclidsPath.Engine.ClassicalPNPBridge -- мост к классическим P/NP: несущее поле = извлечение локального резолвера из P-decider'а; ЧЕСТНОСТЬ: фрейм абстрактен (trivialFrame разделяет даром)
import EuclidsPath.Engine.CanonicalSelfReduction -- fuel-протокол self-reduction: run/run_done закрыты ГЕНЕРИЧЕСКИ (терминация доказана); FaithfulPFrame отсекает trivialFrame
import EuclidsPath.Engine.RiemannLayerBoxFront -- layerbox-серия (25): residue-таблицы/move-алгебра/blocker-ядра; ЧЕСТНО: доказана mod-6 арифметика + generic сборки, остальное — каркасы
import EuclidsPath.Engine.RiemannTerminalRankFront -- terminal/rank-flow (18); ЧЕСТНО: target_of_noZeros — вывод как ВХОД; инертные firewall'ы помечены
import EuclidsPath.Engine.MersenneForwardFront -- Мерсенн-форвард (34); ВНИМАНИЕ: поздние noEngine-пакеты НЕОБИТАЕМЫ (свободный witness) — headline-теоремы вакуумны, раскрыто
import EuclidsPath.Engine.ClassicalFrontierRoutes -- P/NP-фронт (42); удалён ложный falseDecider; ~30 слоганов = True; входы-переупаковки помечены
import EuclidsPath.Engine.RankClosureFront -- rank-closure (6); разделение целиком условно на невыстроенном witness
import EuclidsPath.Engine.FiniteKnowledgeBarrier -- СТРОГО: конечная система не знает про близнецов почти ничего (чистота классов, propext-only); две стены — одна природа
import EuclidsPath.Engine.RiemannDualEngineFront -- дуальный маршрут (3): синхронизация оплат фантом/подлинный, встреча⟺смена ранга, счётный мост близнецы↔встречи↔нули; ЧЕСТНО: все законы — поля-входы, мост считает НЕтривиальные (не off-critical) нули
import EuclidsPath.Engine.RiemannManifestationFront -- ЗЕЛЁНАЯ римановская цепь первопричины: закон манифестации отклонений + невозможность на разрешённых масштабах (L2) + essence-лемма (L3) + аудиты (закон⟺RH ПРИ границе, L7)
import EuclidsPath.Engine.RiemannLawEpistemic -- 🟢 эпистемика закона манифестации: самообоснование самоуничтожается (riemannCause_unknowable); отклонение при сведённых книгах строит двигатель (deviation_carries_engine_at_resolved_scale); граница жива — эпистемика о невозможности ВНУТРЕННЕГО обоснования
import EuclidsPath.Engine.PNPRankPaymentFront -- ЗЕЛЁНАЯ P/NP-цепь: NP = полная оплата сертификатов ранга, P = ранго-быстрый проезд; СЕПАРАЦИЯ ПРИ A ≤ 4 БЕЗУСЛОВНА; трилемма кандидатов третьего поля декрета доказана (двое опровержимы, третий вакуумен); ВАКУУМНОСТЬ №4: decider-gated extraction-фронты классически пусты
import EuclidsPath.Engine.PNPFirstCause -- 🟢 ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ P/NP (зеркало CollatzFirstCause): решение P/NP непознаваемо ИЗНУТРИ конечнотопливной строгоправильной машины (pnpCause_unknowable); оплатить изнутри неограниченную поставку = вечный двигатель (no_internalisedPNPGround, реюз no_fullPayment_of_unboundedSupply + no_perpetual_engine_on_nat); БЕЗ декрета (у P/NP честной границы нет — трилемма); НЕ классический P≠NP, НЕ Гёдель; таинт не растёт
import EuclidsPath.Engine.YangMillsFront -- ЗЕЛЁНАЯ ветвь Янга–Миллса: gapless-спектр = вечный двигатель (halving-лестница = ℝ-предупреждение каскада); закон квантования ⟹ масс-гэп (EPMI-убийца); трилемма четвёртой границы: универсал опровержим, экзистенциал вакуумен, манифестация несовместима с границей; per-model закон ⟺ гэп ЗЕЛЕНО — четвёртого поля НЕТ; Клэй не объявлен
import EuclidsPath.Engine.YangMillsEpistemic -- 🟢 эпистемика ЯМ: лестница = подлинный двигатель (ladder_carries_real_engine, quantizedLadder_carries_perpetual_engine); ymCause_unknowable; L9-коллапс раскрыт честно
import EuclidsPath.Engine.NavierStokesFront -- ЗЕЛЁНАЯ НС-ветвь гладкости: сингулярный каскад = вечный двигатель (убит бюджетом при энергобалансе); тождество энергии и интегральная форма решения ВЗЯТИЕМ ИНТЕГРАЛА (FTC, E3-значный); трилемма пятой границы: универсал опровержим (cookedFlow), экзистенциал вакуумен (нуль), манифестация несовместима с границей; суррогат ≠ C^∞ — раскрыто; Клэй не объявлен
import EuclidsPath.Engine.NavierStokesR3Assembly -- ПЕРЕХОД НА ℝ³: интеграл НС собран на боксе — R1 производная энергии под интегралом (доминирование), R2 теорема о дивергенции РЕАЛЬНО задействована (грани гаснут по носителю), энергобаланс ВЫВЕДЕН зелёно для бокс-класса ⟹ каскадная гладкость БЕЗ декрета; давление гейтовано впервые (канал Ковки-B закрыт); предел box→ℝ³ отсутствует в mathlib — внешний разрыв; три E3-киллера — именованные входы
import EuclidsPath.Engine.NavierStokesClayReduction -- РЕДУКЦИЯ К ОДНОЙ ТЕОРЕМЕ: точная постановка Клэя-(A) закодирована; зелёная логическая редукция «известная теория (Като+BKM) + GlobalVorticityControl ⟹ Клэй-(A)»; открытое ЯДРО изолировано и названо (контроль вихря, барьер суперкритичности); НС НЕ решена — честная карта ярусов, таинт неизменен
import EuclidsPath.Engine.CascadeBudget -- T2: абстрактная бюджет-лемма (конечный бюджет не выдержит вечной РАВНОМЕРНОЙ диссипации) + КОНКРЕТНАЯ конечная шелл-модель (реальная ОДУ) + честная граница budget_misses_nonuniform (неравномерный каскад ускользает); первая формализация шелл-модели жидкости
import EuclidsPath.Engine.DyadicBlowup -- T1: ригорозное ядро супер-линейного взрыва (y'≥Cy² ⟹ конечное время) + модель Кац–Павлович (телескоп энергии) → dyadic_blowup; A→B: драйв ВЫВЕДЕН из сырых λⁿ-связей — для точного автомодельного решения (§2bis: ssMode, ssLead_drive) и для КЛАССА через инвариант фронта (§2ter: FrontDomination, frontDrive_of_invariant), монолитная superlinearDrive-гипотеза сужена; бесконечно-модовая сохранность (фронт) честно открыта; §2quater: исток n=0 неказуем изнутри (🟢); каскад = РЕАЛИЗОВАННЫЙ двигатель
import EuclidsPath.Engine.ContinuousEngine -- НЕПРЕРЫВНО-ВРЕМЕННОЙ двигатель H(t)=r^t над ℝ (M1, первый формальный) — ℝ-аналог ложности EPMI на континууме; сходимость≠противоречие (M2), supertask масштаб→0 до T (M3), связь Клэя как Iff.rfl (M4), честный эндпоинт (M5); M6 — ГДЕ двигатель НЕВОЗМОЖЕН: равномерный дренаж на конечном топливе форсирует эндпоинт (T≤H0/β), r^t уцелевает лишь неравномерностью (dividing_line); НЕ решение НС, барьер Тао, таинт неизменен
import EuclidsPath.Engine.DyadicFirstCause -- 🟡 исток каскада = первопричина (манифестация): дядический взрыв присоединяется к маскам через свой исток; зелёный вывод драйва (STEP A/B) от этого НЕ зависит; таинт растёт
import EuclidsPath.Engine.DyadicFrontWindow -- 🟢 T-относительное окно инварианта фронта: FrontPreservedUntil + мост «навсегда ⟺ до любого T» (чистая логика кванторов); обитаемость ssMode на всём [0,T) с ФИКСИРОВАННЫМ m₀=β_{J+1}/T (монотонность g) и обитаемый разрыв с Forever; конечно-оконный MVT-шаг §2ter закрыт (mathlib segment-оценка; скоростные границы зазоров = именованный локальный вход) + стационарный свидетель; красный вход FrontPreservedForever НЕ закрыт, таинт не растёт
import EuclidsPath.Engine.UniversalEngine -- УНИВЕРСАЛЬНЫЙ ПЕРЕНОС двигателя: PerpetualEngine над ЛЮБЫМ отношением; невозможность из ВНУТРЕННЕЙ причины (определение = бесконечный спуск ⟂ WellFounded), perpetualEngine_iff_not_wellFounded; перенос по рангу (no_perpetual_engine_of_rank/natRank — все фронты суть следствия ОДНОЙ теоремы; EPMI показан инстансом); КОНТРОЛЁР — на ℝ двигатель РАБОТАЕТ (perpetualEngine_on_real, реюз), universal_engine_dividing_line (M6); ядро — mathlib-фундированность, вклад формализационно-унифицирующий; зелёно, таинт неизменен
import EuclidsPath.Engine.BSDFront -- ВОСЬМАЯ МАСКА: тень Бёрч–Свиннертон-Дайера. Роль движка ИНАЯ — он сам метод СПУСКА, доказывающий алгебраический ранг: bsd_descent_has_no_engine (спуск по высоте на РЕАЛЬНЫХ точках W.toAffine.Point не имеет двигателя = терминация Морделла–Вейля, реюз UniversalEngine; ссылки на реальные Height/Northcott/fg_of_descent/LSeries); паритет-мост bsd_parity_is_rankParity к Лиувиллю (rank-parity узел). 🔴 честно открыто: AnalyticRank (порядок нуля РЕАЛЬНОЙ WeierstrassCurve.LSeries в s=1), WeakBSD (rank=ord L) — аналитика вне mathlib, движок её НЕ закрывает. Трилемма: честной границы НЕТ (декрет паритета вакуумен над заглушкой корневого числа) — фолбэк 🔴, аксиома нетронута, таинт не растёт. НЕ доказательство BSD
import EuclidsPath.Engine.BSDEpistemic -- 🟢 эпистемика БСД: ВЫРОЖДЕНИЕ ЗАФИКСИРОВАНО МАШИННО (bsdGround_coincides_with_engine — у БСД нет своей эпистемической оси, её связка совпадает с запретом двигателя спуска, и это теорема); ворота AnalyticRank свободно выполнимы (лемма честности); таинт не растёт
import EuclidsPath.Engine.ChowlaFront -- СОСЕД (глава 54): тень Чоулы/Сарнака — rank-parity узел. 🟢 реальный Лиувилль λ=(−1)^Ω: λ²=1, диагональ корреляции = x (совершенная само-корреляция паритета), флип паритета (реюз RiemannLiouville), liouvilleSum_eq_L; «отклонение = коллапс паритета в одну чётность». 🔴 ChowlaConjecture (корреляции o(x)), SarnakConjecture — открыты (Тао: лишь лог/нечётный случай). НЕ доказательство; таинт не растёт
import EuclidsPath.Engine.ChowlaEpistemic -- 🟢 эпистемика Чоулы (P/NP-тип, декрета нет): коллапс паритета = хвостовая константность λ — самоуничтожается об флип-стену (no_parityCollapse_of_flip ПОТРЕБЛЯЕТ флип-поставку, CORR); корреляция ≡ x (mod 2) — ноль недостижим на нечётных срезах; λ(2^k)=(−1)^k — оба знака кофинально; chowlaCause_unknowable; сводка chowla_locked_behind_flip_wall (двигательного факта у Чоулы нет — честно флип-стена); НЕ решение Чоулы/Сарнака, НЕ Гёдель; таинт не растёт
import EuclidsPath.Engine.AbcFront -- СОСЕД (глава 54): тень abc. 🟢 РЕАЛЬНЫЙ Polynomial.abc (Мейсон–Стотерс ДОКАЗАН) — полиномиальный abc = степенная граница через радикал = «нет бесконечного побега» (конечность); реальные Nat/Int.radical. 🔴 AbcConjecture (интегральный) открыт (заявка Мочидзуки не принята сообществом). НЕ доказательство; таинт не растёт
import EuclidsPath.Engine.AbcEpistemic -- 🟢 эпистемика abc: радикальный инструментарий (natRad_pow/mul); наивный закон ε=0 ОПРОВЕРГНУТ (1+8=9, rad=6<9) + неограниченная поставка качества (LTE-семейство 3^(2^k)); связка на LinearAbcLaw с пижонхолом; abcCause_unknowable — честно про НАИВНУЮ форму, настоящий abc-гейт не тронут; таинт не растёт
import EuclidsPath.Engine.BealFront -- СОСЕД (глава 54): тень Бил/Ферма–Каталан — чистый Ферма-спуск = движок. 🟢 РЕАЛЬНЫЙ Polynomial.flt_catalan (ДОКАЗАН, спуск по char p) + fermatLastTheoremFour/Three (спуск) + descent-без-двигателя (реюз EPMI/UniversalEngine). 🔴 BealConjecture, FermatCatalanConjecture (каноническая форма: тройки ЗНАЧЕНИЙ) открыты (Дармон–Гранвиль: лишь фикс. показатели); кортежная форма гейта зелёно ОПРОВЕРГНУТА (fermatCatalan_tupleForm_refuted — урок формализации). НЕ доказательство; таинт не растёт
import EuclidsPath.Engine.LehmerFront -- СОСЕД (глава 54): тень Лемера/меры Малера — высота-конечность как в BSD. 🟢 РЕАЛЬНЫЕ finite_mahlerMeasure_le (Нортокотт: огр. степень+мера ⟹ конечно = нет бесконечного высотного спуска) + pow_eq_one_of_mahlerMeasure_eq_one (Кронекер: мера 1 ⟺ корни из единицы) + descent-без-двигателя. 🔴 LehmerConjecture (острая константа c>1) открыта. НЕ доказательство; таинт не растёт
import EuclidsPath.Engine.LehmerEpistemic -- 🟢 эпистемика Лемера (P/NP-тип): горизонт Норткотта конечен зелёно (mahlerBox), внутренняя оплата бесконечного семейства = пижонхол-двигатель; lehmerCause_unknowable
import EuclidsPath.Engine.LandauFront -- СОСЕД (глава 54): тень Landau n²+1 (зоопарк, зеркало SideInfinitude). 🟢 мост неограниченность⟹бесконечность + факт oddLandauPrime_even_k (нечётное k ⟹ k²+1 чётно ⟹ единственное простое = 2). 🔴 Landau4thUnbounded (Харди–Литтлвуд) открыт (Иванец: ≤2 множителя). НЕ доказательство; таинт не растёт
import EuclidsPath.Engine.LandauEpistemic -- 🟢 эпистемика Ландау: канонизация гейта (iff-бесконечность, чётный канал через max N 1), мост к Дирихле 1 mod 4 (реальный Nat.forall_exists_prime_gt_and_modEq + стена делителей landauFactor_mod_four), закон манифестации НЕ декретирован (полиньяк-класс landauRefutation_carries_engine), landauCause_unknowable; пара ground/beyondOwnHorizon тавтологична — раскрыто машинно; таинт не растёт
import EuclidsPath.Engine.HodgeFront -- ЗЕЛЁНАЯ ветвь Ходжа: квантованный заряд = ℕ-высота; двигатель (цепь спуска) мёртв БЕЗУСЛОВНО (EPMI); закон спуска ⟹ гипотеза модели (сильная индукция по высоте); коллапс закон ⟺ гипотеза зелёный — шестого поля НЕТ; трилемма: V1 опровержим, V2 вакуумен, chain-форма вырождена в зелёную, V3 несовместим с границей; mathlib Ходжа не содержит — Клэй не объявлен
import EuclidsPath.Engine.HodgeEpistemic -- 🟢 эпистемика Ходжа: per-model DescentLaw (универсал КОВАН — hodgeUniversal_forged_refutation); неоплаченный класс = цепь-двигатель; hodgeCause_unknowable
import EuclidsPath.Engine.MersenneManifestationFront -- ЗЕЛЁНАЯ Мерсенн-манифестация: свидетель-отсутствие (Π, ≥ 29), гейченный закон, M3⁺ «опровержение предъявляет двигатель»; цепь 4c+1 НЕ пилится (ковки нет); трилемма пройдена, НО поле отложено — знак эвристики ПРОТИВ (§16-комментарий карантина)
import EuclidsPath.Engine.FermatMersenneEpistemic -- 🟢 эпистемика Ферма+Мерсенна: обе ставки отложены (§16/§17) И внутренних путей нет — опровержение при законе/книгах = двигатель; fermatCause_unknowable, mersenneCause_unknowable
import EuclidsPath.Engine.SideInfinitude              -- Дирихле: стороны 6m±1 порознь бесконечны (🟢); согласование сторон в одном центре = вся открытая суть
import EuclidsPath.Engine.PolignacBranch              -- Полиньяк в сетке: кузены (p,p+4) и секси (p,p+6) на соседних центрах; классификация, инстансы, мосты (🟢)
import EuclidsPath.Engine.SophieGermainBranch         -- Софи Жермен: минус-сторона, удвоение центра m→2m; ЖЕМЧУЖИНА: SG-простые при p≡3 (mod 4) убивают Мерсенна (🟢, 23∣M₁₁)
import EuclidsPath.Engine.FermatBranch                -- Ветка Ферма: F_k ≡ 5 (mod 6) — минус-сторона; квадратичная цепь c'+4c=6c²+1; twin-инстансы k=1,2,4 (до 65537/65539)
import EuclidsPath.Engine.FermatMersenneLadder -- 🟢 лестница Ферма↔Мерсенн: 7∣F_k+2 (нечётный k — половина индексов выбывает), 5∣2^p−3 при p≡3 (mod 4) — эвристика §16 теперь зелёная; мост mersenne(2^n)=∏F_k + гольдбахова единственность слоя; НЕ решение бесконечностей, таинт не растёт
import EuclidsPath.Engine.PerfectNumberBranch         -- Совершенные: Евклид–Эйлер ОБА направления зелёные (Archive); простые Мерсенна ⟺ чётные совершенные неограничены (🟢-iff)
import EuclidsPath.Engine.PolignacManifestationFront    -- Полиньяк-фронты (кузены p+4, секси p+6): свидетель-Π, закон, essence M3; поля НЕТ (§17, знак ЗА)
import EuclidsPath.Engine.PolignacEpistemic -- 🟢 эпистемика Полиньяка: cousinCause_unknowable/sexyCause_unknowable; опровержение при сведённых книгах = двигатель (реюз *Refutation_carries_engine)
import EuclidsPath.Engine.SophieGermainManifestationFront -- Софи Жермен фронт + анти-Мерсенн рестрикт: SG-манифестация кормит составную сторону Мерсенна («две ставки»)
import EuclidsPath.Engine.SophieGermainEpistemic -- 🟢 эпистемика Софи Жермен: sgCause_unknowable (+3 mod 4); опровержение = двигатель (sgRefutation_carries_engine); жемчужина 23∣M₁₁ безусловна
import EuclidsPath.Engine.GoldbachManifestationFront    -- Гольдбах-фронт (объект-свидетель, decide-разрешимый): неоплаченное чётное манифестирует двигатель
import EuclidsPath.Engine.LegendreDesertFront           -- Пустыни простых: ЗЕЛЁНЫЙ Бертран (пустыня не удваивается) + Лежандр-фронт (интервал короче — Бертран не решает)
import EuclidsPath.Engine.GoldbachLegendreEpistemic -- 🟢 эпистемика Гольдбаха+Лежандра: нарушение при сведённых книгах = двигатель; goldbachCause_unknowable/legendreCause_unknowable; свидетель decide-разрешим — «проверка, а не вывод»
import EuclidsPath.Engine.GoldbachLegendreEpistemic     -- 🟢 ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ Гольдбаха+Лежандра (зеркало PNPFirstCause): goldbachCause_unknowable / legendreCause_unknowable; самообоснование = двигатель-объект (builds_engine, оплачено no_deviationFlowSupply_at_resolved_scale, НЕ P∧¬P); сводка goldbachLegendre_locked_behind_engine_status БЕЗ декрет-конъюнкта (§17); НЕ решение задач 1742/1808, НЕ Гёдель; таинт не растёт
import EuclidsPath.Engine.OddPerfectManifestationFront  -- Нечётные совершенные (объект-свидетель): чётная сторона зелёно-конструируема, отклонение живёт на нечётной
import EuclidsPath.Engine.OddPerfectThreePrimes -- 🟢 нечётное совершенное имеет ≥ 3 различных простых делителей (классика через изобилие: σ(n)/n < p/(p−1)·q/(q−1) ≤ 15/8 < 2); ступени: не степень простого, не два простых; таинт не растёт
import EuclidsPath.Engine.OddPerfectEpistemic -- 🟢 эпистемика нечётных совершенных: предъявить свидетеля = предъявить двигатель (условно на закон); oddPerfectCause_unknowable; вариант (b) — невырожденный
import EuclidsPath.Engine.FermatManifestationFront      -- Ферма-фронт: локализация ≥ 65537; знак ИНВЕРТИРОВАН сильнее Мерсенна (только F₀–F₄) — §16 дословно

-- ⚠️ КАРАНТИН: ЕДИНСТВЕННЫЙ axiom репозитория — первопричина с ДВУМЯ границами:
-- twin-узел (causalBoundary) и римановский закон манифестации (riemannBoundary, §10).
-- Всё зависящее от неё — УСЛОВНО, машинно помечается верификатором как AXIOM-TAINTED.
-- twin_prime_conjecture НЕ замыкается через этот модуль и остаётся sorry;
-- riemannHypothesis_from_firstCause — редукция, закрытая декретом, НЕ доказательство RH.
import EuclidsPath.Engine.CausalClosureAxiom
import EuclidsPath.Engine.GeometryFront -- ГЕОМЕТРИЯ ПУТИ: стрела времени (lexRank ↓), кривизна κ=1−outdeg ВЫЧИСЛЕНА (спектр −8…+1, χ(cone3)=−5), плоскость всюду ⟹ двигатель; прямые конечны — падает ВТОРОЙ постулат Евклида, параллельных нет; паутина через могилу нуля; пересечение прямых 🟡 из той же первопричины, но знать изнутри нельзя 🟢 (ровно 2 tainted-декларации)
