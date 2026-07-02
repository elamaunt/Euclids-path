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
import EuclidsPath.Engine.MersenneBranch -- Мерсенн: вложение 2^p−1 = 6m_p+1 + twin-критерий; ЧЕСТНО: Мерсенн-близнецы ⟹ близнецы (НЕ наоборот!)
import EuclidsPath.Engine.LocalPNPNode -- строгий локальный P/NP-узел + конкретная инстанциация (при A≤4 несжимаемость БЕЗУСЛОВНА); scope guard: НЕ классические P/NP

-- ⚠️ КАРАНТИН: ЕДИНСТВЕННЫЙ axiom репозитория (step00CausalClosure = открытый узел, принятый декретом).
-- Всё зависящее от него — УСЛОВНО, машинно помечается верификатором как AXIOM-TAINTED.
-- twin_prime_conjecture НЕ замыкается через этот модуль и остаётся sorry.
import EuclidsPath.Engine.CausalClosureAxiom
