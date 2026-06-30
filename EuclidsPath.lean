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
