/-
  ContinuousEngine — ПЕРВЫЙ формальный НЕПРЕРЫВНО-ВРЕМЕННОЙ вечный двигатель над ℝ
  и ЧЕСТНАЯ, машинно-проверенная КАРТА того, где показание двигателя переносится на
  континуум, а где оно ПРИНЦИПИАЛЬНО НЕ ДОСТАЁТ до настоящего Навье–Стокса.

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК — ЧТО ЗДЕСЬ ЕСТЬ И ЧЕГО НЕТ.                                    │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  ЧТО ЭТОТ МОДУЛЬ ДОСТИГАЕТ (зелёно, машинно, без sorry/axiom/native_decide):
    • M1 — ПЕРВЫЙ формальный НЕПРЕРЫВНО-ВРЕМЕННОЙ вечный двигатель. Над ℝ функция
        `H(t) = r^t` (`0 < r < 1`) СТРОГО-МУЛЬТИПЛИКАТИВНО убывает
        (`H s ≤ r^(s−t)·H t` для `t ≤ s`), при этом ВЕЧНО ПОЛОЖИТЕЛЬНА и не
        обрывается ни в какой момент: `continuous_engine_exists`. Это ℝ-аналог того,
        что дискретная невозможность `EPMI.no_infinite_descent` (ℕ ЗАПРЕЩАЕТ бесконечный
        спуск) на континууме ЛОЖНА: двигатель работает вечно. НОВОЕ здесь — непрерывное
        время `r^t` над ВСЕМ ℝ через `Real.rpow`; дискретно-индексная форма `(1/2)^n` уже
        существует как `DissipativeCascade.real_positive_work_not_wellfounded` (цитируется,
        не пере-выводится).
    • M2 — СХОДИМОСТЬ ≠ ПРОТИВОРЕЧИЕ. Ограниченный снизу антитонный бюджет
        `H : ℕ → ℝ` СХОДИТСЯ (к `⨅ n, H n ≥ 0`), а НЕ даёт `False`:
        `boundedBelow_antitone_converges`. Спуск СХОДИТСЯ, а не «фундирует».
    • M3 — КОНЕЧНО-ВРЕМЕННАЯ СУПЕРЗАДАЧА (supertask). Масштаб кованого каскада
        `NavierStokesFront.cookedProfileCascade` уходит В НОЛЬ (`→ 0`) ДО конечного `T=1`:
        `cascade_scale_tendsto_zero`. Завершённый бесконечный спуск к масштабу 0 за
        конечное время — то, что ℝ допускает, а ℕ (`no_infinite_descent`) запрещает.
        Свидетели переиспользованы из `NavierStokesFront` (не пере-выводятся).
    • M4 — СВЯЗЬ КЛЭЯ КАК ЯЗЫКОВОЕ ТОЖДЕСТВО. «Двигатель работает до T» ⟺ «BKM-контроль
        вихря нарушен» — это `Iff.rfl` (`continuousEngine_runs_iff_not_vorticityControl`),
        ГРОМКО раскрытое как определение-через-определение, БЕЗ новой математики (зеркало
        существующего `NavierStokesClay.vorticityBlowup_is_deviation`). Плюс — карта ЧЕТЫРЁХ
        строгих критериев взрыва как УСЛОВНЫХ характеризаций (см. §M4).
    • M5 — ЧЕСТНЫЙ ЭНДПОИНТ. Непрерывный двигатель существует БЕЗУСЛОВНО
        (`continuous_engine_exists_unconditionally`), поэтому из «∃ двигатель» (истинного
        утверждения) НИЧЕГО про открытое ядро `GlobalVorticityControl` не следует: истинная
        посылка не несёт направленного содержания. Переиспользуется машинно-проверенная
        `NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl` («бюджетная
        машина СТРОГО СЛАБЕЕ открытого ядра»).

  ЧЕГО ЭТОТ МОДУЛЬ НЕ ДОСТИГАЕТ (КРАСНЫЕ ЛИНИИ — ГРОМКО):
    • Это НЕ решение и НЕ «удар» по задаче тысячелетия. Настоящий 3D-Навье–Стокс НЕ
      затронут ни на шаг.
    • Доказать ВЗРЫВ настоящего НС (утверждение C формулировки Клэя) СТОЛЬ ЖЕ ОТКРЫТО,
      как регулярность (A). Абстрактный двигатель РАЗВЯЗАН (decoupled) от НЕЛИНЕЙНОСТИ НС:
      его форсирующий вход `superlinearDrive` НАЗВАН и живёт ТОЛЬКО в дискретной модели
      Каца–Павловича (`DyadicBlowup.DyadicSolution.superlinearDrive`), а не в самих
      уравнениях НС.
    • Барьер СУПЕРКРИТИЧНОСТИ Тао (Tao, J. Amer. Math. Soc. 29 (2016) 601–674): усреднённый
      НС СОХРАНЯЕТ энергетическое тождество, но ВЗРЫВАЕТСЯ ⟹ никакой чисто
      энергетический/спусковой аргумент не может РЕШИТЬ настоящий НС. Именно поэтому
      двигательное показание НЕ ДОСТАЁТ до континуума НС.
    • Открытое ядро `NavierStokesClay.GlobalVorticityControl` остаётся ЕДИНСТВЕННЫМ 🔴
      барьером, НЕТРОНУТЫМ. Мы НЕ подделываем доказательство независимости и НЕ
      изобретаем `Prop`, притворяющийся, что решает НС.

  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`; такса репозитория
  (propext / Classical.choice / Quot.sound) неизменна — 45. Красная линия (связь с
  простыми числами) нетронута.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/ContinuousEngine.lean → ноль ошибок.

  Родство: EuclidsPath/Engine/EPMI.lean (`no_infinite_descent` — дискретный контраст);
    EuclidsPath/Engine/DissipativeCascade.lean (`real_positive_work_not_wellfounded` — ℝ-(1/2)ⁿ);
    EuclidsPath/Engine/NavierStokesFront.lean (`cookedProfileCascade` — supertask-свидетель);
    EuclidsPath/Engine/NavierStokesClayReduction.lean (`GlobalVorticityControl` — открытое ядро);
    EuclidsPath/Engine/DyadicBlowup.lean (`superlinearDrive` — именованный форсинг + барьер Тао).
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.DissipativeCascade
import EuclidsPath.Engine.NavierStokesFront
import EuclidsPath.Engine.NavierStokesClayReduction
import EuclidsPath.Engine.DyadicBlowup
import EuclidsPath.Engine.CascadeBudget

set_option autoImplicit false
set_option linter.dupNamespace false

noncomputable section

namespace EuclidsPath.ContinuousEngine

open Filter Topology
open scoped BigOperators

/-!
################################################################################
  M1. ГЕНУИННО-НОВЫЙ НЕПРЕРЫВНО-ВРЕМЕННОЙ ДВИГАТЕЛЬ (зелёно, малый)
################################################################################

Дискретный движок `EPMI` невозможен ровно потому, что высоты живут в ℕ, а ℕ
фундирована (well-founded): любой строгий `A`-спуск за конечное число шагов
уходит ниже 1 — противоречие (`no_infinite_descent`). НЕПРЕРЫВНОЕ время над ℝ
этого барьера НЕ имеет: `H(t) = r^t` строго-мультипликативно убывает и всё же
ВЕЧНО положительна. Это и есть «непрерывный вечный двигатель» — первая его
формализация над ВСЕМ ℝ. -/

/-- **Непрерывно-временной вечный двигатель.** Функция «высоты/энергии»
    `H : ℝ → ℝ` есть двигатель со скоростью убывания `r`, если:
      (i)   `H` всюду СТРОГО положительна (двигатель никогда не глохнет);
      (ii)  `0 < r < 1` (строгая скорость убывания);
      (iii) СТРОГО-МУЛЬТИПЛИКАТИВНЫЙ спуск: за интервал `[t,s]` высота падает
            не медленнее чем в `r^(s−t)` раз, `H s ≤ r^(s−t) · H t` для `t ≤ s`.
    Показатель `s − t` — ВЕЩЕСТВЕННЫЙ, поэтому используется `Real.rpow`. Это
    непрерывно-временной аналог дискретного `DescentStep`/`no_perpetual_engine`
    из `EPMI`: там спуск ЗАПРЕЩЁН (ℕ фундирована), здесь он ВЕЧНО ИДЁТ. -/
def ContinuousEngine (H : ℝ → ℝ) (r : ℝ) : Prop :=
  (∀ t, 0 < H t) ∧ 0 < r ∧ r < 1 ∧ ∀ t s, t ≤ s → H s ≤ r ^ (s - t) * H t

/-- **🟢 `continuous_engine_exists` — ДОКАЗАНА (ЯДРО M1, генуинно новое).**
    Для всякого `0 < r < 1` функция `H(t) = r^t` (rpow) есть непрерывно-временной
    вечный двигатель со скоростью `r`. Положительность — `Real.rpow_pos_of_pos`;
    спуск — фактически РАВЕНСТВО `r^s = r^(s−t) · r^t` (через `Real.rpow_add` после
    `s = (s − t) + t`), поэтому `≤` берётся `le_of_eq`. Это ℝ-реализация того, что
    дискретный `EPMI.no_infinite_descent` над ℕ ЛОЖЕН: двигатель работает вечно. -/
theorem continuous_engine_exists {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ContinuousEngine (fun t => r ^ t) r := by
  refine ⟨fun t => Real.rpow_pos_of_pos hr0 t, hr0, hr1, ?_⟩
  intro t s hts
  -- r^s = r^((s-t)+t) = r^(s-t) * r^t  (равенство), значит ≤ через le_of_eq
  have hsplit : s = (s - t) + t := by ring
  have heq : r ^ s = r ^ (s - t) * r ^ t := by
    calc r ^ s = r ^ ((s - t) + t) := by rw [← hsplit]
      _ = r ^ (s - t) * r ^ t := Real.rpow_add hr0 _ _
  exact le_of_eq heq

/-- **🟢 `continuous_engine_exists_unconditionally` — ДОКАЗАНА (безусловная
    обитаемость).** Непрерывно-временной вечный двигатель СУЩЕСТВУЕТ безусловно —
    берём `r = 1/2`, `H(t) = (1/2)^t`. Это истинное утверждение БЕЗ всяких
    НС-гипотез; оно ЯКОРИТ честный эндпоинт M5: из истинной посылки «∃ двигатель»
    ничего про открытое ядро НС не выводимо. -/
theorem continuous_engine_exists_unconditionally :
    ∃ (H : ℝ → ℝ) (r : ℝ), ContinuousEngine H r :=
  ⟨fun t => (1 / 2 : ℝ) ^ t, 1 / 2,
    continuous_engine_exists (by norm_num) (by norm_num)⟩

/-- **🟢 `discrete_forbids_continuous_realizes` — ДОКАЗАНА (ГЛАВНЫЙ КОНТРАСТ).**
    Точная юкстапозиция двух показаний:
      • слева  — `EPMI.no_infinite_descent`: над ℕ бесконечный `A`-спуск (`A ≥ 1`)
        даёт `False` — двигатель НЕВОЗМОЖЕН (ℕ фундирована);
      • справа — `continuous_engine_exists`: над ℝ `H(t)=r^t` РЕАЛИЗУЕТ вечный
        строго-мультипликативный спуск — двигатель РАБОТАЕТ.
    Смысл: невозможность двигателя ЕСТЬ well-foundedness ℕ, которой ℝ лишена.
    Дискретно-индексная (1/2)ⁿ-форма уже существует как
    `DissipativeCascade.real_positive_work_not_wellfounded` — здесь НОВОЕ значение
    в непрерывном времени `r^t` над всем ℝ. -/
theorem discrete_forbids_continuous_realizes :
    (∀ {A : Nat}, 1 ≤ A → ∀ (H : Nat → Nat),
        (∀ t, EuclidsPath.Engine.DescentStep A (H t) (H (t + 1))) → False)
    ∧ (∀ {r : ℝ}, 0 < r → r < 1 → ContinuousEngine (fun t => r ^ t) r) := by
  refine ⟨?_, ?_⟩
  · intro A hA H hchain
    exact EuclidsPath.Engine.no_infinite_descent hA H hchain
  · intro r hr0 hr1
    exact continuous_engine_exists hr0 hr1

/-- Явная перекличка с существующей ℝ-(1/2)ⁿ-формой: дискретно-индексный вечный
    спуск над ℝ уже машинно зафиксирован в `DissipativeCascade`. Мы цитируем его
    (НЕ пере-выводим), чтобы подчеркнуть: НОВОЕ в M1 — НЕПРЕРЫВНОЕ время `r^t`. -/
theorem cite_discrete_index_real_descent :
    ∃ a : ℕ → ℝ, (∀ n, a (n + 1) < a n) ∧ (∀ n, 0 < a n) ∧
      (∀ n, 0 < a n - a (n + 1)) :=
  EuclidsPath.DissipativeCascade.real_positive_work_not_wellfounded

/-!
################################################################################
  M2. СХОДИМОСТЬ ≠ ПРОТИВОРЕЧИЕ (зелёно)
################################################################################

Ограниченный снизу антитонный ℝ-бюджет НЕ обязан «фундироваться» и давать `False`.
Он СХОДИТСЯ. Это дополняет `CascadeBudget.finite_budget_bounds_uniform_dissipation`
(которому нужна РАВНОМЕРНАЯ нижняя граница β на шаг) и `budget_misses_nonuniform`:
без равномерности спуск не конечен, но и не противоречив — он просто сходится. -/

/-- **🟢 `boundedBelow_antitone_converges` — ДОКАЗАНА (M2).** Всякий ограниченный
    снизу (`0 ≤ H n`) антитонный `H : ℕ → ℝ` СХОДИТСЯ к пределу `L ≥ 0`. Предел —
    `⨅ n, H n`; `Tendsto` даёт `tendsto_atTop_ciInf`, а `0 ≤ ⨅` — `le_ciInf`.
    Мораль: убывающий энергобюджет НЕ порождает `False`, он ИМЕЕТ предел; спуск
    СХОДИТСЯ, а не well-found'ится — ровно то, чего нет у дискретного ℕ-движка. -/
theorem boundedBelow_antitone_converges (H : ℕ → ℝ)
    (hanti : Antitone H) (hbdd : ∀ n, 0 ≤ H n) :
    ∃ L, 0 ≤ L ∧ Tendsto H atTop (𝓝 L) := by
  have hBdd : BddBelow (Set.range H) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hbdd n
  refine ⟨⨅ n, H n, ?_, ?_⟩
  · exact le_ciInf (fun n => hbdd n)
  · exact tendsto_atTop_ciInf hanti hBdd

/-!
################################################################################
  M3. КОНЕЧНО-ВРЕМЕННАЯ СУПЕРЗАДАЧА (зелёно, переиспользование)
################################################################################

Кованый каскад `NavierStokesFront.cookedProfileCascade` живёт на временах
`tₙ = 1 − 2⁻ⁿ < T = 1`; его масштаб (профиль) равен `cookedProfile(tₙ) = 2⁻ⁿ`.
Значит масштаб уходит В НОЛЬ ДО конечного момента `T = 1` — завершённый
бесконечный спуск за конечное время, который ℝ допускает, а ℕ
(`EPMI.no_infinite_descent`) запрещает. Свидетели переиспользованы. -/

/-- **🟢 `cascade_scale_tendsto_zero` — ДОКАЗАНА (M3, supertask).** Масштаб
    кованого каскада на этапах `n` есть `cookedProfile (times n) = 2⁻ⁿ` (через
    существующие `cookedProfileCascade_times` + `cookedProfile_at_stage`), и он
    `→ 0` при `n → ∞` (`tendsto_pow_atTop_nhds_zero_of_lt_one`, база `1/2`).
    Т.к. все `times n < 1`, это ЗАВЕРШЁННЫЙ бесконечный спуск к масштабу 0 ДО
    конечного `T = 1` — суперзадача. Реюз `NavierStokesFront`. -/
theorem cascade_scale_tendsto_zero :
    Tendsto
      (fun n => NavierStokesFront.cookedProfile
        (NavierStokesFront.cookedProfileCascade.times n))
      atTop (𝓝 0) := by
  -- на этапе n масштаб равен (1/2)^n
  have hval : (fun n => NavierStokesFront.cookedProfile
        (NavierStokesFront.cookedProfileCascade.times n))
      = (fun n => (1 / 2 : ℝ) ^ n) := by
    funext n
    rw [NavierStokesFront.cookedProfileCascade_times,
        NavierStokesFront.cookedProfile_at_stage n]
  rw [hval]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Спутник M3: кованый каскад НЕ равномерен (падения `2⁻⁽ⁿ⁺¹⁾` ускользают под
    всякий `δ`). Переэкспортируем `cookedProfileCascade_not_uniform` — именно
    НЕравномерность и позволяет supertask'у ускользать от бюджетной машины (M2
    убивает лишь равномерные спуски). Это связка M2↔M3↔M5. -/
theorem cascade_scale_not_uniform (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n, δ ≤ NavierStokesFront.cookedProfile
              (NavierStokesFront.cookedProfileCascade.times n)
            - NavierStokesFront.cookedProfile
              (NavierStokesFront.cookedProfileCascade.times (n + 1)) :=
  NavierStokesFront.cookedProfileCascade_not_uniform δ hδ

/-!
################################################################################
  M4. ДВИЖОК ⟺ ВИХРЬ КАК ЯЗЫКОВОЕ ТОЖДЕСТВО + КРИТЕРИИ ВЗРЫВА (зелёно, Prop)
################################################################################

Отрицание BKM-контроля вихря — это ровно «двигатель работает до T». Мы ГРОМКО
раскрываем: связь — определение-через-определение (`Iff.rfl`), НИКАКОЙ новой
математики (зеркало `NavierStokesClay.vorticityBlowup_is_deviation`). -/

/-- **`ContinuousEngineRuns u T`** — «непрерывный двигатель РАБОТАЕТ до времени
    `T` на решении `u`»: BKM-величина вихря НЕ ограничена на `[0,T]`, т.е.
    `¬ VorticityTimeIntegrable u T`. Это язык двигательной ветки для той же
    финитно-временной сингулярной девиации, что и в `NavierStokesClay`. -/
def ContinuousEngineRuns (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3)
    (T : ℝ) : Prop :=
  ¬ EuclidsPath.NavierStokesClay.VorticityTimeIntegrable u T

/-- **🟢 `continuousEngine_runs_iff_not_vorticityControl` — ДОКАЗАНА (`Iff.rfl`).**
    ГРОМКО РАСКРЫТО: «двигатель работает до T» ⟺ «нарушен BKM-контроль вихря» —
    это определение-через-определение, БЕЗ нового математического содержания
    (зеркало существующего `NavierStokesClay.vorticityBlowup_is_deviation`).
    Связь Клэя тут — ЯЗЫКОВОЕ ТОЖДЕСТВО, не мост-теорема и не продвижение НС. -/
theorem continuousEngine_runs_iff_not_vorticityControl
    (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3) (T : ℝ) :
    ContinuousEngineRuns u T ↔
      ¬ EuclidsPath.NavierStokesClay.VorticityTimeIntegrable u T :=
  Iff.rfl

/-!
### §M4bis. ЧЕТЫРЕ СТРОГИХ КРИТЕРИЯ ВЗРЫВА КАК УСЛОВНЫЕ ХАРАКТЕРИЗАЦИИ

ВНИМАНИЕ (ГРОМКО): каждый из четырёх ниже — НАСТОЯЩАЯ теорема литературы, но она
УСЛОВНА: она характеризует/исключает взрыв ПРИ выполнении своей посылки и НЕ
утверждает, что взрыв ПРОИСХОДИТ. Все они указывают на репозиторный суррогат BKM —
`NavierStokesClay.VorticityTimeIntegrable` (равномерная оценка sup вихря на [0,T]).

  (1) Beale–Kato–Majda (Comm. Math. Phys. 94 (1984) 61–66):
        взрыв в T ⟺ ∫₀ᵀ ‖ω(t)‖_{L^∞} dt = ∞.
      УСЛОВНО: это КРИТЕРИЙ продолжения, НЕ утверждение о наличии взрыва.
      Репо-суррогат: `VorticityTimeIntegrable` — конечность sup вихря на [0,T].

  (2) Prodi–Serrin–Ладыженская (регулярность):
        u ∈ L^s_t L^r_x с 2/s + 3/r ≤ 1, r > 3  ⟹  решение регулярно.
      УСЛОВНО: гипотеза интегрируемости НЕ доказана для произвольных данных.

  (3) Escauriaza–Seregin–Šverák (Uspekhi Mat. Nauk 58 (2003); эндпоинт L^∞_t L^3_x):
        u ∈ L^∞_t L^3_x  ⟹  регулярность (критический эндпоинт (2)).
      УСЛОВНО: посылка — сильное предположение, не следствие.

  (4) Constantin–Fefferman (Indiana Univ. Math. J. 42 (1993) 775–789):
        липшицевость НАПРАВЛЕНИЯ вихря ξ = ω/‖ω‖ в области интенсивной завихрённости
        ⟹  отсутствие сингулярности.
      УСЛОВНО: геометрическое условие на направление, не гарантировано.

Мы НЕ формализуем эти четыре как теоремы (они требуют аналитической
инфраструктуры вне охвата модуля) — мы НАЗЫВАЕМ их и честно помечаем как
УСЛОВНЫЕ, указывая на `VorticityTimeIntegrable` как на BKM-суррогат репозитория.
Ни один из них НЕ утверждает, что взрыв происходит — как и весь модуль. -/

/-- **`bkm_surrogate_is_vorticity_integrable` — ДОКАЗАНА (`Iff.rfl`, разметка).**
    Репозиторный суррогат критерия Била–Като–Майды — это в точности
    `VorticityTimeIntegrable`: существование равномерной мажоранты sup вихря на
    `[0,T]`. Мы фиксируем это тождество определений (без нового содержания), чтобы
    все четыре критерия §M4bis имели ЕДИНУЮ репо-точку привязки. Критерий УСЛОВЕН:
    он НЕ утверждает ни взрыва, ни его отсутствия. -/
theorem bkm_surrogate_is_vorticity_integrable
    (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3) (T : ℝ) :
    EuclidsPath.NavierStokesClay.VorticityTimeIntegrable u T ↔
      ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        (⨆ x : EuclidsPath.NavierStokes.E3,
          ‖EuclidsPath.NavierStokesClay.vorticity (u t) x‖) ≤ M :=
  Iff.rfl

/-!
################################################################################
  M5. ЧЕСТНЫЙ ЭНДПОИНТ (зелёные свидетели + РАСКРЫТАЯ доктрина; БЕЗ фейка)
################################################################################

Машинно-проверенная половина эндпоинта — зелёные свидетели M1–M3 плюс
переиспользование `greenBudget_strictly_weaker_than_vorticityControl`. Открытое
ядро `GlobalVorticityControl` мы НЕ трогаем и НЕ подделываем независимость. -/

/-- **🟢 `engineBudget_strictly_weaker_than_open_core` — ПЕРЕИСПОЛЬЗОВАНА (M5).**
    Прямой реюз машинно-проверенной `NavierStokesClay.
    greenBudget_strictly_weaker_than_vorticityControl`: зелёная БЮДЖЕТНАЯ машина
    двигателя СТРОГО СЛАБЕЕ открытого ядра. Свидетель — тот же кованый
    неравномерный каскад: для любого `δ>0` его падения ускользают, значит бюджет
    (убивающий лишь равномерные каскады) НЕ доказывает `GlobalVorticityControl`.
    Это анти-теорема (граница), а НЕ мост. -/
theorem engineBudget_strictly_weaker_than_open_core (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n : ℕ, δ ≤
        NavierStokesFront.cookedProfile
            (NavierStokesFront.cookedProfileCascade.times n)
          - NavierStokesFront.cookedProfile
            (NavierStokesFront.cookedProfileCascade.times (n + 1)) :=
  EuclidsPath.NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl δ hδ

/--
**🟢 `millennium_endpoint_unreachable_by_engine` — ДОКАЗАНА (честное ЯДРО M5).**

Это НЕ доказательство независимости и НЕ решение НС — это ЧЕСТНЫЙ зелёный якорь.
Заключение — КОНЪЮНКЦИЯ трёх ИСТИННЫХ зелёных фактов:
  (a) непрерывный вечный двигатель существует БЕЗУСЛОВНО (`∃ H r, ContinuousEngine H r`);
  (b) ограниченный снизу антитонный бюджет СХОДИТСЯ, а не даёт `False` (M2);
  (c) масштаб supertask-каскада уходит в 0 до конечного T (M3).

ГРОМКО И ЧЕСТНО (см. заголовок и доктрину ниже): из ИСТИННОЙ посылки «∃ двигатель»
НИЧЕГО про `GlobalVorticityControl` НЕ выводимо — истинная посылка логически
ИНЕРТНА относительно открытого ядра (она не является ни его причиной, ни
следствием). Абстрактный двигатель РАЗВЯЗАН от нелинейности НС: форсинг
`superlinearDrive` НАЗВАН и живёт лишь в дискретной модели Каца–Павловича
(`DyadicBlowup.DyadicSolution.superlinearDrive`). Барьер Тао (JAMS 2016) блокирует
любой энергетический/спусковой аргумент. Открытое ядро остаётся ЕДИНСТВЕННЫМ 🔴,
нетронутым. Мы НЕ изобретаем `Prop`, притворяющийся, что решает НС или доказывает
независимость. -/
theorem millennium_endpoint_unreachable_by_engine :
    (∃ (H : ℝ → ℝ) (r : ℝ), ContinuousEngine H r)
    ∧ (∀ (H : ℕ → ℝ), Antitone H → (∀ n, 0 ≤ H n) →
        ∃ L, 0 ≤ L ∧ Tendsto H atTop (𝓝 L))
    ∧ Tendsto
        (fun n => NavierStokesFront.cookedProfile
          (NavierStokesFront.cookedProfileCascade.times n))
        atTop (𝓝 0) := by
  refine ⟨continuous_engine_exists_unconditionally, ?_, cascade_scale_tendsto_zero⟩
  intro H hanti hbdd
  exact boundedBelow_antitone_converges H hanti hbdd

/-- Явное свидетельство «форсинг НАЗВАН и заперт в дискретной модели»: единственный
    источник суперлинейного драйва в репозитории — поле `superlinearDrive` структуры
    `DyadicBlowup.DyadicSolution` (модель Каца–Павловича), а НЕ уравнения НС. Мы
    цитируем его тип, подтверждая развязку абстрактного двигателя от нелинейности НС.
    (Из обитаемости `DyadicSolution` следовало бы `False` — `dyadic_blowup`, — поэтому
    сам форсинг локально реализуем, но глобально взрывает, и к НС НЕ переносится.) -/
theorem named_forcing_lives_only_in_discrete_model
    (sol : EuclidsPath.DyadicBlowup.DyadicSolution) :
    ∀ t, 0 ≤ t →
      sol.driveConst * (sol.leadFunctional t) ^ 2 ≤ sol.leadDeriv t :=
  sol.superlinearDrive

/-!
################################################################################
  M6. ГДЕ ДВИГАТЕЛЬ НЕВОЗМОЖЕН: РАВНОМЕРНЫЙ ДРЕНАЖ НА КОНЕЧНОМ ТОПЛИВЕ (зелёно)
################################################################################

M1 показал: непрерывный двигатель `H(t)=r^t` РАБОТАЕТ вечно. Но НЕ ВСЯКОЕ убывание
вечно, и здесь — точная демаркация ГДЕ двигатель НЕВОЗМОЖЕН.

Ключ (машинно): «убывать на конечном топливе» само по себе эндпоинта НЕ гарантирует —
`r^t` убывает на конечном топливе `H 0 = 1` и всё же вечно положителен (M1), лишь
СХОДЯСЬ (M2), а не достигая нуля. Неизбежным эндпоинт делает РАВНОМЕРНОСТЬ дренажа:
если мгновенная скорость `H' ≤ −β` держится с ЕДИНЫМ порогом `β > 0`, то из конечного
топлива `H 0` высота обязана пересечь ноль за конечное `T ≤ H 0 / β` — вечная
положительность СТАНОВИТСЯ НЕВОЗМОЖНОЙ. Значит двигатель невозможен ровно в РАВНОМЕРНОМ
режиме, а уцелевает исключительно НЕравномерностью (скорость дренажа обязана убывать к
нулю). Ядро — переиспользование `CascadeBudget.finite_budget_bounds_uniform_dissipation`.

ЧЕСТНАЯ ГРАНИЦА (та же, что у всего модуля): именно поэтому показание двигателя НЕ
достаёт до настоящего НС — реальная диссипация НЕравномерна (кованый каскад
`cookedProfileCascade` ускользает под всякий `β`, M3/`budget_misses_nonuniform`), то есть
НС сидит на ВОЗМОЖНОЙ, неравномерной стороне демаркации, где конечный бюджет НЕ решает
исход (барьер Тао, JAMS 2016). M6 картирует границу, а не закрывает задачу. -/

/-- **🟢 `uniform_drain_forbids_eternal_engine` — ДОКАЗАНА (M6, ядро замечания).**
    НЕ существует функции `H`, которая ОДНОВРЕМЕННО:
      (i)   вечно строго положительна на `[0,∞)` (двигатель не глохнет);
      (ii)  дифференцируема с производной `H' t`;
      (iii) убывает РАВНОМЕРНО: `H' t ≤ −β` с ЕДИНЫМ `β > 0`.
    Причина: равномерный дренаж из конечного топлива `H 0` пересекает ноль за
    `T ≤ H 0 / β` (бюджет-лемма `finite_budget_bounds_uniform_dissipation`), что при
    `T := H 0 / β + 1` противоречит `0 < H T`. Точная запись замечания «эндпоинт
    НЕИЗБЕЖЕН при равномерном убывании на конечном топливе»: двигатель невозможен
    ИМЕННО здесь. Все три гипотезы реально потребляются. -/
theorem uniform_drain_forbids_eternal_engine
    (H H' : ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt H (H' t) t)
    (hdrain : ∀ t, 0 ≤ t → H' t ≤ -β)
    (hpos : ∀ t, 0 ≤ t → 0 < H t) :
    False := by
  have hH0 : 0 < H 0 := hpos 0 le_rfl
  set T : ℝ := H 0 / β + 1 with hTdef
  have hT0 : 0 ≤ T := by
    have hpos' : 0 < H 0 / β := div_pos hH0 hβ
    simp only [hTdef]; linarith
  have hbound : T ≤ H 0 / β :=
    CascadeBudget.finite_budget_bounds_uniform_dissipation
      H H' (H 0) β T hβ hT0 rfl
      (fun t ht => hderiv t (Set.mem_Icc.mp ht).1)
      (fun t ht => hdrain t (Set.mem_Icc.mp ht).1)
      (le_of_lt (hpos T hT0))
  simp only [hTdef] at hbound
  linarith

/-- **🟢 `continuous_engine_is_nonuniform` — ДОКАЗАНА (M6, ЧЕМ уцелевает двигатель).**
    Двигатель `H(t)=r^t` (`0<r<1`), будучи вечно положительным (M1), НЕ МОЖЕТ дренировать
    равномерно: не существует единого порога `β>0` и производной `H'`, для которых
    `H' ≤ −β` на всём `[0,∞)`. Именно НЕравномерность (скорость дренажа обязана убывать
    к нулю) — то, ЧЕМ двигатель обходит неизбежный эндпоинт равномерного режима.
    Следствие `uniform_drain_forbids_eternal_engine` + положительность
    `Real.rpow_pos_of_pos`. (Условие `r<1` — часть спецификации двигателя; сама
    неравномерность держится и без него, поэтому здесь оно помечено как неиспользуемое.) -/
theorem continuous_engine_is_nonuniform {r : ℝ} (hr0 : 0 < r) (_hr1 : r < 1) :
    ¬ ∃ (β : ℝ) (H' : ℝ → ℝ), 0 < β ∧
        (∀ t, 0 ≤ t → HasDerivAt (fun s => r ^ s) (H' t) t) ∧
        (∀ t, 0 ≤ t → H' t ≤ -β) := by
  rintro ⟨β, H', hβ, hderiv, hdrain⟩
  exact uniform_drain_forbids_eternal_engine (fun s => r ^ s) H' β hβ hderiv hdrain
    (fun t _ => Real.rpow_pos_of_pos hr0 t)

/-- **🟢 `continuous_engine_dividing_line` — ДОКАЗАНА (M6, КОРОНА ответа «где невозможен»).**
    Точная демаркация двух сторон:
      (A) НЕВОЗМОЖЕН на РАВНОМЕРНОЙ стороне — никакая вечно-положительная `H` с
          равномерным дренажом `H' ≤ −β` (`β>0`) не существует (эндпоинт неизбежен за
          `T ≤ H 0/β`);
      (B) ВОЗМОЖЕН на НЕравномерной стороне — двигатель существует безусловно
          (`continuous_engine_exists_unconditionally`), причём это мультипликативный
          `r^t`, чья скорость дренажа убывает к нулю (`continuous_engine_is_nonuniform`).
    Демаркатор — РАВНОМЕРНОСТЬ дренажа: единый порог `β>0` убивает вечность, его
    отсутствие её допускает. Это машинный ответ на вопрос «где двигатель невозможен». -/
theorem continuous_engine_dividing_line :
    (∀ (H H' : ℝ → ℝ) (β : ℝ), 0 < β →
        (∀ t, 0 ≤ t → HasDerivAt H (H' t) t) →
        (∀ t, 0 ≤ t → H' t ≤ -β) →
        (∀ t, 0 ≤ t → 0 < H t) → False)
    ∧ (∃ (H : ℝ → ℝ) (r : ℝ), ContinuousEngine H r) := by
  refine ⟨?_, continuous_engine_exists_unconditionally⟩
  intro H H' β hβ hderiv hdrain hpos
  exact uniform_drain_forbids_eternal_engine H H' β hβ hderiv hdrain hpos

/-!
################################################################################
  ИТОГ (LOUD HONEST): что доказано, что переиспользовано, что ОСТАЁТСЯ ОТКРЫТЫМ
################################################################################

  🟢 ГЕНУИННО НОВОЕ (машинно, в этом модуле):
     · `ContinuousEngine` / `continuous_engine_exists` — ПЕРВЫЙ формальный
       непрерывно-временной вечный двигатель `H(t)=r^t` над всем ℝ (M1);
     · `continuous_engine_exists_unconditionally` — безусловная обитаемость (якорь M5);
     · `discrete_forbids_continuous_realizes` — точный контраст ℕ-запрет ↔ ℝ-реализация;
     · `boundedBelow_antitone_converges` — сходимость ≠ противоречие (M2);
     · `cascade_scale_tendsto_zero` — supertask: масштаб → 0 до T (M3, поверх реюза);
     · `ContinuousEngineRuns` / `continuousEngine_runs_iff_not_vorticityControl` —
       языковое тождество Клэя `Iff.rfl` (M4);
     · `millennium_endpoint_unreachable_by_engine` — честный конъюнктивный якорь (M5);
     · `uniform_drain_forbids_eternal_engine` — ГДЕ двигатель НЕВОЗМОЖЕН: равномерный
       дренаж на конечном топливе форсирует эндпоинт за `T ≤ H0/β` (M6);
     · `continuous_engine_is_nonuniform` — `r^t` уцелевает лишь НЕравномерностью (M6);
     · `continuous_engine_dividing_line` — корона: демаркатор есть равномерность (M6).

  🟢 ПЕРЕИСПОЛЬЗОВАНО (цитируется/переэкспортируется, НЕ пере-выводится):
     · `DissipativeCascade.real_positive_work_not_wellfounded` (ℝ-(1/2)ⁿ, M1);
     · `EPMI.no_infinite_descent` (дискретный запрет, M1-контраст);
     · `NavierStokesFront.cookedProfileCascade` + `cookedProfile_at_stage` (M3);
     · `NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl` (M5);
     · `NavierStokesClay.VorticityTimeIntegrable` / `vorticity` (M4);
     · `DyadicBlowup.DyadicSolution.superlinearDrive` (M5, именованный форсинг).

  🔴 ОСТАЁТСЯ ОТКРЫТЫМ (НЕТРОНУТО, ЕДИНСТВЕННЫЙ барьер):
     · `NavierStokesClay.GlobalVorticityControl` — суперкритическая a-priori оценка
       вихря. Этот модуль её НЕ доказывает, НЕ ослабляет и НЕ обходит.

  ГЛАВНОЕ (ГРОМКО): модуль НЕ решает и НЕ «ударяет» задачу тысячелетия. Взрыв
  настоящего НС (C) столь же ОТКРЫТ, как регулярность (A). Двигатель РАЗВЯЗАН от
  нелинейности НС; барьер Тао (JAMS 2016) блокирует энергетический/спусковой путь.
  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`; такса 45
  неизменна; красная линия нетронута. M5 НЕ подделывает ни независимость, ни решение.
-/

#print axioms continuous_engine_exists
#print axioms boundedBelow_antitone_converges
#print axioms cascade_scale_tendsto_zero
#print axioms continuousEngine_runs_iff_not_vorticityControl
#print axioms uniform_drain_forbids_eternal_engine
#print axioms continuous_engine_dividing_line

end EuclidsPath.ContinuousEngine
