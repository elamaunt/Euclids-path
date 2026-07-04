/-
  BSDAnalyticAnchor — СОДЕРЖАТЕЛЬНЫЕ ворота аналитического ранга BSD:
  data-якорь аналитического продолжения L-ряда + НАСТОЯЩИЙ mathlib-порядок нуля.

  ┌─────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК. ЧТО КРАСНОЕ, ЧТО ЗЕЛЁНОЕ И В ЧЁМ КОНТРАСТ.  │
  └─────────────────────────────────────────────────────────────────────────┘

  ПРЕДЫСТОРИЯ. Старые ворота `AnalyticRank` (BSDFront §3) — маркер цитирования:
  они лишь ссылаются на реальную `WeierstrassCurve.LSeries` и СВОБОДНО
  ВЫПОЛНИМЫ при любом ранге (`analyticRank_gate_satisfiable`, BSDEpistemic §2),
  отчего `WeakBSD` доказуемо сводится к голому равенству
  (`weakBSD_reduces_to_bare_equality`). Этот модуль строит СОДЕРЖАТЕЛЬНУЮ
  замену: аналитический ранг = настоящий mathlib-порядок нуля `analyticOrderAt`
  (`Mathlib/Analysis/Analytic/Order.lean`, `analyticOrderAt f z₀ : ℕ∞`)
  функции-продолжения в точке `s = 1`.

  🔴 КРАСНЫЙ DATA-ЯКОРЬ (назван, ниоткуда не выводится):
   · `ContinuedLFunction W` — ДАННЫЕ аналитического продолжения L-ряда кривой:
     функция `Lambda : ℂ → ℂ`, совпадающая с `WeierstrassCurve.LSeries W`
     всюду, где ряд Дирихле абсолютно суммируем (`agreement`, через
     `LSeriesSummable`), и аналитичная в `s = 1` (`analyticAtOne`).

  🟢 ЗЕЛЁНОЕ (машинно, std-тройка аксиом):
   · `dirichletCoeffs_def` / `weierstrassLSeries_eq_LSeries_coeffs` —
     rfl-аудиты цитирования: коэффициенты и ряд — В ТОЧНОСТИ mathlib-объекты
     `WeierstrassCurve.LFunction` / `WeierstrassCurve.LSeries`, без подмены;
   · `analyticRankOf L = analyticOrderAt L.Lambda 1` — СОДЕРЖАТЕЛЬНЫЙ ранг:
     порядок нуля — настоящее mathlib-понятие, а не свободный параметр;
   · `weakBSDContentful_iff_analyticOrderAt` — аудит на переименование: новые
     ворота РАЗВЁРНУТЫ машинно в равенство mathlib-порядков (`Iff.rfl`);
   · `contentfulGate_pins_rank` / `contentfulGate_not_free_at_two_ranks` —
     новые ворота держатся НЕ БОЛЕЕ чем при одном ранге на данный якорь;
   · `oldGate_free_at_every_rank` + `gate_contrast` — КОНТРАСТ машинно: старые
     ворота выполнимы даром при ВСЕХ рангах сразу (реюз
     `analyticRank_gate_satisfiable`), новые требуют ДАННЫХ и пришпиливают ранг;
   · `analytic_order_realizes_every_rank` — невакуумность САМОГО ПОНЯТИЯ ранга:
     для каждого n есть функция, аналитичная в 1, с порядком ровно n
     (центрированный моном, `analyticOrderAt_centeredMonomial`);
   · `skeletonOfNowhereSummable` + `analyticRankOf_skeleton` — невакуумность
     ТИПА данных: скелет с `Lambda = const 1` (порядок 0), ЧЕСТНО помеченный
     «скелет, НЕ настоящая L» и условный на нигде-несуммируемость ряда.

  ЧТО МАТЕМАТИКА ДОЛЖНА ПРЕДЪЯВИТЬ ДЛЯ НАСТОЯЩЕГО ЯКОРЯ (и чего в mathlib
  v4.31 НЕТ, ни теоремой, ни `proof_wanted`):
   1. Аналитическое продолжение `WeierstrassCurve.LSeries W` до `s = 1`. Для
      K = ℚ это модулярность (Wiles–Taylor 1995, BCDT 2001) + продолжение
      L-функций модулярных форм. mathlib даёт аналитичность L-рядов ТОЛЬКО в
      открытой полуплоскости абсолютной сходимости:
      `LSeries_analyticOnNhd f : AnalyticOnNhd ℂ (LSeries f)
        {s | LSeries.abscissaOfAbsConv f < s.re}` — и точка 1 в неё не попадает
      никаким дешёвым способом (см. пункт 2).
   2. Оценки коэффициентов `WeierstrassCurve.LFunction` (граница Хассе
      `|aₚ| ≤ 2√p` — в mathlib отсутствует), дающие
      `LSeries.abscissaOfAbsConv (dirichletCoeffs W) ≤ 3/2`. ВАЖНО: даже с
      Хассе `re 1 = 1 < 3/2`, т.е. `s = 1` лежит СТРОГО ВНЕ полуплоскости
      абсолютной сходимости — продолжение генуинно необходимо, сходимостью его
      не заменить. Якорь — не «лень», а честная точка стыковки.

  ЧЕСТНОСТЬ. Мы НЕ утверждаем ничего о настоящей L-функции: ни существования
  продолжения, ни значения порядка. `ContinuedLFunction` — именованный вход
  для внешних данных; скелет — вырожденный обитатель типа при контрфактическом
  (для настоящих кривых) допущении нигде-несуммируемости, которое mathlib v4.31
  не может ни доказать, ни опровергнуть (нет оценок коэффициентов ни сверху,
  ни снизу). ЭТО НЕ РЕШЕНИЕ BSD И НЕ ГЁДЕЛЬ. Если внешняя математика предъявит
  настоящий якорь `L`, ворота `WeakBSDContentful L r` станут содержательным
  равенством «алгебраический ранг = порядок нуля продолжения в 1».

  Никакого `sorry`, никакого `admit`, никакого `native_decide`, никакой новой
  аксиомы; карантин (CausalClosureAxiom) НЕ импортируется. Зелёные
  грузонесущие — стандартная тройка `propext` / `Classical.choice` /
  `Quot.sound`. Такса репозитория (таинт 47) этим файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BSDAnalyticAnchor.lean
    → ноль ошибок.

  Родство: EuclidsPath/Engine/BSDFront.lean (`AnalyticRank`, `WeakBSD`);
    EuclidsPath/Engine/BSDEpistemic.lean (`analyticRank_gate_satisfiable`,
    `weakBSD_reduces_to_bare_equality`); зеркало аудита переименования:
    EuclidsPath/Engine/BoundedGapsAnchor.lean (`boundedGaps_two_iff_twins`).
-/
import Mathlib
import EuclidsPath.Engine.BSDFront
import EuclidsPath.Engine.BSDEpistemic

set_option autoImplicit false

namespace EuclidsPath.BSDFront.AnalyticAnchor

variable {K : Type*} [Field K] [NumberField K]

/-! ### 🟢 Именованное цитирование коэффициентов (rfl-аудиты) -/

/-- **🟢 Коэффициенты ряда Дирихле кривой — именованное цитирование.**
    В ТОЧНОСТИ `(↑) ∘ W.LFunction` из mathlib-определения
    `WeierstrassCurve.LSeries` (rfl-аудит `dirichletCoeffs_def`). Отдельное имя
    служит двум целям: честная точка цитирования И def-барьер унификатора —
    сырое `(↑) ∘ W.LFunction` в повторяющихся сигнатурах взрывает `isDefEq`
    (под коэффициентами лежит гигантское эйлерово произведение по
    `HeightOneSpectrum (𝓞 K)` с адическими пополнениями). -/
noncomputable def dirichletCoeffs (W : WeierstrassCurve K) : ℕ → ℂ :=
  (↑) ∘ W.LFunction

/-- **🟢 rfl-аудит цитирования (доказано):** `dirichletCoeffs` — буквально
    коэффициенты из mathlib, никакой подмены. -/
theorem dirichletCoeffs_def (W : WeierstrassCurve K) :
    dirichletCoeffs W = (↑) ∘ W.LFunction :=
  rfl

/-- **🟢 rfl-аудит ряда (доказано):** реальная `WeierstrassCurve.LSeries W` —
    это `LSeries (dirichletCoeffs W)`, по определению mathlib. -/
theorem weierstrassLSeries_eq_LSeries_coeffs (W : WeierstrassCurve K) (s : ℂ) :
    WeierstrassCurve.LSeries W s = LSeries (dirichletCoeffs W) s :=
  rfl

/-! ### 🔴 Красный data-якорь: данные аналитического продолжения -/

/-- **🔴 КРАСНЫЙ DATA-ЯКОРЬ — данные аналитического продолжения L-ряда.**

    Поля: `Lambda` — кандидат-продолжение; `agreement` — совпадение с реальной
    `WeierstrassCurve.LSeries W` всюду, где ряд Дирихле абсолютно суммируем
    (форма через `LSeriesSummable (dirichletCoeffs W) s` — это в точности
    область, где mathlib-значение `LSeries` есть честная сумма ряда, а не
    junk-значение `0` из `tsum`); `analyticAtOne` — аналитичность в `s = 1`.

    ЧЕГО НЕТ В MATHLIB v4.31 (потому это данные, а не теорема): продолжения
    `WeierstrassCurve.LSeries` за полуплоскость абсолютной сходимости
    (mathlib даёт лишь `LSeries_analyticOnNhd` ВНУТРИ полуплоскости
    `LSeries.abscissaOfAbsConv f < s.re`); модулярности; функционального
    уравнения; даже границы Хассе `|aₚ| ≤ 2√p` для коэффициентов
    `WeierstrassCurve.LFunction`. И даже с Хассе `s = 1` лежит ВНЕ полуплоскости
    (`1 < 3/2`) — продолжение генуинно необходимо.

    Мы НЕ утверждаем, что такие данные существуют, — только ИМЕНУЕМ вход. -/
structure ContinuedLFunction (W : WeierstrassCurve K) where
  /-- Кандидат-продолжение L-ряда кривой. -/
  Lambda : ℂ → ℂ
  /-- Совпадение с РЕАЛЬНОЙ `WeierstrassCurve.LSeries W` на области абсолютной
      суммируемости ряда Дирихле. Раскрытие: `LSeriesSummable f s` =
      `Summable (LSeries.term f s)` — там, где ряд определён как честная
      сумма; вне этой области `LSeries` возвращает junk `0`, и совпадения
      честно НЕ требуем. -/
  agreement : ∀ s : ℂ, LSeriesSummable (dirichletCoeffs W) s →
    Lambda s = WeierstrassCurve.LSeries W s
  /-- Аналитичность продолжения в `s = 1` — то, чего mathlib НЕ даёт ни для
      одной кривой (нет ни продолжения, ни попадания `1` в полуплоскость
      сходимости). Именно это поле делает якорь ДАННЫМИ. -/
  analyticAtOne : AnalyticAt ℂ Lambda 1

/-- **🟢 Сантехника (доказано):** поле `agreement` потребляемо — при любом
    свидетельстве суммируемости ряда в точке `s` данные якоря обязаны совпасть
    с реальной mathlib-суммой `WeierstrassCurve.LSeries W s`. -/
theorem lambda_agrees_on_summable {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) {s : ℂ}
    (hs : LSeriesSummable (dirichletCoeffs W) s) :
    L.Lambda s = WeierstrassCurve.LSeries W s :=
  L.agreement s hs

/-! ### 🟢 Содержательный аналитический ранг: настоящий mathlib-порядок нуля -/

/-- **🟢 СОДЕРЖАТЕЛЬНЫЙ аналитический ранг данного якоря:** порядок нуля
    `analyticOrderAt L.Lambda 1 : ℕ∞` — НАСТОЯЩЕЕ mathlib-понятие
    (`Mathlib/Analysis/Analytic/Order.lean`): `⊤`, если `Lambda` локально
    тождественный нуль у `1`, иначе единственное `n` с локальным разложением
    `Lambda z = (z − 1) ^ n • g z`, `g` аналитична и `g 1 ≠ 0`
    (`AnalyticAt.analyticOrderAt_eq_natCast`). В отличие от старых ворот
    `AnalyticRank` (свободный параметр `aRank`), это число ВЫЧИСЛЯЕТСЯ из
    данных якоря, а не постулируется. -/
noncomputable def analyticRankOf {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) : ℕ∞ :=
  analyticOrderAt L.Lambda 1

/-- **🟢 Невакуумность ПОНЯТИЯ ранга (доказано):** mathlib-порядок нуля в `1`
    реализует КАЖДОЕ `n : ℕ` — свидетель `(· − 1) ^ n`, аналитичный в `1`, с
    порядком ровно `n` (`analyticOrderAt_centeredMonomial`). Понятие
    различает все ранги — в максимальном контрасте со старыми воротами,
    свободными при всех рангах сразу. -/
theorem analytic_order_realizes_every_rank (n : ℕ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 1 ∧ analyticOrderAt f 1 = (n : ℕ∞) :=
  ⟨(· - 1) ^ n, by fun_prop, analyticOrderAt_centeredMonomial⟩

/-! ### 🟢 Невакуумность ТИПА данных: скелет-обитатель (НЕ настоящая L) -/

/-- **🟢 Порядок константы `1` в точке `1` равен нулю (доказано):** константа
    не обнуляется, `analyticOrderAt_eq_zero` отдаёт `0` даром. Кирпич скелета. -/
theorem analyticOrderAt_const_one_at_one :
    analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 1 = 0 :=
  analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)

/-- **⚠️ СКЕЛЕТ, НЕ НАСТОЯЩАЯ L (честная пометка).** Обитатель типа
    `ContinuedLFunction W` с `Lambda = const 1` ПРИ УСЛОВИИ, что ряд Дирихле
    кривой нигде не суммируем: тогда `agreement` вакуумно истинно, а
    аналитичность константы бесплатна (`analyticAt_const`).

    ДВОЙНАЯ ЧЕСТНОСТЬ: (1) это НЕ данные о настоящей L-функции — константа
    ничего не продолжает; (2) допущение `h` для настоящих эллиптических кривых
    КОНТРФАКТИЧНО (по Хассе ряд сходится при `re s > 3/2`), но mathlib v4.31
    не может его ни доказать, ни опровергнуть — нет НИКАКИХ оценок
    коэффициентов `WeierstrassCurve.LFunction`. Скелет существует только чтобы
    машинно засвидетельствовать: ТИП данных непуст, конструктор потребляем,
    и даже вырожденный обитатель пришпиливает ранг (`analyticRankOf_skeleton`).
    Безусловного обитателя у честного `agreement` НЕТ — и это не дефект, а
    само СОДЕРЖАНИЕ ворот: они требуют данных. -/
noncomputable def skeletonOfNowhereSummable (W : WeierstrassCurve K)
    (h : ∀ s : ℂ, ¬ LSeriesSummable (dirichletCoeffs W) s) :
    ContinuedLFunction W where
  Lambda := fun _ => 1
  agreement := fun s hs => absurd hs (h s)
  analyticAtOne := analyticAt_const

/-- **🟢 Ранг скелета равен нулю (доказано):** даже вырожденный обитатель
    потребляется содержательно — `analyticOrderAt (const 1) 1 = 0`, никакой
    свободы выбора ранга (ср. старые ворота, свободные при ЛЮБОМ ранге). -/
theorem analyticRankOf_skeleton (W : WeierstrassCurve K)
    (h : ∀ s : ℂ, ¬ LSeriesSummable (dirichletCoeffs W) s) :
    analyticRankOf (skeletonOfNowhereSummable W h) = 0 := by
  show analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 1 = 0
  exact analyticOrderAt_const_one_at_one

/-! ### 🔴→🟢 Содержательные ворота WeakBSDContentful и аудит контраста -/

/-- **СОДЕРЖАТЕЛЬНЫЕ ворота слабой BSD при данном якоре:** алгебраический ранг
    `algRank` равен порядку нуля продолжения в `1`. В отличие от старого
    `WeakBSD` (BSDFront §3), где аналитический конъюнкт свободно выполним и
    всё сводится к голому равенству двух свободных ℕ-параметров
    (`weakBSD_reduces_to_bare_equality`), здесь правая часть ВЫЧИСЛЕНА из
    данных `L` настоящим mathlib-понятием `analyticOrderAt`. Предикат честно
    ОТКРЫТ: мы не доказываем и не опровергаем его ни для одного настоящего
    якоря (настоящих якорей в mathlib нет — см. `ContinuedLFunction`). -/
def WeakBSDContentful {W : WeierstrassCurve K} (L : ContinuedLFunction W)
    (algRank : ℕ) : Prop :=
  analyticRankOf L = algRank

/-- **🟢 АУДИТ НА ПЕРЕИМЕНОВАНИЕ ЦЕЛИ (доказано; зеркало
    `offCriticalBridge_iff_RH` / `boundedGaps_two_iff_twins`):** новые ворота
    машинно РАЗВЁРНУТЫ (`Iff.rfl`) в равенство `analyticOrderAt L.Lambda 1 =
    algRank` — чистое mathlib-утверждение о порядке нуля, БЕЗ упоминания BSD.
    Ворота не прячут цель под новым именем: принять их — значит принять ровно
    это равенство порядков, ни больше ни меньше. -/
theorem weakBSDContentful_iff_analyticOrderAt {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) (algRank : ℕ) :
    WeakBSDContentful L algRank ↔ analyticOrderAt L.Lambda 1 = (algRank : ℕ∞) :=
  Iff.rfl

/-- **🟢 Новые ворота ПРИШПИЛИВАЮТ ранг (доказано):** на одном якоре `L` ворота
    держатся не более чем при одном ранге — `analyticOrderAt` есть функция
    данных, инъективность каста ℕ → ℕ∞ довершает. Ср. старые ворота: выполнимы
    при всех рангах СРАЗУ (`oldGate_free_at_every_rank`). -/
theorem contentfulGate_pins_rank {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) {r₁ r₂ : ℕ}
    (h₁ : WeakBSDContentful L r₁) (h₂ : WeakBSDContentful L r₂) :
    r₁ = r₂ := by
  have e₁ : analyticRankOf L = (r₁ : ℕ∞) := h₁
  have e₂ : analyticRankOf L = (r₂ : ℕ∞) := h₂
  exact_mod_cast e₁.symm.trans e₂

/-- **🟢 Новые ворота НЕ свободны (доказано):** ни один якорь не пропускает два
    разных ранга — конкретно, `0` и `1` одновременно невозможны. Контраст со
    старыми воротами, где `AnalyticRank W 0 ∧ AnalyticRank W 1` доказуемо даром
    (см. `gate_contrast`). -/
theorem contentfulGate_not_free_at_two_ranks {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) :
    ¬ (WeakBSDContentful L 0 ∧ WeakBSDContentful L 1) :=
  fun ⟨h0, h1⟩ => zero_ne_one (contentfulGate_pins_rank L h0 h1)

/-- **🟢 Старые ворота выполнимы даром (реюз, доказано):** прямое цитирование
    `analyticRank_gate_satisfiable` (BSDEpistemic §2) — `AnalyticRank W aRank`
    держится при ЛЮБОМ `aRank` без каких-либо данных. Это лемма честности
    старого слоя; здесь она нужна как одна нога машинного контраста. -/
theorem oldGate_free_at_every_rank (W : WeierstrassCurve K) (aRank : ℕ) :
    AnalyticRank W aRank :=
  Epistemic.analyticRank_gate_satisfiable W aRank

/-- **🟢 МАШИННЫЙ КОНТРАСТ СТАРОЕ/НОВОЕ (доказано, одна теорема):** старые
    ворота держатся при ВСЕХ рангах одновременно (свободная выполнимость,
    реюз `analyticRank_gate_satisfiable`), новые — не более чем при ОДНОМ ранге
    на якорь. «Старые выполнимы даром, новые требуют данных и пришпиливают
    ранг» — не комментарий, а конъюнкция двух доказанных ног. -/
theorem gate_contrast (W : WeierstrassCurve K) :
    (∀ r : ℕ, AnalyticRank W r) ∧
      ∀ L : ContinuedLFunction W, ∀ r₁ r₂ : ℕ,
        WeakBSDContentful L r₁ → WeakBSDContentful L r₂ → r₁ = r₂ :=
  ⟨fun r => Epistemic.analyticRank_gate_satisfiable W r,
   fun L _ _ h₁ h₂ => contentfulGate_pins_rank L h₁ h₂⟩

/-- **🟢 Старый фронт закрывается под якорем — но ОПЛАЧЕН СВОБОДОЙ СТАРЫХ ВОРОТ
    (доказано, с честной пометкой):** из `WeakBSDContentful L algRank` следует
    `WeakBSD W algRank algRank`. ЧЕСТНОСТЬ МАШИННО ВИДНА: гипотеза `_h` в
    доказательстве НЕ ПОТРЕБЛЯЕТСЯ (подчёркнутая переменная) — старый фронт
    закрывается даром для любой диагональной пары, ибо его аналитический
    конъюнкт свободен (`analyticRank_gate_satisfiable`). Никакого переноса
    содержания из новых ворот в старые НЕТ; стрелка существует лишь как
    аудит вырожденности старого слоя. -/
theorem weakBSD_of_contentful {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) (algRank : ℕ)
    (_h : WeakBSDContentful L algRank) :
    WeakBSD W algRank algRank :=
  ⟨Epistemic.analyticRank_gate_satisfiable W algRank, rfl⟩

/-- **🟢 Скелет пришпиливает ранг 0 (доказано, условно на допущении скелета):**
    вырожденный обитатель проходит новые ворота ТОЛЬКО при `algRank = 0` —
    даже он не даёт свободы выбора. НЕ утверждение о настоящей L: константа
    `1` ничего не продолжает, допущение нигде-несуммируемости контрфактично
    для настоящих кривых (см. `skeletonOfNowhereSummable`). -/
theorem skeleton_contentful_zero (W : WeierstrassCurve K)
    (h : ∀ s : ℂ, ¬ LSeriesSummable (dirichletCoeffs W) s) :
    WeakBSDContentful (skeletonOfNowhereSummable W h) 0 := by
  show analyticRankOf (skeletonOfNowhereSummable W h) = ((0 : ℕ) : ℕ∞)
  simpa using analyticRankOf_skeleton W h

/-! ################################################################################
    ИТОГ (LOUD HONEST)
    ################################################################################

  🔴 КРАСНЫЙ DATA-ЯКОРЬ: `ContinuedLFunction W` — данные продолжения
     (`Lambda`, `agreement` на области `LSeriesSummable`, `analyticAtOne`).
     В mathlib v4.31 таких данных нет ни для одной кривой: нет продолжения
     `WeierstrassCurve.LSeries` за полуплоскость `abscissaOfAbsConv < re s`
     (есть лишь `LSeries_analyticOnNhd` внутри неё), нет модулярности, нет
     функционального уравнения, нет границы Хассе; и даже с Хассе `s = 1`
     лежит вне полуплоскости — продолжение генуинно необходимо.

  🟢 МАШИННО, В ЭТОМ ФАЙЛЕ:
     · `dirichletCoeffs_def`, `weierstrassLSeries_eq_LSeries_coeffs` —
       rfl-аудиты: цитируются В ТОЧНОСТИ mathlib-объекты, без подмены;
     · `analyticRankOf` — содержательный ранг: mathlib-`analyticOrderAt` в `1`;
     · `weakBSDContentful_iff_analyticOrderAt` — аудит: ворота = чистое
       равенство порядков, `Iff.rfl`, БЕЗ скрытого переименования цели;
     · `contentfulGate_pins_rank`, `contentfulGate_not_free_at_two_ranks`,
       `gate_contrast` — новые ворота требуют данных и пришпиливают ранг;
       старые (`oldGate_free_at_every_rank`, реюз
       `analyticRank_gate_satisfiable`) выполнимы даром при всех рангах;
     · `analytic_order_realizes_every_rank` — понятие порядка реализует
       каждое n (центрированный моном);
     · `skeletonOfNowhereSummable`, `analyticRankOf_skeleton`,
       `skeleton_contentful_zero` — тип данных непуст (скелет, НЕ настоящая L,
       условно на контрфактической нигде-несуммируемости), и даже скелет
       пришпилен к рангу 0;
     · `weakBSD_of_contentful` — старый фронт закрывается под якорем, но
       оплачен свободой старых ворот (гипотеза не потребляется — видно машине).

  🟢 ПЕРЕИСПОЛЬЗОВАНО (цитируется, НЕ пере-выводится):
     `AnalyticRank`, `WeakBSD` (BSDFront); `analyticRank_gate_satisfiable`
     (BSDEpistemic); mathlib: `analyticOrderAt`, `analyticOrderAt_eq_zero`,
     `analyticOrderAt_centeredMonomial`, `analyticAt_const`, `LSeriesSummable`,
     `WeierstrassCurve.LFunction` / `WeierstrassCurve.LSeries`.

  🔴 ЧЕСТНО ОТКРЫТО (и НЕ трогается): существование настоящего продолжения,
     его порядок в 1, сама BSD. Мы НЕ утверждаем ничего о настоящей L-функции.
     ЭТО НЕ ДОКАЗАТЕЛЬСТВО BSD И НЕ ГЁДЕЛЬ.

  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`; карантин
  не импортирован; таинт 47 не меняется.
-/

#print axioms dirichletCoeffs
#print axioms dirichletCoeffs_def
#print axioms weierstrassLSeries_eq_LSeries_coeffs
#print axioms ContinuedLFunction
#print axioms lambda_agrees_on_summable
#print axioms analyticRankOf
#print axioms analytic_order_realizes_every_rank
#print axioms analyticOrderAt_const_one_at_one
#print axioms skeletonOfNowhereSummable
#print axioms analyticRankOf_skeleton
#print axioms WeakBSDContentful
#print axioms weakBSDContentful_iff_analyticOrderAt
#print axioms contentfulGate_pins_rank
#print axioms contentfulGate_not_free_at_two_ranks
#print axioms oldGate_free_at_every_rank
#print axioms gate_contrast
#print axioms weakBSD_of_contentful
#print axioms skeleton_contentful_zero

end EuclidsPath.BSDFront.AnalyticAnchor
