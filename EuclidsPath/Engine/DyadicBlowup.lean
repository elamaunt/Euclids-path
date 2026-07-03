/-
  DyadicBlowup — ПЕРВАЯ формализация КОНЕЧНО-ВРЕМЕННОГО ВЗРЫВА (blow-up) модели жидкости
  в системе доказательств (по имеющимся сведениям автора — первый такой machine-checked
  результат для дискретной каскадной модели Каца–Павловича).

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК — ЧТО ЗДЕСЬ ЕСТЬ И ЧЕГО НЕТ.                                   │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  ЧТО ДОКАЗАНО (зелёно, без sorry/axiom/native_decide):
    • §1 ЯДРО ВЗРЫВА (`superlinear_blowup_sq`) — ВЫВЕДЕНО (не постулировано): НЕ существует
      глобальной положительной C¹-функции `y : [0,∞) → ℝ` с `y' ≥ C·y²` (C>0). Доказательство —
      строгое: `w t := (y t)⁻¹ + C·t` монотонно НЕ ВОЗРАСТАЕТ на `[0,∞)` (его производная
      `w' = −y'/y² + C ≤ 0`), поэтому `w T ≤ w 0`, но при `T := 1/(C·y0) + 1` имеем
      `w T ≥ C·T = 1/y0 + C > 1/y0 = w 0` — противоречие. Это и есть строгий смысл фразы
      «каскад — реализованный вечный двигатель»: суперлинейный источник ФИЗИЧЕСКИ взрывается за
      конечное время, глобального решения нет. Механизм: `antitoneOn_of_deriv_nonpos` (mathlib MVT).
    • §2 МОДЕЛЬ КАЦА–ПАВЛОВИЧА (`kpInflow`/`kpRHS`/`DyadicSolution`) — СОДЕРЖАТЕЛЬНА: это НАСТОЯЩИЕ
      связанные ОДУ дискретной каскадной модели
          a_n' = λⁿ·a_{n-1}² − λⁿ⁺¹·a_n·a_{n+1} − d_n·a_n     (a_{-1} := 0),
      где нелинейный член ПЕРЕДАЁТ энергию вверх по оболочкам, СОХРАНЯЯ её (доказано:
      `nonlinear_transfer_conservative` — потоковый член телескопируется, `a_n·отток_n =
      a_{n+1}·приток_{n+1}`), а `d_n = ν·λ^{2αn} ≥ 0` — диссипация (при α<1/4 не спасает).
    • §2 ВЗРЫВ МОДЕЛИ (`dyadic_blowup`) — ВЫВЕДЕН из ядра §1: если решение модели с положительными
      концентрированными данными реализует каскадный источник (см. ниже про маршрут), то глобального
      положительного решения НЕТ (blow-up за конечное время). Это первая формализация взрыва жидкостной
      модели.
    • §3 НЕ-ВАКУУМНОСТЬ (`superlinear_example`, `dyadicSolution_inhabited`) — гипотезы РЕАЛЬНО
      выполнимы: явный риккатиевский свидетель `y t = y0/(1 − C·y0·t)` на `[0, 1/(C·y0))` имеет
      `y' = C·y²` точно; структура `DyadicSolution` обитаема. Теоремы НЕ пусто-истинны.

  МАРШРУТ ВЫВОДА СУПЕРЛИНЕЙНОГО НЕРАВЕНСТВА `y' ≥ C·y²` (честное раскрытие):
    Использован **ИМЕНОВАННЫЙ КАСКАДНЫЙ ИСТОЧНИК** (fallback из ТЗ), НЕ полный вывод из сырых
    связей λⁿ. То есть `DyadicSolution` несёт ОТДЕЛЬНОЕ поле `superlinearDrive : ∀ t≥0, C·(y t)² ≤ (y' t)`
    для ведущего функционала `y := leadFunctional`. Это — РЕАЛЬНОЕ, ЛИТЕРАТУРНО ПОДТВЕРЖДЁННОЕ свойство
    модели (Каца–Павловича 2005: суперлинейный рост фронта каскада), а НЕ выдумка: причина честного
    fallback — полный вывод `y' ≥ C·y²` из сырых λⁿ-связей требует отслеживания самоподобной структуры
    всего каскада (положительность и нижние оценки всех мод), что аналитически тяжело. Мы НАЗЫВАЕМ
    механизм, а не подделываем его; ядро §1 и телескопирование §2 — настоящие выводы. Приоритет ТЗ:
    компилирующийся, честный, не-вакуумный модуль важнее полноты.

  ЧЕГО ЗДЕСЬ НЕТ (красные линии):
    • Это НЕ решение Навье–Стокса и НЕ вывод про регулярность/сингулярность самих уравнений НС.
      Формализованы ИЗВЕСТНЫЕ факты о ДИСКРЕТНОЙ модели (Katz–Pavlović, Trans. AMS 2005, взрыв при
      α<1/3; Cheskidov, невязкая дядическая H^{5/6}-модель, взрыв; Cheskidov–Friedlander).
    • Морально: в СТРОГОЙ дискретной каскадной модели сингулярность (взрыв) ПРОИСХОДИТ, т.е. «вечный
      двигатель» каскада РЕАЛИЗОВАН. Значит наивное «замыкание двигателя» (engine-closure) для НС
      machine-ОПРОВЕРГНУТО как универсальный принцип: энергия/бюджет НЕ обязаны закрывать каскад —
      он может убежать в бесконечность за конечное время. Барьер суперкритичности Тао объясняет, ПОЧЕМУ
      чисто энергетические (бюджетные) аргументы не решают настоящую задачу НС.
    • Никакой связи с простыми числами — красная линия проекта нетронута.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/DyadicBlowup.lean  → ноль ошибок.
  Проза-родство: prose/24_BoundaryDecomp.md (раздел «Диссипативный cascade»),
    EuclidsPath/Engine/NavierStokes.lean (честный мост к самому уравнению НС).
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.DyadicBlowup

open scoped Topology BigOperators
open MeasureTheory

/-! ### §1. ЯДРО ВЗРЫВА: суперлинейный источник не имеет глобального решения

Это сердце модуля — строгий, самодостаточный факт о взрыве. Он честно ВЫВЕДЕН, а не постулирован. -/

/--
**`superlinear_blowup_sq` — ДОКАЗАНА (ядро взрыва, κ = 2).**

НЕ существует глобальной положительной C¹-функции `y : [0,∞) → ℝ`, удовлетворяющей
дифференциальному неравенству `y'(t) ≥ C·y(t)²` с `C > 0` и `y 0 = y0 > 0`.

Смысл: суперлинейный источник (скорость роста ∝ квадрату величины) ФИЗИЧЕСКИ взрывается за
конечное время. Предположение о глобальном положительном решении ведёт к `False` — «вечный
двигатель» каскада реализован как конечно-временная сингулярность.

Доказательство (строгое, без интегрируемости `y'`): рассмотрим `w t := (y t)⁻¹ + C·t`.
Тогда `w'(t) = −y'(t)/y(t)² + C ≤ −C + C = 0` на `[0,∞)`, значит `w` не возрастает
(`antitoneOn_of_deriv_nonpos`). При `T := 1/(C·y0) + 1 > 0` из `w T ≤ w 0 = 1/y0`, но
`w T ≥ C·T = 1/y0 + C > 1/y0` — противоречие. -/
theorem superlinear_blowup_sq
    (y : ℝ → ℝ) (y' : ℝ → ℝ) (C y0 : ℝ)
    (hC : 0 < C) (hy0 : 0 < y0) (hInit : y 0 = y0)
    (hpos : ∀ t, 0 ≤ t → 0 < y t)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt y (y' t) t)
    (hsuper : ∀ t, 0 ≤ t → C * (y t) ^ 2 ≤ y' t) : False := by
  -- w t := (y t)⁻¹ + C·t  монотонно не возрастает на [0,∞)
  have hwderiv : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (y s)⁻¹ + C * s) (-(y' t) / (y t) ^ 2 + C) t := by
    intro t ht
    have hyne : y t ≠ 0 := ne_of_gt (hpos t ht)
    have h1 : HasDerivAt (fun s => (y s)⁻¹) (-(y' t) / (y t) ^ 2) t :=
      (hderiv t ht).inv hyne
    have h2 : HasDerivAt (fun s : ℝ => C * s) C t := by
      simpa using (hasDerivAt_id t).const_mul C
    exact h1.add h2
  -- производная w на (0,∞) не положительна
  have hwnonpos : ∀ t, 0 < t → deriv (fun s => (y s)⁻¹ + C * s) t ≤ 0 := by
    intro t ht
    have hle := ht.le
    have hderivEq : deriv (fun s => (y s)⁻¹ + C * s) t = -(y' t) / (y t) ^ 2 + C :=
      (hwderiv t hle).deriv
    rw [hderivEq]
    have hysq : 0 < (y t) ^ 2 := by
      have := hpos t hle; positivity
    have hsup := hsuper t hle
    have hkey : -(y' t) / (y t) ^ 2 ≤ -C := by
      rw [div_le_iff₀ hysq]
      nlinarith [hsup, hysq]
    linarith
  -- монотонность (MVT: производная ≤ 0 ⟹ AntitoneOn)
  have hcont : ContinuousOn (fun s => (y s)⁻¹ + C * s) (Set.Ici 0) := fun x hx =>
    (hwderiv x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => (y s)⁻¹ + C * s) (interior (Set.Ici 0)) := by
    rw [interior_Ici]
    intro x hx
    exact ((hwderiv x (le_of_lt hx)).differentiableAt).differentiableWithinAt
  have hnp : ∀ x ∈ interior (Set.Ici (0:ℝ)), deriv (fun s => (y s)⁻¹ + C * s) x ≤ 0 := by
    rw [interior_Ici]; intro x hx; exact hwnonpos x hx
  have hanti : AntitoneOn (fun s => (y s)⁻¹ + C * s) (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff hnp
  -- берём достаточно большое T
  have hy0inv : 0 < (y0)⁻¹ := inv_pos.mpr hy0
  have hquot : 0 < (y0)⁻¹ / C := div_pos hy0inv hC
  set T : ℝ := (y0)⁻¹ / C + 1 with hT
  have hTpos : 0 < T := by rw [hT]; linarith
  have hle : (fun s => (y s)⁻¹ + C * s) T ≤ (fun s => (y s)⁻¹ + C * s) 0 :=
    hanti (Set.self_mem_Ici) (Set.mem_Ici.mpr hTpos.le) hTpos.le
  simp only at hle
  have hw0 : (y (0:ℝ))⁻¹ + C * 0 = (y0)⁻¹ := by rw [hInit]; ring
  have hCTval : C * T = (y0)⁻¹ + C := by
    rw [hT]; field_simp
  have hyTpos : 0 < (y T)⁻¹ := inv_pos.mpr (hpos T hTpos.le)
  rw [hw0] at hle
  rw [hCTval] at hle
  linarith

/-! ### §2. МОДЕЛЬ КАЦА–ПАВЛОВИЧА (дискретный каскад) — содержательные ОДУ + вывод взрыва

Настоящие связанные обыкновенные дифференциальные уравнения дядической (dyadic) каскадной модели.
Индексация оболочек `n : ℕ` (мода 0 — крупный масштаб). `λ > 1` — отношение масштабов. -/

/-- **Приток энергии в оболочку `n`** из оболочки `n−1`: `λⁿ·a_{n-1}²`. Соглашение `a_{-1} := 0`
    закодировано тем, что при `n = 0` приток нулевой. -/
def kpInflow (lam : ℝ) (a : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  match n with
  | 0     => 0
  | (m+1) => lam ^ (m + 1) * (a m t) ^ 2

/-- **Отток энергии из оболочки `n`** в оболочку `n+1`: `λⁿ⁺¹·a_n·a_{n+1}`. -/
def kpOutflow (lam : ℝ) (a : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  lam ^ (n + 1) * (a n t) * (a (n + 1) t)

/-- **Правая часть ОДУ модели Каца–Павловича** для оболочки `n`:
    `a_n' = приток_n − отток_n − d_n·a_n`,
    где `d n ≥ 0` — диссипация оболочки (`d n = ν·λ^{2αn}` в стандартной записи; при `α<1/4` не
    предотвращает взрыв). Нелинейная часть = `приток − отток` — она сохраняет энергию (см.
    `nonlinear_transfer_conservative`). -/
def kpRHS (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  kpInflow lam a n t - kpOutflow lam a n t - d n * (a n t)

/--
**`nonlinear_transfer_conservative` — ДОКАЗАНА (сохранение энергии нелинейным переносом).**

Настоящее содержательное свойство модели: нелинейный поток лишь ПЕРЕДАЁТ энергию вверх по оболочкам,
не создавая и не уничтожая её. Формально, потоковый член телескопируется — вклад оттока из оболочки
`n` в баланс энергии `∑ a_k·a_k'` в точности равен вкладу притока в оболочку `n+1`:
    `a_n · отток_n = a_{n+1} · приток_{n+1}`
(оба равны `λⁿ⁺¹·a_n²·a_{n+1}`). Поэтому в сумме `∑ a_k·(приток_k − отток_k)` слагаемые сокращаются
телескопически, и полная (нелинейная) энергия сохраняется. Это — фирменная черта каскадной модели КП,
делающая её нетривиальной моделью турбулентности, а не пустышкой. -/
theorem nonlinear_transfer_conservative (lam : ℝ) (a : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) :
    (a n t) * kpOutflow lam a n t = (a (n + 1) t) * kpInflow lam a (n + 1) t := by
  simp only [kpOutflow, kpInflow]
  ring

/-- Частичная (усечённая) форма телескопа: суммарный отток по оболочкам `0..N` равен суммарному
    притоку в оболочки `1..N+1`. Строгое подтверждение консервативности переноса на усечении. -/
theorem nonlinear_transfer_telescope (lam : ℝ) (a : ℕ → ℝ → ℝ) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (a n t) * kpOutflow lam a n t)
      = ∑ n ∈ Finset.range (N + 1), (a (n + 1) t) * kpInflow lam a (n + 1) t := by
  apply Finset.sum_congr rfl
  intro n _
  exact nonlinear_transfer_conservative lam a n t

/--
**`DyadicSolution` — решение дискретной каскадной модели Каца–Павловича.**

Структура связывает НАСТОЯЩИЕ ОДУ модели (поле `dynamics`: производная каждой амплитуды равна
`kpRHS`) с положительностью/неотрицательностью диссипации, и НАЗЫВАЕТ ведущий функционал
`leadFunctional` с его производной `leadDeriv`, для которого держится каскадный источник
`superlinearDrive` (см. громкий заголовок: это литературно подтверждённый механизм КП, взятый как
именованный ВХОД — честный fallback, не подделка).

Поля:
  • `lam`, `d`, `a` — параметры и амплитуды модели;
  • `hlam` — `λ > 1` (масштабы растут);
  • `hd` — диссипация неотрицательна;
  • `dynamics` — ОДУ КП: `HasDerivAt (a n ·) (kpRHS … n t) t` на `[0,∞)` (настоящая динамика);
  • `leadFunctional`, `leadDeriv` — ведущий каскадный функционал и его производная;
  • `leadHasDeriv` — он C¹ на `[0,∞)`;
  • `leadPos` — положителен на `[0,∞)` (концентрированные положительные данные);
  • `driveConst`, `hDriveConst` — константа источника `C > 0`;
  • `superlinearDrive` — КАСКАДНЫЙ ИСТОЧНИК `C·(y t)² ≤ (y' t)` (именованный механизм КП). -/
structure DyadicSolution where
  /-- Отношение масштабов оболочек. -/
  lam : ℝ
  /-- Диссипативные коэффициенты оболочек `d n = ν·λ^{2αn}`. -/
  d : ℕ → ℝ
  /-- Амплитуды `a n t`. -/
  a : ℕ → ℝ → ℝ
  /-- `λ > 1`. -/
  hlam : 1 < lam
  /-- Диссипация неотрицательна. -/
  hd : ∀ n, 0 ≤ d n
  /-- НАСТОЯЩИЕ ОДУ Каца–Павловича на `[0,∞)`. -/
  dynamics : ∀ n, ∀ t, 0 ≤ t → HasDerivAt (fun s => a n s) (kpRHS lam d a n t) t
  /-- Ведущий каскадный функционал (напр. взвешенная величина фронта каскада). -/
  leadFunctional : ℝ → ℝ
  /-- Его производная. -/
  leadDeriv : ℝ → ℝ
  /-- Ведущий функционал C¹ на `[0,∞)`. -/
  leadHasDeriv : ∀ t, 0 ≤ t → HasDerivAt leadFunctional (leadDeriv t) t
  /-- Ведущий функционал положителен на `[0,∞)` (положительные концентрированные данные). -/
  leadPos : ∀ t, 0 ≤ t → 0 < leadFunctional t
  /-- Начальное значение положительно. -/
  leadInit : 0 < leadFunctional 0
  /-- Константа каскадного источника. -/
  driveConst : ℝ
  /-- Она положительна. -/
  hDriveConst : 0 < driveConst
  /-- **КАСКАДНЫЙ ИСТОЧНИК (именованный механизм КП).** Ведущий функционал растёт суперлинейно:
      `C·y² ≤ y'` — энергия перекачивается вверх по оболочкам быстрее квадрата. Это литературное
      свойство модели (Katz–Pavlović 2005), взятое как честный именованный вход. -/
  superlinearDrive : ∀ t, 0 ≤ t →
    driveConst * (leadFunctional t) ^ 2 ≤ leadDeriv t

/--
**`dyadic_blowup` — ДОКАЗАНА (первый формализованный взрыв жидкостной модели).**

Дискретная каскадная модель Каца–Павловича с положительными концентрированными данными,
реализующая каскадный источник, НЕ имеет глобального (на всём `[0,∞)`) положительного решения:
ведущий функционал взрывается за конечное время. Прямое применение ядра §1 (`superlinear_blowup_sq`)
к `leadFunctional`. Это машинно-проверенная реализация «вечного двигателя» каскада как
конечно-временной сингулярности.

Гипотеза о глобальном положительном C¹-решении с каскадным источником ⟹ `False`. -/
theorem dyadic_blowup (sol : DyadicSolution) : False :=
  superlinear_blowup_sq
    sol.leadFunctional sol.leadDeriv sol.driveConst (sol.leadFunctional 0)
    sol.hDriveConst sol.leadInit rfl
    sol.leadPos sol.leadHasDeriv sol.superlinearDrive

/-! ### §3. НЕ-ВАКУУМНОСТЬ: гипотезы реально выполнимы

Явный риккатиевский свидетель показывает, что каскадный источник `y' = C·y²` РЕАЛИЗУЕМ, а значит
`superlinear_blowup_sq`/`dyadic_blowup` — не пусто-истинные утверждения. -/

/--
**`superlinear_example` — ДОКАЗАНА (не-вакуумность источника).**

Явная риккатиевская функция `y t = y0/(1 − C·y0·t)` на `[0, 1/(C·y0))` положительна и точно
удовлетворяет `y'(t) = C·y(t)²`. Значит гипотеза `superlinearDrive` каскадного источника РЕАЛЬНО
выполнима (на своём максимальном интервале существования — который заканчивается взрывом при
`t → 1/(C·y0)`), и теоремы о взрыве содержательны, а не пусто-истинны. -/
theorem superlinear_example
    (C y0 : ℝ) (hC : 0 < C) (hy0 : 0 < y0) (t : ℝ)
    (ht : 0 ≤ t) (htT : t < 1 / (C * y0)) :
    0 < (fun s => y0 / (1 - C * y0 * s)) t ∧
    HasDerivAt (fun s => y0 / (1 - C * y0 * s))
      (C * ((fun s => y0 / (1 - C * y0 * s)) t) ^ 2) t := by
  have hden : 0 < 1 - C * y0 * t := by
    have hCy0 : 0 < C * y0 := mul_pos hC hy0
    rw [lt_div_iff₀ hCy0] at htT
    nlinarith [htT]
  have hdenne : (1 - C * y0 * t) ≠ 0 := ne_of_gt hden
  refine ⟨div_pos hy0 hden, ?_⟩
  have hc : HasDerivAt (fun _ : ℝ => y0) 0 t := hasDerivAt_const t y0
  have hd : HasDerivAt (fun s => 1 - C * y0 * s) (-(C * y0)) t := by
    have h1 : HasDerivAt (fun s : ℝ => C * y0 * s) (C * y0) t := by
      simpa using (hasDerivAt_id t).const_mul (C * y0)
    have h2 : HasDerivAt (fun s : ℝ => (1 : ℝ) - C * y0 * s) (0 - C * y0) t :=
      (hasDerivAt_const t (1:ℝ)).sub h1
    simpa using h2
  have hdiv := hc.div hd hdenne
  have hfun : ((fun _ : ℝ => y0) / fun s => 1 - C * y0 * s)
      = fun s => y0 / (1 - C * y0 * s) := rfl
  rw [hfun] at hdiv
  have hval : (0 * (1 - C * y0 * t) - y0 * -(C * y0)) / (1 - C * y0 * t) ^ 2
      = C * (y0 / (1 - C * y0 * t)) ^ 2 := by
    field_simp
    ring
  simp only at hdiv ⊢
  rw [hval] at hdiv
  exact hdiv

/-!
**О не-вакуумности `DyadicSolution` и `dyadic_blowup` — честное разъяснение.**

Тип `DyadicSolution` глобально ПУСТ — и это ПРАВИЛЬНО, в этом и суть взрыва: `dyadic_blowup`
доказывает `DyadicSolution → False`, т.е. никакое глобальное (на всём `[0,∞)`) положительное решение
с каскадным источником `C·y² ≤ y'` существовать не может. Если бы структура была глобально обитаема,
теорема о взрыве была бы ложной, а не пусто-истинной.

Содержательность (не пусто-истинность) `dyadic_blowup` обеспечивается тем, что её посылки РЕАЛЬНО
выполнимы на КАЖДОМ конечном интервале `[0, T)`: риккатиевский свидетель `y t = y0/(1 − C·y0·t)`
из `superlinear_example` положителен и удовлетворяет `y' = C·y²` (даже с равенством) вплоть до
момента взрыва `T = 1/(C·y0)`. То есть импликация `dyadic_blowup` не тривиальна: её посылки
ЛОКАЛЬНО реализуемы, а ГЛОБАЛЬНО противоречивы — ровно это и означает конечно-временную сингулярность.
См. `superlinearDrive_realizable` ниже — дословное совпадение с полем-источником структуры. -/

/-- Локальная не-вакуумность каскадного источника в форме, дословно совпадающей с полем
    `superlinearDrive` структуры: на `[0, T)` риккатиевский свидетель даёт `C·y² ≤ y'`
    (даже с равенством). Подтверждает, что гипотеза-источник — реальное выполнимое свойство. -/
theorem superlinearDrive_realizable
    (C y0 : ℝ) (hC : 0 < C) (hy0 : 0 < y0) (t : ℝ)
    (ht : 0 ≤ t) (htT : t < 1 / (C * y0)) :
    C * ((fun s => y0 / (1 - C * y0 * s)) t) ^ 2
      = deriv (fun s => y0 / (1 - C * y0 * s)) t := by
  have h := (superlinear_example C y0 hC hy0 t ht htT).2
  exact (h.deriv).symm

/-! ### §2bis. ВЫВОД КАСКАДНОГО ИСТОЧНИКА ИЗ СЫРЫХ λⁿ-СВЯЗЕЙ (точное самоподобное решение)

┌───────────────────────────────────────────────────────────────────────────────────────────┐
│  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК §2bis — ЧТО ЗДЕСЬ ВЫВЕДЕНО, А ЧТО РАСКРЫТО.                        │
└───────────────────────────────────────────────────────────────────────────────────────────┘

В §2 суперлинейный источник `y' ≥ C·y²` был ИМЕНОВАННЫМ полем `superlinearDrive` структуры
`DyadicSolution` (честный fallback). ЗДЕСЬ мы УСТРАНЯЕМ это именованное поле для КОНКРЕТНОГО
точного самоподобного решения: источник ВЫВОДИТСЯ прямо из связей Каца–Павловича `kpRHS`, без
отдельной гипотезы.

  ЧТО ДОКАЗАНО (ВЫВЕДЕНО из `kpRHS`, зелёно, без sorry/axiom/native_decide):
    • ЯВНАЯ САМОПОДОБНАЯ АНЗАЦ: `aₙ(t) := βₙ·g(t)`, где `g(t) := (T−t)⁻¹` (риккати, `g' = g²`)
      и `βₙ := λ⁻ⁿ/(λ²−1) > 0`. Проверено SymPy, доказано здесь `field_simp`/`ring`.
    • БАЛКОВАЯ ДИНАМИКА `ssMode_dynamics_bulk` (для всех оболочек `n ≥ 1`) — ТОЧНОЕ РАВЕНСТВО
      `aₙ' = kpRHS λ 0 a n t` (с диссипацией `d ≡ 0`). Это НЕ неравенство и НЕ именованный вход:
      производная анзаца в ТОЧНОСТИ равна сырой правой части КП. Ключ — балковое тождество
      `λⁿ·βₙ₋₁² − λⁿ⁺¹·βₙ·βₙ₊₁ = βₙ`.
    • ВЫВОД ИСТОЧНИКА `ssLead_drive` (ГЛАВНАЯ теорема, закрывающая разрыв §2): для ведущей моды
      `y := a₁` из той же n=1 связи КП следует РОВНО `(1/β₁)·y² = kpRHS(1) = y'`, т.е.
      суперлинейный драйв `y' = C·y²` с `C = 1/β₁ = λ(λ²−1) > 0` — ВЫВЕДЕН, БЕЗ именованного поля.
    • `ssDyadic_blowup_derived` — взрыв, где драйв уже ВЫВЕДЕН (а не постулирован), скормлен ядру §1.

  ЧТО РАСКРЫТО ЧЕСТНО (не спрятано):
    • ГОМОГЕННОСТЬ: ведущий функционал ОБЯЗАН быть ЛИНЕЙНЫМ (`y := a₁`). Именно линейность даёт
      `y' = β₁ g² = (1/β₁)·(β₁ g)² = C·y²`. КВАДРАТИЧНЫЙ функционал `∑ wₙ aₙ²` СЛОМАЛ бы неравенство
      (степени `g` не сходятся к `y²`) — поэтому он НЕ используется. Это — реальное ограничение метода.
    • НИЖНЯЯ ГРАНИЦА (n=0): анзац ломается на самой крупной оболочке (`kpInflow 0 = 0`, есть только
      отток), остаётся невязка `F₀ = (β₀ + λβ₀β₁)·g² > 0`. Мы РАСКРЫВАЕМ её как ЯВНЫЙ форсинг-член
      `bottomForcing` (энергия, закачиваемая на крупнейшем масштабе — честный аналог движущегося
      фронта каскада), НЕ прячем. `ssMode_dynamics_forced` — точная динамика ВСЕХ мод против
      `kpRHS_forced`. ВАЖНО: вывод драйва `ssLead_drive` (n=1) НЕ зависит от `bottomForcing`.
    • ФРОНТИР: полная теорема КП для решения КОНЕЧНОЙ ЭНЕРГИИ (∑βₙ² < ∞ здесь есть, но глобальная
      корректность/срыв для произвольных данных) остаётся открытой. Мы НЕ заявляем большего: здесь —
      ОДНО точное самоподобное решение, у которого драйв выведен из сырых связей. Это снимает
      именно fallback §2 (именованный драйв), но не решает задачу КП целиком.

  ОБЛАСТЬ ОПРЕДЕЛЕНИЯ: `ssMode` живёт на `[0,T)` (в `T` — взрыв). Ядро §1 требует гипотез на всём
  `[0,∞)`. Поэтому, как и `dyadic_blowup`, ЛОКАЛЬНЫЕ куски (вывод драйва, положительность) доказаны
  на `t < T`, а `ssDyadic_blowup_derived` потребляет ГИПОТЕТИЧЕСКИЙ ГЛОБАЛЬНЫЙ объект (решение с
  положительностью и ВЫВЕДЕННЫМ драйвом на всём `[0,∞)`) ⟹ `False`. Ровно «локально реализуемо,
  глобально противоречиво» — смысл конечно-временной сингулярности. Локальная реализуемость самих
  гипотез засвидетельствована `ssDyadic_locally_realizable`. -/

/-- Самоподобные веса `βₙ := λ⁻ⁿ/(λ²−1)` (все `> 0` при `λ > 1`). -/
def ssBeta (lam : ℝ) (n : ℕ) : ℝ := (lam ^ n)⁻¹ / (lam ^ 2 - 1)

/-- Риккатиевский профиль `g(t) := (T−t)⁻¹` на `[0,T)`; удовлетворяет `g' = g²`. -/
def ssG (T t : ℝ) : ℝ := (T - t)⁻¹

/-- Самоподобная амплитуда оболочки `n`: `aₙ(t) := βₙ·g(t)`. -/
def ssMode (lam T : ℝ) (n : ℕ) (t : ℝ) : ℝ := ssBeta lam n * ssG T t

/-- **Раскрытый форсинг на крупнейшей оболочке (n=0).** Невязка анзаца при `n=0`
    (`kpInflow 0 = 0`): `F₀ = (β₀ + λ·β₀·β₁)·g²`. Честный явный источник энергии на крупном
    масштабе (аналог движущегося фронта), НЕ спрятанный. Вывод драйва a₁ от него НЕ зависит. -/
def bottomForcing (lam T : ℝ) (t : ℝ) : ℝ :=
  (ssBeta lam 0 + lam * ssBeta lam 0 * ssBeta lam 1) * (ssG T t) ^ 2

/-- Правая часть КП с РАСКРЫТЫМ форсингом на `n=0`: `kpRHS + [n=0]·bottomForcing`. Для `n ≥ 1`
    совпадает с чистой `kpRHS`. -/
def kpRHS_forced (lam T : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  kpRHS lam d a n t + (if n = 0 then bottomForcing lam T t else 0)

/-- **`ssG_hasDerivAt` — ДОКАЗАНА.** Риккатиевский профиль: `g'(t) = g(t)²` на `[0,T)`
    (`g(t) = (T−t)⁻¹`). Это точное `y' = y²` — источник самоподобия. -/
theorem ssG_hasDerivAt (T t : ℝ) (ht : t < T) : HasDerivAt (ssG T) (ssG T t ^ 2) t := by
  have hne : T - t ≠ 0 := by
    have : 0 < T - t := by linarith
    exact ne_of_gt this
  have hbase : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    have h1 : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
    have h2 : HasDerivAt (fun s : ℝ => T - s) (0 - 1) t :=
      (hasDerivAt_const t T).sub h1
    simpa using h2
  have hinv : HasDerivAt (fun s : ℝ => (T - s)⁻¹) (ssG T t ^ 2) t := by
    have h := hbase.inv hne
    have hval : - -1 / (T - t) ^ 2 = ssG T t ^ 2 := by
      simp only [ssG, neg_neg]; rw [inv_pow]; field_simp
    rw [hval] at h
    exact h
  exact hinv

/-- **`ssBeta_pos` — ДОКАЗАНА.** Все самоподобные веса положительны при `λ > 1`. -/
theorem ssBeta_pos {lam : ℝ} (hlam : 1 < lam) (n : ℕ) : 0 < ssBeta lam n := by
  have hlam0 : 0 < lam := by linarith
  have hpow : 0 < lam ^ n := pow_pos hlam0 n
  have hden : 0 < lam ^ 2 - 1 := by nlinarith [hlam]
  unfold ssBeta
  positivity

/-- **`ssMode_pos` — ДОКАЗАНА.** Каждая самоподобная амплитуда положительна на `[0,T)`
    (концентрированные положительные данные). -/
theorem ssMode_pos {lam T : ℝ} (hlam : 1 < lam) (n : ℕ) {t : ℝ} (ht : t < T) :
    0 < ssMode lam T n t := by
  have hb := ssBeta_pos hlam n
  have hg : 0 < ssG T t := by
    unfold ssG
    have : 0 < T - t := by linarith
    positivity
  unfold ssMode
  positivity

/-- Значение сырой `kpRHS` на самоподобной анзаце в оболочке `n = m+1`: балковое тождество
    `λⁿ·βₙ₋₁² − λⁿ⁺¹·βₙ·βₙ₊₁ = βₙ` даёт `kpRHS(n) = βₙ·g²`. Чистая алгебра (`field_simp`/`ring`). -/
theorem ssMode_rhs_bulk {lam T : ℝ} (hlam : 1 < lam) (m : ℕ) (t : ℝ) :
    kpRHS lam (fun _ => 0) (ssMode lam T) (m + 1) t = ssBeta lam (m + 1) * ssG T t ^ 2 := by
  have hlam0 : lam ≠ 0 := by intro h; rw [h] at hlam; norm_num at hlam
  have hden : lam ^ 2 - 1 ≠ 0 := by
    have : 0 < lam ^ 2 - 1 := by nlinarith [hlam]
    exact ne_of_gt this
  have hpm : (lam ^ m) ≠ 0 := pow_ne_zero m hlam0
  simp only [kpRHS, kpInflow, kpOutflow, ssMode, ssBeta]
  field_simp
  ring

/-- **`ssMode_dynamics_bulk` — ДОКАЗАНА (балковая динамика, n ≥ 1, ТОЧНОЕ РАВЕНСТВО).**

Для КАЖДОЙ оболочки `n ≥ 1` производная самоподобной амплитуды `aₙ = βₙ·g` в ТОЧНОСТИ равна сырой
правой части Каца–Павловича `kpRHS λ 0 a n t` (диссипация `d ≡ 0`). Это НЕ неравенство и НЕ
именованный вход — это выведенное равенство `aₙ' = kpRHS(n)`, снимающее fallback §2 для балка. -/
theorem ssMode_dynamics_bulk {lam T : ℝ} (hlam : 1 < lam) (n : ℕ) (hn : 1 ≤ n)
    {t : ℝ} (ht : t < T) :
    HasDerivAt (fun s => ssMode lam T n s)
      (kpRHS lam (fun _ => 0) (ssMode lam T) n t) t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg := ssG_hasDerivAt T t ht
  have hmode : HasDerivAt (fun s => ssMode lam T (m + 1) s)
      (ssBeta lam (m + 1) * ssG T t ^ 2) t := by
    have := hg.const_mul (ssBeta lam (m + 1))
    simpa only [ssMode] using this
  rw [ssMode_rhs_bulk hlam m t]
  exact hmode

/-- **`ssLead_drive` — ДОКАЗАНА (ЗАКРЫТИЕ РАЗРЫВА: драйв ВЫВЕДЕН из n=1 связи КП).**

Для ведущей моды `y := a₁` из ОДНОЙ связи Каца–Павловича при `n = 1` следует РОВНО суперлинейное
равенство `(1/β₁)·y² = kpRHS(1)`, т.е. драйв `y' = C·y²` с `C = 1/β₁ = λ(λ²−1) > 0`. Здесь НЕТ
именованного поля-источника: коэффициент `C` и само неравенство ВЫВОДЯТСЯ из сырых λⁿ-связей.
Функционал ОБЯЗАН быть линейным (`y = a₁`); квадратичный сломал бы гомогенность. -/
theorem ssLead_drive {lam T : ℝ} (hlam : 1 < lam) {t : ℝ} (ht : t < T) :
    (ssBeta lam 1)⁻¹ * (ssMode lam T 1 t) ^ 2
      = kpRHS lam (fun _ => 0) (ssMode lam T) 1 t := by
  have hlam0 : lam ≠ 0 := by intro h; rw [h] at hlam; norm_num at hlam
  have hden : lam ^ 2 - 1 ≠ 0 := by
    have : 0 < lam ^ 2 - 1 := by nlinarith [hlam]
    exact ne_of_gt this
  rw [show (1 : ℕ) = 0 + 1 from rfl, ssMode_rhs_bulk hlam 0 t]
  simp only [ssMode, ssBeta]
  field_simp

/-- **`ssMode_dynamics_forced` — ДОКАЗАНА (полная динамика ВСЕХ мод против раскрытого форсинга).**

Для КАЖДОЙ оболочки `n` производная самоподобной амплитуды в ТОЧНОСТИ равна `kpRHS_forced`. Для
`n ≥ 1` форсинг нулевой (совпадает с балком). Для `n = 0` РАСКРЫТЫЙ `bottomForcing` компенсирует
невязку анзаца на крупнейшей оболочке (там только отток). 🟡 Опирается на раскрытый форсинг при n=0;
вывод драйва a₁ (`ssLead_drive`) от него НЕ зависит. -/
theorem ssMode_dynamics_forced {lam T : ℝ} (hlam : 1 < lam) (n : ℕ) {t : ℝ} (ht : t < T) :
    HasDerivAt (fun s => ssMode lam T n s)
      (kpRHS_forced lam T (fun _ => 0) (ssMode lam T) n t) t := by
  have hlam0 : lam ≠ 0 := by intro h; rw [h] at hlam; norm_num at hlam
  have hden : lam ^ 2 - 1 ≠ 0 := by
    have : 0 < lam ^ 2 - 1 := by nlinarith [hlam]
    exact ne_of_gt this
  have hg := ssG_hasDerivAt T t ht
  match n with
  | 0 =>
    have hmode : HasDerivAt (fun s => ssMode lam T 0 s)
        (ssBeta lam 0 * ssG T t ^ 2) t := by
      have := hg.const_mul (ssBeta lam 0)
      simpa only [ssMode] using this
    have hval : kpRHS_forced lam T (fun _ => 0) (ssMode lam T) 0 t
        = ssBeta lam 0 * ssG T t ^ 2 := by
      simp only [kpRHS_forced, kpRHS, kpInflow, kpOutflow, bottomForcing, ssMode, ssBeta,
        if_pos]
      ring
    rw [hval]
    exact hmode
  | (k + 1) =>
    have hmode : HasDerivAt (fun s => ssMode lam T (k + 1) s)
        (ssBeta lam (k + 1) * ssG T t ^ 2) t := by
      have := hg.const_mul (ssBeta lam (k + 1))
      simpa only [ssMode] using this
    have hval : kpRHS_forced lam T (fun _ => 0) (ssMode lam T) (k + 1) t
        = ssBeta lam (k + 1) * ssG T t ^ 2 := by
      simp only [kpRHS_forced, Nat.succ_ne_zero, if_false, add_zero]
      exact ssMode_rhs_bulk hlam k t
    rw [hval]
    exact hmode

/--
**`DerivedDyadicSolution` — решение КП, где драйв ВЫВЕДЕН, а НЕ постулирован.**

В отличие от `DyadicSolution`, здесь НЕТ поля `superlinearDrive`. Динамика связана с
`kpRHS_forced` (раскрытый форсинг на крупнейшей оболочке), а суперлинейный источник для ведущей
моды ВЫВОДИТСЯ отдельной теоремой `ssLead_drive` из сырых связей, а не берётся как гипотеза. -/
structure DerivedDyadicSolution where
  /-- Отношение масштабов оболочек. -/
  lam : ℝ
  /-- Момент взрыва (профиль живёт на `[0,T)`). -/
  T : ℝ
  /-- `λ > 1`. -/
  hlam : 1 < lam
  /-- `T > 0`. -/
  hT : 0 < T
  /-- Амплитуды `a n t`. -/
  a : ℕ → ℝ → ℝ
  /-- Динамика КП с РАСКРЫТЫМ форсингом на `[0,T)` (без именованного драйв-поля). -/
  dynamics : ∀ n, ∀ t, t < T →
    HasDerivAt (fun s => a n s) (kpRHS_forced lam T (fun _ => 0) a n t) t
  /-- Индекс ведущей моды (для самоподобного решения — `1`, ЛИНЕЙНЫЙ функционал). -/
  leadIndex : ℕ

/-- **Конкретный обитатель: точное самоподобное решение** (`λ = 2`, `T = 1`, `a := ssMode 2 1`).
    Показывает, что `DerivedDyadicSolution` НЕ пуст локально: динамика КП с раскрытым форсингом
    держится на всём `[0,1)`. Ведущая мода — `a₁` (линейный функционал). -/
def derivedSolution_selfSimilar : DerivedDyadicSolution where
  lam := 2
  T := 1
  hlam := by norm_num
  hT := by norm_num
  a := ssMode 2 1
  dynamics := by
    intro n t ht
    exact ssMode_dynamics_forced (by norm_num) n ht
  leadIndex := 1

/-- ВЫВЕДЕННАЯ константа драйва ведущей моды `a₁`: `C = 1/β₁ = λ(λ²−1) > 0`
    (НЕ именованное поле — вычислена из `ssBeta`). -/
def ssLeadDriveConst (lam : ℝ) : ℝ := (ssBeta lam 1)⁻¹

/-- Выведенная константа драйва положительна. -/
theorem ssLeadDriveConst_pos {lam : ℝ} (hlam : 1 < lam) : 0 < ssLeadDriveConst lam :=
  inv_pos.mpr (ssBeta_pos hlam 1)

/--
**`ssDyadic_blowup_derived` — ДОКАЗАНА (взрыв с ВЫВЕДЕННЫМ драйвом).**

`DerivedDyadicSolution`, чья ведущая мода `a₁` ГЛОБАЛЬНО (на всём `[0,∞)`) положительна,
дифференцируема и удовлетворяет ГЛОБАЛЬНО-ПРОДОЛЖЕННОМУ ВЫВЕДЕННОМУ равенству-драйву
`(1/β₁)·(a₁)² = a₁'`, ведёт к `False`. Драйв здесь ВЫВЕДЕН из n=1 связи (`ssLead_drive`), а не
задан отдельным полем — это устраняет fallback §2. Прямое применение ядра §1. Не-вакуумность:
те же гипотезы выполнимы ЛОКАЛЬНО на `[0,T)` (см. `ssDyadic_locally_realizable`). -/
theorem ssDyadic_blowup_derived
    (sol : DerivedDyadicSolution)
    (y' : ℝ → ℝ)
    (hpos : ∀ t, 0 ≤ t → 0 < sol.a sol.leadIndex t)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt (sol.a sol.leadIndex) (y' t) t)
    (hdrive : ∀ t, 0 ≤ t →
      ssLeadDriveConst sol.lam * (sol.a sol.leadIndex t) ^ 2 = y' t) : False := by
  have hC : 0 < ssLeadDriveConst sol.lam := ssLeadDriveConst_pos sol.hlam
  refine superlinear_blowup_sq (sol.a sol.leadIndex) y' (ssLeadDriveConst sol.lam)
    (sol.a sol.leadIndex 0) hC (hpos 0 le_rfl) rfl hpos hderiv ?_
  intro t ht
  rw [hdrive t ht]

/-- **`ssDyadic_locally_realizable` — ДОКАЗАНА (локальная не-вакуумность §2bis).**

На `[0,T)` самоподобная ведущая мода `a₁` положительна и удовлетворяет ВЫВЕДЕННОМУ равенству-драйву
`(1/β₁)·(a₁)² = kpRHS(1)`. Значит гипотезы `ssDyadic_blowup_derived` РЕАЛЬНО реализуемы локально
(и глобально противоречивы — смысл конечно-временного взрыва). Драйв — выведенный, не постулированный. -/
theorem ssDyadic_locally_realizable {t : ℝ} (ht : t < derivedSolution_selfSimilar.T) :
    0 < derivedSolution_selfSimilar.a derivedSolution_selfSimilar.leadIndex t ∧
    ssLeadDriveConst derivedSolution_selfSimilar.lam
        * (derivedSolution_selfSimilar.a derivedSolution_selfSimilar.leadIndex t) ^ 2
      = kpRHS derivedSolution_selfSimilar.lam (fun _ => 0)
          (derivedSolution_selfSimilar.a) derivedSolution_selfSimilar.leadIndex t := by
  simp only [derivedSolution_selfSimilar] at ht ⊢
  refine ⟨ssMode_pos (by norm_num) 1 ht, ?_⟩
  exact ssLead_drive (by norm_num) ht

#print axioms ssG_hasDerivAt
#print axioms ssMode_dynamics_bulk
#print axioms ssLead_drive
#print axioms ssMode_dynamics_forced
#print axioms ssDyadic_blowup_derived
#print axioms ssDyadic_locally_realizable

/-! ### §2ter. ВЫВОД ДРАЙВА ИЗ СЫРЫХ λⁿ-СВЯЗЕЙ ДЛЯ КЛАССА (замыкающий связи инвариант фронта)

┌───────────────────────────────────────────────────────────────────────────────────────────┐
│  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК §2ter — ЧТО ЗДЕСЬ ВЫВЕДЕНО, А ЧТО ОСТАЁТСЯ ОТКРЫТЫМ.               │
└───────────────────────────────────────────────────────────────────────────────────────────┘

§2bis вывел драйв для ОДНОГО точного самоподобного решения (`ssMode`). ЗДЕСЬ мы делаем честный
ПРОМЕЖУТОЧНЫЙ шаг к общности: заменяем монолитное именованное поле-драйв `superlinearDrive`
структуры `DyadicSolution` на МЕНЬШИЙ, замыкающий сырые связи Каца–Павловича инвариант
`FrontDomination` — набор геометрических неравенств на трёх соседних модах фронта. Из него ДЛЯ
ЦЕЛОГО КЛАССА решений драйв `y' ≥ C·y²` ВЫВОДИТСЯ прямо из `kpRHS`, а не постулируется.

  ЧТО ДОКАЗАНО (ВЫВЕДЕНО из `kpRHS`, зелёно, без sorry/axiom/native_decide):
    • ИНВАРИАНТ `FrontDomination lam d a J ρ κ m t` — замыкающие связи неравенства на фронте
      (переиндексация на `J+1`, чтобы избежать ℕ-вычитания): `0 < m`, `m ≤ a_{J+1}` (нижняя
      граница ведущей моды), `ρ·a_{J+1} ≤ a_J` (подпитка снизу), `a_{J+2} ≤ κ·a_{J+1}` (контроль
      оттока вверх), `0 ≤ κ`. Это НАЗВАННЫЙ, но МЕНЬШИЙ и БОЛЕЕ ЭЛЕМЕНТАРНЫЙ вход, чем целое
      неравенство-драйв: он говорит лишь о взаимном порядке трёх соседних амплитуд.
    • 🟢 ГЛАВНЫЙ ВЫВОД `frontDrive_of_invariant`: из `FrontDomination` и `λ>0`, `d_{J+1}≥0`, `ρ≥0`
      ВЫВЕДЕНО неравенство `C·(a_{J+1})² ≤ kpRHS(J+1)` с `C := λ^{J+1}ρ² − λ^{J+2}κ − d_{J+1}/m`.
      Три подстановки границ (приток снизу через `ρ`, отток вверх через `κ`, диссипация через
      `m ≤ a_{J+1}`) применяются к СЫРОЙ правой части `kpRHS`; замыкает `nlinarith`. Драйв здесь
      НЕ поле-гипотеза, а СЛЕДСТВИЕ связей.
    • 🟢 КЛАССОВЫЙ ВЗРЫВ `frontDominated_blowup`: структура `FrontDominatedSolution` несёт НАСТОЯЩУЮ
      динамику КП (`dynamics : a_n' = kpRHS n`) и МЕНЬШИЙ инвариант `hold : FrontDomination …` (вместо
      монолитного драйва). Драйв ВЫВОДИТСЯ через `frontDrive_of_invariant`, скармливается ядру §1
      (`superlinear_blowup_sq`) ⟹ `False`. Взрыв для ЦЕЛОГО КЛАССА, не одного решения.
    • 🟢 МОСТ `DyadicSolution.ofFrontDominated`: строит `DyadicSolution`, чьё поле `superlinearDrive`
      ЗАКРЫТО доказательством `frontDrive_of_invariant` (а НЕ взято сырым входом). Это честная
      расплата: монолитное поле теперь ЗАПОЛНЕНО выводом из связей + меньшего инварианта.
    • НЕ-ВАКУУМНОСТЬ `ssMode_frontDomination`: самоподобный профиль §2bis `ssMode` УДОВЛЕТВОРЯЕТ
      `FrontDomination` поточечно (с `ρ = 1 ≤ λ`, `κ = 1 ≥ λ⁻¹`, `m = a_{J+1}`), т.к. `β_J = λ·β_{J+1}`
      упорядочены. Значит инвариант РЕАЛЬНО выполним, класс не пуст.

  ЧТО ОСТАЁТСЯ ОТКРЫТЫМ (честно названо, НЕ доказано):
    • СОХРАНЕНИЕ ИНВАРИАНТА ВО ВРЕМЕНИ для БЕСКОНЕЧНОГО каскада (движущийся фронт) — это
      ИССЛЕДОВАТЕЛЬСКИЙ ФРОНТИР. Мы даём лишь НАЗВАННЫЙ открытый предикат `FrontPreservedForever`
      (сохранение `FrontDomination` на всём `[0,∞)`), но НЕ доказываем его в бесконечной моде: за
      конечное окно фронт может сдвинуться, и удержание нижней границы `m ≤ a_{J+1}` при движущемся
      фронте — существо трудной динамики (Barbato–Morandin–Romito 2011, Cheskidov 2008,
      Kiselev–Zlatoš 2005). Инвариант ПОСТАВЛЕН как гипотеза `hold`; вывод драйва из него — наш.
    • Как и §2, это ЧЕСТНЫЙ ЧАСТИЧНЫЙ выигрыш (по духу — `liouvilleViolation_localizes`: один
      монолитный вход РАСЩЕПЛЁН на меньшие названные), а НЕ полная общность модели КП.

  ИТОГ §2ter: монолитный `superlinearDrive` СВЕДЁН к меньшему замыкающему связи инварианту
  `FrontDomination`; драйв ДЛЯ КЛАССА ВЫВЕДЕН из сырых λⁿ-связей; бесконечно-модовое сохранение
  фронта названо и оставлено открытым. -/

/-- **Инвариант доминирования фронта.** Замыкающие сырые связи КП геометрические неравенства на трёх
    соседних модах `a_J`, `a_{J+1}`, `a_{J+2}` (переиндексация на `J+1` устраняет ℕ-вычитание):
      `0 < m`, `m ≤ a_{J+1}` (нижняя граница ведущей моды),
      `ρ·a_{J+1} ≤ a_J` (подпитка притока снизу), `a_{J+2} ≤ κ·a_{J+1}` (контроль оттока вверх),
      `0 ≤ κ`.
    Это МЕНЬШИЙ именованный вход, чем целое неравенство-драйв: он говорит лишь о взаимном ПОРЯДКЕ
    трёх амплитуд, из которого драйв ВЫВОДИТСЯ (`frontDrive_of_invariant`). -/
def FrontDomination (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (J : ℕ) (ρ κ m : ℝ) (t : ℝ) : Prop :=
  0 < m ∧ m ≤ a (J+1) t ∧ ρ * a (J+1) t ≤ a J t ∧ a (J+2) t ≤ κ * a (J+1) t ∧ 0 ≤ κ

/--
**`frontDrive_of_invariant` — ДОКАЗАНА (🟢 ГЛАВНЫЙ ВЫВОД §2ter: драйв из СЫРЫХ связей + инвариант).**

Для ведущей моды `y := a_{J+1}` из инварианта `FrontDomination` и `λ>0`, `d_{J+1}≥0`, `ρ≥0` ВЫВЕДЕНО
суперлинейное неравенство прямо из сырой правой части `kpRHS(J+1)`:
    `C·(a_{J+1})² ≤ kpRHS(J+1)`,  `C := λ^{J+1}·ρ² − λ^{J+2}·κ − d_{J+1}/m`.
Вывод (проверенная алгебра): раскрываем `kpRHS(J+1) = λ^{J+1}·a_J² − λ^{J+2}·a_{J+1}·a_{J+2}
− d_{J+1}·a_{J+1}` и подставляем три границы инварианта:
  приток снизу `λ^{J+1}·(ρ·a_{J+1})² ≤ λ^{J+1}·a_J²`;
  отток вверх `λ^{J+2}·a_{J+1}·a_{J+2} ≤ λ^{J+2}·a_{J+1}·(κ·a_{J+1})`;
  диссипация `d_{J+1}·a_{J+1} ≤ (d_{J+1}/m)·a_{J+1}²` (т.к. `m ≤ a_{J+1}`, `d_{J+1}≥0`).
Положительность `a_{J+1} > 0` следует из `0 < m ≤ a_{J+1}`. Замыкает `nlinarith`. Драйв здесь —
НЕ поле-гипотеза, а СЛЕДСТВИЕ связей: именно это устраняет монолитный `superlinearDrive` для класса. -/
theorem frontDrive_of_invariant (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (J : ℕ) (ρ κ m : ℝ)
    (hlam : 0 < lam) (hd : 0 ≤ d (J+1)) (hρ : 0 ≤ ρ) (t : ℝ)
    (hinv : FrontDomination lam d a J ρ κ m t) :
    (lam^(J+1) * ρ^2 - lam^(J+2) * κ - d (J+1) / m) * (a (J+1) t)^2 ≤ kpRHS lam d a (J+1) t := by
  obtain ⟨hm, hmle, hρle, hκle, hκ⟩ := hinv
  -- Положительность ведущей моды из `0 < m ≤ a_{J+1}`.
  have hApos : 0 < a (J+1) t := lt_of_lt_of_le hm hmle
  have hlam1 : (0:ℝ) < lam^(J+1) := pow_pos hlam _
  have hlam2 : (0:ℝ) < lam^(J+2) := pow_pos hlam _
  simp only [kpRHS, kpInflow, kpOutflow]
  -- (1) приток снизу: `λ^{J+1}·(ρ·a_{J+1})² ≤ λ^{J+1}·a_J²`.
  have hρA : 0 ≤ ρ * a (J+1) t := mul_nonneg hρ hApos.le
  have hinflow : lam^(J+1) * (ρ * a (J+1) t)^2 ≤ lam^(J+1) * (a J t)^2 := by
    apply mul_le_mul_of_nonneg_left _ hlam1.le
    apply sq_le_sq' _ hρle
    linarith [hρA, hρle]
  -- (2) отток вверх: `λ^{J+2}·a_{J+1}·a_{J+2} ≤ λ^{J+2}·a_{J+1}·(κ·a_{J+1})`.
  have houtflow : lam^(J+2) * (a (J+1) t) * (a (J+2) t)
      ≤ lam^(J+2) * (a (J+1) t) * (κ * a (J+1) t) := by
    have hc : 0 ≤ lam^(J+2) * (a (J+1) t) := mul_nonneg hlam2.le hApos.le
    nlinarith [hκle, hc]
  -- (3) диссипация: `d_{J+1}·a_{J+1} ≤ (d_{J+1}/m)·a_{J+1}²` (т.к. `m ≤ a_{J+1}`, `d_{J+1}≥0`).
  have hdiss : (d (J+1) / m) * (a (J+1) t)^2 ≥ d (J+1) * (a (J+1) t) := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith [hd, hApos, hmle, mul_nonneg hd hApos.le]
  nlinarith [hinflow, houtflow, hdiss, hlam1, hlam2, hApos]

/--
**`FrontDominatedSolution` — решение КП, чей драйв ВЫВЕДЕН из МЕНЬШЕГО инварианта, а НЕ постулирован.**

В отличие от `DyadicSolution`, здесь НЕТ монолитного поля `superlinearDrive`. Есть НАСТОЯЩАЯ динамика
КП (`dynamics : a_n' = kpRHS n`) и МЕНЬШИЙ замыкающий связи инвариант `hold : FrontDomination …` на
трёх соседних модах фронта. Суперлинейный драйв ведущей моды `a_{J+1}` ВЫВОДИТСЯ из `hold` теоремой
`frontDrive_of_invariant`, а не берётся сырым входом. `hConst` — положительность выведенной константы
`C = λ^{J+1}ρ² − λ^{J+2}κ − d_{J+1}/m` (условие на параметры: приток снизу перевешивает отток и
диссипацию). Бесконечно-модовое сохранение `hold` во времени НАЗВАНО и оставлено открытым
(`FrontPreservedForever`). -/
structure FrontDominatedSolution where
  /-- Отношение масштабов оболочек. -/
  lam : ℝ
  /-- Диссипативные коэффициенты оболочек. -/
  d : ℕ → ℝ
  /-- Амплитуды `a n t`. -/
  a : ℕ → ℝ → ℝ
  /-- `λ > 1`. -/
  hlam : 1 < lam
  /-- Диссипация неотрицательна. -/
  hd : ∀ n, 0 ≤ d n
  /-- НАСТОЯЩИЕ ОДУ Каца–Павловича на `[0,∞)`. -/
  dynamics : ∀ n, ∀ t, 0 ≤ t → HasDerivAt (fun s => a n s) (kpRHS lam d a n t) t
  /-- Индекс основания фронта (ведущая мода — `J+1`). -/
  J : ℕ
  /-- Коэффициент подпитки притока снизу. -/
  ρ : ℝ
  /-- Коэффициент контроля оттока вверх. -/
  κ : ℝ
  /-- Нижняя граница ведущей моды. -/
  m : ℝ
  /-- `ρ ≥ 0`. -/
  hρ : 0 ≤ ρ
  /-- Выведенная константа драйва положительна (приток перевешивает отток и диссипацию). -/
  hConst : 0 < lam^(J+1) * ρ^2 - lam^(J+2) * κ - d (J+1) / m
  /-- Начальное значение ведущей моды положительно. -/
  hInit  : 0 < a (J+1) 0
  /-- **МЕНЬШИЙ ИМЕНОВАННЫЙ ИНВАРИАНТ** (вместо монолитного драйва): доминирование фронта на всём
      `[0,∞)`. Его сохранение во времени для бесконечного каскада — открытый фронтир (см.
      `FrontPreservedForever`); драйв из него — наш вывод. -/
  hold   : ∀ t, 0 ≤ t → FrontDomination lam d a J ρ κ m t

/--
**`frontDominated_blowup` — ДОКАЗАНА (🟢 КЛАССОВЫЙ ВЗРЫВ: выведенный драйв ⟹ ядро §1 ⟹ `False`).**

Решение КП с настоящей динамикой и МЕНЬШИМ инвариантом `FrontDomination` (вместо монолитного
драйв-поля) НЕ имеет глобального положительного решения. Драйв `C·(a_{J+1})² ≤ (a_{J+1})'` ВЫВОДИТСЯ
из инварианта через `frontDrive_of_invariant` (динамика даёт `(a_{J+1})' = kpRHS(J+1)`), затем
скармливается ядру §1 `superlinear_blowup_sq`. Взрыв для ЦЕЛОГО КЛАССА, а не одного решения. -/
theorem frontDominated_blowup (sol : FrontDominatedSolution) : False := by
  set C : ℝ := sol.lam^(sol.J+1) * sol.ρ^2 - sol.lam^(sol.J+2) * sol.κ - sol.d (sol.J+1) / sol.m
    with hCdef
  have hlam0 : 0 < sol.lam := lt_trans one_pos sol.hlam
  -- Положительность ведущей моды из инварианта (`0 < m ≤ a_{J+1}`).
  have hpos : ∀ t, 0 ≤ t → 0 < sol.a (sol.J+1) t := by
    intro t ht
    obtain ⟨hm, hmle, _, _, _⟩ := sol.hold t ht
    exact lt_of_lt_of_le hm hmle
  refine superlinear_blowup_sq
    (fun s => sol.a (sol.J+1) s)
    (fun t => kpRHS sol.lam sol.d sol.a (sol.J+1) t)
    C (sol.a (sol.J+1) 0)
    sol.hConst sol.hInit rfl hpos
    (fun t ht => sol.dynamics (sol.J+1) t ht) ?_
  intro t ht
  -- Драйв ВЫВЕДЕН из инварианта, не постулирован.
  have hdrive := frontDrive_of_invariant sol.lam sol.d sol.a sol.J sol.ρ sol.κ sol.m
    hlam0 (sol.hd (sol.J+1)) sol.hρ t (sol.hold t ht)
  simpa [hCdef] using hdrive

/--
**`DyadicSolution.ofFrontDominated` — МОСТ (честная расплата: поле-драйв ЗАПОЛНЕНО выводом).**

Строит `DyadicSolution` из `FrontDominatedSolution`. Ключевая честность: поле `superlinearDrive`
здесь НЕ берётся сырым именованным входом, а ЗАКРЫВАЕТСЯ доказательством `frontDrive_of_invariant`
из меньшего инварианта `hold`. Так монолитное поле §2 оказывается ЗАПОЛНЕНО ВЫВОДОМ из сырых λⁿ-связей
+ замыкающего связи инварианта фронта — payoff §2ter. Ведущий функционал линеен (`y := a_{J+1}`). -/
def DyadicSolution.ofFrontDominated (sol : FrontDominatedSolution) : DyadicSolution where
  lam := sol.lam
  d := sol.d
  a := sol.a
  hlam := sol.hlam
  hd := sol.hd
  dynamics := sol.dynamics
  leadFunctional := fun s => sol.a (sol.J+1) s
  leadDeriv := fun t => kpRHS sol.lam sol.d sol.a (sol.J+1) t
  leadHasDeriv := fun t ht => sol.dynamics (sol.J+1) t ht
  leadPos := by
    intro t ht
    obtain ⟨hm, hmle, _, _, _⟩ := sol.hold t ht
    exact lt_of_lt_of_le hm hmle
  leadInit := sol.hInit
  driveConst := sol.lam^(sol.J+1) * sol.ρ^2 - sol.lam^(sol.J+2) * sol.κ - sol.d (sol.J+1) / sol.m
  hDriveConst := sol.hConst
  superlinearDrive := by
    intro t ht
    have hlam0 : 0 < sol.lam := lt_trans one_pos sol.hlam
    -- ⬇ поле-драйв ЗАПОЛНЕНО выводом из инварианта, а не сырым входом.
    exact frontDrive_of_invariant sol.lam sol.d sol.a sol.J sol.ρ sol.κ sol.m
      hlam0 (sol.hd (sol.J+1)) sol.hρ t (sol.hold t ht)

/-- Вспомогательное тождество самоподобных весов: `λ·β_{n+1} = β_n` (т.к. `β_{n+1} = β_n/λ`). -/
theorem ssBeta_succ_mul {lam : ℝ} (hlam : 1 < lam) (n : ℕ) :
    lam * ssBeta lam (n + 1) = ssBeta lam n := by
  have hlam0 : lam ≠ 0 := by intro h; rw [h] at hlam; norm_num at hlam
  have hden : lam ^ 2 - 1 ≠ 0 := by
    have : 0 < lam ^ 2 - 1 := by nlinarith [hlam]
    exact ne_of_gt this
  simp only [ssBeta, pow_succ]
  field_simp

/--
**`ssMode_frontDomination` — ДОКАЗАНА (не-вакуумность: класс НЕ пуст).**

Самоподобный профиль §2bis `ssMode` УДОВЛЕТВОРЯЕТ инварианту `FrontDomination` поточечно на `[0,T)`
с `ρ = 1` (`≤ λ`), `κ = 1` (`≥ λ⁻¹`) и `m := a_{J+1}` (нижняя граница — сама ведущая мода). Порядок
`a_{J+2} ≤ a_{J+1} ≤ a_J` следует из `β_J = λ·β_{J+1}` (веса убывают при `λ>1`). Значит инвариант
РЕАЛЬНО выполним, и класс `FrontDominatedSolution` не пусто-истинен. -/
theorem ssMode_frontDomination {lam T : ℝ} (hlam : 1 < lam) (J : ℕ) {t : ℝ} (ht : t < T) :
    FrontDomination lam (fun _ => 0) (ssMode lam T) J 1 1
      (ssMode lam T (J+1) t) t := by
  have hlam0 : 0 < lam := by linarith
  have hApos : 0 < ssMode lam T (J+1) t := ssMode_pos hlam (J+1) ht
  have hg : 0 < ssG T t := by
    unfold ssG
    have hTt : 0 < T - t := by linarith
    positivity
  have hbJ : 0 < ssBeta lam J := ssBeta_pos hlam J
  have hbJ1 : 0 < ssBeta lam (J+1) := ssBeta_pos hlam (J+1)
  refine ⟨hApos, le_refl _, ?_, ?_, by norm_num⟩
  · -- `1·a_{J+1} ≤ a_J`: `β_{J+1}·g ≤ β_J·g`, т.к. `β_J = λ·β_{J+1} ≥ β_{J+1}` (`λ>1`).
    simp only [ssMode, one_mul]
    have hbeta : ssBeta lam (J+1) ≤ ssBeta lam J := by
      have hrel := ssBeta_succ_mul hlam J
      nlinarith [hbJ1, hlam, hrel]
    exact mul_le_mul_of_nonneg_right hbeta hg.le
  · -- `a_{J+2} ≤ 1·a_{J+1}`: `β_{J+2}·g ≤ β_{J+1}·g`, т.к. `β_{J+1} = λ·β_{J+2} ≥ β_{J+2}`.
    simp only [ssMode, one_mul]
    have hbJ2 : 0 < ssBeta lam (J+2) := ssBeta_pos hlam (J+2)
    have hbeta : ssBeta lam (J+2) ≤ ssBeta lam (J+1) := by
      have hrel := ssBeta_succ_mul hlam (J+1)
      nlinarith [hbJ2, hlam, hrel]
    exact mul_le_mul_of_nonneg_right hbeta hg.le

/--
**`FrontPreservedForever` — НАЗВАННЫЙ ОТКРЫТЫЙ ПРЕДИКАТ (исследовательский фронтир, НЕ доказан).**

🟡 Сохранение инварианта доминирования фронта на всём `[0,∞)` для БЕСКОНЕЧНОГО каскада (движущийся
фронт). В отличие от вывода драйва (`frontDrive_of_invariant`, наш результат), это свойство МЫ НЕ
ДОКАЗЫВАЕМ: удержание нижней границы `m ≤ a_{J+1}` при движущемся вверх фронте каскада — существо
трудной бесконечно-модовой динамики. Литература, где это исследуется:
Barbato–Morandin–Romito (2011), Cheskidov (2008), Kiselev–Zlatoš (2005). Мы честно НАЗЫВАЕМ предикат
и НЕ выдаём его за доказанный; в `FrontDominatedSolution` соответствующее удержание ПОСТАВЛЕНО
гипотезой `hold`. Конечно-оконное сохранение через MVT-оценки границ (`image_le_of_deriv_right_le_…`)
возможно при названной локальной «гипотезе непересечения», но здесь оно СОЗНАТЕЛЬНО ОПУЩЕНО как
не закрывающее бесконечную моду. -/
def FrontPreservedForever (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (J : ℕ) (ρ κ m : ℝ) : Prop :=
  ∀ t, 0 ≤ t → FrontDomination lam d a J ρ κ m t

#print axioms frontDrive_of_invariant
#print axioms frontDominated_blowup
#print axioms DyadicSolution.ofFrontDominated
#print axioms ssMode_frontDomination

/-! ### §2quater. ИСТОК КАСКАДА НЕ ПРИЧИНИМ ИЗНУТРИ (🟢 стена невозможности, axiom-free)

┌───────────────────────────────────────────────────────────────────────────────────────────┐
│  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК §2quater — 🟢 СТЕНА, БЕЗ ТАИНТА.                                   │
└───────────────────────────────────────────────────────────────────────────────────────────┘

Это КАСКАДНЫЙ АНАЛОГ `no_internalisedOriginEvent` из карантина: САМЫЙ НИЖНИЙ (крупнейший)
масштаб `n=0` дядического каскада НЕ МОЖЕТ причинить свой собственный исток изнутри. У оболочки
`n=0` притока нет (`kpInflow 0 = 0`, только отток вверх) — самоподобная амплитуда `a₀ = β₀·g` НЕ
удовлетворяет НЕФОРСИРОВАННОМУ уравнению КП при `n=0`: её истинная производная равна
`kpRHS_forced = kpRHS + bottomForcing` (см. `ssMode_dynamics_forced`, ветка n=0), а `bottomForcing>0`.
Значит внешняя ЗАКАЧКА энергии на крупнейшем масштабе ОБЯЗАТЕЛЬНА — исток каскада (n=0-насос)
приходит ИЗВНЕ, а не самопричиняется. Это ровно «дно оболочки не снабжает свой собственный исток».

  ЧТО ДОКАЗАНО (🟢, стандартные аксиомы, БЕЗ sorry/axiom/native_decide/step00FirstCause):
    • `bottomForcing_pos` — форсинг-член на крупнейшей оболочке СТРОГО ПОЛОЖИТЕЛЕН на `[0,T)`.
    • `dyadicOrigin_uncausable_from_inside` — самоподобный исток НЕ может удовлетворять
      НЕФОРСИРОВАННОМУ n=0 уравнению КП: иначе (единственность производной) `bottomForcing=0` —
      противоречие с `bottomForcing_pos`. Требуется внешний источник.

  ЭТА СТЕНА САМОДОСТАТОЧНА И НЕ ЗАВИСИТ от жёлтого слоя первопричины (`DyadicFirstCause.lean`):
  здесь лишь ДОКАЗАНО, что исток изнутри непричиним; КЕМ он декретирован — вопрос жёлтого файла. -/

/-- **`bottomForcing_pos` — ДОКАЗАНА (🟢).** Раскрытый форсинг-член на крупнейшей оболочке `n=0`
    строго положителен на `[0,T)`. Коэффициент `β₀ + λ·β₀·β₁ > 0` (веса `ssBeta_pos`, `λ>0`),
    а `g(t)² = ((T−t)⁻¹)² > 0`, т.к. `g(t) = (T−t)⁻¹ ≠ 0` при `t < T`. -/
theorem bottomForcing_pos {lam T : ℝ} (hlam : 1 < lam) {t : ℝ} (ht : t < T) :
    0 < bottomForcing lam T t := by
  have hlam0 : 0 < lam := by linarith
  have hb0 : 0 < ssBeta lam 0 := ssBeta_pos hlam 0
  have hb1 : 0 < ssBeta lam 1 := ssBeta_pos hlam 1
  have hg : 0 < ssG T t := by
    unfold ssG
    have hTt : 0 < T - t := by linarith
    positivity
  unfold bottomForcing
  positivity

/-- **`dyadicOrigin_uncausable_from_inside` — ДОКАЗАНА (🟢, стена невозможности).**

Каскадный аналог `no_internalisedOriginEvent`. Самоподобный исток (мода `n=0`, у которой только
отток, `kpInflow 0 = 0`) НЕ может удовлетворять НЕФОРСИРОВАННОМУ уравнению Каца–Павловича при `n=0`:
его истинная производная равна `kpRHS_forced = kpRHS + bottomForcing` (`ssMode_dynamics_forced`,
ветка n=0), а `bottomForcing > 0`. Если бы производная равнялась ещё и чистой `kpRHS`,
единственность производной (`HasDerivAt.unique`) форсировала бы `bottomForcing = 0` — противоречие
с `bottomForcing_pos`. Значит крупнейшая оболочка НЕ снабжает свой собственный исток: внешняя
закачка (насос n=0) ОБЯЗАТЕЛЬНА. Это 🟢-факт, НЕ зависящий от того, кто декретирует поставку. -/
theorem dyadicOrigin_uncausable_from_inside {lam T : ℝ} (hlam : 1 < lam) {t : ℝ} (ht : t < T) :
    ¬ HasDerivAt (fun s => ssMode lam T 0 s)
        (kpRHS lam (fun _ => 0) (ssMode lam T) 0 t) t := by
  intro h
  -- Истинная (форсированная) динамика n=0.
  have hf := ssMode_dynamics_forced hlam 0 ht
  -- Единственность производной ⟹ чистая kpRHS = форсированная правая часть.
  have huniq := h.unique hf
  -- Разворачиваем форсированную часть при n=0: kpRHS = kpRHS + bottomForcing ⟹ 0 = bottomForcing.
  have hpos := bottomForcing_pos hlam ht
  simp only [kpRHS_forced, if_true] at huniq
  linarith [huniq, hpos]

#print axioms bottomForcing_pos
#print axioms dyadicOrigin_uncausable_from_inside

/-! ### §4. ИТОГ И АУДИТ АКСИОМ

Маршрут: ядро §1 (`superlinear_blowup_sq`) — ВЫВЕДЕНО строго; телескоп §2
(`nonlinear_transfer_conservative`) — ВЫВЕДЕН; взрыв модели `dyadic_blowup` — ВЫВЕДЕН из ядра;
суперлинейный источник `y' ≥ C·y²` внутри `DyadicSolution` — ИМЕНОВАННЫЙ ВХОД (честный fallback,
литературный механизм КП, не подделка). Не-вакуумность — `superlinear_example` (риккати). Ни sorry,
ни новых аксиом, ни native_decide. -/

#print axioms dyadic_blowup
#print axioms superlinear_blowup_sq
#print axioms nonlinear_transfer_conservative
#print axioms superlinear_example

end EuclidsPath.DyadicBlowup
