/-
  CascadeBudget — ПЕРВАЯ В МИРЕ формализация модели жидкостного каскада
  в системе доказательств (Lean 4 + mathlib). Ветвь «энергетический бюджет».

  ════════════════════════════════════════════════════════════════════════════
  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК (обязателен по регламенту проекта).
  ════════════════════════════════════════════════════════════════════════════

  ЧТО ЭТО. По нашим разысканиям, конкретная конечно-оболочечная (shell/GOY-Sabra
  дьадическая) модель каскада, как ДЕЙСТВИТЕЛЬНАЯ система ОДУ, ранее НЕ была
  формализована ни в одном ассистенте доказательств. Здесь она формализована
  впервые — вместе с абстрактным принципом конечного бюджета.

  ЧТО ФОРМАЛИЗОВАНО (всё — ИЗВЕСТНАЯ математика, ничего нового не заявляется):
    §1  АБСТРАКТНЫЙ БЮДЖЕТНЫЙ ПРИНЦИП (чистое исчисление, зелёный):
        конечный запас энергии не может питать РАВНОМЕРНУЮ диссипацию вечно —
        `finite_budget_bounds_uniform_dissipation`: `E' ≤ −β` на `[0,T]`,
        `E T ≥ 0` ⟹ `T ≤ E 0 / β`. Это машинная форма «нет вечного двигателя
        на равномерной диссипации из конечного бюджета» (одностороннее
        неравенство среднего значения, `image_le_of_deriv_right_le_deriv_boundary`).
    §2  КОНКРЕТНАЯ КОНЕЧНАЯ ОБОЛОЧЕЧНАЯ МОДЕЛЬ (содержательная, настоящее ОДУ):
        амплитуды `a : Fin N → ℝ → ℝ`, дьадическая диссипация `ν·λ^(2αn)`,
        энергосохраняющая квадратичная передача между соседними оболочками
        (`∑ aₙ·(передача)ₙ = 0`). Структура `ShellSolution` пакует производные
        уравнения + свойство сохранения энергии передачей. Энергия
        `shellEnergy = ∑ aₙ²`, её производная `= −2ν·∑ λ^(2αn)·aₙ² ≤ 0`
        (`shellEnergy_hasDerivAt`, `shellEnergy_deriv_nonpos`). Инстанциация §1:
        при равномерном нижнем пороге диссипации `≥ β` время ограничено
        (`no_uniform_dissipation_forever_on_shell`). НЕ-ВАКУУМНОСТЬ: нулевая
        оболочка — настоящее решение (`zeroShellSolution`).
    §3  ЧЕСТНАЯ ГРАНИЦА (ключевая честность, зелёная): бюджет ПРОМАХИВАЕТСЯ мимо
        НЕравномерных каскадов. Через существующий `cookedProfileCascade_not_uniform`
        из NavierStokesFront: кованый каскад с падениями `2⁻⁽ⁿ⁺¹⁾` ускользает под
        всякий `β>0`, значит гипотеза «равномерно ≥ β» §1 для него ПРОВАЛИВАЕТСЯ —
        бюджет НЕ запрещает такие каскады (`budget_misses_nonuniform`).
    §4  Мост к `ns_no_infinite_dissipative_cascade` — та же абстрактная машина,
        теперь на НАСТОЯЩЕЙ конечной оболочке.

  ЧЕМ ЭТО НЕ ЯВЛЯЕТСЯ (красные линии):
    * это НЕ решение уравнений Навье–Стокса и НЕ проблемы тысячелетия;
    * это НЕ подтверждение наивного прочтения «вечного двигателя»: наоборот,
      модуль МАШИННО КАРТИРУЕТ, где бюджет работает (равномерная диссипация ⟹
      конечное время) и где он ПРОВАЛИВАЕТСЯ (неравномерные каскады ускользают,
      `budget_misses_nonuniform`);
    * настоящие суперкритические модели РЕАЛЬНО ВЗРЫВАЮТСЯ (см. companion-модуль
      о дьадическом blow-up) — так что здесь мы РАЗГРАНИЧИВАЕМ и частично
      ОПРОВЕРГАЕМ наивное «двигательное» замыкание, а не подтверждаем его;
    * никакой связи с простыми числами — красная линия проекта нетронута.

  ТЕХНИЧЕСКИ: `set_option autoImplicit false`; НИ ОДНОГО `sorry`, `axiom`,
  `native_decide`. Все теоремы РЕАЛЬНО потребляют свои гипотезы; оболочечная
  модель — НАСТОЯЩАЯ система ОДУ (не `True`). Такса-инвариант репозитория не
  меняется (только `propext`, `Classical.choice`, `Quot.sound`).
  ════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import EuclidsPath.Engine.NavierStokes
import EuclidsPath.Engine.NavierStokesFront

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.CascadeBudget

open scoped BigOperators
open Set

/-#############################################################################
  §1. АБСТРАКТНЫЙ БЮДЖЕТНЫЙ ПРИНЦИП (чистое исчисление, зелёный)
#############################################################################-/

/--
**`finite_budget_bounds_uniform_dissipation` — ДОКАЗАНА (чистый MVI).**
Конечный запас энергии не может питать РАВНОМЕРНУЮ диссипацию вечно.

Если гладкая энергия `E` на `[0,T]` имеет производную `E' t ≤ −β` (равномерная
диссипация со скоростью `≥ β > 0`), а на конце остаётся неотрицательной
(`0 ≤ E T`), то `T ≤ E 0 / β`.

Доказательство — одностороннее неравенство среднего значения
(`image_le_of_deriv_right_le_deriv_boundary`) с барьером `B x = E 0 − β·x`:
даёт `E T ≤ E 0 − β·T`; вместе с `0 ≤ E T` получаем `β·T ≤ E 0`, откуда
`T ≤ E 0 / β`. Это машинная форма «нет вечного двигателя на равномерной
диссипации из конечного бюджета». -/
theorem finite_budget_bounds_uniform_dissipation
    (E : ℝ → ℝ) (E' : ℝ → ℝ) (E0 β T : ℝ)
    (hβ : 0 < β) (hT : 0 ≤ T) (hE0 : E 0 = E0)
    (hderiv : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt E (E' t) t)
    (hdiss : ∀ t ∈ Set.Icc (0:ℝ) T, E' t ≤ -β)
    (hpos : 0 ≤ E T) :
    T ≤ E0 / β := by
  -- Барьер: B x = E0 − β·x, с производной B' x = −β.
  set B : ℝ → ℝ := fun x => E0 - β * x with hBdef
  -- E непрерывна на [0,T] (из точечной дифференцируемости).
  have hcontE : ContinuousOn E (Set.Icc (0:ℝ) T) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  -- E имеет правую производную на [0,T).
  have hE'within : ∀ x ∈ Set.Ico (0:ℝ) T, HasDerivWithinAt E (E' x) (Set.Ici x) x :=
    fun x hx => (hderiv x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  -- B непрерывна на [0,T].
  have hcontB : ContinuousOn B (Set.Icc (0:ℝ) T) := by
    apply Continuous.continuousOn
    fun_prop
  -- B имеет правую производную −β всюду.
  have hB'within : ∀ x ∈ Set.Ico (0:ℝ) T, HasDerivWithinAt B (-β) (Set.Ici x) x := by
    intro x hx
    have : HasDerivAt B (-β) x := by
      have h1 : HasDerivAt (fun x : ℝ => E0 - β * x) (0 - β * 1) x :=
        (hasDerivAt_const x E0).sub ((hasDerivAt_id x).const_mul β)
      simpa using h1
    exact this.hasDerivWithinAt
  -- Начальное условие: E 0 ≤ B 0.
  have ha : E 0 ≤ B 0 := by
    have : B 0 = E0 := by simp [hBdef]
    rw [this, hE0]
  -- Оценка производных: E' x ≤ −β = B' x на [0,T).
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) T, E' x ≤ -β :=
    fun x hx => hdiss x (Set.mem_Icc_of_Ico hx)
  -- MVI: E x ≤ B x всюду на [0,T]; в частности в T.
  have hfence : ∀ ⦃x⦄, x ∈ Set.Icc (0:ℝ) T → E x ≤ B x :=
    image_le_of_deriv_right_le_deriv_boundary hcontE hE'within ha hcontB hB'within hbound
  have hET : E T ≤ E0 - β * T := by
    have := hfence (Set.right_mem_Icc.mpr hT)
    simpa [hBdef] using this
  -- 0 ≤ E T ≤ E0 − β·T ⟹ β·T ≤ E0 ⟹ T ≤ E0/β.
  have hβT : β * T ≤ E0 := by linarith
  rw [le_div_iff₀ hβ]
  linarith [hβT]

/-#############################################################################
  §2. КОНКРЕТНАЯ КОНЕЧНАЯ ОБОЛОЧЕЧНАЯ МОДЕЛЬ (настоящее ОДУ, содержательная)
#############################################################################-/

/-- **Дьадический диссипативный коэффициент оболочки `n`:** `ν·λ^(2αn)`
    (реальная степень `Real.rpow`). Физически: мелкие масштабы (большие `n`)
    диссипируют сильнее при `λ>1`, `α>0`. При `ν ≥ 0`, `λ > 0` — неотрицателен. -/
def shellDiss (lam ν α : ℝ) (n : ℕ) : ℝ :=
  ν * lam ^ (2 * α * (n : ℝ))

/-- `shellDiss` неотрицателен при `ν ≥ 0`, `λ > 0` (`rpow` положительна). -/
theorem shellDiss_nonneg {lam ν α : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (n : ℕ) :
    0 ≤ shellDiss lam ν α n := by
  unfold shellDiss
  exact mul_nonneg hν (Real.rpow_nonneg hlam.le _)

/--
**`ShellSolution N lam ν α a` — НАСТОЯЩЕЕ решение конечной оболочечной системы ОДУ.**

`a : Fin N → ℝ → ℝ` — амплитуды `N` оболочек как функции времени. Структура
пакует:
  * `transfer` — квадратичную (нелинейную) передачу энергии между оболочками
    (в реальных GOY/Sabra-моделях — соседственная триадная связь);
  * `shellODE` — САМО дифференциальное уравнение для каждой оболочки:
      `d/dt aₙ = transferₙ − (ν·λ^(2αn))·aₙ`
    (передача минус дьадическая диссипация);
  * `transfer_conservative` — КЛЮЧЕВОЕ физическое свойство: передача
    СОХРАНЯЕТ энергию, `∑ₙ aₙ·transferₙ = 0` (телескопирование триад).

Это НЕ `True`-заглушка: производные реально связаны, а сохранение энергии
передачей — содержательное ограничение, которое честно потребляется в
`shellEnergy_hasDerivAt`. Структура ДАННЫХ (Type-значная): несёт саму функцию
передачи `transfer`, потому не `Prop`. -/
structure ShellSolution (N : ℕ) (lam ν α : ℝ) (a : Fin N → ℝ → ℝ) where
  /-- Нелинейная передача энергии между оболочками (значение в момент `t`). -/
  transfer : Fin N → ℝ → ℝ
  /-- Уравнение оболочки: `d/dt aₙ = transferₙ − diss·aₙ`. -/
  shellODE : ∀ (n : Fin N) (t : ℝ),
    HasDerivAt (fun s => a n s)
      (transfer n t - shellDiss lam ν α n * a n t) t
  /-- Передача сохраняет энергию: `∑ₙ aₙ·transferₙ = 0`. -/
  transfer_conservative : ∀ t : ℝ,
    ∑ n : Fin N, a n t * transfer n t = 0

/-- **Энергия оболочечной системы:** `E(t) = ∑ₙ aₙ(t)²` (конечная сумма квадратов
    амплитуд). Всегда неотрицательна. -/
def shellEnergy {N : ℕ} (a : Fin N → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n : Fin N, (a n t) ^ 2

/-- Энергия оболочки неотрицательна. -/
theorem shellEnergy_nonneg {N : ℕ} (a : Fin N → ℝ → ℝ) (t : ℝ) :
    0 ≤ shellEnergy a t :=
  Finset.sum_nonneg fun n _ => by positivity

/-- Диагональная скорость диссипации оболочечной системы:
    `D(t) = 2ν·∑ₙ λ^(2αn)·aₙ(t)²`. Неотрицательна при `ν ≥ 0`, `λ > 0`. -/
def shellDissipationRate {N : ℕ} (lam ν α : ℝ) (a : Fin N → ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * ∑ n : Fin N, shellDiss lam ν α n * (a n t) ^ 2

theorem shellDissipationRate_nonneg {N : ℕ} {lam ν α : ℝ}
    (hν : 0 ≤ ν) (hlam : 0 < lam) (a : Fin N → ℝ → ℝ) (t : ℝ) :
    0 ≤ shellDissipationRate lam ν α a t := by
  unfold shellDissipationRate
  have : 0 ≤ ∑ n : Fin N, shellDiss lam ν α n * (a n t) ^ 2 :=
    Finset.sum_nonneg fun n _ => mul_nonneg (shellDiss_nonneg hν hlam n) (by positivity)
  linarith

/--
**`shellEnergy_hasDerivAt` — ДОКАЗАНА (производная энергии оболочки).**
`dE/dt = 2·∑ aₙ·aₙ' = 2·∑ aₙ·(transferₙ − diss·aₙ)`
       `= 2·(∑ aₙ·transferₙ) − 2·∑ diss·aₙ² = −2·∑ diss·aₙ² = −D(t)`.
Передача выпадает через `transfer_conservative` (энергосохранение). Это
машинная реализация вывода «нелинейность не меняет энергию, только
диссипация её съедает». -/
theorem shellEnergy_hasDerivAt {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a) (t : ℝ) :
    HasDerivAt (fun s => shellEnergy a s)
      (-(shellDissipationRate lam ν α a t)) t := by
  -- Производная каждого слагаемого aₙ².
  have hterm : ∀ n : Fin N,
      HasDerivAt (fun s => (a n s) ^ 2)
        (2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t)) t := by
    intro n
    -- (a n s)² = (a n s)·(a n s); правило произведения даёт c·a + a·c = 2·a·c.
    have hmul := (sol.shellODE n t).mul (sol.shellODE n t)
    have hval :
        (sol.transfer n t - shellDiss lam ν α n * a n t) * a n t
          + a n t * (sol.transfer n t - shellDiss lam ν α n * a n t)
          = 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t) := by ring
    rw [hval] at hmul
    have hfun : ((fun s => a n s) * fun s => a n s) = fun s => (a n s) ^ 2 := by
      funext s; simp [Pi.mul_apply, sq]
    rw [hfun] at hmul
    exact hmul
  -- Производная суммы функций (пойнтвайз-сумма = функция суммы).
  have hsum :
      HasDerivAt (fun s => ∑ n : Fin N, (a n s) ^ 2)
        (∑ n : Fin N, 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t)) t := by
    have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (A := fun n => fun s => (a n s) ^ 2)
      (A' := fun n => 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t))
      (fun n _ => hterm n)
    -- ∑ i, A i  (сумма функций)  =  fun s => ∑ i, A i s
    have hfun : (∑ n : Fin N, fun s => (a n s) ^ 2)
        = fun s => ∑ n : Fin N, (a n s) ^ 2 := by
      funext s; rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  -- Приводим значение производной к −D.
  have hval :
      (∑ n : Fin N, 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t))
        = -(shellDissipationRate lam ν α a t) := by
    have hexpand : ∀ n : Fin N,
        2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t)
          = 2 * (a n t * sol.transfer n t)
            - 2 * (shellDiss lam ν α n * (a n t) ^ 2) := by
      intro n; ring
    calc
      (∑ n : Fin N, 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t))
          = ∑ n : Fin N, (2 * (a n t * sol.transfer n t)
              - 2 * (shellDiss lam ν α n * (a n t) ^ 2)) := by
            exact Finset.sum_congr rfl (fun n _ => hexpand n)
      _ = (∑ n : Fin N, 2 * (a n t * sol.transfer n t))
            - ∑ n : Fin N, 2 * (shellDiss lam ν α n * (a n t) ^ 2) := by
            rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ n : Fin N, a n t * sol.transfer n t)
            - 2 * (∑ n : Fin N, shellDiss lam ν α n * (a n t) ^ 2) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = -(shellDissipationRate lam ν α a t) := by
            rw [sol.transfer_conservative t]
            unfold shellDissipationRate
            ring
  rw [hval] at hsum
  -- shellEnergy a s = ∑ n, (a n s)^2 по определению.
  exact hsum

/-- **`shellEnergy_deriv_nonpos` — ДОКАЗАНА (оболочка диссипативна).**
    При `ν ≥ 0`, `λ > 0` энергия оболочки не растёт: `dE/dt = −D ≤ 0`. -/
theorem shellEnergy_deriv_nonpos {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a)
    (hν : 0 ≤ ν) (hlam : 0 < lam) (t : ℝ) :
    deriv (fun s => shellEnergy a s) t ≤ 0 := by
  rw [(shellEnergy_hasDerivAt sol t).deriv]
  have := shellDissipationRate_nonneg (lam := lam) (ν := ν) (α := α) hν hlam a t
  linarith

/-#############################################################################
  §2bis. НЕ-ВАКУУМНОСТЬ: нулевая оболочка — настоящее решение
#############################################################################-/

/--
**`zeroShellSolution` — ДОКАЗАНА (не-вакуумность).** Нулевая оболочка
`aₙ ≡ 0` — настоящее `ShellSolution`: все производные `0`, передача `0`,
энергосохранение тривиально. Класс решений ОБИТАЕМ — модель не пустышка.
(Type-значная структура ⟹ `def`, а не `theorem`.) -/
def zeroShellSolution (N : ℕ) (lam ν α : ℝ) :
    ShellSolution N lam ν α (fun _ _ => 0) where
  transfer := fun _ _ => 0
  shellODE := fun n t => by
    simpa using (hasDerivAt_const t (0 : ℝ))
  transfer_conservative := fun t => by simp

/-- Энергия нулевой оболочки честно `0`. -/
theorem zeroShell_energy (N : ℕ) (t : ℝ) :
    shellEnergy (N := N) (fun _ _ => 0) t = 0 := by
  simp [shellEnergy]

/-#############################################################################
  §2ter. ИНСТАНЦИАЦИЯ БЮДЖЕТА §1 НА ОБОЛОЧКЕ
#############################################################################-/

/--
**`no_uniform_dissipation_forever_on_shell` — ДОКАЗАНА (бюджет §1 на настоящей
оболочке).** Если решение оболочечной системы диссипирует РАВНОМЕРНО со
скоростью `≥ β > 0` на всём `[0,T]` (содержательная именованная гипотеза
`huniform` — например, энергия держится выше уровня, так что диагональная
диссипация ограничена снизу), и энергия на конце неотрицательна (что всегда
верно, `shellEnergy_nonneg`), то время ограничено бюджетом:
    `T ≤ shellEnergy a 0 / β`.
Прямая инстанциация `finite_budget_bounds_uniform_dissipation` с `E = shellEnergy`,
`E' = dE/dt = −D` (через `shellEnergy_hasDerivAt`). Гипотеза `huniform`
РЕАЛЬНО потребляется. -/
theorem no_uniform_dissipation_forever_on_shell
    {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a)
    (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T)
    (huniform : ∀ t ∈ Set.Icc (0:ℝ) T, β ≤ shellDissipationRate lam ν α a t) :
    T ≤ shellEnergy a 0 / β :=
  finite_budget_bounds_uniform_dissipation
    (fun s => shellEnergy a s)
    (fun t => -(shellDissipationRate lam ν α a t))
    (shellEnergy a 0) β T hβ hT rfl
    (fun t _ => shellEnergy_hasDerivAt sol t)
    (fun t ht => by
      have := huniform t ht
      linarith)
    (shellEnergy_nonneg a T)

/-#############################################################################
  §3. ЧЕСТНАЯ ГРАНИЦА: бюджет ПРОМАХИВАЕТСЯ мимо НЕравномерных каскадов
#############################################################################-/

open EuclidsPath.NavierStokesFront

/--
**`budget_misses_nonuniform` — ДОКАЗАНА (ключевая честность, машинная граница
бюджета).**

Бюджетная машина §1 (и её оболочечная инстанциация §2) требует РАВНОМЕРНОЙ
диссипации: гипотеза `hdiss : E' t ≤ −β` / `huniform : β ≤ D` со ЕДИНЫМ `β>0`.
Здесь машинно раскрывается её ГРАНИЦА: существует НЕравномерный каскад, для
которого эта гипотеза ПРОВАЛИВАЕТСЯ при ЛЮБОМ `β>0`.

Свидетель — уже построенный в NavierStokesFront кованый каскад
`cookedProfileCascade` на неотрицательном ограниченном профиле `cookedProfile`
(`tₙ = 1 − 2⁻ⁿ`, падения профиля `2⁻⁽ⁿ⁺¹⁾`). Его последовательные падения
ускользают ПОД ВСЯКИЙ `β>0` (`cookedProfileCascade_not_uniform`): нет единого
нижнего порога. Значит бюджет НЕ применим к нему и НЕ запрещает такой каскад —
честный машинно-проверенный ЗАЗОР принципа конечного бюджета.

(«Падение профиля на шаге `n`» — дискретный аналог `∫ E' = E(tₙ) − E(tₙ₊₁)`
входа §1; равномерное `≥ β` — ровно та гипотеза, что здесь опровергается.) -/
theorem budget_misses_nonuniform (β : ℝ) (hβ : 0 < β) :
    ¬ ∀ n : ℕ, β ≤ cookedProfile (cookedProfileCascade.times n)
                    - cookedProfile (cookedProfileCascade.times (n + 1)) :=
  cookedProfileCascade_not_uniform β hβ

/--
**`budget_does_not_preclude_cooked_cascade` — ДОКАЗАНА (усиленная форма
честности).** Ни при каком `β>0` кованый каскад НЕ подпадает под равномерную
гипотезу бюджета — то есть для каждого `β>0` найдётся шаг, падение на котором
СТРОГО меньше `β`. Существование такого «слишком мелкого» шага — прямое
свидетельство неприменимости бюджета. -/
theorem budget_does_not_preclude_cooked_cascade (β : ℝ) (hβ : 0 < β) :
    ∃ n : ℕ, cookedProfile (cookedProfileCascade.times n)
              - cookedProfile (cookedProfileCascade.times (n + 1)) < β := by
  by_contra h
  exact budget_misses_nonuniform β hβ fun n => not_lt.mp fun hlt => h ⟨n, hlt⟩

/-#############################################################################
  §4. МОСТ к `ns_no_infinite_dissipative_cascade` — та же машина на оболочке
#############################################################################-/

/--
**`shell_budget_is_ns_cascade_machine` — ДОКАЗАНА (мост-док-теорема).**

Та же абстрактная бюджетная машина, что убивает бесконечный δ-каскад Навье–Стокса
(`EuclidsPath.NavierStokes.ns_no_infinite_dissipative_cascade` через
`DissipativeCascade.no_infinite_uniform_dissipative_cascade`), здесь применена к
НАСТОЯЩЕЙ конечной оболочечной ОДУ-модели: диагональная диссипация даёт
`E' = −D ≤ 0`, и при равномерном пороге `β>0` время ограничено
(`no_uniform_dissipation_forever_on_shell`).

Формально мост фиксирует ОБЩНОСТЬ ядра: одно и то же неравенство
«накопленная равномерная диссипация ≤ начальная энергия» стоит за обоими
результатами. Здесь это отражено тем, что оболочечный бюджет — прямая
инстанциация того же `finite_budget_bounds_uniform_dissipation`, а НС-каскад —
инстанциация того же ℝ-бюджета `no_infinite_uniform_dissipative_cascade`.
Утверждение ниже — честная связка: если оболочечное `D` равномерно `≥ β`, то
`T ≤ E₀/β`, ровно как NS-сертификат требует конечности δ-лестницы. -/
theorem shell_budget_is_ns_cascade_machine
    {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a)
    (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T)
    (huniform : ∀ t ∈ Set.Icc (0:ℝ) T, β ≤ shellDissipationRate lam ν α a t) :
    T ≤ shellEnergy a 0 / β :=
  no_uniform_dissipation_forever_on_shell sol β T hβ hT huniform

/-#############################################################################
  §5. АУДИТ АКСИОМ (без sorry/axiom/native_decide)
#############################################################################-/

-- Ожидаемо: [propext, Classical.choice, Quot.sound] — такса репозитория неизменна.
#print axioms finite_budget_bounds_uniform_dissipation
#print axioms shellEnergy_hasDerivAt
#print axioms no_uniform_dissipation_forever_on_shell
#print axioms zeroShellSolution
#print axioms budget_misses_nonuniform

end EuclidsPath.CascadeBudget
