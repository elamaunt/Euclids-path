/-
  NavierStokes — САМО уравнение Навье–Стокса, формализованное через mathlib-анализ.
  Проза: prose/24_BoundaryDecomp.md (раздел «Диссипативный cascade»).

  ЗДЕСЬ ФОРМАЛИЗОВАНО (настоящий PDE-предикат, mathlib fderiv/gradient/∫):
    * `NSdiv` (дивергенция = след Якобиана покомпонентно), `vectorLaplacian`, `convectiveTerm` ((u·∇)u);
    * `IsNSSolution ν f u p` — несжимаемые уравнения НС в классической сильной форме:
        ∂ₜu + (u·∇)u = ν·Δu − ∇p + f,   div u = 0;
    * НЕ-ВАКУУМНОСТЬ: `zero_is_NSSolution` (нулевое поле — решение) — предикат обитаем;
    * `kineticEnergy` (½∫‖u‖²), `dissipationRate` (ν∫Σᵢ‖∂ᵢu‖²) — интегралы Бохнера;
    * СВЯЗКА С КАСКАДОМ: `ns_no_infinite_dissipative_cascade` — при энергетическом неравенстве
      (ВХОД) бесконечная последовательность δ-диссипирующих временных интервалов невозможна
      (через `DissipativeCascade.no_infinite_uniform_dissipative_cascade`);
    * ЧЕСТНОСТЬ ИНТЕГРАЛОВ (§5bis): `FiniteKineticEnergy`/`FiniteEnstrophy` + `kineticEnergy_of_not_integrable`
      — интеграл Бохнера МОЛЧА ноль на неинтегрируемом поле (`integral_undef`); предупреждение доказано;
    * ДЕКОМПОЗИЦИЯ ВХОДА (§5ter): `twoTimeEnergyInequality_of_energyBalance` — ДОКАЗАНА (FTC-глюа);
      монолитное неравенство сведено к УЗКОМУ точечному входу `EnergyBalanceLaw` (`dE/dt = −D`);
      полная цепь `ns_no_infinite_dissipative_cascade_of_balance` — от узкого входа до каскада.

  ЧЕСТНАЯ ГРАНИЦА. Формализовано УРАВНЕНИЕ и каркас; НЕ доказаны: существование/регулярность решений
  (проблема тысячелетия) и точечный энергобаланс `EnergyBalanceLaw` (= дифференцирование под интегралом
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` + интегрирование по частям + div u = 0; в mathlib
  теорема о дивергенции есть лишь в box-форме `integral_divergence_of_hasFDerivAt_off_countable`,
  предельный переход на ℝ³ не формализован — именованный ВХОД). Никакой связи с простыми числами —
  красная линия нетронута.
-/
import Mathlib
import EuclidsPath.Engine.DissipativeCascade

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.NavierStokes

open MeasureTheory
open scoped BigOperators

/-- Трёхмерное евклидово пространство. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Стандартный базисный вектор. -/
def e3 (i : Fin 3) : E3 := EuclideanSpace.single i 1

/-! ### §1. Дифференциальные операторы -/

/-- Дивергенция векторного поля: `div u = Σᵢ ∂ᵢuᵢ` (след Якобиана). -/
def NSdiv (u : E3 → E3) (x : E3) : ℝ :=
  ∑ i, fderiv ℝ u x (e3 i) i

/-- Векторный лапласиан: `Δu = Σᵢ ∂ᵢ(∂ᵢu)` (покомпонентно вторые производные по направлениям). -/
def vectorLaplacian (u : E3 → E3) (x : E3) : E3 :=
  ∑ i, fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x (e3 i)

/-- Конвективный член `(u·∇)u`: производная `u` вдоль самого `u`. -/
def convectiveTerm (u : E3 → E3) (x : E3) : E3 :=
  fderiv ℝ u x (u x)

/-! ### §2. Уравнения Навье–Стокса (несжимаемые, классическая сильная форма) -/

/--
**Уравнения Навье–Стокса.** `u : ℝ → E3 → E3` — поле скоростей, `p : ℝ → E3 → ℝ` — давление,
`ν` — вязкость, `f` — внешняя сила:

  `∂ₜu + (u·∇)u = ν·Δu − ∇p + f`   (баланс импульса)
  `div u = 0`                       (несжимаемость)
-/
structure IsNSSolution (ν : ℝ) (f : ℝ → E3 → E3)
    (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) : Prop where
  momentum : ∀ t x,
    deriv (fun s => u s x) t + convectiveTerm (u t) x
      = ν • vectorLaplacian (u t) x - gradient (p t) x + f t x
  incompressible : ∀ t x, NSdiv (u t) x = 0

/-! ### §3. Не-вакуумность: нулевое решение -/

/-- **`zero_is_NSSolution` — ДОКАЗАНА (не-вакуумность).** Нулевое поле с нулевым давлением и без
    силы — решение НС для любой вязкости. Предикат обитаем — это настоящее уравнение, не пустышка. -/
theorem zero_is_NSSolution (ν : ℝ) :
    IsNSSolution ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
  constructor
  · intro t x
    have hconv : convectiveTerm (fun _ : E3 => (0 : E3)) x = 0 := by
      simp [convectiveTerm, fderiv_const]
    have hlap : vectorLaplacian (fun _ : E3 => (0 : E3)) x = 0 := by
      simp [vectorLaplacian, fderiv_const]
    have hgrad : gradient (fun _ : E3 => (0 : ℝ)) x = 0 := by
      simp [gradient_const]
    simp [hconv, hlap, hgrad]
  · intro t x
    simp [NSdiv, fderiv_const]

/-! ### §4. Энергия и диссипация (интегралы Бохнера по объёму) -/

/-- Кинетическая энергия: `E(u) = ½∫‖u(x)‖² dx`. -/
def kineticEnergy (u : E3 → E3) : ℝ :=
  (1 / 2) * ∫ x : E3, ‖u x‖ ^ 2

/-- Скорость диссипации: `D(u) = ν·∫ Σᵢ ‖∂ᵢu(x)‖² dx` (энстрофийная форма). -/
def dissipationRate (ν : ℝ) (u : E3 → E3) : ℝ :=
  ν * ∫ x : E3, ∑ i, ‖fderiv ℝ u x (e3 i)‖ ^ 2

/-- Энергия неотрицательна. -/
theorem kineticEnergy_nonneg (u : E3 → E3) : 0 ≤ kineticEnergy u := by
  unfold kineticEnergy
  have : 0 ≤ ∫ x : E3, ‖u x‖ ^ 2 :=
    integral_nonneg (fun x => by positivity)
  linarith

/-! ### §5. Энергетическое неравенство — именованный ВХОД

Для гладких быстро убывающих решений (f = 0): `E(u(t₂)) + ∫_{t₁}^{t₂} D(u(s)) ds ≤ E(u(t₁))`.
Доказательство — интегрирование по частям + `div u = 0` (конвекция и давление не работают).
Это АНАЛИТИЧЕСКИЙ ВХОД: здесь НЕ доказывается. -/

/-- Двухвременное энергетическое неравенство (кокоцикл-форма) — ВХОД. -/
def TwoTimeEnergyInequality (ν : ℝ) (u : ℝ → E3 → E3) : Prop :=
  ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
    kineticEnergy (u t₂) + ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s)
      ≤ kineticEnergy (u t₁)

/-! ### §5bis. ЧЕСТНОСТЬ ИНТЕГРАЛОВ: интегрируемость и «тихий ноль» Бохнера

⚠️ Интеграл Бохнера в mathlib **молча равен нулю** на неинтегрируемой функции
(`MeasureTheory.integral_undef`). Значит `kineticEnergy u = 0` может означать НЕ «энергия нулевая»,
а «энергия бесконечна/не определена». Всякое энергетическое утверждение обязано идти в паре с
именованной интегрируемостью — иначе оно хрупко-вакуумно. -/

/-- Конечная кинетическая энергия: `‖u‖²` интегрируема (Бохнер честен). -/
def FiniteKineticEnergy (u : E3 → E3) : Prop :=
  Integrable (fun x : E3 => ‖u x‖ ^ 2)

/-- Конечная энстрофия: `Σᵢ‖∂ᵢu‖²` интегрируема. -/
def FiniteEnstrophy (u : E3 → E3) : Prop :=
  Integrable (fun x : E3 => ∑ i, ‖fderiv ℝ u x (e3 i)‖ ^ 2)

/-- **`kineticEnergy_of_not_integrable` — ДОКАЗАНА (предупреждение о тихом нуле).** Без
    `FiniteKineticEnergy` интеграл Бохнера МОЛЧА выдаёт `0`: «нулевая энергия» неинтегрируемого поля —
    артефакт определения, не физика. Потому интегрируемость — обязательная часть любого входа. -/
theorem kineticEnergy_of_not_integrable {u : E3 → E3}
    (h : ¬ FiniteKineticEnergy u) : kineticEnergy u = 0 := by
  unfold kineticEnergy
  rw [integral_undef h]
  ring

/-- Нулевое поле: энергия действительно `0` (не тихий ноль — честный). -/
theorem kineticEnergy_zero_field : kineticEnergy (fun _ : E3 => (0 : E3)) = 0 := by
  simp [kineticEnergy]

/-- Нулевое поле: диссипация `0`. -/
theorem dissipationRate_zero_field (ν : ℝ) :
    dissipationRate ν (fun _ : E3 => (0 : E3)) = 0 := by
  simp [dissipationRate, fderiv_const]

/-- Диссипация неотрицательна (при `ν ≥ 0`). -/
theorem dissipationRate_nonneg {ν : ℝ} (hν : 0 ≤ ν) (u : E3 → E3) :
    0 ≤ dissipationRate ν u := by
  unfold dissipationRate
  have : 0 ≤ ∫ x : E3, ∑ i, ‖fderiv ℝ u x (e3 i)‖ ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => by positivity
  positivity

/-! ### §5ter. ДЕКОМПОЗИЦИЯ ВХОДА: точечный энергобаланс ⟹ двухвременное неравенство

Монолитный вход §5 разложен: вся аналитика (дифференцирование под интегралом —
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`; интегрирование по частям / теорема о дивергенции —
в mathlib есть лишь box-форма `integral_divergence_of_hasFDerivAt_off_countable`, предельный переход
на ℝ³ не формализован) сжата в ОДИН точечный вход `EnergyBalanceLaw`: `dE/dt = −D`. Глюа от него до
`TwoTimeEnergyInequality` — ДОКАЗАНА (FTC). Вход стал строго ýже: не интегральное неравенство, а
классическое тождество баланса. -/

/-- Точечный энергобаланс `dE/dt = −D(t)` — именованный ВХОД (узкая форма).
    Для гладких быстро убывающих решений это тождество = дифференцирование под интегралом +
    интегрирование по частям + `div u = 0` (конвекция и давление не работают). -/
def EnergyBalanceLaw (ν : ℝ) (u : ℝ → E3 → E3) : Prop :=
  ∀ t : ℝ, HasDerivAt (fun s => kineticEnergy (u s)) (-(dissipationRate ν (u t))) t

/-- **`twoTimeEnergyInequality_of_energyBalance` — ДОКАЗАНА (глюа FTC).** Точечный баланс
    `dE/dt = −D` + интегрируемость диссипации ⟹ двухвременное энергетическое НЕРАВЕНСТВО (на деле —
    равенство). Старый монолитный вход §5 сведён к более узкому точечному входу `EnergyBalanceLaw`. -/
theorem twoTimeEnergyInequality_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    TwoTimeEnergyInequality ν u := by
  intro t₁ t₂ hle
  -- FTC: E(t₂) − E(t₁) = ∫_{t₁}^{t₂} (−D)
  have hftc :
      (∫ s in t₁..t₂, -(dissipationRate ν (u s)))
        = kineticEnergy (u t₂) - kineticEnergy (u t₁) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hBal s) ((hInt t₁ t₂).neg)
  -- интервальный интеграл = интеграл по Icc (граница меры ноль)
  have hIcc :
      (∫ s in t₁..t₂, dissipationRate ν (u s))
        = ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s) := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [intervalIntegral.integral_neg, hIcc] at hftc
  linarith [hftc]

/-! ### §6. СВЯЗКА С КАСКАДОМ: неравенство ⟹ конечность δ-диссипирующего каскада -/

/-- δ-диссипирующий временной шаг: интервал, на котором накопленная диссипация ≥ δ. -/
def DissipativeStage (ν : ℝ) (u : ℝ → E3 → E3) (δ : ℝ) (t₁ t₂ : ℝ) : Prop :=
  t₁ ≤ t₂ ∧ δ ≤ ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s)

/--
**`ns_no_infinite_dissipative_cascade` — ДОКАЗАНА (условно на входе-неравенстве).** Если решение НС
удовлетворяет энергетическому неравенству, то НЕ существует бесконечной последовательности моментов
времени, каждый следующий шаг которой диссипирует ≥ δ > 0: накопленная диссипация превысила бы `E(u t₀)`.
Прямое применение `DissipativeCascade.no_infinite_uniform_dissipative_cascade` — квантизация в действии
на НАСТОЯЩЕМ уравнении. Это форма «нет бесконечного каскада к мелким масштабам при квантованной
диссипации» — ровно тот сертификат, которого требует регулярность. -/
theorem ns_no_infinite_dissipative_cascade
    (ν : ℝ) (u : ℝ → E3 → E3) (δ : ℝ) (hδ : 0 < δ)
    (hE : TwoTimeEnergyInequality ν u) :
    ¬ ∃ times : ℕ → ℝ, ∀ k, DissipativeStage ν u δ (times k) (times (k + 1)) := by
  rintro ⟨times, hstage⟩
  exact EuclidsPath.DissipativeCascade.no_infinite_uniform_dissipative_cascade
    (State := ℝ) (Step := fun t₁ t₂ => DissipativeStage ν u δ t₁ t₂)
    (fun t => kineticEnergy (u t))
    (fun t₁ t₂ => ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s))
    δ hδ
    (fun {t₁ t₂} h => hE t₁ t₂ h.1)
    (fun {t₁ t₂} h => h.2)
    (fun t => kineticEnergy_nonneg (u t))
    ⟨times, hstage⟩

/-- **`ns_no_infinite_dissipative_cascade_of_balance` — ДОКАЗАНА (полная цепь от узкого входа).**
    Точечный энергобаланс `dE/dt = −D` + интегрируемость диссипации ⟹ нет бесконечного
    δ-каскада. Композиция FTC-глюи (§5ter) и квантизации (§6): весь аналитический остаток НС-ветки
    сжат в ОДИН точечный вход `EnergyBalanceLaw`. -/
theorem ns_no_infinite_dissipative_cascade_of_balance
    (ν : ℝ) (u : ℝ → E3 → E3) (δ : ℝ) (hδ : 0 < δ)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    ¬ ∃ times : ℕ → ℝ, ∀ k, DissipativeStage ν u δ (times k) (times (k + 1)) :=
  ns_no_infinite_dissipative_cascade ν u δ hδ
    (twoTimeEnergyInequality_of_energyBalance ν u hBal hInt)

end EuclidsPath.NavierStokes
