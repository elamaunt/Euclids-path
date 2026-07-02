/-
  NavierStokesFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль ветви гладкости
  Навье–Стокса в программе вечного двигателя: «движение двигателя внутри ранга
  гладко всюду — точка разрыва создала бы вечный двигатель; решение выводится
  ВЗЯТИЕМ ИНТЕГРАЛА».

  Архитектура:
    * двигатель: `SingularCascade` — бесконечно много δ-диссипативных стадий,
      сжатых до конечного времени T (гипотетическая сингулярность как
      бесконечная квантованная лестница); зелёный убийца — существующая
      бюджетная машина (`ns_no_infinite_dissipative_cascade`);
    * суррогат гладкости `NoSingularCascade` — ГЕРОЙ
      `noSingularCascade_of_energyBalance`: энергобаланс + интегрируемость ⟹
      суррогат (зелёная условная цепь, NS-паттерн);
    * «ИНТЕГРАЛ ВЗЯТ» дважды: энергетическое ТОЖДЕСТВО равенством
      (`energy_identity_of_energyBalance`, FTC-2 — старое неравенство §5
      оказывается огрублением выведенного интегрированием равенства) и
      интегральная форма решения (`isNSSolution_integral_form`, E3-значный
      FTC: u t x = u 0 x + ∫₀ᵗ (νΔu − ∇p + f − (u·∇)u)).

  ЧЕСТНАЯ ГРАНИЦА (громко): `NoSingularCascade` — суррогат в каскадном языке,
  НЕ C^∞-регулярность; НЕ доказаны существование Лерэ, единственность,
  регулярность; `EnergyBalanceLaw` остаётся именованным 🔴-входом; проблема
  тысячелетия НЕ решается и НЕ объявляется. Кованые свидетели живут на уровне
  полей/потоков/ПРОФИЛЕЙ энергии — ни один не является нетривиальным
  IsNSSolution (раскрыто).

  ТРИЛЕММА пятой границы декрета — все вердикты машинны (§7):
    V1 универсальная форма ОПРОВЕРЖИМА (cookedFlow — размешиваемый поток
       набирает энергию: баланс проваливается через HasDerivAt.unique);
    V2 экзистенциальная форма УЖЕ ДОКАЗАНА (нулевое решение) — декрет вакуумен;
    V3 манифестационная (риманово зеркало) форма НЕСОВМЕСТИМА с принятой
       границей: кованый профильный каскад (tₙ = 1 − 2⁻ⁿ) зелёно ПРЕДЪЯВИМ,
       в отличие от off-critical нуля.
  ℝ-предупреждение (урок cookedLadder ЯМ): равномерный профильный каскад убит
  бюджетом (L10), но кованый НЕравномерный существует даже при неотрицательном
  ограниченном профиле (L11) — суррогат говорит именно о РАВНОМЕРНОМ
  квантовании. Модуль карантин НЕ импортирует; axiom/sorry нет.
-/
import Mathlib
import EuclidsPath.Engine.NavierStokes
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

noncomputable section

namespace EuclidsPath
namespace NavierStokesFront

open MeasureTheory
open EuclidsPath.NavierStokes
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-#############################################################################
  §1. Двигатель: сингулярный каскад и его зелёные убийцы
#############################################################################-/

/-- **D1. СИНГУЛЯРНЫЙ КАСКАД = ВЕЧНЫЙ ДВИГАТЕЛЬ:** бесконечная
    последовательность моментов до времени `T`, каждый шаг которой —
    δ-диссипирующий этап (`DissipativeStage`): бесконечно много квантованных
    диссипаций, сжатых до гипотетического сингулярного времени. Поле `before`
    несёт семантику «до сингулярности»; РАСКРЫТО: убийца L1 его не
    потребляет — бюджет запрещает бесконечный δ-каскад ВООБЩЕ, сжатый тем
    более (инертность раскрыта, зеркало vacuum_mem у ЯМ). -/
structure SingularCascade (ν : ℝ) (u : ℝ → E3 → E3) (δ T : ℝ) where
  times : ℕ → ℝ
  before : ∀ n, times n < T
  stage : ∀ n, DissipativeStage ν u δ (times n) (times (n + 1))

/-- **L1 — ЗЕЛЁНЫЙ УБИЙЦА (прямое применение существующей машины):**
    при энергетическом неравенстве сингулярных каскадов нет. -/
theorem no_singularCascade_of_energyInequality
    (ν : ℝ) (u : ℝ → E3 → E3) (δ T : ℝ) (hδ : 0 < δ)
    (hE : TwoTimeEnergyInequality ν u) :
    IsEmpty (SingularCascade ν u δ T) :=
  ⟨fun C => ns_no_infinite_dissipative_cascade ν u δ hδ hE ⟨C.times, C.stage⟩⟩

/-- **D2. Честный суррогат гладкости** в языке каскада: ни при каком
    квантовании δ > 0 и ни к какому конечному времени T сингулярный каскад
    не сжимается. РАСКРЫТО ГРОМКО: это НЕ C^∞-регулярность и НЕ утверждение
    Клэя — только «нет бесконечной равномерно-квантованной диссипативной
    лестницы до конечного времени». -/
def NoSingularCascade (ν : ℝ) (u : ℝ → E3 → E3) : Prop :=
  ∀ δ T : ℝ, 0 < δ → IsEmpty (SingularCascade ν u δ T)

/-- **L2 — ГЕРОЙ (полная цепь от узкого входа, NS-паттерн):**
    точечный энергобаланс `dE/dt = −D` + интегрируемость ⟹ суррогат
    гладкости: точек разрыва каскадного типа НЕТ. -/
theorem noSingularCascade_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    NoSingularCascade ν u :=
  fun δ T hδ => no_singularCascade_of_energyInequality ν u δ T hδ
    (twoTimeEnergyInequality_of_energyBalance ν u hBal hInt)

/-#############################################################################
  §2. «Взять интеграл» I: энергетическое ТОЖДЕСТВО (FTC-равенство)
#############################################################################-/

/-- **L3 — ЭНЕРГЕТИЧЕСКОЕ ТОЖДЕСТВО (интеграл ВЗЯТ; равенство, не
    неравенство):** `E(t₂) = E(t₁) − ∫_{t₁}^{t₂} D` — FTC-2 от энергобаланса.
    Ориентация времени свободна (интервальный интеграл). -/
theorem energy_identity_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)
    (t₁ t₂ : ℝ) :
    kineticEnergy (u t₂)
      = kineticEnergy (u t₁) - ∫ s in t₁..t₂, dissipationRate ν (u s) := by
  have hftc :
      (∫ s in t₁..t₂, -(dissipationRate ν (u s)))
        = kineticEnergy (u t₂) - kineticEnergy (u t₁) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hBal s) ((hInt t₁ t₂).neg)
  rw [intervalIntegral.integral_neg] at hftc
  linarith

/-- **L4 — Icc-форма тождества** (тот же вид, что `TwoTimeEnergyInequality`,
    но РАВЕНСТВОМ): старое неравенство §5 — огрубление выведенного
    интегрированием тождества. -/
theorem energy_identity_Icc_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)
    {t₁ t₂ : ℝ} (hle : t₁ ≤ t₂) :
    kineticEnergy (u t₂) + ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s)
      = kineticEnergy (u t₁) := by
  have h := energy_identity_of_energyBalance ν u hBal hInt t₁ t₂
  have hIcc :
      (∫ s in t₁..t₂, dissipationRate ν (u s))
        = ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s) := by
    rw [intervalIntegral.integral_of_le hle,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hIcc] at h
  linarith

/-#############################################################################
  §3. «Взять интеграл» II: интегральная (mild) форма решения
#############################################################################-/

/-- **L5 — АБСТРАКТНАЯ ИНТЕГРАЛЬНАЯ РЕКОНСТРУКЦИЯ (E3-значный FTC):**
    траектория восстанавливается интегрированием своей производной:
    `F t = F 0 + ∫₀ᵗ f`. Интеграл Бохнера банахово-значный; `E3` полно —
    mathlib-FTC применим дословно. -/
theorem trajectory_eq_integral_of_hasDerivAt
    (F f : ℝ → E3)
    (hF : ∀ t : ℝ, HasDerivAt F (f t) t)
    (hInt : ∀ t₁ t₂ : ℝ, IntervalIntegrable f volume t₁ t₂)
    (t : ℝ) :
    F t = F 0 + ∫ s in (0:ℝ)..t, f s := by
  have h : (∫ s in (0:ℝ)..t, f s) = F t - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) (hInt 0 t)
  rw [h]
  abel

/-- Правая часть НС, разрешённая относительно ∂ₜu (точная форма, выпадающая
    из `momentum` через `eq_sub_of_add_eq`). -/
def nsTimeDerivative (ν : ℝ) (f : ℝ → E3 → E3) (u : ℝ → E3 → E3)
    (p : ℝ → E3 → ℝ) (t : ℝ) (x : E3) : E3 :=
  ν • vectorLaplacian (u t) x - gradient (p t) x + f t x - convectiveTerm (u t) x

/-- **L6:** решение НС + дифференцируемость по времени ⟹ производная
    траектории каждой точки — правая часть уравнения. -/
theorem hasDerivAt_of_isNSSolution
    {ν : ℝ} {f : ℝ → E3 → E3} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (sol : IsNSSolution ν f u p)
    (hdiff : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (t : ℝ) (x : E3) :
    HasDerivAt (fun s => u s x) (nsTimeDerivative ν f u p t x) t := by
  have h := (hdiff t x).hasDerivAt
  rw [eq_sub_of_add_eq (sol.momentum t x)] at h
  exact h

/-- **L7 — «ВЫВЕСТИ РЕШЕНИЕ» (интегральная/mild-форма, честно условная):**
    классическое решение с дифференцируемой и интегрируемой временной
    динамикой ВОССТАНАВЛИВАЕТСЯ интегрированием уравнения:
    `u t x = u 0 x + ∫₀ᵗ (νΔu − ∇p + f − (u·∇)u)`.
    РАСКРЫТО: это НЕ существование решения (условно на sol/hdiff/hInt) —
    но связь «дифференциальная форма ⟹ интегральная форма» machine-checked. -/
theorem isNSSolution_integral_form
    {ν : ℝ} {f : ℝ → E3 → E3} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (sol : IsNSSolution ν f u p)
    (hdiff : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (hInt : ∀ (x : E3) (t₁ t₂ : ℝ),
      IntervalIntegrable (fun s => nsTimeDerivative ν f u p s x) volume t₁ t₂)
    (t : ℝ) (x : E3) :
    u t x = u 0 x + ∫ s in (0:ℝ)..t, nsTimeDerivative ν f u p s x :=
  trajectory_eq_integral_of_hasDerivAt (fun s => u s x)
    (fun s => nsTimeDerivative ν f u p s x)
    (fun s => hasDerivAt_of_isNSSolution sol hdiff s x) (hInt x) t

/-- Правая часть на нулевом решении — ноль (топливо невакуумности L7). -/
theorem nsTimeDerivative_zero (ν : ℝ) (t : ℝ) (x : E3) :
    nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) t x = 0 := by
  simp [nsTimeDerivative, vectorLaplacian, convectiveTerm]

/-- Невакуумность L7: на нулевом решении все три гипотезы обитаемы. -/
theorem zero_integral_form_inhabited (ν : ℝ) (t : ℝ) (x : E3) :
    (fun _ _ => (0:E3)) t x
      = (fun _ _ => (0:E3)) 0 x + ∫ s in (0:ℝ)..t,
          nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) s x :=
  isNSSolution_integral_form (zero_is_NSSolution ν)
    (fun _ _ => differentiableAt_const _)
    (fun x t₁ t₂ => by
      simp only [nsTimeDerivative_zero]
      exact (continuous_const : Continuous fun _ : ℝ => (0:E3)).intervalIntegrable t₁ t₂)
    t x

/-#############################################################################
  §4. Нулевое решение: баланс + суррогат (топливо V2)
#############################################################################-/

/-- **L8: энергобаланс нулевого решения — ДОКАЗАН** (`E ≡ 0`, `D ≡ 0`,
    `hasDerivAt_const`). Экзистенциальная форма пятого поля отсюда вакуумна. -/
theorem zero_energyBalance (ν : ℝ) : EnergyBalanceLaw ν (fun _ _ => 0) := by
  intro t
  simpa [dissipationRate_zero_field] using
    hasDerivAt_const t (kineticEnergy (fun _ : E3 => (0 : E3)))

theorem zero_noSingularCascade (ν : ℝ) :
    NoSingularCascade ν (fun _ _ => 0) :=
  noSingularCascade_of_energyBalance ν _ (zero_energyBalance ν)
    (fun t₁ t₂ => by
      simp only [dissipationRate_zero_field]
      exact (continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable t₁ t₂)

/-#############################################################################
  §5. Кованый несбалансированный поток — свидетель V1
      (индикатор шара: тихий ноль Бохнера честно обойдён)
#############################################################################-/

/-- Кованое поле: единичный вектор внутри единичного шара, ноль вне.
    Интегрируемо ЧЕСТНО (не тихий ноль — константные поля для ковки
    непригодны, их энергия молча коллапсирует в 0). -/
def cookedField : E3 → E3 :=
  Set.indicator (Metric.ball (0 : E3) 1) (fun _ => e3 0)

theorem cookedField_normSq (x : E3) :
    ‖cookedField x‖ ^ 2
      = Set.indicator (Metric.ball (0 : E3) 1) (fun _ => (1 : ℝ)) x := by
  unfold cookedField
  by_cases hx : x ∈ Metric.ball (0 : E3) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simp [e3]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

theorem cookedField_energy :
    kineticEnergy cookedField
      = (1 / 2) * (volume (Metric.ball (0 : E3) 1)).toReal := by
  unfold kineticEnergy
  simp only [cookedField_normSq]
  rw [MeasureTheory.integral_indicator measurableSet_ball,
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]

theorem cookedField_energy_pos : 0 < kineticEnergy cookedField := by
  rw [cookedField_energy]
  have h0 : volume (Metric.ball (0 : E3) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : E3) one_pos).ne'
  have htop : volume (Metric.ball (0 : E3) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have := ENNReal.toReal_pos h0 htop
  linarith

/-- Кованый «размешиваемый» поток: `u t x = t • cookedField x` — энергия
    РАСТЁТ (внешнее размешивание), баланс обязан провалиться. -/
def cookedFlow : ℝ → E3 → E3 := fun t x => t • cookedField x

theorem cookedFlow_energy (t : ℝ) :
    kineticEnergy (cookedFlow t) = t ^ 2 * kineticEnergy cookedField := by
  unfold kineticEnergy cookedFlow
  have h : ∀ x : E3, ‖t • cookedField x‖ ^ 2 = t ^ 2 * ‖cookedField x‖ ^ 2 := by
    intro x
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [h]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **L9 — КОВАНЫЙ ПРОВАЛ БАЛАНСА (без вычисления D!):** `E(t) = c·t²` с
    `c > 0`; в `t = 1` производная `2c > 0`, а баланс требовал бы `−D ≤ 0` —
    единственность производной (`HasDerivAt.unique`) сжигает. -/
theorem cookedFlow_not_energyBalance : ¬ EnergyBalanceLaw 1 cookedFlow := by
  intro hBal
  have h1 := hBal 1
  have hfun : (fun s => kineticEnergy (cookedFlow s))
      = fun s => kineticEnergy cookedField * s ^ 2 :=
    funext fun s => by rw [cookedFlow_energy]; ring
  rw [hfun] at h1
  have h2 : HasDerivAt (fun s : ℝ => kineticEnergy cookedField * s ^ 2)
      (kineticEnergy cookedField * 2) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).const_mul (kineticEnergy cookedField)
  have huniq : kineticEnergy cookedField * 2
      = -(dissipationRate 1 (cookedFlow 1)) := h2.unique h1
  have hD : 0 ≤ dissipationRate 1 (cookedFlow 1) :=
    dissipationRate_nonneg zero_le_one _
  have hc := cookedField_energy_pos
  linarith

/-- **L9b:** тот же свидетель опровергает и монолитную ∀-форму НЕРАВЕНСТВА. -/
theorem cookedFlow_not_twoTimeEnergyInequality :
    ¬ TwoTimeEnergyInequality 1 cookedFlow := by
  intro h
  have h01 := h 0 1 zero_le_one
  have hD : 0 ≤ ∫ s in Set.Icc (0:ℝ) 1, dissipationRate 1 (cookedFlow s) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun s _ => dissipationRate_nonneg zero_le_one _)
  have h0 : kineticEnergy (cookedFlow 0) = 0 := by rw [cookedFlow_energy]; ring
  have h1 : kineticEnergy (cookedFlow 1) = kineticEnergy cookedField := by
    rw [cookedFlow_energy]; ring
  have hc := cookedField_energy_pos
  rw [h0, h1] at h01
  linarith

/-#############################################################################
  §6. Уровень профилей: ℝ-предупреждение (равномерный каскад убит,
      кованый неравномерный существует)
#############################################################################-/

/-- **D3. Профильный каскад (абстрактный; НИКАКОГО НС-содержания — кованые
    свидетели живут на уровне профилей энергии, не решений; раскрыто):**
    бесконечно много этапов с положительным падением профиля, все до `T`. -/
structure ProfileCascade (E : ℝ → ℝ) (T : ℝ) where
  times : ℕ → ℝ
  mono : ∀ n, times n ≤ times (n + 1)
  before : ∀ n, times n < T
  drop_pos : ∀ n, 0 < E (times n) - E (times (n + 1))

/-- **L10 — РАВНОМЕРНЫЙ профильный каскад при неотрицательном профиле УБИТ**
    (бюджет, generic-машина каскада; зеркало `no_uniformlyDissipative_ladder`
    у ЯМ). -/
theorem no_uniform_profileCascade_of_nonneg
    (E : ℝ → ℝ) (T δ : ℝ) (hδ : 0 < δ) (hE : ∀ t, 0 ≤ E t)
    (C : ProfileCascade E T)
    (huniform : ∀ n, δ ≤ E (C.times n) - E (C.times (n + 1))) : False :=
  EuclidsPath.DissipativeCascade.no_infinite_uniform_dissipative_cascade
    (State := ℕ) (Step := fun m n => n = m + 1)
    (fun n => E (C.times n)) (fun m n => E (C.times m) - E (C.times n)) δ hδ
    (fun {m n} h => by subst h; exact le_of_eq (by ring))
    (fun {m n} h => by subst h; exact huniform m)
    (fun n => hE (C.times n))
    ⟨fun k => k, fun _ => rfl⟩

/-- Кованый НЕОТРИЦАТЕЛЬНЫЙ профиль `max (1−t) 0`. -/
def cookedProfile : ℝ → ℝ := fun t => max (1 - t) 0

theorem cookedProfile_at_stage (n : ℕ) :
    cookedProfile (1 - (1 / 2 : ℝ) ^ n) = (1 / 2 : ℝ) ^ n := by
  unfold cookedProfile
  have h : (1 : ℝ) - (1 - (1 / 2) ^ n) = (1 / 2) ^ n := by ring
  rw [h, max_eq_left (by positivity)]

/-- Кованый каскад на `tₙ = 1 − 2⁻ⁿ`: падения `2⁻⁽ⁿ⁺¹⁾ > 0` — бесконечный
    каскад, сжатый до `T = 1`, при неотрицательном ограниченном профиле. -/
def cookedProfileCascade : ProfileCascade cookedProfile 1 where
  times := fun n => 1 - (1 / 2 : ℝ) ^ n
  mono := fun n => by
    have hp : (0:ℝ) < (1/2) ^ n := by positivity
    have h : (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
    nlinarith
  before := fun n => by
    have : (0:ℝ) < (1/2) ^ n := by positivity
    linarith
  drop_pos := fun n => by
    rw [cookedProfile_at_stage n, cookedProfile_at_stage (n + 1)]
    have hp : (0:ℝ) < (1/2) ^ n := by positivity
    have h : (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
    nlinarith

@[simp] theorem cookedProfileCascade_times (n : ℕ) :
    cookedProfileCascade.times n = 1 - (1 / 2 : ℝ) ^ n := rfl

/-- **L11 — ℝ-ПРЕДУПРЕЖДЕНИЕ (урок cookedLadder ЯМ, машинно):** кованый
    каскад НЕ равномерен — его падения `2⁻⁽ⁿ⁺¹⁾` ускользают под всякий δ.
    Потому бюджет (L10) его НЕ убивает: `NoSingularCascade` — суррогат про
    РАВНОМЕРНОЕ квантование; неравномерные каскады профилей существуют даже
    при неотрицательном ограниченном профиле. Суррогат ≠ C^∞ — раскрыто. -/
theorem cookedProfileCascade_not_uniform (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n, δ ≤ cookedProfile (cookedProfileCascade.times n)
              - cookedProfile (cookedProfileCascade.times (n + 1)) := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2 : ℝ) < 1)
  have hstep := h n
  rw [cookedProfileCascade_times, cookedProfileCascade_times,
      cookedProfile_at_stage n, cookedProfile_at_stage (n + 1)] at hstep
  have hp : (0:ℝ) < (1/2) ^ n := by positivity
  have heq : (1/2 : ℝ) ^ n - (1/2) ^ (n + 1) = (1/2) ^ (n + 1) := by ring
  rw [heq] at hstep
  have hlt : ((1:ℝ)/2) ^ (n + 1) < (1/2) ^ n := by
    calc ((1:ℝ)/2) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
      _ < (1/2) ^ n := by nlinarith
  linarith

/-#############################################################################
  §7. ТРИЛЕММА пятой границы декрета — все вердикты машинны
#############################################################################-/

/-- **D4a. КАНДИДАТ 1 (универсальная форма пятого поля):** всякий поток
    подчиняется энергобалансу. -/
def NsBalanceLawUniversal : Prop :=
  ∀ (ν : ℝ) (u : ℝ → E3 → E3), EnergyBalanceLaw ν u

/-- **D4b. КАНДИДАТ 2 (экзистенциальная форма):** НЕКОТОРОЕ решение НС
    сбалансировано и свободно от сингулярных каскадов. -/
def NsBalanceLawExistential : Prop :=
  ∃ (ν : ℝ) (u : ℝ → E3 → E3),
    (∃ (f : ℝ → E3 → E3) (p : ℝ → E3 → ℝ), IsNSSolution ν f u p) ∧
    EnergyBalanceLaw ν u ∧ NoSingularCascade ν u

/-- **D4c. КАНДИДАТ 3 (манифестационная форма, риманово зеркало):** каскад
    манифестирует неоплатимой поставкой потоков на всех разрешённых
    леджер-масштабах (тот же объект `DeviationFlowSupply`, что у
    riemannBoundary и ЯМ-лестницы). Семейство СВОБОДНО от C — D-инертность
    вскрыта аудитами §8. -/
def CascadeManifests {E : ℝ → ℝ} {T : ℝ} (_C : ProfileCascade E T) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def NsManifestationLaw : Prop :=
  ∀ (E : ℝ → ℝ) (T : ℝ) (C : ProfileCascade E T), CascadeManifests C

/-- **V1: КАНДИДАТ 1 ЗЕЛЁНО-ОПРОВЕРЖИМ** — декрет был бы противоречив.
    Свидетель: cookedFlow (размешиваемый поток набирает энергию). -/
theorem nsLawUniversal_refuted : ¬ NsBalanceLawUniversal :=
  fun h => cookedFlow_not_energyBalance (h 1 cookedFlow)

/-- **V2: КАНДИДАТ 2 ЗЕЛЁНО-ДОКАЗУЕМ** — декрет был бы вакуумен.
    Свидетель: нулевое решение. -/
theorem nsLawExistential_green : NsBalanceLawExistential :=
  ⟨1, fun _ _ => 0,
   ⟨fun _ _ => 0, fun _ _ => 0, zero_is_NSSolution 1⟩,
   zero_energyBalance 1, zero_noSingularCascade 1⟩

/-- **V3: КАНДИДАТ 3 НЕСОВМЕСТИМ С ПРИНЯТОЙ ГРАНИЦЕЙ** (зелёная условная
    форма, зеркало ЯМ-V3): кованый профильный каскад — в отличие от
    off-critical нуля — зелёно ПРЕДЪЯВИМ; закон + граница ⟹ False. -/
theorem nsManifestationLaw_refutes_boundary
    (hLaw : NsManifestationLaw) : ¬ TheStrictLastStep00Obligation := by
  rintro ⟨A, projOf, hres⟩
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf 1) :=
    strictSemanticExtended_resolves_old (hres 1)
  exact no_deviationFlowSupply_at_resolved_scale (projOf 1) hResolves
    (hLaw cookedProfile 1 cookedProfileCascade A 1 (projOf 1) hResolves)

theorem not_nsManifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) : ¬ NsManifestationLaw :=
  fun hLaw => nsManifestationLaw_refutes_boundary hLaw hBoundary

/-- **V3-характеризация (безусловная — квантор зелёно обитаем):** закон ⟺
    глобальная заморозка всех леджеров. -/
theorem nsManifestationLaw_iff_no_resolution :
    NsManifestationLaw ↔
      ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw A M0 proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw cookedProfile 1 cookedProfileCascade A M0 proj hres)
  · intro hFreeze E T C A M0 proj hres
    exact ((hFreeze A M0 proj) hres).elim

/-#############################################################################
  §8. Origin-anchor аудиты (инстанциация осуждающей машины)
#############################################################################-/

theorem ns_bundling_audit (E : ℝ → ℝ) (T : ℝ) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun C : ProfileCascade E T => CascadeManifests C) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun C : ProfileCascade E T => CascadeManifests C)) ↔
      ¬ Nonempty (ProfileCascade E T) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

theorem ns_bundle_refuted_at_cooked :
    ¬ (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
         (fun C : ProfileCascade cookedProfile 1 => CascadeManifests C) ∧
       EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
         (fun C : ProfileCascade cookedProfile 1 => CascadeManifests C)) :=
  fun h => (ns_bundling_audit cookedProfile 1).mp h ⟨cookedProfileCascade⟩

theorem nsLaw_freeCollapse (E : ℝ → ℝ) (T : ℝ) :
    EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.FreeLawCollapse
      (fun C : ProfileCascade E T => CascadeManifests C)
      (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
          DeviationFlowSupply A M0) :=
  fun _C => Iff.rfl

theorem nsLaw_cannot_separate (E : ℝ → ℝ) (T : ℝ) :
    ¬ EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.ZeroSeparating
        (fun C : ProfileCascade E T => CascadeManifests C) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.no_zero_separation_under_freeCollapse
    (nsLaw_freeCollapse E T)

end NavierStokesFront
end EuclidsPath

end

-- Машинная видимость чистоты в build-логе
-- (ожидаемо [propext, Classical.choice, Quot.sound]):
#print axioms EuclidsPath.NavierStokesFront.energy_identity_of_energyBalance
#print axioms EuclidsPath.NavierStokesFront.isNSSolution_integral_form
#print axioms EuclidsPath.NavierStokesFront.noSingularCascade_of_energyBalance
#print axioms EuclidsPath.NavierStokesFront.nsLawUniversal_refuted
#print axioms EuclidsPath.NavierStokesFront.nsLawExistential_green
#print axioms EuclidsPath.NavierStokesFront.nsManifestationLaw_refutes_boundary
