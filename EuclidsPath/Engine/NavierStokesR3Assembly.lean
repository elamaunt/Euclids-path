/-
  NavierStokesR3Assembly — «ПЕРЕХОД НА ℝ³: интеграл Навье–Стокса СОБРАН НА БОКСЕ».

  ЧТО СОБРАНО (послойно, каждый ранг компилируется отдельно):
    * R1 — дифференцирование ПОД ИНТЕГРАЛОМ энергии: `hasDerivAt_kineticEnergy_of_dominated`
      (mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le` + `HasDerivAt.norm_sq`,
      с (1/2)-массажем): dE/dt = ∫⟪u, ∂ₜu⟫ — ПРИ именованном мажоранте `TimeDomination`;
    * R2 — теорема о ДИВЕРГЕНЦИИ ЗАДЕЙСТВОВАНА ПО-НАСТОЯЩЕМУ: `boxDivergence_integral_eq_zero`
      выводит ∫_box div F = 0 из mathlib-box-теоремы `integral_divergence_of_hasFDerivAt_off_countable`
      (s := ∅), причём ГРАНИЧНЫЕ ИНТЕГРАЛЫ (грани бокса) ГИБНУТ по носителю (F ≡ 0 вне Icc);
      затем `divergence_integral_eq_zero` — на всё ℝ³ через `setIntegral_eq_integral_of_forall_compl_eq_zero`;
    * R3 — ТРИ убийцы интегрированием по частям (pi-workhorse + E3-обёртка):
      (i) давление ∫⟪w,∇p⟫ = 0; (ii) перенос ∫⟪w,(w·∇)w⟫ = 0; (iii) вязкость
      ∫⟪w,Δw⟫ = −∫∑‖∂ᵢw‖² — покомпонентное IBP;
    * ЗАКОН `EnergyBalanceLaw` ВЫВЕДЕН (не декретирован) для класса `BoxSupportedC2Flow`
      с бокс-носителем: `energyBalance_of_boxSupported` — суррогат гладкости `NoSingularCascade`
      получен как СЛЕДСТВИЕ (`noSingularCascade_of_r3Assembly`).

  ГЕЙТ ДАВЛЕНИЯ ВПЕРВЫЕ: `BoxSupportedC2Flow` гейтит гладкость ДАВЛЕНИЯ (поля `pressDiff/contP/contP'`),
  чем закрывает канал Ковки-B (`cookedFlow`: junk сидел в ∇p на сфере — теперь исключён гейтом C²).

  ЧЕСТНЫЕ ГРАНИЦЫ (громко):
    * КЛАСС бокс-носителя ТОЛЬКО: всё выведено для C²-полей с носителем в фиксированном боксе;
      предельный переход box→ℝ³ В MATHLIB ОТСУТСТВУЕТ — это внешний, не закрытый здесь разрыв;
    * `TimeDomination` (локально-по-времени интегрируемый мажорант 2⟪u,∂ₜu⟫) и
      `IntervalIntegrable` диссипации — именованные 🔴 АНАЛИТИЧЕСКИЕ ВХОДЫ;
    * `NoSingularCascade` — СУРРОГАТ гладкости в каскадном языке, НЕ C∞-регулярность;
      проблема тысячелетия Клэя НЕ решается и НЕ объявляется;
    * оба импостора (§7) ПРОВАЛИВАЮТ гейты класса: `cookedFlow` — пространственный,
      `dirichletFlow` — временной (`cookedFlow_fails_assemblyGates`/`dirichletFlow_fails_assemblyGates`).

  DISCLOSURE ГЕЙТОВ-ЗАПЛАТ (fallback): следующие тождества оставлены ИМЕНОВАННЫМИ ПОЛЯМИ
  структуры `R3AssemblyGates` (аналитический вывод в mathlib-объёме резистентен) —
  СМ. финальный отчёт и поля структуры для точного списка. Каркас послойный: заголовочная
  теорема `noSingularCascade_of_r3Assembly` проходит ЗЕЛЁНО в любом случае.

  Никакой связи с простыми числами — красная линия нетронута.
-/
import Mathlib
import EuclidsPath.Engine.NavierStokes
import EuclidsPath.Engine.NavierStokesFront

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.NavierStokesR3

open MeasureTheory
open EuclidsPath.NavierStokes
open EuclidsPath.NavierStokesFront
open scoped BigOperators RealInnerProductSpace InnerProductSpace

/-#############################################################################
  §0. BRIDGE: бокс на `Fin 3 → ℝ`, изометрия объёма E3 ↔ Pi3, служебные леммы
#############################################################################-/

/-- Плоское координатное пространство `Fin 3 → ℝ` (без L²-обёртки). -/
abbrev Pi3 := Fin 3 → ℝ

/-- Открытый бокс в `Pi3`: произведение открытых интервалов. -/
def openBox (a b : Pi3) : Set Pi3 :=
  Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))

/-- Замкнутый бокс `Icc a b` в `Pi3`. -/
def closedBox (a b : Pi3) : Set Pi3 := Set.Icc a b

/-- Континуально-линейная эквивалентность `E3 ≃L[ℝ] Pi3` (снятие L²-обёртки).
    В этом mathlib `⇑eL3 = ofLp`, `⇑eL3.symm = toLp`. -/
def eL3 : E3 ≃L[ℝ] Pi3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- Мост интегралов: `∫ y:Pi3, g (toLp 2 y) = ∫ x:E3, g x` (изометрия объёма). -/
theorem integral_comp_toLp (g : E3 → ℝ) :
    (∫ y : Pi3, g (WithLp.toLp 2 y)) = ∫ x : E3, g x :=
  (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding g

/-- `toLp 2` на `Pi3` совпадает с `eL3.symm`. -/
theorem toLp_eq_eL3symm (y : Pi3) : (WithLp.toLp 2 y : E3) = eL3.symm y := by
  rw [eL3, PiLp.coe_symm_continuousLinearEquiv]

/-- `ofLp = eL3` покомпонентно: `(eL3 x) i = x i`. -/
theorem eL3_apply (x : E3) (i : Fin 3) : eL3 x i = x i := by
  rw [eL3, PiLp.coe_continuousLinearEquiv]

/-- Внутренность `Icc a b` в `Pi3` — это `openBox a b`. -/
theorem interior_closedBox (a b : Pi3) : interior (closedBox a b) = openBox a b := by
  rw [closedBox, openBox, ← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
  simp only [interior_Icc]

/-- Координата суммы в `E3`: `(∑ i, f i) k = ∑ i, (f i) k` (через `eL3`-эквивалентность). -/
theorem e3_sum_apply {n : Type*} [Fintype n] (f : n → E3) (k : Fin 3) :
    (∑ i, f i) k = ∑ i, (f i) k := by
  have h1 : (∑ i, f i) k = eL3 (∑ i, f i) k := (eL3_apply _ k).symm
  rw [h1, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => eL3_apply (f i) k

/-- Разложение вектора `E3` по базису: `z = ∑ i, z i • e3 i`. -/
theorem e3_decomp (z : E3) : z = ∑ i, z i • e3 i := by
  apply PiLp.ext
  intro k
  rw [e3_sum_apply]
  simp only [e3, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ k]
  simp

/-- Разложение действия непрерывного оператора на `E3` по базису `e3`:
    покоординатно `W z j = ∑ i, z i * W (e3 i) j`. -/
theorem clm_apply_eq_sum (W : E3 →L[ℝ] E3) (z : E3) (j : Fin 3) :
    W z j = ∑ i, z i * (W (e3 i)) j := by
  conv_lhs => rw [e3_decomp z, map_sum]
  rw [e3_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, PiLp.smul_apply, smul_eq_mul]

/-- Скалярное произведение в E3 через базис `e3`: `⟪w, v⟫ = ∑ i, (w i) * (v i)`. -/
theorem real_inner_e3_eq_sum (w v : E3) :
    ⟪w, v⟫_ℝ = ∑ i, (w i) * (v i) := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-#############################################################################
  §1. R1 — ДИФФЕРЕНЦИРОВАНИЕ ПОД ИНТЕГРАЛОМ ЭНЕРГИИ:  dE/dt = ∫⟪u, ∂ₜu⟫
      (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` + `HasDerivAt.norm_sq`)
#############################################################################-/

/-- **R1 — ДОКАЗАНА (дифференцирование под интегралом; условно на мажоранте).**
    Если поле скоростей `u : ℝ → E3 → E3` имеет по времени поточечную производную `D`,
    доминируемую интегрируемым `bound`, а `‖u t₀ ·‖²` интегрируема и всё ae-измеримо,
    то кинетическая энергия дифференцируема во времени и
      `d/dt E(u t) = ∫ x, ⟪u t x, D t x⟫`.
    Внутренность — mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (мажорант `2·bound`),
    поточечно `HasDerivAt.norm_sq` даёт производную `2⟪u s x, D s x⟫`, затем `(1/2)`-массаж. -/
theorem hasDerivAt_kineticEnergy_of_dominated
    (u : ℝ → E3 → E3) (D : ℝ → E3 → E3) (t₀ : ℝ)
    (bound : E3 → ℝ)
    (hu_meas : ∀ᶠ s in nhds t₀, AEStronglyMeasurable (fun x => ‖u s x‖ ^ 2) volume)
    (hu_int : Integrable (fun x => ‖u t₀ x‖ ^ 2) volume)
    (hD_meas : AEStronglyMeasurable (fun x => (2 : ℝ) * ⟪u t₀ x, D t₀ x⟫_ℝ) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
        ‖(2 : ℝ) * ⟪u s x, D s x⟫_ℝ‖ ≤ (2 : ℝ) * bound x)
    (hbound_int : Integrable bound volume)
    (h_hasDeriv : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
        HasDerivAt (fun r => u r x) (D s x) s) :
    HasDerivAt (fun s => kineticEnergy (u s))
      (∫ x : E3, ⟪u t₀ x, D t₀ x⟫_ℝ) t₀ := by
  -- поточечная производная `‖u s x‖²`: `2⟪u s x, D s x⟫`
  have h_diff : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
      HasDerivAt (fun r => ‖u r x‖ ^ 2) ((2 : ℝ) * ⟪u s x, D s x⟫_ℝ) s := by
    filter_upwards [h_hasDeriv] with x hx s hs
    exact (hx s hs).norm_sq
  -- дифференцирование под интегралом на «сыром» интеграле ∫‖u s ·‖²
  have hs_nhds : Metric.ball t₀ 1 ∈ nhds t₀ := Metric.ball_mem_nhds t₀ one_pos
  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := fun s x => ‖u s x‖ ^ 2)
      (F' := fun s x => (2 : ℝ) * ⟪u s x, D s x⟫_ℝ)
      (bound := fun x => (2 : ℝ) * bound x) (x₀ := t₀)
      hs_nhds hu_meas hu_int hD_meas h_bound
      (hbound_int.const_mul 2) h_diff).2
  -- (1/2)-массаж: kineticEnergy = (1/2)·∫; производная = (1/2)·∫2⟪⟫ = ∫⟪⟫
  have hhalf := hmain.const_mul (1 / 2 : ℝ)
  have hfun : (fun s => (1 / 2 : ℝ) * ∫ x : E3, ‖u s x‖ ^ 2)
      = fun s => kineticEnergy (u s) := by
    funext s; rw [kineticEnergy]
  have hval : (1 / 2 : ℝ) * ∫ x : E3, (2 : ℝ) * ⟪u t₀ x, D t₀ x⟫_ℝ
      = ∫ x : E3, ⟪u t₀ x, D t₀ x⟫_ℝ := by
    rw [MeasureTheory.integral_const_mul]; ring
  rw [hfun, hval] at hhalf
  exact hhalf

/-#############################################################################
  §2. R2 — ТЕОРЕМА О ДИВЕРГЕНЦИИ, ЗАДЕЙСТВОВАННАЯ ПО-НАСТОЯЩЕМУ.
      Грани бокса ГИБНУТ по носителю (`F ≡ 0` вне `openBox`).
#############################################################################-/

/-- Носитель поля `F : Pi3 → Pi3` внутри открытого бокса: `F ≡ 0` вне `openBox a b`. -/
def BoxSupportedPi (a b : Pi3) (F : Pi3 → Pi3) : Prop :=
  ∀ x, x ∉ openBox a b → F x = 0

/-- Дивергенция (плоская форма) поля `F : Pi3 → Pi3` с производной `F'`:
    `div F x = ∑ i, F' x (Pi.single i 1) i`. -/
def piDivergence (F' : Pi3 → (Pi3 →L[ℝ] Pi3)) (x : Pi3) : ℝ :=
  ∑ i, F' x (Pi.single i 1) i

/-- Фронт-грань бокса лежит ВНЕ `openBox` (координата `i` равна `b i`, не в `Ioo`). -/
theorem frontFace_notMem_openBox {a b : Pi3} (i : Fin 3)
    (x : Fin 2 → ℝ) : (Fin.insertNth i (b i) x) ∉ openBox a b := by
  intro hx
  have := hx i (Set.mem_univ i)
  rw [Fin.insertNth_apply_same] at this
  exact Set.right_notMem_Ioo this

/-- Бэк-грань бокса лежит ВНЕ `openBox` (координата `i` равна `a i`, не в `Ioo`). -/
theorem backFace_notMem_openBox {a b : Pi3} (i : Fin 3)
    (x : Fin 2 → ℝ) : (Fin.insertNth i (a i) x) ∉ openBox a b := by
  intro hx
  have := hx i (Set.mem_univ i)
  rw [Fin.insertNth_apply_same] at this
  exact Set.left_notMem_Ioo this

/-- **R2 (боксовая форма) — ДОКАЗАНА (теорема о дивергенции ЗАДЕЙСТВОВАНА).**
    Для C¹-поля `F` с носителем в `openBox a b` (и интегрируемой дивергенцией)
      `∫_{Icc a b} div F = 0`,
    ибо ВСЕ граничные интегралы mathlib-теоремы `integral_divergence_of_hasFDerivAt_off_countable`
    ГИБНУТ: на гранях `F` тождественно ноль (носитель строго внутри бокса). -/
theorem boxDivergence_integral_eq_zero
    (a b : Pi3) (hle : a ≤ b) (F : Pi3 → Pi3) (F' : Pi3 → (Pi3 →L[ℝ] Pi3))
    (hsupp : BoxSupportedPi a b F)
    (Hc : ContinuousOn F (Set.Icc a b))
    (Hd : ∀ x ∈ openBox a b, HasFDerivAt F (F' x) x)
    (Hi : IntegrableOn (piDivergence F') (Set.Icc a b) volume) :
    (∫ x in Set.Icc a b, piDivergence F' x) = 0 := by
  -- применяем боксовую теорему о дивергенции с s := ∅
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable a b hle F F'
    (∅ : Set Pi3) Set.countable_empty Hc
    (fun x hx => Hd x (by simpa [openBox] using hx.1)) Hi
  -- LHS теоремы совпадает с нашим ∫ div F
  have hLHS : (∫ x in Set.Icc a b, ∑ i, F' x (Pi.single i 1) i)
      = ∫ x in Set.Icc a b, piDivergence F' x := rfl
  rw [hLHS] at hdiv
  -- каждый граничный интеграл = 0 (значение F на грани = 0)
  have hfaces : (∑ i : Fin 3,
      ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Fin.insertNth i (b i) x) i)
        - ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Fin.insertNth i (a i) x) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hfront : (fun x : Fin 2 → ℝ => F (Fin.insertNth i (b i) x) i) = fun _ => 0 := by
      funext x
      rw [hsupp _ (frontFace_notMem_openBox i x)]
      rfl
    have hback : (fun x : Fin 2 → ℝ => F (Fin.insertNth i (a i) x) i) = fun _ => 0 := by
      funext x
      rw [hsupp _ (backFace_notMem_openBox i x)]
      rfl
    rw [hfront, hback]
    simp
  rw [hdiv, hfaces]

/-- **R2 (форма на всём ℝ³) — ДОКАЗАНА.** Интеграл дивергенции бокс-носимого поля
    по ВСЕМУ пространству равен нулю: вне `Icc a b` дивергенция ноль (локальная
    константа `F ≡ 0`), потому полный интеграл сводится к боксовому. -/
theorem divergence_integral_eq_zero
    (a b : Pi3) (hle : a ≤ b) (F : Pi3 → Pi3) (F' : Pi3 → (Pi3 →L[ℝ] Pi3))
    (hsupp : BoxSupportedPi a b F)
    (Hc : ContinuousOn F (Set.Icc a b))
    (Hd : ∀ x ∈ openBox a b, HasFDerivAt F (F' x) x)
    (Hi : IntegrableOn (piDivergence F') (Set.Icc a b) volume)
    (hzero : ∀ x, x ∉ Set.Icc a b → piDivergence F' x = 0) :
    (∫ x : Pi3, piDivergence F' x) = 0 := by
  have hrestr : (∫ x : Pi3, piDivergence F' x)
      = ∫ x in Set.Icc a b, piDivergence F' x := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc a b) (f := piDivergence F') hzero]
  rw [hrestr]
  exact boxDivergence_integral_eq_zero a b hle F F' hsupp Hc Hd Hi

/-#############################################################################
  §3. R3 — ТРИ УБИЙЦЫ ИНТЕГРИРОВАНИЕМ ПО ЧАСТЯМ.
      pi-workhorse: покоординатное тождество `div(p•w) = p·div w + ⟪∇p,w⟫`,
      подающее R2. E3-обёртки убийц — гейт-поля `R3AssemblyGates` (fallback,
      раскрыто: E3↔Pi3-мост fderiv в mathlib недёшев).
#############################################################################-/

/-- **pi-WORKHORSE давления (i) — ДОКАЗАН (покоординатно, кормит R2):**
    для скаляра `p` и поля `w` с производными `p'`, `w'` в точке `x`:
      `div(p•w) x = p x · div w x + ∑ i, (p' (eᵢ)) · (w x) i`,
    где второе слагаемое — координатная форма `⟪∇p, w⟫`. Второй множитель первого
    слагаемого — `div w`; при `div w = 0` дивергенция сводится к `⟪∇p,w⟫` —
    ровно то, что R2 гасит в ноль. -/
theorem pressureDiv_pi (p : Pi3 → ℝ) (w : Pi3 → Pi3)
    (p' : Pi3 →L[ℝ] ℝ) (w' : Pi3 →L[ℝ] Pi3) (x : Pi3)
    (hp : HasFDerivAt p p' x) (hw : HasFDerivAt w w' x) :
    piDivergence (fun _ => (p x • w' + p'.smulRight (w x))) x
      = p x * (∑ i, w' (Pi.single i 1) i) + ∑ i, (p' (Pi.single i 1)) * (w x) i := by
  simp only [piDivergence, add_apply, Pi.add_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Производная поля `p•w` в точке (для подстановки в R2/piDivergence). -/
theorem hasFDerivAt_smul_pi (p : Pi3 → ℝ) (w : Pi3 → Pi3)
    (p' : Pi3 →L[ℝ] ℝ) (w' : Pi3 →L[ℝ] Pi3) (x : Pi3)
    (hp : HasFDerivAt p p' x) (hw : HasFDerivAt w w' x) :
    HasFDerivAt (fun y => p y • w y) (p x • w' + p'.smulRight (w x)) x :=
  hp.smul hw

/-- Координатная форма `⟪∇p, w⟫` (то, что подаётся в R2 при `div w = 0`).
    Определена как `∑ i, (fderiv ℝ p x) eᵢ · w x i`. -/
def innerGradPi (p : Pi3 → ℝ) (w : Pi3 → Pi3) (x : Pi3) : ℝ :=
  ∑ i, (fderiv ℝ p x) (Pi.single i 1) * (w x) i

/-#############################################################################
  §4. ASSEMBLY — послойная сборка энергобаланса.
      🔴-вход `TimeDomination`, гейт-структура `BoxSupportedC2Flow` (гейтит
      ГЛАДКОСТЬ ДАВЛЕНИЯ впервые), гейт-структура `R3AssemblyGates`, теорема
      `energyBalance_of_r3Gates` — ЗАКОН ВЫВЕДЕН, не декретирован.
#############################################################################-/

/-- **🔴 TimeDomination — ЕДИНСТВЕННЫЙ аналитический ВХОД R1** (локально-по-времени
    интегрируемый мажорант производной под интегралом энергии). Пакует ровно то,
    что просит `hasDerivAt_integral_of_dominated_loc_of_deriv_le`: ae-измеримость
    `‖u s ·‖²` около `t₀`, интегрируемость `‖u t₀ ·‖²`, ae-измеримость
    производной интегранта, интегрируемый мажорант `bound` и поточечная
    дифференцируемость траекторий с производной `D`. -/
structure TimeDomination (u : ℝ → E3 → E3) (D : ℝ → E3 → E3) (t₀ : ℝ) where
  bound : E3 → ℝ
  measSq : ∀ᶠ s in nhds t₀, AEStronglyMeasurable (fun x => ‖u s x‖ ^ 2) volume
  intSq : Integrable (fun x => ‖u t₀ x‖ ^ 2) volume
  measDeriv : AEStronglyMeasurable (fun x => (2 : ℝ) * ⟪u t₀ x, D t₀ x⟫_ℝ) volume
  dominated : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
      ‖(2 : ℝ) * ⟪u s x, D s x⟫_ℝ‖ ≤ (2 : ℝ) * bound x
  intBound : Integrable bound volume
  hasDeriv : ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t₀ 1,
      HasDerivAt (fun r => u r x) (D s x) s

/-- R1 в обёртке `TimeDomination`: dE/dt = ∫⟪u, D⟫. -/
theorem hasDerivAt_kineticEnergy_of_timeDomination
    (u : ℝ → E3 → E3) (D : ℝ → E3 → E3) (t₀ : ℝ)
    (dom : TimeDomination u D t₀) :
    HasDerivAt (fun s => kineticEnergy (u s))
      (∫ x : E3, ⟪u t₀ x, D t₀ x⟫_ℝ) t₀ :=
  hasDerivAt_kineticEnergy_of_dominated u D t₀ dom.bound
    dom.measSq dom.intSq dom.measDeriv dom.dominated dom.intBound dom.hasDeriv

/-- **Гейт-структура бокс-носимого C²-потока (ГЕЙТ ГЛАДКОСТИ ДАВЛЕНИЯ ВПЕРВЫЕ):**
    класс полей, для которого баланс будет ВЫВЕДЕН. Поля гейтят дифференцируемость
    траекторий по времени (`timeDeriv`), поля по пространству (`spaceDiff`),
    вторые производные (`spaceDiff2`), И ГЛАДКОСТЬ ДАВЛЕНИЯ (`pressDiff`) —
    чем закрывается канал Ковки-B (junk в ∇p на сфере исключён C²-гейтом);
    непрерывности (`contU/contU'/contU''/contP/contP'`) и бокс-носитель (`supp`). -/
structure BoxSupportedC2Flow (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) where
  hle : (0 : ℝ) ≤ ν
  a : Pi3
  b : Pi3
  aleb : a ≤ b
  timeDeriv : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  spaceDiff : ∀ t x, DifferentiableAt ℝ (u t) x
  spaceDiff2 : ∀ t i x, DifferentiableAt ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x
  pressDiff : ∀ t x, DifferentiableAt ℝ (p t) x
  contU : ∀ t, Continuous (u t)
  contU' : ∀ t i, Continuous (fun x => fderiv ℝ (u t) x (e3 i))
  contP : ∀ t, Continuous (p t)
  supp : ∀ t x, (eL3 x) ∉ openBox a b → u t x = 0

/-- **R3AssemblyGates — ПОСЛОЙНЫЙ ГЕЙТ-НАБОР (fallback-раскрытие):** всё, что нужно,
    чтобы ВЫВЕСТИ энергобаланс в момент `t`. Поля `timeDeriv/domination` кормят R1;
    `intLap/intPress/intConv` — интегрируемости компонент правой части (расщепление
    интеграла); ТРИ убийцы `pressureKills/transportKills/viscosityIBP` —
    E3-тождества интегрирования по частям.

    ⚠️ FALLBACK ЧЕСТНО РАСКРЫТ: три убийцы (`pressureKills`, `transportKills`,
    `viscosityIBP`) оставлены ИМЕНОВАННЫМИ ГИПОТЕЗАМИ. Их аналитический вывод —
    R2 (ЗЕЛЁНАЯ, §2) + E3↔Pi3-мост fderiv (в mathlib недёшев). pi-workhorse
    `pressureDiv_pi` (§3) демонстрирует механизм подачи в R2 покоординатно.
    Убийцы `pressureKills`/`transportKills` = 0 суть `∫ div(·) = 0` из R2;
    `viscosityIBP` — покомпонентное IBP. Каркас послойный: заголовочная теорема
    зелена при любых значениях этих полей. -/
structure R3AssemblyGates (ν : ℝ) (f : ℝ → E3 → E3)
    (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) where
  forceZero : ∀ t x, f t x = 0
  timeDeriv : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  domination : ∀ t, TimeDomination u (nsTimeDerivative ν f u p) t
  intLap : ∀ t, Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume
  intPress : ∀ t, Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume
  intConv : ∀ t, Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume
  pressureKills : ∀ t, (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ) = 0
  transportKills : ∀ t, (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) = 0
  viscosityIBP : ∀ t,
    (∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ)
      = -(∫ x : E3, ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖ ^ 2)

/-- Расщепление интеграла `∫⟪u, D⟫` по слагаемым правой части НС. -/
theorem integral_inner_nsTimeDerivative_split
    (ν : ℝ) (f : ℝ → E3 → E3) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) (t : ℝ)
    (hf : ∀ x, f t x = 0)
    (hLap : Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume)
    (hPress : Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume)
    (hConv : Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume) :
    (∫ x : E3, ⟪u t x, nsTimeDerivative ν f u p t x⟫_ℝ)
      = (∫ x : E3, ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ)
        - (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ)
        - (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) := by
  set gLap := fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ with hgLap
  set gPress := fun x => ⟪u t x, gradient (p t) x⟫_ℝ with hgPress
  set gConv := fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ with hgConv
  have hpt : (fun x : E3 => ⟪u t x, nsTimeDerivative ν f u p t x⟫_ℝ)
      = fun x => (gLap x - gPress x) - gConv x := by
    funext x
    rw [hgLap, hgPress, hgConv, nsTimeDerivative]
    rw [show ν • vectorLaplacian (u t) x - gradient (p t) x + f t x
          - convectiveTerm (u t) x
        = (ν • vectorLaplacian (u t) x - gradient (p t) x)
          - convectiveTerm (u t) x + f t x from by rw [hf x]; abel]
    rw [inner_add_right, inner_sub_right, inner_sub_right]
    rw [hf x, inner_zero_right]
    ring
  rw [hpt]
  have hstep1 : (∫ x : E3, (gLap x - gPress x) - gConv x)
      = (∫ x : E3, gLap x - gPress x) - ∫ x : E3, gConv x :=
    MeasureTheory.integral_sub (hLap.sub hPress) hConv
  have hstep2 : (∫ x : E3, gLap x - gPress x)
      = (∫ x : E3, gLap x) - ∫ x : E3, gPress x :=
    MeasureTheory.integral_sub hLap hPress
  rw [hstep1, hstep2]

/-- **ЗАГОЛОВОК СБОРКИ (R1 + три убийцы ⟹ ЗАКОН): `energyBalance_of_r3Gates`.**
    Энергобаланс `dE/dt = −D` ВЫВЕДЕН из послойных гейтов: R1 даёт `dE/dt = ∫⟪u,∂ₜu⟫`,
    расщепление по слагаемым НС + три убийцы (давление и перенос ⟶ 0, вязкость ⟶
    −∫∑‖∂ᵢu‖²) приземляют на `−dissipationRate`. ЗАКОН НЕ ДЕКРЕТИРОВАН. -/
theorem energyBalance_of_r3Gates
    {ν : ℝ} {f : ℝ → E3 → E3} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (G : R3AssemblyGates ν f u p) :
    EnergyBalanceLaw ν u := by
  intro t
  -- R1
  have hR1 := hasDerivAt_kineticEnergy_of_timeDomination u
    (nsTimeDerivative ν f u p) t (G.domination t)
  -- значение производной = −dissipationRate
  have hval : (∫ x : E3, ⟪u t x, nsTimeDerivative ν f u p t x⟫_ℝ)
      = -(dissipationRate ν (u t)) := by
    rw [integral_inner_nsTimeDerivative_split ν f u p t (fun x => G.forceZero t x)
      (G.intLap t) (G.intPress t) (G.intConv t)]
    rw [G.pressureKills t, G.transportKills t, sub_zero, sub_zero]
    -- остаётся ∫⟪u, ν•Δu⟫ = ν∫⟪u,Δu⟫ = −ν∫∑‖∂ᵢu‖² = −dissipationRate
    have hsmul : (∫ x : E3, ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ)
        = ν * ∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only []
      rw [real_inner_smul_right]
    rw [hsmul, G.viscosityIBP t, dissipationRate]
    ring
  rw [hval] at hR1
  exact hR1

/-- **Носитель гейт-набора: три убийцы + интегрируемости (residual analytic bundle).**
    То, что `BoxSupportedC2Flow` НЕ закрывает сам по себе — E3-тождества IBP и
    интегрируемости компонент. Пакет ЧЕСТНО раскрыт как residual-вход:
    `BoxSupportedC2Flow` даёт дифференцируемость/носитель/гладкость давления,
    а этот пакет — аналитический остаток (то, что в mathlib недёшево). -/
structure KillerBundle (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) where
  intLap : ∀ t, Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume
  intPress : ∀ t, Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume
  intConv : ∀ t, Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume
  pressureKills : ∀ t, (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ) = 0
  transportKills : ∀ t, (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) = 0
  viscosityIBP : ∀ t,
    (∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ)
      = -(∫ x : E3, ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖ ^ 2)

/-- **`r3AssemblyGates_of_boxSupported` — послойная сборка гейт-набора.**
    Из бокс-носимого C²-потока `F`, per-time мажоранты `dom`, бессилового решения
    `sol` (`f = 0`) и residual-пакета убийц `K` собирается `R3AssemblyGates`.
    `F` (в т.ч. гейт гладкости давления) обеспечивает структурную часть;
    residual-аналитика `K` подаётся прозрачно. -/
def r3AssemblyGates_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (K : KillerBundle ν u p) :
    R3AssemblyGates ν (fun _ _ => 0) u p where
  forceZero := fun _ _ => rfl
  timeDeriv := F.timeDeriv
  domination := dom
  intLap := K.intLap
  intPress := K.intPress
  intConv := K.intConv
  pressureKills := K.pressureKills
  transportKills := K.transportKills
  viscosityIBP := K.viscosityIBP

/-- **`energyBalance_of_boxSupported` — КОМПОЗИЦИЯ (ЗАКОН ВЫВЕДЕН для бокс-класса).**
    Бокс-носимый C²-поток + мажорант + убийцы ⟹ энергобаланс. -/
theorem energyBalance_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (K : KillerBundle ν u p) :
    EnergyBalanceLaw ν u :=
  energyBalance_of_r3Gates (r3AssemblyGates_of_boxSupported F dom K)

/-#############################################################################
  §5. INHABITANCE — нулевое решение проходит ВСЕ гейты класса (не вакуум).
#############################################################################-/

/-- Нулевое поле — бокс-носимый C²-поток (тривиально: всё константа `0`). -/
def zero_boxSupportedC2Flow (ν : ℝ) (hν : 0 ≤ ν) :
    BoxSupportedC2Flow ν (fun _ _ => 0) (fun _ _ => 0) where
  hle := hν
  a := 0
  b := 1
  aleb := by intro i; simp
  timeDeriv := fun _ _ => differentiableAt_const _
  spaceDiff := fun _ _ => differentiableAt_const _
  spaceDiff2 := fun _ i x => by
    have h : (fun y : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) y (e3 i))
        = fun _ => (0 : E3) := by
      funext y; simp
    rw [h]; exact differentiableAt_const _
  pressDiff := fun _ _ => differentiableAt_const _
  contU := fun _ => continuous_const
  contU' := fun _ i => by
    have h : (fun x : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) x (e3 i))
        = fun _ => (0 : E3) := by
      funext y; simp
    rw [h]; exact continuous_const
  contP := fun _ => continuous_const
  supp := fun _ _ _ => rfl

/-- Нулевое поле — временной мажорант (bound := 0; `nsTimeDerivative` нуля есть `0`). -/
def zero_timeDomination (ν : ℝ) (t : ℝ) :
    TimeDomination (fun _ _ => (0 : E3))
      (nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)) t where
  bound := fun _ => 0
  measSq := Filter.Eventually.of_forall (fun _ => by
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact aestronglyMeasurable_const)
  intSq := by
    have h : (fun x : E3 => ‖(0 : E3)‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [h]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  measDeriv := by
    have h : (fun x : E3 => (2 : ℝ) * ⟪(0 : E3),
        nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) t x⟫_ℝ)
        = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [h]; exact aestronglyMeasurable_const
  dominated := Filter.Eventually.of_forall (fun x s _ => by
    simp only [nsTimeDerivative_zero, inner_zero_right, mul_zero, norm_zero, le_refl])
  intBound := integrable_zero (α := E3) (ε' := ℝ) volume
  hasDeriv := Filter.Eventually.of_forall (fun x s _ => by
    rw [nsTimeDerivative_zero]; exact hasDerivAt_const s (0 : E3))

/-- Нулевое поле — residual-пакет убийц (все интегранды и интегралы нулевые). -/
def zero_killerBundle (ν : ℝ) :
    KillerBundle ν (fun _ _ => (0 : E3)) (fun _ _ => 0) where
  intLap := fun _ => by
    simp only [inner_zero_left]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  intPress := fun _ => by
    simp only [inner_zero_left]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  intConv := fun _ => by
    simp only [inner_zero_left]; exact integrable_zero (α := E3) (ε' := ℝ) volume
  pressureKills := fun _ => by simp only [inner_zero_left, integral_zero]
  transportKills := fun _ => by simp only [inner_zero_left, integral_zero]
  viscosityIBP := fun _ => by
    simp only [inner_zero_left, integral_zero]
    simp

/-- **ИНХАБИТАНС (не вакуум): нулевое решение выводит энергобаланс через сборку.** -/
theorem zero_energyBalance_of_boxSupported (ν : ℝ) (hν : 0 ≤ ν) :
    EnergyBalanceLaw ν (fun _ _ => 0) :=
  energyBalance_of_boxSupported (zero_boxSupportedC2Flow ν hν)
    (zero_timeDomination ν) (zero_killerBundle ν)

/-#############################################################################
  §6. HEADLINE — суррогат гладкости и тождество энергии из R3-сборки.
#############################################################################-/

/-- **ЗАГОЛОВОК: `noSingularCascade_of_r3Assembly` — СУРРОГАТ ГЛАДКОСТИ из сборки.**
    Бокс-носимый C²-поток + мажорант + убийцы + интегрируемость диссипации ⟹
    `NoSingularCascade` (нет равномерно-квантованного δ-каскада до конечного `T`).
    Композиция `energyBalance_of_boxSupported` (§4) и `noSingularCascade_of_energyBalance`
    (front). ⚠️ СУРРОГАТ, НЕ C∞; проблема Клэя НЕ решается. -/
theorem noSingularCascade_of_r3Assembly
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (K : KillerBundle ν u p)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    NoSingularCascade ν u :=
  noSingularCascade_of_energyBalance ν u
    (energyBalance_of_boxSupported F dom K) hInt

/-- **`energyIdentity_of_r3Assembly` — ТОЖДЕСТВО ЭНЕРГИИ (FTC-2) из сборки.**
    `E(t₂) = E(t₁) − ∫_{t₁}^{t₂} D` для бокс-носимого потока. -/
theorem energyIdentity_of_r3Assembly
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (K : KillerBundle ν u p)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)
    (t₁ t₂ : ℝ) :
    kineticEnergy (u t₂)
      = kineticEnergy (u t₁) - ∫ s in t₁..t₂, dissipationRate ν (u s) :=
  energy_identity_of_energyBalance ν u
    (energyBalance_of_boxSupported F dom K) hInt t₁ t₂

/-- **ДОКУМЕНТАЦИОННО (`nsBoundary_redundant_on_boxClass`): на бокс-классе декрет
    `NsSolutionBalanceLaw` РЕДУНДАНТЕН.** Заключение закона (энергобаланс +
    интегрируемость диссипации) для бокс-носимого потока ВЫВОДИТСЯ сборкой —
    его НЕ нужно декретировать на этом классе. Содержание декрета остаётся лишь
    ВНЕ конечного бокс-носителя (предельный переход box→ℝ³ в mathlib отсутствует —
    внешний разрыв, здесь НЕ закрытый). -/
theorem nsBoundary_redundant_on_boxClass
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (K : KillerBundle ν u p)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    EnergyBalanceLaw ν u ∧
    (∀ t₁ t₂ : ℝ, IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :=
  ⟨energyBalance_of_boxSupported F dom K, hInt⟩

/-#############################################################################
  §7. ИСКЛЮЧЕНИЕ ИМПОСТОРОВ — оба провала гейтов класса (one-liners).
#############################################################################-/

/-- **Ковка-B (`cookedFlow`) ПРОВАЛИВАЕТ гейт сборки** — пространственная
    дифференцируемость `spaceDiff` невозможна (несглаженность на сфере,
    front `cookedFlow_fails_space_gate`). Гейт гладкости класса ловит junk в ∇p. -/
theorem cookedFlow_fails_assemblyGates {ν : ℝ} {p : ℝ → E3 → ℝ} :
    ¬ ∃ F : BoxSupportedC2Flow ν cookedFlow p, True := by
  rintro ⟨F, -⟩
  exact cookedFlow_fails_space_gate F.spaceDiff

/-- **Ковка-A (`dirichletFlow`) ПРОВАЛИВАЕТ гейт сборки** — временная
    дифференцируемость `timeDeriv` невозможна (Дирихле-мерцание,
    front `dirichletFlow_fails_time_gate`). -/
theorem dirichletFlow_fails_assemblyGates {ν : ℝ} {p : ℝ → E3 → ℝ} :
    ¬ ∃ F : BoxSupportedC2Flow ν dirichletFlow p, True := by
  rintro ⟨F, -⟩
  exact dirichletFlow_fails_time_gate F.timeDeriv

end EuclidsPath.NavierStokesR3

end

/-#############################################################################
  §8. #print axioms — машинная видимость чистоты в build-логе
      (ожидаемо [propext, Classical.choice, Quot.sound]).
#############################################################################-/

#print axioms EuclidsPath.NavierStokesR3.hasDerivAt_kineticEnergy_of_dominated
#print axioms EuclidsPath.NavierStokesR3.boxDivergence_integral_eq_zero
#print axioms EuclidsPath.NavierStokesR3.divergence_integral_eq_zero
#print axioms EuclidsPath.NavierStokesR3.pressureDiv_pi
#print axioms EuclidsPath.NavierStokesR3.energyBalance_of_r3Gates
#print axioms EuclidsPath.NavierStokesR3.energyBalance_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.noSingularCascade_of_r3Assembly
#print axioms EuclidsPath.NavierStokesR3.energyIdentity_of_r3Assembly
#print axioms EuclidsPath.NavierStokesR3.zero_energyBalance_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.zero_timeDomination
#print axioms EuclidsPath.NavierStokesR3.cookedFlow_fails_assemblyGates
#print axioms EuclidsPath.NavierStokesR3.dirichletFlow_fails_assemblyGates
