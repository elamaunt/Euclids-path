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
    * R3 — ТРИ убийцы интегрированием по частям ДОКАЗАНЫ (не гипотезы!) через
      МАСТЕР-ЛЕММУ `integral_e3_divergence_eq_zero` (§3bis: E3↔Pi3-мост fderiv
      comp-цепью `ContinuousLinearEquiv`/`HasFDerivAt.comp`, подающий R2):
      (i) давление ∫⟪w,∇p⟫ = 0 (`pressureKills_of_boxSupported`);
      (ii) перенос ∫⟪w,(w·∇)w⟫ = 0 (`transportKills_of_boxSupported`);
      (iii) вязкость ∫⟪w,Δw⟫ = −∫∑‖∂ᵢw‖² (`viscosityIBP_of_boxSupported`,
      покомпонентное IBP). Все три выведены из `BoxSupportedC2Flow` + `IsNSSolution`;
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

  ТРИ УБИЙЦЫ ЗАКРЫТЫ (было fallback — стало ДОКАЗАНО): интеграл R3 доведён «в точности».
  `energyBalance_of_boxSupported` / `noSingularCascade_of_r3Assembly` БОЛЬШЕ НЕ берут
  `KillerBundle` — вместо него внутри строится `killerBundle_of_boxSupported F sol` из
  мастер-леммы §3bis. ОСТАВШИЕСЯ честные входы: ТОЛЬКО `TimeDomination` (🔴 R1),
  `IntervalIntegrable` диссипации и предел box→ℝ³ (внешний, в mathlib отсутствует).
  Слои `KillerBundle`/`R3AssemblyGates` СОХРАНЕНЫ как переиспользуемая абстракция
  (их поля теперь ВЫВОДИМЫ), но заголовочные теоремы их напрямую не требуют.

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
  §3bis. МАСТЕР-ЛЕММА E3↔Pi3: ∫_{ℝ³} div_{E3} G = 0 для бокс-носимого C¹-поля.
      Это мост E3→Pi3 fderiv (comp-цепь `ContinuousLinearEquiv.comp`+`HasFDerivAt.comp`),
      подающий R2 (§2). Все ТРИ убийцы редуцируются к нему. ДОКАЗАНА (не гейт).
#############################################################################-/

/-- `eL3.symm (Pi.single i 1) = e3 i` (снятие L²-обёртки со стандартного орта). -/
theorem eL3symm_single (i : Fin 3) : eL3.symm (Pi.single i 1) = e3 i := by
  rw [← toLp_eq_eL3symm]
  simp [e3, EuclideanSpace.single]

/-- Открытый бокс лежит в замкнутом: `openBox a b ⊆ Icc a b`. -/
theorem openBox_subset_Icc (a b : Pi3) : openBox a b ⊆ Set.Icc a b := by
  rw [openBox, ← Set.pi_univ_Icc]
  intro z hz i hi
  exact Set.Ioo_subset_Icc_self (hz i hi)

/-- **МАСТЕР-ЛЕММА R3 — ДОКАЗАНА (E3↔Pi3-мост, кормит R2).**
    Для C¹-поля `G : E3 → E3` с производной `G'` (всюду), с непрерывной
    E3-дивергенцией `x ↦ ∑ i, G' x (e3 i) i` и с носителем в боксе (`G ≡ 0`, когда
    `eL3 x ∉ openBox a b`) интеграл дивергенции по ВСЕМУ `E3` равен нулю:
      `∫ x:E3, (∑ i, G' x (e3 i) i) = 0`.
    Механизм: перенос поля на `Pi3` через `eL3` (`F z := eL3 (G (eL3.symm z))`,
    `F' z := eL3 ∘SL (G' (eL3.symm z)) ∘SL eL3.symm`), тождество
    `piDivergence F' z = ∑ i, G' (eL3.symm z) (e3 i) i` (через `eL3symm_single`),
    мост объёма `integral_comp_toLp`, затем R2 `divergence_integral_eq_zero`.
    ВСЕ ТРИ убийцы (давление/перенос/вязкость) — частные случаи. -/
theorem integral_e3_divergence_eq_zero
    (a b : Pi3) (hle : a ≤ b) (G : E3 → E3) (G' : E3 → E3 →L[ℝ] E3)
    (hG : ∀ x, HasFDerivAt G (G' x) x)
    (hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i))
    (hsupp : ∀ x : E3, eL3 x ∉ openBox a b → G x = 0) :
    (∫ x : E3, ∑ i, (G' x (e3 i)) i) = 0 := by
  set F : Pi3 → Pi3 := fun z => eL3 (G (eL3.symm z)) with hF
  set F' : Pi3 → (Pi3 →L[ℝ] Pi3) := fun z =>
    (eL3 : E3 →L[ℝ] Pi3).comp ((G' (eL3.symm z)).comp (eL3.symm : Pi3 →L[ℝ] E3)) with hF'
  have hGcont : Continuous G := continuous_iff_continuousAt.mpr fun x => (hG x).continuousAt
  -- перенос производной: F' — производная F всюду (comp-цепь)
  have hFderiv : ∀ z, HasFDerivAt F (F' z) z := by
    intro z
    have h1 : HasFDerivAt (⇑eL3.symm) (eL3.symm : Pi3 →L[ℝ] E3) z := eL3.symm.hasFDerivAt
    have h2 : HasFDerivAt G (G' (eL3.symm z)) (eL3.symm z) := hG (eL3.symm z)
    have h3 : HasFDerivAt (⇑eL3) (eL3 : E3 →L[ℝ] Pi3) (G (eL3.symm z)) := eL3.hasFDerivAt
    exact (h3.comp z (h2.comp z h1))
  -- КЛЮЧЕВОЕ тождество: piDivergence F' z = ∑ i, G' (eL3.symm z) (e3 i) i
  have hpiDiv : ∀ z, piDivergence F' z = ∑ i, (G' (eL3.symm z) (e3 i)) i := by
    intro z
    unfold piDivergence
    apply Finset.sum_congr rfl
    intro i _
    show ((eL3 : E3 →L[ℝ] Pi3).comp ((G' (eL3.symm z)).comp (eL3.symm : Pi3 →L[ℝ] E3)))
        (Pi.single i 1) i = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [eL3_apply, eL3symm_single]
  -- мост объёма: ∫ x:E3 = ∫ y:Pi3 piDivergence
  have hbridge : (∫ x : E3, ∑ i, (G' x (e3 i)) i)
      = ∫ y : Pi3, piDivergence F' y := by
    rw [← integral_comp_toLp (fun x => ∑ i, (G' x (e3 i)) i)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    rw [hpiDiv]
    show (∑ i, (G' (WithLp.toLp 2 y) (e3 i)) i) = ∑ i, (G' (eL3.symm y) (e3 i)) i
    rw [toLp_eq_eL3symm]
  rw [hbridge]
  -- носитель на Pi3
  have hFsupp : BoxSupportedPi a b F := by
    intro z hz
    show eL3 (G (eL3.symm z)) = 0
    have : eL3 (eL3.symm z) ∉ openBox a b := by
      rw [ContinuousLinearEquiv.apply_symm_apply]; exact hz
    rw [hsupp _ this]; simp
  -- непрерывность дивергенции на Pi3 (для интегрируемости)
  have hcontPi : Continuous (piDivergence F') := by
    have heq : (fun z => piDivergence F' z)
        = (fun x : E3 => ∑ i, (G' x (e3 i)) i) ∘ (eL3.symm) := by
      funext z; rw [hpiDiv]; rfl
    rw [show (piDivergence F') = (fun z => piDivergence F' z) from rfl, heq]
    exact hcont.comp eL3.symm.continuous
  have Hi : IntegrableOn (piDivergence F') (Set.Icc a b) volume :=
    hcontPi.continuousOn.integrableOn_compact isCompact_Icc
  have HcF : ContinuousOn F (Set.Icc a b) :=
    (eL3.continuous.comp (hGcont.comp eL3.symm.continuous)).continuousOn
  have Hd : ∀ x ∈ openBox a b, HasFDerivAt F (F' x) x := fun x _ => hFderiv x
  -- вне Icc: F локально ноль ⟹ F' = 0 ⟹ piDivergence F' = 0
  have hzero : ∀ y, y ∉ Set.Icc a b → piDivergence F' y = 0 := by
    intro y hy
    have hFev : F =ᶠ[nhds y] fun _ => 0 := by
      apply Filter.eventuallyEq_of_mem
        (isOpen_compl_iff.mpr isClosed_Icc |>.mem_nhds hy)
      intro z hz
      show F z = 0
      exact hFsupp z (fun hzo => hz (openBox_subset_Icc a b hzo))
    have hderiv0 : HasFDerivAt F (0 : Pi3 →L[ℝ] Pi3) y :=
      (hasFDerivAt_const (0 : Pi3) y).congr_of_eventuallyEq hFev
    have hF'0 : F' y = 0 := (hFderiv y).unique hderiv0
    unfold piDivergence
    rw [hF'0]; simp
  exact divergence_integral_eq_zero a b hle F F' hFsupp HcF Hd Hi hzero

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
  contU'' : ∀ t i j,
    Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 j))
  contP : ∀ t, Continuous (p t)
  contP' : ∀ t i, Continuous (fun x => fderiv ℝ (p t) x (e3 i))
  supp : ∀ t x, (eL3 x) ∉ openBox a b → u t x = 0

/-#############################################################################
  §4bis. ТРИ УБИЙЦЫ + ИНТЕГРИРУЕМОСТИ — ДОКАЗАНЫ из `BoxSupportedC2Flow`
      (через мастер-лемму §3bis + гейты гладкости). Больше НЕ гипотезы.
#############################################################################-/

/-- Координатная форма `⟪u, ∇p⟫ = ∑ i, (fderiv p x eᵢ)·(u x) i` (через
    `inner_gradient_left` + разложение `u` по базису). -/
theorem inner_gradient_eq_sum (p : E3 → ℝ) (u : E3 → E3) (x : E3) :
    ⟪u x, gradient p x⟫_ℝ = ∑ i, (fderiv ℝ p x (e3 i)) * (u x) i := by
  rw [real_inner_comm, inner_gradient_left]
  conv_lhs => rw [e3_decomp (u x), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]

/-- **Интегрируемость бокс-носимого непрерывного интегранта на `E3`.** Непрерывная
    функция `g : E3 → ℝ`, зануляющаяся вне бокс-носителя (`eL3 x ∉ openBox`), —
    интегрируема: её носитель лежит в компакте `eL3 ⁻¹' (Icc a b)`. -/
theorem integrable_of_boxSupported_E3
    (a b : Pi3) (g : E3 → ℝ) (hg : Continuous g)
    (hsupp : ∀ x : E3, eL3 x ∉ openBox a b → g x = 0) :
    Integrable g volume := by
  have hcpt : IsCompact (eL3 ⁻¹' (Set.Icc a b)) := by
    have heq : eL3 ⁻¹' (Set.Icc a b) = eL3.symm '' (Set.Icc a b) := by
      ext z; simp only [Set.mem_preimage, Set.mem_image]
      exact ⟨fun h => ⟨eL3 z, h, by simp⟩,
        fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw⟩
    rw [heq]; exact (isCompact_Icc).image eL3.symm.continuous
  have hIntOn : IntegrableOn g (eL3 ⁻¹' (Set.Icc a b)) volume :=
    hg.continuousOn.integrableOn_compact hcpt
  have hzero : ∀ x ∉ eL3 ⁻¹' (Set.Icc a b), g x = 0 :=
    fun x hx => hsupp x (fun ho => hx (Set.mem_preimage.mpr (openBox_subset_Icc a b ho)))
  exact hIntOn.integrable_of_forall_notMem_eq_zero hzero

/-- Непрерывность интегранта давления `⟪u, ∇p⟫` (из гейтов `contP'`, `contU`). -/
theorem contPressIntegrand
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) :
    Continuous (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) := by
  have heq : (fun x => ⟪u t x, gradient (p t) x⟫_ℝ)
      = fun x => ∑ i, (fderiv ℝ (p t) x (e3 i)) * (u t x) i :=
    funext fun x => inner_gradient_eq_sum (p t) (u t) x
  rw [heq]
  apply continuous_finset_sum
  intro i _
  exact (F.contP' t i).mul ((EuclideanSpace.proj i).continuous.comp (F.contU t))

/-- Непрерывность интегранта переноса `⟪u, (u·∇)u⟫` (из `contU`, `contU'`). -/
theorem contConvIntegrand
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) :
    Continuous (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) := by
  have heq : (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ)
      = fun x => ∑ j, (u t x) j
          * (∑ i, (u t x) i * (fderiv ℝ (u t) x (e3 i)) j) := by
    funext x
    rw [real_inner_e3_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [convectiveTerm, clm_apply_eq_sum]
  rw [heq]
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
  apply continuous_finset_sum
  intro i _
  exact ((EuclideanSpace.proj i).continuous.comp (F.contU t)).mul
    ((EuclideanSpace.proj j).continuous.comp (F.contU' t i))

/-- Непрерывность интегранта вязкости `⟪u, ν•Δu⟫` (из `contU`, `contU''`). -/
theorem contLapIntegrand
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) :
    Continuous (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) := by
  have heq : (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ)
      = fun x => ν * ∑ j, (u t x) j
          * (∑ i, (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 i)) j) := by
    funext x
    rw [real_inner_smul_right, real_inner_e3_eq_sum]
    congr 1
  rw [heq]
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
  apply continuous_finset_sum
  intro i _
  exact (EuclideanSpace.proj j).continuous.comp (F.contU'' t i i)

/-- **Интегрируемость давления `∫⟪u,∇p⟫` — ДОКАЗАНА** (непрерывность + бокс-носитель). -/
theorem intPress_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume := by
  intro t
  refine integrable_of_boxSupported_E3 F.a F.b _ (contPressIntegrand F t) ?_
  intro x hx
  rw [F.supp t x hx, inner_zero_left]

/-- **Интегрируемость переноса `∫⟪u,(u·∇)u⟫` — ДОКАЗАНА.** -/
theorem intConv_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume := by
  intro t
  refine integrable_of_boxSupported_E3 F.a F.b _ (contConvIntegrand F t) ?_
  intro x hx
  rw [F.supp t x hx, inner_zero_left]

/-- **Интегрируемость вязкости `∫⟪u,ν•Δu⟫` — ДОКАЗАНА.** -/
theorem intLap_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume := by
  intro t
  refine integrable_of_boxSupported_E3 F.a F.b _ (contLapIntegrand F t) ?_
  intro x hx
  rw [F.supp t x hx, inner_zero_left]

/-- **УБИЙЦА I (ДАВЛЕНИЕ) — ДОКАЗАНА:** `∫⟪u,∇p⟫ = 0`. Поле `G := p•u` имеет
    E3-дивергенцию `p·div u + ⟪u,∇p⟫`; при `div u = 0` (несжимаемость)
    остаётся `⟪u,∇p⟫`, а мастер-лемма §3bis даёт `∫ = 0`. -/
theorem pressureKills_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p) :
    ∀ t, (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ) = 0 := by
  intro t
  set G : E3 → E3 := fun x => p t x • u t x with hG
  set G' : E3 → E3 →L[ℝ] E3 := fun x =>
    (p t x • (fderiv ℝ (u t) x) + (fderiv ℝ (p t) x).smulRight (u t x)) with hG'
  have hGderiv : ∀ x, HasFDerivAt G (G' x) x :=
    fun x => (F.pressDiff t x).hasFDerivAt.smul (F.spaceDiff t x).hasFDerivAt
  have hcomp : ∀ x i, (G' x (e3 i)) i
      = p t x * (fderiv ℝ (u t) x (e3 i)) i + (fderiv ℝ (p t) x (e3 i)) * (u t x) i := by
    intro x i
    show ((p t x • (fderiv ℝ (u t) x)
        + (fderiv ℝ (p t) x).smulRight (u t x)) (e3 i)) i = _
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hpt2 : ∀ x, (∑ i, (G' x (e3 i)) i) = ⟪u t x, gradient (p t) x⟫_ℝ := by
    intro x
    rw [inner_gradient_eq_sum]
    have hsum : (∑ i, (G' x (e3 i)) i)
        = p t x * NSdiv (u t) x + ∑ i, (fderiv ℝ (p t) x (e3 i)) * (u t x) i := by
      rw [NSdiv, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hcomp x i
    rw [hsum, sol.incompressible t x, mul_zero, zero_add]
  have hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i) := by
    have heq : (fun x : E3 => ∑ i, (G' x (e3 i)) i)
        = fun x => ⟪u t x, gradient (p t) x⟫_ℝ := funext hpt2
    rw [heq]; exact contPressIntegrand F t
  have hsupp : ∀ x : E3, eL3 x ∉ openBox F.a F.b → G x = 0 := by
    intro x hx
    show p t x • u t x = 0
    rw [F.supp t x hx, smul_zero]
  have hmaster :=
    integral_e3_divergence_eq_zero F.a F.b F.aleb G G' hGderiv hcont hsupp
  rw [← hmaster]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt2 x).symm)

/-- Производная `½‖u‖²` вдоль направления: `fderiv (½‖u‖²) x h = ⟪u x, fderiv u x h⟫`
    (из `HasFDerivAt.norm_sq` c `(1/2)`-массажем). -/
theorem fderiv_half_normSq (u : E3 → E3) (x : E3)
    (hu : DifferentiableAt ℝ u x) (h : E3) :
    fderiv ℝ (fun y => (1/2 : ℝ) * ‖u y‖^2) x h = ⟪u x, fderiv ℝ u x h⟫_ℝ := by
  have hd := (hu.hasFDerivAt.norm_sq).const_mul (1/2 : ℝ)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

/-- `⟪u, (u·∇)u⟫ = ∑ i, (u x)ᵢ · ⟪u x, ∂ᵢu⟫` (разложение направления `u x` по базису). -/
theorem inner_conv_eq_sum (u : E3 → E3) (x : E3) :
    ⟪u x, convectiveTerm u x⟫_ℝ = ∑ i, (u x) i * ⟪u x, fderiv ℝ u x (e3 i)⟫_ℝ := by
  rw [convectiveTerm]
  conv_lhs => rw [show (fderiv ℝ u x) (u x)
    = (fderiv ℝ u x) (∑ i, (u x) i • e3 i) from by rw [← e3_decomp]]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, real_inner_smul_right]

/-- **УБИЙЦА II (ПЕРЕНОС) — ДОКАЗАНА:** `∫⟪u,(u·∇)u⟫ = 0`. Поле `G := (½‖u‖²)•u`
    имеет E3-дивергенцию `⟪u,(u·∇)u⟫ + (½‖u‖²)·div u`; при `div u = 0` остаётся
    `⟪u,(u·∇)u⟫`, а мастер-лемма §3bis даёт `∫ = 0`. Тождество направления:
    `fderiv (½‖u‖²) x = ⟪u x, fderiv u x ·⟫` (`fderiv_half_normSq`). -/
theorem transportKills_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p) :
    ∀ t, (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) = 0 := by
  intro t
  set c : E3 → ℝ := fun y => (1/2 : ℝ) * ‖u t y‖^2 with hc
  set G : E3 → E3 := fun x => c x • u t x with hG
  set G' : E3 → E3 →L[ℝ] E3 := fun x =>
    (c x • (fderiv ℝ (u t) x) + (fderiv ℝ c x).smulRight (u t x)) with hG'
  have hcDiff : ∀ x, DifferentiableAt ℝ c x := fun x =>
    (((F.spaceDiff t x).hasFDerivAt.norm_sq).const_mul (1/2:ℝ)).differentiableAt
  have hGderiv : ∀ x, HasFDerivAt G (G' x) x :=
    fun x => (hcDiff x).hasFDerivAt.smul (F.spaceDiff t x).hasFDerivAt
  have hcomp : ∀ x i, (G' x (e3 i)) i
      = c x * (fderiv ℝ (u t) x (e3 i)) i
        + ⟪u t x, fderiv ℝ (u t) x (e3 i)⟫_ℝ * (u t x) i := by
    intro x i
    show ((c x • (fderiv ℝ (u t) x)
        + (fderiv ℝ c x).smulRight (u t x)) (e3 i)) i = _
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [fderiv_half_normSq (u t) x (F.spaceDiff t x)]
  have hpt2 : ∀ x, (∑ i, (G' x (e3 i)) i) = ⟪u t x, convectiveTerm (u t) x⟫_ℝ := by
    intro x
    have hsum : (∑ i, (G' x (e3 i)) i)
        = c x * NSdiv (u t) x
          + ∑ i, ⟪u t x, fderiv ℝ (u t) x (e3 i)⟫_ℝ * (u t x) i := by
      rw [NSdiv, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hcomp x i
    rw [hsum, sol.incompressible t x, mul_zero, zero_add, inner_conv_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i) := by
    have heq : (fun x : E3 => ∑ i, (G' x (e3 i)) i)
        = fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ := funext hpt2
    rw [heq]; exact contConvIntegrand F t
  have hsupp : ∀ x : E3, eL3 x ∉ openBox F.a F.b → G x = 0 := by
    intro x hx
    show c x • u t x = 0
    rw [F.supp t x hx, smul_zero]
  have hmaster :=
    integral_e3_divergence_eq_zero F.a F.b F.aleb G G' hGderiv hcont hsupp
  rw [← hmaster]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt2 x).symm)

/-#############################################################################
  §4ter. УБИЙЦА III (ВЯЗКОСТЬ) — ДОКАЗАНА покомпонентным IBP.
      Для каждой компоненты `j` поле `H_j := u_j • ∇u_j` имеет E3-дивергенцию
      `‖∇u_j‖² + u_j·(Δu)_j`; мастер-лемма §3bis даёт `∫ = 0` покомпонентно,
      суммирование по `j` + `Finset.sum_comm` приземляют на энстрофию.
#############################################################################-/

/-- Производная скалярной компоненты `u_j = (proj j) ∘ u`:
    `fderiv u_j x = (proj j) ∘L fderiv u x`. -/
theorem hasFDerivAt_phij (u : E3 → E3) (x : E3) (j : Fin 3) (hu : DifferentiableAt ℝ u x) :
    HasFDerivAt (fun y => (u y) j)
      ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ u x)) x :=
  ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ).hasFDerivAt (x := u x)).comp x hu.hasFDerivAt

/-- Производная градиента компоненты `w_j y = ∑ i, (∂ᵢu_j)(y)·eᵢ`
    (из гейта вторых производных `spaceDiff2`). -/
theorem hasFDerivAt_wj (u : E3 → E3) (x : E3) (j : Fin 3)
    (h2 : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ u y (e3 i)) x) :
    HasFDerivAt (fun y => ∑ i, (fderiv ℝ u y (e3 i) j) • e3 i)
      (∑ i, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
        (fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x)).smulRight (e3 i)) x := by
  have hpt : (fun y => ∑ i, (fderiv ℝ u y (e3 i) j) • e3 i)
      = ∑ i, (fun y => (fderiv ℝ u y (e3 i) j) • e3 i) := by funext y; rw [Finset.sum_apply]
  rw [hpt]; apply HasFDerivAt.sum; intro i _
  have hg2 : HasFDerivAt (fun y => (fderiv ℝ u y (e3 i)) j)
      ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x)) x :=
    ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ).hasFDerivAt).comp x (h2 i).hasFDerivAt
  exact hg2.smul_const (e3 i)

/-- `i`-я координата градиента компоненты: `(w_j x)ᵢ = ∂ᵢu_j`. -/
theorem wj_apply (u : E3 → E3) (x : E3) (j i : Fin 3) :
    (∑ k, (fderiv ℝ u x (e3 k) j) • e3 k) i = fderiv ℝ u x (e3 i) j := by
  rw [e3_sum_apply]
  simp only [PiLp.smul_apply, e3, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ i]; simp

/-- Квадрат нормы градиента компоненты: `‖∇u_j‖² = ∑ i, (∂ᵢu_j)²`. -/
theorem wj_normSq (u : E3 → E3) (x : E3) (j : Fin 3) :
    ‖(∑ k, (fderiv ℝ u x (e3 k) j) • e3 k : E3)‖^2 = ∑ i, (fderiv ℝ u x (e3 i) j)^2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_e3_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [wj_apply]; ring

/-- Дивергенция градиента компоненты = `j`-я компонента лапласиана:
    `div(∇u_j) = (Δu)_j`. -/
theorem wj_div (u : E3 → E3) (x : E3) (j : Fin 3) :
    (∑ m, ((∑ i, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
        (fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x)).smulRight (e3 i)) (e3 m)) m)
      = (vectorLaplacian u x) j := by
  rw [vectorLaplacian, e3_sum_apply]; apply Finset.sum_congr rfl; intro m _
  rw [ContinuousLinearMap.sum_apply, e3_sum_apply, Finset.sum_eq_single m]
  · simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      PiLp.smul_apply, e3, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]; simp
  · intro i _ hi
    simp only [ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, e3,
      PiLp.single_apply, smul_eq_mul]
    rw [if_neg (Ne.symm hi)]; ring
  · intro h; exact absurd (Finset.mem_univ m) h

/-- **Покомпонентное IBP-тождество:** E3-дивергенция поля `H_j = u_j • ∇u_j`
    равна `‖∇u_j‖² + u_j·(Δu)_j`. -/
theorem Hj_div (u : E3 → E3) (x : E3) (j : Fin 3) :
    (∑ i, (((u x j) • (∑ k, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ u y (e3 k)) x)).smulRight (e3 k))
      + ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ u x)).smulRight
          (∑ k, (fderiv ℝ u x (e3 k) j) • e3 k)) (e3 i)) i)
      = ‖(∑ k, (fderiv ℝ u x (e3 k) j) • e3 k : E3)‖^2 + (u x j) * (vectorLaplacian u x) j := by
  have hcomp : ∀ i, (((u x j) • (∑ k, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ u y (e3 k)) x)).smulRight (e3 k))
      + ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ u x)).smulRight
          (∑ k, (fderiv ℝ u x (e3 k) j) • e3 k)) (e3 i)) i
      = (u x j) * ((∑ k, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ u y (e3 k)) x)).smulRight (e3 k)) (e3 i)) i
        + (fderiv ℝ u x (e3 i) j) * ((∑ k, (fderiv ℝ u x (e3 k) j) • e3 k) i) := by
    intro i
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; rfl
  rw [Finset.sum_congr rfl (fun i _ => hcomp i), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [wj_div, wj_normSq, add_comm]; congr 1
  apply Finset.sum_congr rfl; intro i _; rw [wj_apply]; ring

/-- **Интегрируемость Icc-носимого непрерывного интегранта на `E3`.** Аналог
    `integrable_of_boxSupported_E3`, но носитель — по замкнутому `Icc` (граница
    бокса меры ноль): для энстрофийного слагаемого `‖∇u_j‖²`, зануляющегося на
    ОТКРЫТОМ дополнении `Icc` (где `u ≡ 0` ⟹ `fderiv u = 0`). -/
theorem integrable_of_IccSupported_E3
    (a b : Pi3) (g : E3 → ℝ) (hg : Continuous g)
    (hsupp : ∀ x : E3, eL3 x ∉ Set.Icc a b → g x = 0) :
    Integrable g volume := by
  have hcpt : IsCompact (eL3 ⁻¹' (Set.Icc a b)) := by
    have heq : eL3 ⁻¹' (Set.Icc a b) = eL3.symm '' (Set.Icc a b) := by
      ext z; simp only [Set.mem_preimage, Set.mem_image]
      exact ⟨fun h => ⟨eL3 z, h, by simp⟩, fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw⟩
    rw [heq]; exact (isCompact_Icc).image eL3.symm.continuous
  have hIntOn : IntegrableOn g (eL3 ⁻¹' (Set.Icc a b)) volume :=
    hg.continuousOn.integrableOn_compact hcpt
  exact hIntOn.integrable_of_forall_notMem_eq_zero
    (fun x hx => hsupp x (fun ho => hx (Set.mem_preimage.mpr ho)))

/-- Вне бокса производная бокс-носимого поля ноль: если `eL3 x ∉ Icc`, то `u ≡ 0`
    на ОТКРЫТОЙ окрестности `x` (дополнение `Icc`), потому `fderiv u x (eᵢ) = 0`. -/
theorem fderiv_zero_outside_Icc {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) (i : Fin 3) {x : E3}
    (hx : eL3 x ∉ Set.Icc F.a F.b) :
    fderiv ℝ (u t) x (e3 i) = 0 := by
  have hopen : IsOpen (eL3 ⁻¹' (Set.Icc F.a F.b)ᶜ) :=
    (isClosed_Icc.isOpen_compl).preimage eL3.continuous
  have hev : u t =ᶠ[nhds x] fun _ => 0 := by
    apply Filter.eventuallyEq_of_mem (hopen.mem_nhds hx)
    intro z hz
    exact F.supp t z (fun ho => hz (openBox_subset_Icc F.a F.b ho))
  rw [Filter.EventuallyEq.fderiv_eq hev]; simp

/-- Непрерывность покомпонентного дивергентного интегранта `‖∇u_j‖² + u_j·(Δu)_j`
    (из гейтов `contU`, `contU'`, `contU''`). -/
theorem contHjdiv {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) (t : ℝ) (j : Fin 3) :
    Continuous (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j) := by
  apply Continuous.add
  · have heq : (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
        = fun x => ∑ i, (fderiv ℝ (u t) x (e3 i) j)^2 := funext fun x => wj_normSq (u t) x j
    rw [heq]; apply continuous_finset_sum; intro i _
    exact ((EuclideanSpace.proj j).continuous.comp (F.contU' t i)).pow 2
  · apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
    have heq : (fun x => (vectorLaplacian (u t) x) j)
        = fun x => ∑ i, (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 i)) j := by
      funext x; rw [vectorLaplacian, e3_sum_apply]
    rw [heq]; apply continuous_finset_sum; intro i _
    exact (EuclideanSpace.proj j).continuous.comp (F.contU'' t i i)

/-- **УБИЙЦА III (ВЯЗКОСТЬ) — ДОКАЗАНА:** `∫⟪u,Δu⟫ = −∫∑ᵢ‖∂ᵢu‖²` (IBP).
    Покомпонентно поле `H_j := u_j•∇u_j` имеет дивергенцию `‖∇u_j‖² + u_j·(Δu)_j`,
    мастер-лемма §3bis даёт `∫ = 0` для каждого `j`; суммирование по `j`, расщепление
    (обе части интегрируемы: `⟪u,Δu⟫` бокс-носимо, `∑‖∂ᵢu‖²` Icc-носимо) и
    `Finset.sum_comm` (`∑_j‖∇u_j‖² = ∑_i‖∂ᵢu‖²`) приземляют на энстрофию. -/
theorem viscosityIBP_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p) :
    ∀ t, (∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ)
      = -(∫ x : E3, ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖ ^ 2) := by
  intro t
  have perj : ∀ j, (∫ x : E3, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j) = 0 := by
    intro j
    set G : E3 → E3 := fun y => (u t y j) • (∑ i, (fderiv ℝ (u t) y (e3 i) j) • e3 i) with hG
    set G' : E3 → E3 →L[ℝ] E3 := fun x =>
      ((u t x j) • (∑ i, ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L
          (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x)).smulRight (e3 i))
        + ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ) ∘L (fderiv ℝ (u t) x)).smulRight
            (∑ i, (fderiv ℝ (u t) x (e3 i) j) • e3 i)) with hG'
    have hGderiv : ∀ x, HasFDerivAt G (G' x) x := fun x =>
      (hasFDerivAt_phij (u t) x j (F.spaceDiff t x)).smul
        (hasFDerivAt_wj (u t) x j (fun i => F.spaceDiff2 t i x))
    have hdivpt : ∀ x, (∑ i, (G' x (e3 i)) i)
        = ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
          + (u t x j) * (vectorLaplacian (u t) x) j := fun x => Hj_div (u t) x j
    have hcont : Continuous (fun x : E3 => ∑ i, (G' x (e3 i)) i) := by
      have heq : (fun x : E3 => ∑ i, (G' x (e3 i)) i)
          = fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
            + (u t x j) * (vectorLaplacian (u t) x) j := funext hdivpt
      rw [heq]; exact contHjdiv F t j
    have hsupp : ∀ x : E3, eL3 x ∉ openBox F.a F.b → G x = 0 := by
      intro x hx
      show (u t x j) • (∑ i, (fderiv ℝ (u t) x (e3 i) j) • e3 i) = 0
      rw [F.supp t x hx]; simp
    have hmaster :=
      integral_e3_divergence_eq_zero F.a F.b F.aleb G G' hGderiv hcont hsupp
    rw [← hmaster]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hdivpt x).symm)
  have hIntW : ∀ j, Integrable
      (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2) volume := by
    intro j
    apply integrable_of_IccSupported_E3 F.a F.b _
    · have heq : (fun x => ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
          = fun x => ∑ i, (fderiv ℝ (u t) x (e3 i) j)^2 := funext fun x => wj_normSq (u t) x j
      rw [heq]; apply continuous_finset_sum; intro i _
      exact ((EuclideanSpace.proj j).continuous.comp (F.contU' t i)).pow 2
    · intro x hx
      have hz : ∀ k, fderiv ℝ (u t) x (e3 k) j = 0 := fun k => by
        rw [fderiv_zero_outside_Icc F t k hx]; simp
      simp only [hz]
      rw [show (∑ k, (0:ℝ) • e3 k : E3) = 0 from by simp]; simp
  have hIntUL : ∀ j, Integrable
      (fun x => (u t x j) * (vectorLaplacian (u t) x) j) volume := by
    intro j
    apply integrable_of_IccSupported_E3 F.a F.b _
    · apply Continuous.mul ((EuclideanSpace.proj j).continuous.comp (F.contU t))
      have heq : (fun x => (vectorLaplacian (u t) x) j)
          = fun x => ∑ i, (fderiv ℝ (fun y => fderiv ℝ (u t) y (e3 i)) x (e3 i)) j := by
        funext x; rw [vectorLaplacian, e3_sum_apply]
      rw [heq]; apply continuous_finset_sum; intro i _
      exact (EuclideanSpace.proj j).continuous.comp (F.contU'' t i i)
    · intro x hx
      have hu0 : u t x = 0 := F.supp t x (fun ho => hx (openBox_subset_Icc F.a F.b ho))
      rw [show (u t x) j = 0 from by rw [hu0]; simp]; ring
  have hsum0 : (∫ x : E3, ∑ j, (‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j)) = 0 := by
    rw [MeasureTheory.integral_finset_sum]
    · rw [Finset.sum_eq_zero]; intro j _; exact perj j
    · intro j _; exact (hIntW j).add (hIntUL j)
  have hsplit : (∫ x : E3, ∑ j, (‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
      + (u t x j) * (vectorLaplacian (u t) x) j))
      = (∫ x : E3, ∑ j, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
        + ∫ x : E3, ∑ j, (u t x j) * (vectorLaplacian (u t) x) j := by
    rw [← MeasureTheory.integral_add]
    · apply integral_congr_ae; apply Filter.Eventually.of_forall; intro x
      exact Finset.sum_add_distrib
    · exact integrable_finset_sum _ (fun j _ => hIntW j)
    · exact integrable_finset_sum _ (fun j _ => hIntUL j)
  have hConvUL : (fun x => ∑ j, (u t x j) * (vectorLaplacian (u t) x) j)
      = fun x => ⟪u t x, vectorLaplacian (u t) x⟫_ℝ := by
    funext x; rw [real_inner_e3_eq_sum]
  have hConvW : (fun x => ∑ j, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2)
      = fun x => ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖^2 := by
    funext x
    have h1 : ∀ j, ‖(∑ k, (fderiv ℝ (u t) x (e3 k) j) • e3 k : E3)‖^2
        = ∑ i, (fderiv ℝ (u t) x (e3 i) j)^2 := fun j => wj_normSq (u t) x j
    have h2 : ∀ i, ‖fderiv ℝ (u t) x (e3 i)‖^2 = ∑ j, (fderiv ℝ (u t) x (e3 i) j)^2 := by
      intro i; rw [← real_inner_self_eq_norm_sq, real_inner_e3_eq_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [h1, h2]; exact Finset.sum_comm
  rw [hConvUL, hConvW] at hsplit
  rw [hsplit] at hsum0
  linarith [hsum0]

/-- **R3AssemblyGates — ПОСЛОЙНЫЙ ГЕЙТ-НАБОР (fallback-раскрытие):** всё, что нужно,
    чтобы ВЫВЕСТИ энергобаланс в момент `t`. Поля `timeDeriv/domination` кормят R1;
    `intLap/intPress/intConv` — интегрируемости компонент правой части (расщепление
    интеграла); ТРИ убийцы `pressureKills/transportKills/viscosityIBP` —
    E3-тождества интегрирования по частям.

    ✅ FALLBACK ЗАКРЫТ: три убийцы (`pressureKills`, `transportKills`,
    `viscosityIBP`) БОЛЬШЕ НЕ ГИПОТЕЗЫ — они ДОКАЗАНЫ (§4bis/§4ter) мастер-леммой
    §3bis (`integral_e3_divergence_eq_zero`: E3↔Pi3-мост fderiv comp-цепью, подающий
    R2). `killerBundle_of_boxSupported` собирает все их значения из
    `BoxSupportedC2Flow` + `IsNSSolution`. Структура СОХРАНЕНА как послойная
    абстракция (её поля выводимы); заголовочные теоремы её напрямую не требуют. -/
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

/-- **Пакет убийц + интегрируемости — ТЕПЕРЬ ВЫВОДИМ (не residual-вход).**
    Три убийцы (E3-тождества IBP) и три интегрируемости компонент. РАНЬШЕ пакет был
    честным аналитическим остатком; ТЕПЕРЬ `killerBundle_of_boxSupported F sol`
    строит ВСЕ его поля из `BoxSupportedC2Flow` + `IsNSSolution` через мастер-лемму
    §3bis. Структура СОХРАНЕНА как переиспользуемая абстракция послойной сборки. -/
structure KillerBundle (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) where
  intLap : ∀ t, Integrable (fun x => ⟪u t x, ν • vectorLaplacian (u t) x⟫_ℝ) volume
  intPress : ∀ t, Integrable (fun x => ⟪u t x, gradient (p t) x⟫_ℝ) volume
  intConv : ∀ t, Integrable (fun x => ⟪u t x, convectiveTerm (u t) x⟫_ℝ) volume
  pressureKills : ∀ t, (∫ x : E3, ⟪u t x, gradient (p t) x⟫_ℝ) = 0
  transportKills : ∀ t, (∫ x : E3, ⟪u t x, convectiveTerm (u t) x⟫_ℝ) = 0
  viscosityIBP : ∀ t,
    (∫ x : E3, ⟪u t x, vectorLaplacian (u t) x⟫_ℝ)
      = -(∫ x : E3, ∑ i, ‖fderiv ℝ (u t) x (e3 i)‖ ^ 2)

/-- **`killerBundle_of_boxSupported` — ВЕСЬ ПАКЕТ УБИЙЦ ВЫВЕДЕН (не гипотеза).**
    Из бокс-носимого C²-потока `F` и бессилового решения `sol` собираются ВСЕ шесть
    полей `KillerBundle`: три интегрируемости (§4bis, §4ter) и три убийцы
    (§4bis `pressureKills`, §4bis `transportKills`, §4ter `viscosityIBP`).
    Убийцы более НЕ именованные входы — они ДОКАЗАНЫ мастер-леммой §3bis. -/
def killerBundle_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p) :
    KillerBundle ν u p where
  intLap := intLap_of_boxSupported F
  intPress := intPress_of_boxSupported F
  intConv := intConv_of_boxSupported F
  pressureKills := pressureKills_of_boxSupported F sol
  transportKills := transportKills_of_boxSupported F sol
  viscosityIBP := viscosityIBP_of_boxSupported F

/-- **`r3AssemblyGates_of_boxSupported` — послойная сборка гейт-набора.**
    Из бокс-носимого C²-потока `F`, per-time мажоранты `dom`, бессилового решения
    `sol` (`f = 0`) и residual-пакета убийц `K` собирается `R3AssemblyGates`.
    `F` (в т.ч. гейт гладкости давления) обеспечивает структурную часть;
    residual-аналитика `K` подаётся прозрачно (СЛОЙ сохранён; `K` теперь ВЫВОДИМ
    через `killerBundle_of_boxSupported`). -/
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
    Бокс-носимый C²-поток `F` + бессиловое решение `sol` + мажорант `dom` ⟹
    энергобаланс. Три убийцы БОЛЬШЕ НЕ ВХОД — они собраны внутри
    `killerBundle_of_boxSupported F sol` (мастер-лемма §3bis). Остаётся честный
    вход `dom` (🔴 `TimeDomination`, R1). -/
theorem energyBalance_of_boxSupported
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t) :
    EnergyBalanceLaw ν u :=
  energyBalance_of_r3Gates
    (r3AssemblyGates_of_boxSupported F dom (killerBundle_of_boxSupported F sol))

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
  contU'' := fun _ i j => by
    have h : (fun x : E3 =>
        fderiv ℝ (fun y : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) y (e3 i)) x (e3 j))
        = fun _ => (0 : E3) := by
      funext x
      have h0 : (fun y : E3 => fderiv ℝ (fun _ : E3 => (0 : E3)) y (e3 i))
          = fun _ => (0 : E3) := by funext y; simp
      rw [h0]; simp
    rw [h]; exact continuous_const
  contP := fun _ => continuous_const
  contP' := fun _ i => by
    have h : (fun x : E3 => fderiv ℝ (fun _ : E3 => (0 : ℝ)) x (e3 i))
        = fun _ => (0 : ℝ) := by
      funext y; simp
    rw [h]; exact continuous_const
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

/-- **ИНХАБИТАНС (не вакуум): нулевое решение выводит энергобаланс через сборку.**
    Убийцы теперь ВЫВЕДЕНЫ — на вход идёт лишь решение `zero_is_NSSolution` и
    мажорант `zero_timeDomination`. -/
theorem zero_energyBalance_of_boxSupported (ν : ℝ) (hν : 0 ≤ ν) :
    EnergyBalanceLaw ν (fun _ _ => 0) :=
  energyBalance_of_boxSupported (zero_boxSupportedC2Flow ν hν)
    (zero_is_NSSolution ν) (zero_timeDomination ν)

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
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    NoSingularCascade ν u :=
  noSingularCascade_of_energyBalance ν u
    (energyBalance_of_boxSupported F sol dom) hInt

/-- **`energyIdentity_of_r3Assembly` — ТОЖДЕСТВО ЭНЕРГИИ (FTC-2) из сборки.**
    `E(t₂) = E(t₁) − ∫_{t₁}^{t₂} D` для бокс-носимого потока. -/
theorem energyIdentity_of_r3Assembly
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)
    (t₁ t₂ : ℝ) :
    kineticEnergy (u t₂)
      = kineticEnergy (u t₁) - ∫ s in t₁..t₂, dissipationRate ν (u s) :=
  energy_identity_of_energyBalance ν u
    (energyBalance_of_boxSupported F sol dom) hInt t₁ t₂

/-- **ДОКУМЕНТАЦИОННО (`nsBoundary_redundant_on_boxClass`): на бокс-классе декрет
    `NsSolutionBalanceLaw` РЕДУНДАНТЕН.** Заключение закона (энергобаланс +
    интегрируемость диссипации) для бокс-носимого потока ВЫВОДИТСЯ сборкой —
    его НЕ нужно декретировать на этом классе. Содержание декрета остаётся лишь
    ВНЕ конечного бокс-носителя (предельный переход box→ℝ³ в mathlib отсутствует —
    внешний разрыв, здесь НЕ закрытый). -/
theorem nsBoundary_redundant_on_boxClass
    {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (F : BoxSupportedC2Flow ν u p)
    (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (dom : ∀ t, TimeDomination u (nsTimeDerivative ν (fun _ _ => 0) u p) t)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    EnergyBalanceLaw ν u ∧
    (∀ t₁ t₂ : ℝ, IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :=
  ⟨energyBalance_of_boxSupported F sol dom, hInt⟩

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
#print axioms EuclidsPath.NavierStokesR3.integral_e3_divergence_eq_zero
#print axioms EuclidsPath.NavierStokesR3.pressureKills_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.transportKills_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.viscosityIBP_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.killerBundle_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.energyBalance_of_r3Gates
#print axioms EuclidsPath.NavierStokesR3.energyBalance_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.noSingularCascade_of_r3Assembly
#print axioms EuclidsPath.NavierStokesR3.energyIdentity_of_r3Assembly
#print axioms EuclidsPath.NavierStokesR3.zero_energyBalance_of_boxSupported
#print axioms EuclidsPath.NavierStokesR3.zero_timeDomination
#print axioms EuclidsPath.NavierStokesR3.cookedFlow_fails_assemblyGates
#print axioms EuclidsPath.NavierStokesR3.dirichletFlow_fails_assemblyGates
