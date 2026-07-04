/-
  RiemannSpectralAnchor — якорь Гильберта–Пойи двухслойно: форма данных и оператор.

  Классическая мечта (Гильберт–Пойя): нетривиальные нули дзеты суть `1/2 + t·I`,
  где `t` пробегает СПЕКТР самосопряжённого оператора; самосопряжённость даёт
  вещественность `t` — и нули сами встают на критическую прямую. Здесь эта мечта
  разобрана на два честных слоя:

  (а) СЛОЙ ДАННЫХ — `SpectralRealisation`: существует множество `E ⊆ ℝ`,
      реализующее все нетривиальные нули в форме `1/2 + t·I`, `t ∈ E`.
      Зелёная: реализация ⟹ критическая прямая ⟹ mathlib-`RiemannHypothesis`
      (мост дословный: mathlib-RH — это и есть «все нетривиальные на прямой»,
      маршруты `riemannHypothesis_of_*` из RiemannBranch не нужны — они дороже,
      требуют входы `EngineBridge`/`TrivialBelowZeroClassification`).

  (б) ОБЯЗАТЕЛЬНЫЙ АУДИТ ПЕРЕИМЕНОВАНИЯ — обратная строится ДАРОМ: при RH берём
      `E := Set.univ` и `t := ρ.im`. Итог: `spectralRealisation_iff_critical` и
      `spectralRealisation_iff_RH` — слой данных ЭКВИВАЛЕНТЕН цели дословно,
      зеркало `offCriticalBridge_iff_RH`. Вывод аудита: содержательный якорь
      обязан нести ОПЕРАТОР, а не голое множество вещественных чисел.

  (в) СЛОЙ ОПЕРАТОРА — `OperatorSpectralAnchor`: самосопряжённый ограниченный
      оператор `T` на комплексном гильбертовом пространстве, спектр которого
      реализует нули. Зелёный мост `operatorAnchor_implies_realisation`:
      спектр самосопряжённого вещественен (mathlib
      `IsSelfAdjoint.mem_spectrum_eq_re`, C*-алгебра `H →L[ℂ] H` — mathlib-
      инстанс из Analysis/CStarAlgebra/ContinuousLinearMap). Обратный аудит
      слоя (в) НЕ проходит даром — и это хорошо: зелёная негативная теорема
      `no_operatorAnchor_of_unbounded_ordinates` показывает, что при
      неограниченности ординат нулей (классика, в mathlib v4.31 ОТСУТСТВУЕТ)
      ОГРАНИЧЕННЫЙ якорь вообще невыполним: спектр ограниченного оператора
      лежит в шаре радиуса ‖T‖ (`spectrum.norm_le_norm_of_mem`). Честный
      Гильберт–Пойя обязан быть НЕОГРАНИЧЕННЫМ оператором; в mathlib v4.31
      есть `LinearPMap.adjoint` и `IsSelfAdjoint` для `E →ₗ.[𝕜] E`
      (Analysis/InnerProductSpace/LinearPMap), но НЕТ спектральной теории
      неограниченных операторов (нет `spectrum` для `LinearPMap`, нет
      спектральной теоремы) — это и есть точная недостача якоря.

  СТЫКОВКА с RiemannSpectralAnchorAudit (не дублируя его абстрактный аудит):
  `zeroOrdinateLaw` — конкретный `DataAnchoredLaw` (Zero := нетривиальные нули,
  Atom := ℝ), `zeroOrdinateInvariantAnchor` — настоящий `SpectralInvariantAnchor`
  (инвариант = мнимая часть; respects ДОКАЗАН), `zeroOrdinateBridge_iff_RH` —
  Prop-тень этого data-закона снова дословно RH. Недостающее для
  `NonVacuousDataAnchor.separates` — ДВА нетривиальных нуля с разными
  ординатами; в mathlib v4.31 нет НИ ОДНОГО конкретного нетривиального нуля.

  ЧЕСТНОСТЬ: это НЕ решение RH и НЕ Гёдель. Красные def-входы — именованные
  данные, которые математика ДОЛЖНА предъявить; зелёные теоремы — что фронт
  закрывается ПРИ якоре. Карантин (CausalClosureAxiom) НЕ импортируется;
  axiom/sorry/native_decide нет; таинт 47 не меняется.
-/
import Mathlib
import EuclidsPath.Engine.RiemannBranch
import EuclidsPath.Engine.RiemannSpectralAnchorAudit

set_option autoImplicit false

namespace EuclidsPath.RiemannSpectralAnchor

open Complex EuclidsPath.RiemannBranch

/-! ## §0. Арифметика формы `1/2 + t·I` -/

/-- Вещественная часть формы `1/2 + t·I` равна `1/2`. -/
lemma half_add_mul_I_re (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).re = 1 / 2 := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
  ring

/-- Мнимая часть формы `1/2 + t·I` равна `t`. -/
lemma half_add_mul_I_im (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).im = t := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
  ring

/-- Точка на критической прямой ИМЕЕТ форму `1/2 + t·I` с `t := ρ.im` —
    техническое ядро аудита переименования (обратная сторона строится даром). -/
lemma eq_half_add_of_re_eq_half {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ρ = 1 / 2 + (ρ.im : ℂ) * Complex.I := by
  have h := (Complex.re_add_im ρ).symm
  rw [hre] at h
  rw [h]
  norm_num

/-! ## §1. Слой (а): форма данных -/

/--
  **`SpectralRealisation` — КРАСНЫЙ вход слоя данных (якорь Гильберта–Пойи без
  оператора).** Существует множество `E ⊆ ℝ` такое, что каждый нетривиальный
  нуль `ρ` (в смысле mathlib-RH, предикат `NontrivialZeroM` из RiemannBranch)
  имеет форму `1/2 + t·I` с `t ∈ E`: нули реализованы вещественным «спектром».

  ⚠️ Аудит §2 покажет: этот вход — ПЕРЕИМЕНОВАНИЕ RH (`spectralRealisation_iff_RH`),
  потому что множество `E` — голые данные без носителя. Содержательный якорь
  обязан нести ОПЕРАТОР (§3). -/
def SpectralRealisation : Prop :=
  ∃ E : Set ℝ, ∀ ρ : ℂ, NontrivialZeroM ρ → ∃ t ∈ E, ρ = 1 / 2 + (t : ℂ) * Complex.I

/-- **ЗЕЛЁНАЯ: реализация ⟹ критическая прямая.** Из формы `1/2 + t·I`
    мгновенно `Re ρ = 1/2` для всякого нетривиального нуля. -/
theorem spectralRealisation_implies_critical
    (h : SpectralRealisation) {ρ : ℂ} (hρ : NontrivialZeroM ρ) : ρ.re = 1 / 2 := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨t, _, hform⟩ := hE ρ hρ
  rw [hform]
  exact half_add_mul_I_re t

/-- **ЗЕЛЁНАЯ: реализация ⟹ mathlib-`RiemannHypothesis`.** Мост дословный:
    mathlib-RH — ровно «каждый нетривиальный нуль имеет `Re = 1/2`», поэтому
    дорогие маршруты RiemannBranch (`riemannHypothesis_of_engine_bridge` с
    входами) здесь не нужны. -/
theorem riemannHypothesis_of_spectralRealisation
    (h : SpectralRealisation) : RiemannHypothesis := by
  intro ρ hz htriv hne1
  exact spectralRealisation_implies_critical h ⟨hz, htriv, hne1⟩

/-! ## §2. Обязательный аудит переименования (зеркало `offCriticalBridge_iff_RH`) -/

/-- **АУДИТ (обратная строится ДАРОМ).** При RH реализация собирается из ничего:
    `E := Set.univ`, `t := ρ.im` — нуль на прямой сам сообщает свою ординату.
    Никакого оператора, никакого спектра: голое множество данных бесплатно. -/
theorem spectralRealisation_of_RH (hRH : RiemannHypothesis) : SpectralRealisation := by
  refine ⟨Set.univ, fun ρ hρ => ⟨ρ.im, Set.mem_univ _, ?_⟩⟩
  exact eq_half_add_of_re_eq_half (hRH ρ hρ.1 hρ.2.1 hρ.2.2)

/-- **АУДИТ-ИТОГ (критическая прямая).** Слой данных ⟺ «все нетривиальные нули
    на прямой» — дословное переименование утверждения о прямой. -/
theorem spectralRealisation_iff_critical :
    SpectralRealisation ↔ ∀ ρ : ℂ, NontrivialZeroM ρ → ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ
    exact spectralRealisation_implies_critical h hρ
  · intro h
    refine ⟨Set.univ, fun ρ hρ => ⟨ρ.im, Set.mem_univ _, ?_⟩⟩
    exact eq_half_add_of_re_eq_half (h ρ hρ)

/--
  **`spectralRealisation_iff_RH` — ГЛАВНЫЙ АУДИТ слоя данных (честность,
  зеркало `offCriticalBridge_iff_RH`).** Вход `SpectralRealisation` ЭКВИВАЛЕНТЕН
  mathlib-`RiemannHypothesis` — машинно и без всяких гипотез. «Спектральная
  реализация множеством» — не редукция, а переименование цели: множество `E`
  не несёт носителя, из которого нули ДОБЫВАЮТСЯ.

  ВЫВОД АУДИТА: содержательный якорь Гильберта–Пойи обязан нести ОПЕРАТОР —
  структуру, чей спектр вещественен ПО ПРИЧИНЕ (самосопряжённость), а не по
  декрету. Это §3. -/
theorem spectralRealisation_iff_RH : SpectralRealisation ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_spectralRealisation, spectralRealisation_of_RH⟩

/-! ## §3. Слой (в): оператор -/

/--
  **`OperatorSpectralAnchor` — КРАСНЫЙ вход следующего слоя (настоящий
  Гильберт–Пойя, ограниченная форма).** Данные: комплексное гильбертово
  пространство `H` (mathlib-структуры: `NormedAddCommGroup` +
  `InnerProductSpace ℂ` + `CompleteSpace`) и ограниченный оператор
  `T : H →L[ℂ] H`, для которых:
    * `T` самосопряжён (`IsSelfAdjoint T`, звезда = сопряжение mathlib);
    * каждый нетривиальный нуль имеет форму `1/2 + z·I` с `z ∈ spectrum ℂ T`.

  Что математика ДОЛЖНА предъявить: сам оператор. В mathlib v4.31 нет ни
  кандидата, ни (для честной неограниченной формы — см. аудит §4) самой
  спектральной теории неограниченных операторов. Полнота формы не канонична
  (классический Гильберт–Пойя — неограниченный оператор); здесь честно названа
  ОГРАНИЧЕННАЯ форма — и §4 покажет, чего она стоит. -/
def OperatorSpectralAnchor (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint T ∧
    ∀ ρ : ℂ, NontrivialZeroM ρ →
      ∃ z ∈ spectrum ℂ T, ρ = 1 / 2 + z * Complex.I

/-- **ЗЕЛЁНЫЙ МОСТ: оператор ⟹ реализация.** Спектр самосопряжённого
    вещественен — mathlib `IsSelfAdjoint.mem_spectrum_eq_re` (C*-алгебра
    `H →L[ℂ] H` — готовый mathlib-инстанс). `E` := вещественные точки спектра;
    здесь самосопряжённость ПОТРЕБЛЯЕТСЯ по-настоящему: без неё `z` из
    спектра не обязан быть вещественным и `E ⊆ ℝ` не собрать. -/
theorem operatorAnchor_implies_realisation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hA : OperatorSpectralAnchor H T) : SpectralRealisation := by
  obtain ⟨hsa, hreal⟩ := hA
  refine ⟨{t : ℝ | (t : ℂ) ∈ spectrum ℂ T}, fun ρ hρ => ?_⟩
  obtain ⟨z, hz, hform⟩ := hreal ρ hρ
  have hzre : z = (z.re : ℂ) := hsa.mem_spectrum_eq_re hz
  refine ⟨z.re, ?_, ?_⟩
  · show ((z.re : ℝ) : ℂ) ∈ spectrum ℂ T
    rw [← hzre]; exact hz
  · rw [hform, hzre, Complex.ofReal_re]

/-- **ЗЕЛЁНАЯ КОМПОЗИЦИЯ: оператор ⟹ mathlib-RH.** Полная лестница якоря:
    самосопряжённый оператор реализует нули ⟹ нули на прямой ⟹ RH. -/
theorem riemannHypothesis_of_operatorAnchor
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hA : OperatorSpectralAnchor H T) : RiemannHypothesis :=
  riemannHypothesis_of_spectralRealisation (operatorAnchor_implies_realisation hA)

/-! ## §4. Аудит слоя оператора: ограниченная форма НЕ переименование — она ЖЁСТЧЕ цели -/

/--
  **Аналитический вход `UnboundedZeroOrdinates`.** Ординаты нетривиальных нулей
  неограниченны: выше любого порога есть нуль. Классика (Харди: бесконечно много
  нулей НА прямой; фон Мангольдт: `N(T) ~ (T/2π)log(T/2π)`), но в mathlib v4.31
  НЕТ ни одного конкретного нетривиального нуля и нет теоремы Харди — потому
  явный помеченный вход, а не теорема. -/
def UnboundedZeroOrdinates : Prop :=
  ∀ B : ℝ, ∃ ρ : ℂ, NontrivialZeroM ρ ∧ B < |ρ.im|

/--
  **ЗЕЛЁНАЯ НЕГАТИВНАЯ (аудит слоя оператора).** При неограниченных ординатах
  ОГРАНИЧЕННЫЙ якорь невыполним НИ ДЛЯ КАКОГО `T`: спектр ограниченного
  оператора лежит в шаре радиуса `‖T‖` (`spectrum.norm_le_norm_of_mem`), а нуль
  с `|Im ρ| > ‖T‖` требует спектральной точки `z = Im ρ` за пределами шара.

  Смысл аудита — асимметрия со слоем данных: слой (а) коллапсирует В цель
  (`spectralRealisation_iff_RH` — переименование), слой (в) в ограниченной
  форме падает ЗА цель (при классической аналитике он ложен, а не эквивалентен
  RH). Честный Гильберт–Пойя = НЕОГРАНИЧЕННЫЙ самосопряжённый оператор;
  в mathlib v4.31 есть `LinearPMap.adjoint` / `IsSelfAdjoint` для `E →ₗ.[𝕜] E`,
  но НЕТ `spectrum` для `LinearPMap` и НЕТ спектральной теоремы неограниченных
  операторов — точная недостача, которую математика должна предъявить. -/
theorem no_operatorAnchor_of_unbounded_ordinates
    (hUnb : UnboundedZeroOrdinates)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (T : H →L[ℂ] H) : ¬ OperatorSpectralAnchor H T := by
  rintro ⟨hsa, hreal⟩
  obtain ⟨ρ, hρ, hgt⟩ := hUnb ‖T‖
  obtain ⟨z, hz, hform⟩ := hreal ρ hρ
  have hzre : z = (z.re : ℂ) := hsa.mem_spectrum_eq_re hz
  have hform' : ρ = 1 / 2 + (z.re : ℂ) * Complex.I := by rw [← hzre]; exact hform
  have him : ρ.im = z.re := by rw [hform']; exact half_add_mul_I_im z.re
  have habs : |ρ.im| ≤ ‖T‖ := by
    rw [him]
    exact le_trans (Complex.abs_re_le_norm z) (spectrum.norm_le_norm_of_mem hz)
  exact absurd habs (not_le.mpr hgt)

/-! ## §5. Стыковка со SpectralAnchorAudit: data-уровень конкретного якоря -/

open EuclidsPath.Riemann.ArithmeticTwoTransport.SpectralAnchorData

/--
  **`zeroOrdinateLaw` — конкретный data-закон якоря (стыковка с аудитом).**
  Zero := нетривиальные нули (подтип `NontrivialZeroM`), Atom := ℝ (ординаты),
  Anchor Z t := «Z имеет форму `1/2 + t·I`». Это КАНОНИЧЕСКАЯ инстанциация
  `DataAnchoredLaw` из RiemannSpectralAnchorAudit для якоря Гильберта–Пойи. -/
def zeroOrdinateLaw : DataAnchoredLaw {ρ : ℂ // NontrivialZeroM ρ} ℝ where
  Admissible := fun _ => True
  Anchor := fun Z t => (Z : ℂ) = 1 / 2 + (t : ℂ) * Complex.I

/--
  **`zeroOrdinateInvariantAnchor` — НАСТОЯЩИЙ спектральный инвариант (ДОКАЗАН).**
  Инвариант = мнимая часть: атом `t`, заякоренный в нуле `Z`, обязан равняться
  `Im Z` — условие `respects` из аудита выполняется по-настоящему, значит один
  атом НЕ может обслужить два нуля с разными ординатами
  (`no_single_atom_anchors_two_distinct_invariants` применимо). Чего НЕТ:
  `NonVacuousDataAnchor.separates` требует ДВУХ нулей с разными ординатами,
  а в mathlib v4.31 нет ни одного конкретного нетривиального нуля дзеты. -/
def zeroOrdinateInvariantAnchor : SpectralInvariantAnchor zeroOrdinateLaw where
  Inv := ℝ
  zeroInv := fun Z => (Z : ℂ).im
  atomInv := id
  respects := fun Z t h => by
    show t = (Z : ℂ).im
    rw [h]
    exact (half_add_mul_I_im t).symm

/--
  **АУДИТ Prop-тени data-закона: снова дословно RH.** Мост
  `DataAnchoredLaw.Bridge zeroOrdinateLaw` ⟺ mathlib-`RiemannHypothesis` —
  та же участь, что у слоя (а): Prop-тень data-закона без оператора-поставщика
  атомов есть переименование цели. Урок аудита (SpectralAnchorAudit §2)
  воспроизведён на конкретном якоре: невакуумность обязана жить на уровне
  ДАННЫХ (экстрактор + инвариант), поставщик данных — оператор §3. -/
theorem zeroOrdinateBridge_iff_RH :
    DataAnchoredLaw.Bridge zeroOrdinateLaw ↔ RiemannHypothesis := by
  constructor
  · intro hB ρ hz htriv hne1
    obtain ⟨t, _, hform⟩ := hB ⟨ρ, hz, htriv, hne1⟩
    have hρform : ρ = 1 / 2 + (t : ℂ) * Complex.I := hform
    rw [hρform]
    exact half_add_mul_I_re t
  · intro hRH Z
    exact ⟨(Z : ℂ).im, trivial,
      eq_half_add_of_re_eq_half (hRH Z.val Z.prop.1 Z.prop.2.1 Z.prop.2.2)⟩

end EuclidsPath.RiemannSpectralAnchor

/-! Проверка аксиом: допустимо только подмножество [propext, Classical.choice, Quot.sound]. -/
#print axioms EuclidsPath.RiemannSpectralAnchor.half_add_mul_I_re
#print axioms EuclidsPath.RiemannSpectralAnchor.half_add_mul_I_im
#print axioms EuclidsPath.RiemannSpectralAnchor.eq_half_add_of_re_eq_half
#print axioms EuclidsPath.RiemannSpectralAnchor.SpectralRealisation
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_implies_critical
#print axioms EuclidsPath.RiemannSpectralAnchor.riemannHypothesis_of_spectralRealisation
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_of_RH
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_iff_critical
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_iff_RH
#print axioms EuclidsPath.RiemannSpectralAnchor.OperatorSpectralAnchor
#print axioms EuclidsPath.RiemannSpectralAnchor.operatorAnchor_implies_realisation
#print axioms EuclidsPath.RiemannSpectralAnchor.riemannHypothesis_of_operatorAnchor
#print axioms EuclidsPath.RiemannSpectralAnchor.UnboundedZeroOrdinates
#print axioms EuclidsPath.RiemannSpectralAnchor.no_operatorAnchor_of_unbounded_ordinates
#print axioms EuclidsPath.RiemannSpectralAnchor.zeroOrdinateLaw
#print axioms EuclidsPath.RiemannSpectralAnchor.zeroOrdinateInvariantAnchor
#print axioms EuclidsPath.RiemannSpectralAnchor.zeroOrdinateBridge_iff_RH
