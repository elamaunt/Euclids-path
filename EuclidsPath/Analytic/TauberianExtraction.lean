/-
  Analytic/TauberianExtraction — STAGE P-C1 of the Tauberian campaign:
  the two ELEMENTARY EXTRACTION lemmas (pure real analysis).

  Newman's theorem delivers convergence of `∫_1^X S(t)/t dt`.  The
  arithmetic chains need pointwise asymptotics.  The bridge is purely
  elementary and uses ONLY the Cauchy property of the convergent
  integral over multiplicative windows `(x, (1+δ)x]`:

    * `tendsto_div_of_monotone_of_integral_tendsto` — Newman's classical
      MONOTONE extraction: `P` nondecreasing on `[1,∞)` and
      `∫_1^X (P(t)/t − l)/t dt` convergent force `P(x)/x → l`
      (window contradiction on both sides);
    * `tendsto_partialSum_div_of_integral_tendsto` — the ±1-BOUNDED
      extraction for signed sums (the Liouville consumer): partial sums
      `L` of a `|f| ≤ 1` sequence with `∫_1^X L(t)/t² dt` convergent
      are `o(x)` (one right window serves both signs, threshold
      `x ≥ 8/ε`).

  DISCLOSURES.
    * Pure real analysis: no arithmetic content, no face of the parity
      wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open MeasureTheory Filter Set
open scoped Interval

/-! ### The window engine -/

/-- The CAUCHY WINDOW: if the partial integrals converge, the integral
over the multiplicative window `(x, (1+δ)x]` dies. -/
theorem tendsto_window_integral_zero {h : ℝ → ℝ} {I : ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hloc : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntegrableOn h (Set.Ioc a b))
    (hint : Tendsto (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X, h t)
      atTop (nhds I)) :
    Tendsto (fun x : ℝ => ∫ t in Set.Ioc x ((1 + δ) * x), h t)
      atTop (nhds 0) := by
  have hmul : Tendsto (fun x : ℝ => (1 + δ) * x) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) tendsto_id
  have hdiff := (hint.comp hmul).sub hint
  rw [sub_self] at hdiff
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [Function.comp_apply]
  have hle : x ≤ (1 + δ) * x := by nlinarith
  rw [← Set.Ioc_union_Ioc_eq_Ioc hx hle,
    MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc (hloc 1 x le_rfl hx) (hloc x ((1 + δ) * x) hx hle)]
  ring

/-! ### The monotone extraction -/

section Monotone

variable {P : ℝ → ℝ} {l I : ℝ}

/-- Upper window contradiction: eventually `P x/x < l + ε`. -/
theorem monotone_extraction_upper (hl : 0 < l)
    (hmono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → P x ≤ P y)
    (hloc : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntegrableOn (fun t => (P t / t - l) / t) (Set.Ioc a b))
    (hint : Tendsto
      (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X, (P t / t - l) / t)
      atTop (nhds I))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ x in atTop, P x / x < l + ε := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  set δ : ℝ := ε / (2 * (l + 1)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1δ : 0 < 1 + δ := by linarith
  have hkey : ε / 2 ≤ (l + ε) / (1 + δ) - l := by
    rw [le_sub_iff_add_le, le_div_iff₀ h1δ]
    have hδl : δ * (l + ε / 2) ≤ ε / 2 := by
      rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  set c : ℝ := δ * ε / (2 * (1 + δ)) with hcdef
  have hc0 : 0 < c := by positivity
  have hwin := tendsto_window_integral_zero hδ0 hloc hint
  have hev : ∀ᶠ x in atTop,
      |∫ t in Set.Ioc x ((1 + δ) * x), (P t / t - l) / t| < c := by
    filter_upwards [Metric.tendsto_nhds.mp hwin c hc0] with x hx
    rwa [dist_zero_right, Real.norm_eq_abs] at hx
  obtain ⟨x, hxP, hxW, hx1⟩ :=
    (hcon.and_eventually (hev.and (eventually_ge_atTop 1))).exists
  push Not at hxP
  have hxpos : (0 : ℝ) < x := by linarith
  have hPx : (l + ε) * x ≤ P x := (le_div_iff₀ hxpos).mp hxP
  have hlow : ∀ t ∈ Set.Ioc x ((1 + δ) * x),
      ε / 2 / ((1 + δ) * x) ≤ (P t / t - l) / t := by
    intro t ht
    have htx : x < t := ht.1
    have htub : t ≤ (1 + δ) * x := ht.2
    have htpos : (0 : ℝ) < t := by linarith
    have hPt : P x ≤ P t := hmono x t hx1 htx.le
    have hPtt : (l + ε) / (1 + δ) ≤ P t / t := by
      rw [div_le_div_iff₀ h1δ htpos]
      calc (l + ε) * t ≤ (l + ε) * ((1 + δ) * x) := by nlinarith
        _ = ((l + ε) * x) * (1 + δ) := by ring
        _ ≤ P x * (1 + δ) := by nlinarith
        _ ≤ P t * (1 + δ) := by nlinarith
    have hstep1 : ε / 2 / t ≤ (P t / t - l) / t :=
      (div_le_div_iff_of_pos_right htpos).mpr (by linarith [hkey, hPtt])
    have hstep2 : ε / 2 / ((1 + δ) * x) ≤ ε / 2 / t :=
      (div_le_div_iff_of_pos_left (by positivity)
        (by positivity) htpos).mpr htub
    linarith
  have hintlow : c ≤ ∫ t in Set.Ioc x ((1 + δ) * x), (P t / t - l) / t := by
    have hconst : ∫ _ in Set.Ioc x ((1 + δ) * x), (ε / 2 / ((1 + δ) * x) : ℝ)
        ≤ ∫ t in Set.Ioc x ((1 + δ) * x), (P t / t - l) / t :=
      setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
        (hloc x ((1 + δ) * x) hx1 (by nlinarith)) measurableSet_Ioc hlow
    have hm : (volume : Measure ℝ).real (Set.Ioc x ((1 + δ) * x))
        = (1 + δ) * x - x := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by nlinarith : (0 : ℝ) ≤ (1 + δ) * x - x)]
    have hval : ∫ _ in Set.Ioc x ((1 + δ) * x), (ε / 2 / ((1 + δ) * x) : ℝ)
        = ((1 + δ) * x - x) * (ε / 2 / ((1 + δ) * x)) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hm]
    have hval2 : ((1 + δ) * x - x) * (ε / 2 / ((1 + δ) * x)) = c := by
      rw [hcdef]
      field_simp
      ring
    calc c = ((1 + δ) * x - x) * (ε / 2 / ((1 + δ) * x)) := hval2.symm
      _ = ∫ _ in Set.Ioc x ((1 + δ) * x), (ε / 2 / ((1 + δ) * x) : ℝ) :=
        hval.symm
      _ ≤ _ := hconst
  rw [abs_lt] at hxW
  linarith [hxW.2]

/-- Lower window contradiction: for `ε < l`, eventually `l − ε < P x/x`
(via the LEFT window, reparametrized through the engine). -/
theorem monotone_extraction_lower (hl : 0 < l)
    (hmono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → P x ≤ P y)
    (hloc : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntegrableOn (fun t => (P t / t - l) / t) (Set.Ioc a b))
    (hint : Tendsto
      (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X, (P t / t - l) / t)
      atTop (nhds I))
    {ε : ℝ} (hε : 0 < ε) (hεl : ε < l) (_hε1 : ε ≤ 1) :
    ∀ᶠ x in atTop, l - ε < P x / x := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  set δ : ℝ := ε / (2 * (l + 1)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1δ' : 0 < 1 - δ := by linarith
  have hkey : (l - ε) / (1 - δ) ≤ l - ε / 2 := by
    rw [div_le_iff₀ h1δ']
    have hδl : δ * (l - ε / 2) ≤ ε / 2 := by
      rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  set δ' : ℝ := δ / (1 - δ) with hδ'def
  have hδ'0 : 0 < δ' := by positivity
  set c : ℝ := δ * (ε / 2) with hcdef
  have hc0 : 0 < c := by positivity
  have hwin0 := tendsto_window_integral_zero hδ'0 hloc hint
  have hmul : Tendsto (fun x : ℝ => (1 - δ) * x) atTop atTop :=
    Tendsto.const_mul_atTop h1δ' tendsto_id
  have hwin : Tendsto
      (fun x : ℝ => ∫ t in Set.Ioc ((1 - δ) * x) x, (P t / t - l) / t)
      atTop (nhds 0) := by
    have hend : ∀ x : ℝ, (1 + δ') * ((1 - δ) * x) = x := by
      intro x
      rw [hδ'def]
      field_simp
      ring
    have hcomp := hwin0.comp hmul
    apply hcomp.congr
    intro x
    simp only [Function.comp_apply]
    rw [hend x]
  have hev : ∀ᶠ x in atTop,
      |∫ t in Set.Ioc ((1 - δ) * x) x, (P t / t - l) / t| < c := by
    filter_upwards [Metric.tendsto_nhds.mp hwin c hc0] with x hx
    rwa [dist_zero_right, Real.norm_eq_abs] at hx
  obtain ⟨x, hxP, hxW, hxbig⟩ :=
    (hcon.and_eventually (hev.and
      (eventually_ge_atTop (1 / (1 - δ))))).exists
  push Not at hxP
  have hxlarge : 1 ≤ (1 - δ) * x := by
    rw [div_le_iff₀ h1δ'] at hxbig
    nlinarith [hxbig]
  have hxpos : (0 : ℝ) < x := by nlinarith
  have hx1 : (1 : ℝ) ≤ x := by nlinarith
  have hPx : P x ≤ (l - ε) * x := by
    rw [div_le_iff₀ hxpos] at hxP
    linarith
  have hup : ∀ t ∈ Set.Ioc ((1 - δ) * x) x,
      (P t / t - l) / t ≤ -(ε / 2) / x := by
    intro t ht
    have htlb : (1 - δ) * x < t := ht.1
    have htx : t ≤ x := ht.2
    have htpos : (0 : ℝ) < t := by nlinarith
    have ht1 : (1 : ℝ) ≤ t := by nlinarith
    have hPt : P t ≤ P x := hmono t x ht1 htx
    have hPtt : P t / t ≤ (l - ε) / (1 - δ) := by
      rw [div_le_div_iff₀ htpos h1δ']
      calc P t * (1 - δ) ≤ ((l - ε) * x) * (1 - δ) := by nlinarith
        _ = (l - ε) * ((1 - δ) * x) := by ring
        _ ≤ (l - ε) * t := by nlinarith [sub_pos.mpr hεl]
    have hneg : P t / t - l ≤ -(ε / 2) := by
      linarith [hkey, hPtt]
    calc (P t / t - l) / t ≤ -(ε / 2) / t :=
          (div_le_div_iff_of_pos_right htpos).mpr hneg
      _ ≤ -(ε / 2) / x := by
          rw [neg_div, neg_div, neg_le_neg_iff]
          exact (div_le_div_iff_of_pos_left (by positivity)
            hxpos htpos).mpr htx
  have hinthigh : ∫ t in Set.Ioc ((1 - δ) * x) x, (P t / t - l) / t ≤ -c := by
    have hconst : ∫ t in Set.Ioc ((1 - δ) * x) x, (P t / t - l) / t
        ≤ ∫ _ in Set.Ioc ((1 - δ) * x) x, (-(ε / 2) / x : ℝ) :=
      setIntegral_mono_on
        (hloc ((1 - δ) * x) x hxlarge (by nlinarith))
        (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc hup
    have hm : (volume : Measure ℝ).real (Set.Ioc ((1 - δ) * x) x)
        = x - (1 - δ) * x := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by nlinarith : (0 : ℝ) ≤ x - (1 - δ) * x)]
    have hval : ∫ _ in Set.Ioc ((1 - δ) * x) x, (-(ε / 2) / x : ℝ)
        = (x - (1 - δ) * x) * (-(ε / 2) / x) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hm]
    have hval2 : (x - (1 - δ) * x) * (-(ε / 2) / x) = -c := by
      rw [hcdef]
      field_simp
      ring
    calc ∫ t in Set.Ioc ((1 - δ) * x) x, (P t / t - l) / t
        ≤ ∫ _ in Set.Ioc ((1 - δ) * x) x, (-(ε / 2) / x : ℝ) := hconst
      _ = -c := by rw [hval, hval2]
  rw [abs_lt] at hxW
  linarith [hxW.1]

/-- **NEWMAN'S MONOTONE EXTRACTION**: a nondecreasing `P` on `[1,∞)` whose
weighted deficiency integral converges has `P(x)/x → l`. -/
theorem tendsto_div_of_monotone_of_integral_tendsto (hl : 0 < l)
    (hmono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → P x ≤ P y) (_h0 : 0 ≤ P 1)
    (hloc : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntegrableOn (fun t => (P t / t - l) / t) (Set.Ioc a b))
    (hint : Tendsto
      (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X, (P t / t - l) / t)
      atTop (nhds I)) :
    Tendsto (fun x : ℝ => P x / x) atTop (nhds l) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := min ε (min 1 (l / 2)) with hε'def
  have hε'0 : 0 < ε' := by
    rw [hε'def]
    exact lt_min hε (lt_min one_pos (by linarith))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε'l : ε' < l := lt_of_le_of_lt
    (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  have hup := monotone_extraction_upper hl hmono hloc hint hε'0 hε'1
  have hlo := monotone_extraction_lower hl hmono hloc hint hε'0 hε'l hε'1
  filter_upwards [hup, hlo] with x hx1 hx2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Monotone

/-! ### The ±1-bounded extraction (the Liouville consumer) -/

section BoundedSum

variable {f : ℕ → ℝ}

/-- The increment bound: partial sums of a `|f| ≤ 1` sequence move by at
most `y − x + 1` between `x` and `y`. -/
theorem abs_partialSum_sub_le (hf : ∀ n, |f n| ≤ 1) {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    |(∑ k ∈ Finset.Icc 1 ⌊y⌋₊, f k) - ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k|
      ≤ y - x + 1 := by
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hsplit : Finset.Icc 1 ⌊y⌋₊
      = Finset.Icc 1 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact absurd (Finset.mem_Icc.mp ha).2
      (not_le.mpr (Finset.mem_Ioc.mp ha').1)
  rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
  calc |∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, f k|
      ≤ ∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => hf k)
    _ = ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by
        rw [Finset.sum_const, Nat.card_Ioc]
        simp
    _ ≤ y - x + 1 := by
        have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
        have h2 : x - 1 < (⌊x⌋₊ : ℝ) := by
          linarith [Nat.lt_floor_add_one x]
        rw [Nat.cast_sub hfl]
        linarith

/-- The partial-sum bound: `|L t| ≤ t` for `t ≥ 1`. -/
theorem abs_partialSum_le (hf : ∀ n, |f n| ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    |∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k| ≤ t := by
  calc |∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k|
      ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => hf k)
    _ = (⌊t⌋₊ : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp
    _ ≤ t := Nat.floor_le (by linarith)

/-- **THE ±1-BOUNDED EXTRACTION**: partial sums with convergent
`∫_1^X L(t)/t² dt` are `o(x)` — one right window serves both signs. -/
theorem tendsto_partialSum_div_of_integral_tendsto (hf : ∀ n, |f n| ≤ 1)
    {I : ℝ}
    (hint : Tendsto (fun X : ℝ => ∫ t in Set.Ioc (1 : ℝ) X,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) / t ^ 2) atTop (nhds I)) :
    Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k) / x)
      atTop (nhds 0) := by
  set L : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k with hLdef
  have hLmeas : Measurable L := by
    rw [hLdef]
    exact (measurable_from_nat
      (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor
  have hloc : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntegrableOn (fun t => L t / t ^ 2) (Set.Ioc a b) := by
    intro a b ha hab
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((hLmeas.div (measurable_id.pow_const 2)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : 1 ≤ t := le_trans ha ht.1.le
    have htpos : (0 : ℝ) < t := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2),
      div_le_one (by positivity)]
    calc |L t| ≤ t := abs_partialSum_le hf ht1
      _ ≤ t ^ 2 := by nlinarith
  have hkey : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop, |L x| < ε * x := by
    intro ε hε hε1
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    set δ : ℝ := ε / 4 with hδdef
    have hδ0 : 0 < δ := by positivity
    set c : ℝ := δ * (ε / 2) / (1 + δ) ^ 2 with hcdef
    have hc0 : 0 < c := by positivity
    have hwin := tendsto_window_integral_zero hδ0 hloc hint
    have hev : ∀ᶠ x in atTop,
        |∫ t in Set.Ioc x ((1 + δ) * x), L t / t ^ 2| < c := by
      filter_upwards [Metric.tendsto_nhds.mp hwin c hc0] with x hx
      rwa [dist_zero_right, Real.norm_eq_abs] at hx
    have hsign : (∃ᶠ x in atTop, ε * x ≤ L x)
        ∨ ∃ᶠ x in atTop, L x ≤ -(ε * x) := by
      apply Filter.frequently_or_distrib.mp
      apply hcon.mono
      intro x hx
      push Not at hx
      rcases abs_cases (L x) with ⟨heq, _⟩ | ⟨heq, _⟩
      · left; linarith
      · right; linarith
    have hwindow_est : ∀ x : ℝ, 1 ≤ x → 4 / ε ≤ x →
        ∀ t ∈ Set.Ioc x ((1 + δ) * x),
          (1 ≤ t ∧ t ^ 2 ≤ ((1 + δ) * x) ^ 2 ∧ |L t - L x| ≤ δ * x + 1
            ∧ (ε / 4) * x ≥ 1) := by
      intro x hx1 hx4 t ht
      have htx : x < t := ht.1
      have htub : t ≤ (1 + δ) * x := ht.2
      have ht1 : 1 ≤ t := by linarith
      have hxpos : (0 : ℝ) < x := by linarith
      refine ⟨ht1, ?_, ?_, ?_⟩
      · nlinarith
      · have hstep := abs_partialSum_sub_le hf hx1 htx.le
        calc |L t - L x| ≤ t - x + 1 := hstep
          _ ≤ δ * x + 1 := by nlinarith
      · have hmul := mul_le_mul_of_nonneg_left hx4
          (by positivity : (0 : ℝ) ≤ ε / 4)
        have h14 : ε / 4 * (4 / ε) = 1 := by field_simp
        rw [ge_iff_le]
        linarith
    rcases hsign with hpos | hneg
    · obtain ⟨x, hxL, hxW, hxbig⟩ := (hpos.and_eventually
        (hev.and (eventually_ge_atTop (max 1 (4 / ε))))).exists
      have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hxbig
      have hx4 : 4 / ε ≤ x := le_trans (le_max_right _ _) hxbig
      have hxpos : (0 : ℝ) < x := by linarith
      have hlow : ∀ t ∈ Set.Ioc x ((1 + δ) * x),
          (ε / 2) * x / ((1 + δ) * x) ^ 2 ≤ L t / t ^ 2 := by
        intro t ht
        obtain ⟨ht1, htsq, hinc, hεx⟩ := hwindow_est x hx1 hx4 t ht
        have hLt : (ε / 2) * x ≤ L t := by
          have h1 : L x - (δ * x + 1) ≤ L t := by
            have := abs_le.mp hinc
            linarith [this.1]
          have h2 : (ε / 2) * x ≤ ε * x - (δ * x + 1) := by
            rw [hδdef]
            nlinarith
          linarith
        have htpos : (0 : ℝ) < t := by linarith
        calc (ε / 2) * x / ((1 + δ) * x) ^ 2
            ≤ (ε / 2) * x / t ^ 2 :=
              (div_le_div_iff_of_pos_left (by positivity)
                (by positivity) (by positivity)).mpr htsq
          _ ≤ L t / t ^ 2 :=
              (div_le_div_iff_of_pos_right (by positivity)).mpr hLt
      have hintlow : c ≤ ∫ t in Set.Ioc x ((1 + δ) * x), L t / t ^ 2 := by
        have hconst : ∫ _ in Set.Ioc x ((1 + δ) * x),
            ((ε / 2) * x / ((1 + δ) * x) ^ 2 : ℝ)
            ≤ ∫ t in Set.Ioc x ((1 + δ) * x), L t / t ^ 2 :=
          setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
            (hloc x ((1 + δ) * x) hx1 (by nlinarith)) measurableSet_Ioc hlow
        have hm : (volume : Measure ℝ).real (Set.Ioc x ((1 + δ) * x))
            = (1 + δ) * x - x := by
          rw [measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by nlinarith : (0 : ℝ) ≤ (1 + δ) * x - x)]
        have hval : ∫ _ in Set.Ioc x ((1 + δ) * x),
            ((ε / 2) * x / ((1 + δ) * x) ^ 2 : ℝ)
            = ((1 + δ) * x - x) * ((ε / 2) * x / ((1 + δ) * x) ^ 2) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, hm]
        have hval2 : ((1 + δ) * x - x) * ((ε / 2) * x / ((1 + δ) * x) ^ 2)
            = c := by
          rw [hcdef]
          field_simp
          ring
        calc c = ((1 + δ) * x - x) * ((ε / 2) * x / ((1 + δ) * x) ^ 2) :=
            hval2.symm
          _ = ∫ _ in Set.Ioc x ((1 + δ) * x),
              ((ε / 2) * x / ((1 + δ) * x) ^ 2 : ℝ) := hval.symm
          _ ≤ _ := hconst
      rw [abs_lt] at hxW
      linarith [hxW.2]
    · obtain ⟨x, hxL, hxW, hxbig⟩ := (hneg.and_eventually
        (hev.and (eventually_ge_atTop (max 1 (4 / ε))))).exists
      have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hxbig
      have hx4 : 4 / ε ≤ x := le_trans (le_max_right _ _) hxbig
      have hxpos : (0 : ℝ) < x := by linarith
      have hup : ∀ t ∈ Set.Ioc x ((1 + δ) * x),
          L t / t ^ 2 ≤ -((ε / 2) * x / ((1 + δ) * x) ^ 2) := by
        intro t ht
        obtain ⟨ht1, htsq, hinc, hεx⟩ := hwindow_est x hx1 hx4 t ht
        have hLt : L t ≤ -((ε / 2) * x) := by
          have h1 : L t ≤ L x + (δ * x + 1) := by
            have := abs_le.mp hinc
            linarith [this.2]
          have h2 : -(ε * x) + (δ * x + 1) ≤ -((ε / 2) * x) := by
            rw [hδdef]
            nlinarith
          linarith
        have htpos : (0 : ℝ) < t := by linarith
        calc L t / t ^ 2 ≤ -((ε / 2) * x) / t ^ 2 :=
              (div_le_div_iff_of_pos_right (by positivity)).mpr hLt
          _ ≤ -((ε / 2) * x / ((1 + δ) * x) ^ 2) := by
              rw [neg_div, neg_le_neg_iff]
              exact (div_le_div_iff_of_pos_left (by positivity)
                (by positivity) (by positivity)).mpr htsq
      have hinthigh : ∫ t in Set.Ioc x ((1 + δ) * x), L t / t ^ 2 ≤ -c := by
        have hconst : ∫ t in Set.Ioc x ((1 + δ) * x), L t / t ^ 2
            ≤ ∫ _ in Set.Ioc x ((1 + δ) * x),
              (-((ε / 2) * x / ((1 + δ) * x) ^ 2) : ℝ) :=
          setIntegral_mono_on
            (hloc x ((1 + δ) * x) hx1 (by nlinarith))
            (integrableOn_const (hs := measure_Ioc_lt_top.ne))
            measurableSet_Ioc hup
        have hm : (volume : Measure ℝ).real (Set.Ioc x ((1 + δ) * x))
            = (1 + δ) * x - x := by
          rw [measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by nlinarith : (0 : ℝ) ≤ (1 + δ) * x - x)]
        have hval : ∫ _ in Set.Ioc x ((1 + δ) * x),
            (-((ε / 2) * x / ((1 + δ) * x) ^ 2) : ℝ)
            = ((1 + δ) * x - x) * (-((ε / 2) * x / ((1 + δ) * x) ^ 2)) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, hm]
        have hval2 : ((1 + δ) * x - x)
            * (-((ε / 2) * x / ((1 + δ) * x) ^ 2)) = -c := by
          rw [hcdef]
          field_simp
          ring
        calc ∫ t in Set.Ioc x ((1 + δ) * x), L t / t ^ 2
            ≤ ∫ _ in Set.Ioc x ((1 + δ) * x),
              (-((ε / 2) * x / ((1 + δ) * x) ^ 2) : ℝ) := hconst
          _ = -c := by rw [hval, hval2]
      rw [abs_lt] at hxW
      linarith [hxW.1]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := min ε 1 with hε'def
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  filter_upwards [hkey ε' hε'0 hε'1, eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hxpos,
    div_lt_iff₀ hxpos]
  calc |L x| < ε' * x := hx
    _ ≤ ε * x := by
        have : ε' ≤ ε := min_le_left _ _
        nlinarith

end BoundedSum

end Analytic
end EuclidsPath
