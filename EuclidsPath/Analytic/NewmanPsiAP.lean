/-
  Analytic/NewmanPsiAP — STAGE P-C2 of the Tauberian campaign: THE SINGLE
  NEWMAN APPLICATION for ψ-type sums, uniformly in the modulus.

  `psiRes_div_tendsto`: for a unit class `a` mod `q`,
  `psiRes(a, x)/x → 1/φ(q)`.  At `q = 1` this IS the Prime Number
  Theorem in ψ-form; at `q = 6` it is PNT in the progressions the twin
  wall lives on.  UNCONDITIONAL: the Newman interface was discharged in
  P-A0, so no hypothesis is threaded.

  Assembly: `S(t) := psiRes(a,t)/t − 1/φ(q)` is measurable and uniformly
  bounded (Chebyshev); the Mellin data
  `g(z) := (aux(z+1) − 1/φ(q))/(z+1)` is holomorphic on the shifted
  zero-free set (P-B2) and represents `∫_1^∞ S·t^{−z−1}` on `Re z > 0`
  (P-B1 + the pin's `eqOn_LFunctionResidueClassAux`); Newman (P-A0)
  gives convergence of `∫_1^X S/t`, and the monotone extraction (P-C1)
  turns it into the pointwise limit.  The limit VALUE `g(0)` is never
  evaluated — the extraction only uses the Cauchy property.

  DISCLOSURES.
    * PNT-in-AP machinery over the pin's frame: no face of the parity
      wall is touched, and no §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Analytic.NewmanInterface
import EuclidsPath.Analytic.MellinPartialSums
import EuclidsPath.Analytic.ZeroFreeNbhd
import EuclidsPath.Analytic.TauberianExtraction

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex ArithmeticFunction Filter MeasureTheory Set DirichletCharacter
open scoped LSeries.notation

/-- **PNT in arithmetic progressions, ψ-form** (unconditional): for a
unit class `a` mod `q`, `psiRes(a,x)/x → 1/φ(q)`. -/
theorem psiRes_div_tendsto {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ => psiRes a x / x) atTop
      (nhds ((Nat.totient q : ℝ)⁻¹)) := by
  set l : ℝ := (Nat.totient q : ℝ)⁻¹ with hldef
  have htot : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  have hl0 : 0 < l := by rw [hldef]; exact inv_pos.mpr htot
  have hl1 : l ≤ 1 := by
    rw [hldef]
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  have hmeas : Measurable (psiRes a) := by
    unfold psiRes
    exact (measurable_from_nat
      (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
        vonMangoldt.residueClass a k)).comp Nat.measurable_floor
  -- the uniform bound
  have hSbdd : ∀ t : ℝ, 1 ≤ t →
      |psiRes a t / t - l| ≤ Real.log 4 + 4 + 1 := by
    intro t ht
    have htpos : (0 : ℝ) < t := by linarith
    have h1 : 0 ≤ psiRes a t / t := div_nonneg (psiRes_nonneg a t) htpos.le
    have h2 : psiRes a t / t ≤ Real.log 4 + 4 := by
      rw [div_le_iff₀ htpos]
      exact psiRes_le_linear a htpos.le
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    constructor <;> nlinarith
  -- the open set and the holomorphic data
  have hUopen : IsOpen (((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q)
      ∩ {(-1 : ℂ)}ᶜ) :=
    ((isOpen_zeroFreeSet q).preimage (by fun_prop)).inter
      isOpen_compl_singleton
  have hUmem : {z : ℂ | 0 ≤ z.re}
      ⊆ ((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q) ∩ {(-1 : ℂ)}ᶜ := by
    intro z hz
    have hz0 : 0 ≤ z.re := hz
    constructor
    · apply closedHalfPlane_subset_zeroFreeSet q
      show 1 ≤ (z + 1).re
      simp only [Complex.add_re, Complex.one_re]
      linarith
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [h] at hz0
      norm_num at hz0
  have hgdiff : DifferentiableOn ℂ
      (fun z => (vonMangoldt.LFunctionResidueClassAux a (z + 1)
        - ((l : ℝ) : ℂ)) / (z + 1))
      (((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q) ∩ {(-1 : ℂ)}ᶜ) := by
    apply DifferentiableOn.div
    · apply DifferentiableOn.sub ?_ (differentiableOn_const _)
      exact DifferentiableOn.comp
        (g := vonMangoldt.LFunctionResidueClassAux a)
        (f := fun z : ℂ => z + 1)
        (differentiableOn_LFunctionResidueClassAux q a)
        ((differentiable_id.add_const 1).differentiableOn)
        (fun w hw => hw.1)
    · intro z _
      exact ((differentiable_id.add_const 1) z).differentiableWithinAt
    · intro z hz h0
      apply hz.2
      simp only [Set.mem_singleton_iff]
      linear_combination h0
  -- the Mellin representation of S
  have hrep : ∀ z : ℂ, 0 < z.re →
      (fun z => (vonMangoldt.LFunctionResidueClassAux a (z + 1)
        - ((l : ℝ) : ℂ)) / (z + 1)) z
        = ∫ t in Set.Ioi (1 : ℝ),
            ((psiRes a t / t - l : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    intro z hz
    have hs1 : 1 < (z + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hs0 : (z + 1) ≠ 0 := by
      intro h
      have := congr_arg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
    -- the O(n) bound, complex-cast
    have hOc : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
        ((vonMangoldt.residueClass a k : ℝ) : ℂ))
        =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
      rw [← Asymptotics.isBigO_norm_left]
      refine (Asymptotics.isBigO_norm_left.mpr (isBigO_psiRes a)).congr_left
        fun n => ?_
      rw [show (∑ k ∈ Finset.Icc 1 n, ((vonMangoldt.residueClass a k : ℝ) : ℂ))
          = ((∑ k ∈ Finset.Icc 1 n, vonMangoldt.residueClass a k : ℝ) : ℂ) by
        push_cast; rfl, Complex.norm_real]
    have hint1 : IntegrableOn (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          ((vonMangoldt.residueClass a k : ℝ) : ℂ)) * (t : ℂ) ^ (-(z + 1) - 1))
        (Set.Ioi 1) := integrableOn_partialSum_mul_cpow hOc hs1
    have hlt : (-z - 1 : ℂ).re < -1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    have hint2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt hlt zero_lt_one
    have hval2 : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-z - 1) = 1 / z := by
      rw [integral_Ioi_cpow_of_lt hlt zero_lt_one]
      rw [show (-z - 1 + 1 : ℂ) = -z by ring, Complex.ofReal_one, one_cpow]
      rw [div_eq_div_iff (by simpa using hz0) hz0]
      ring
    -- the split
    have hsplit : ∫ t in Set.Ioi (1 : ℝ),
        ((psiRes a t / t - l : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)
        = (∫ t in Set.Ioi (1 : ℝ),
            (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
              ((vonMangoldt.residueClass a k : ℝ) : ℂ))
              * (t : ℂ) ^ (-(z + 1) - 1))
          - ((l : ℝ) : ℂ) * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-z - 1) := by
      rw [← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_sub hint1 (hint2.const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : (t : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      have hpsi : ((psiRes a t : ℝ) : ℂ)
          = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
              ((vonMangoldt.residueClass a k : ℝ) : ℂ) := by
        unfold psiRes
        push_cast
        rfl
      have hcpow : (t : ℂ) ^ (-(z + 1) - 1)
          = (t : ℂ) ^ (-z - 1) / (t : ℂ) := by
        rw [show (-(z + 1) - 1 : ℂ) = (-z - 1) + (-1) by ring,
          Complex.cpow_add _ _ ht0, Complex.cpow_neg_one]
        ring
      rw [hcpow, ← hpsi]
      push_cast
      field_simp
    rw [hsplit, hval2]
    -- LSeries plug and telescoping
    have hL := LSeries_residueClass_eq_mul_integral a hs1
    have halign : ∫ t in Set.Ioi (1 : ℝ),
        ((psiRes a t : ℝ) : ℂ) * (t : ℂ) ^ (-((z + 1) + 1))
        = ∫ t in Set.Ioi (1 : ℝ),
            (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
              ((vonMangoldt.residueClass a k : ℝ) : ℂ))
              * (t : ℂ) ^ (-(z + 1) - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have hpsi : ((psiRes a t : ℝ) : ℂ)
          = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
              ((vonMangoldt.residueClass a k : ℝ) : ℂ) := by
        unfold psiRes
        push_cast
        rfl
      rw [hpsi, show (-((z + 1) + 1) : ℂ) = -(z + 1) - 1 by ring]
    rw [halign] at hL
    have heq := vonMangoldt.eqOn_LFunctionResidueClassAux ha
      (Set.mem_setOf.mpr hs1)
    simp only at heq
    -- heq : aux (z+1) = L ↗(residueClass a) (z+1) − (totient)⁻¹/((z+1)−1)
    have hltot : ((l : ℝ) : ℂ) = ((Nat.totient q : ℕ) : ℂ)⁻¹ := by
      rw [hldef]
      push_cast
      rfl
    rw [show ((z + 1) - 1 : ℂ) = z by ring] at heq
    -- assemble: goal (aux(z+1) − l)/(z+1) = ∫Σ − l·(1/z)
    -- from hL: ∫Σ = L/(z+1); from heq: L = aux + l/z
    have hInt_eq : ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
          ((vonMangoldt.residueClass a k : ℝ) : ℂ))
          * (t : ℂ) ^ (-(z + 1) - 1)
        = LSeries ↗(vonMangoldt.residueClass a) (z + 1) / (z + 1) := by
      rw [hL]
      field_simp
    rw [hInt_eq]
    show (vonMangoldt.LFunctionResidueClassAux a (z + 1) - ((l : ℝ) : ℂ))
        / (z + 1)
        = LSeries ↗(vonMangoldt.residueClass a) (z + 1) / (z + 1)
          - ((l : ℝ) : ℂ) * (1 / z)
    rw [heq, hltot]
    field_simp
    ring
  -- Newman + extraction
  have hNewman := newmanMellin_proved
    (fun t : ℝ => ((psiRes a t / t - l : ℝ) : ℂ))
    (fun z => (vonMangoldt.LFunctionResidueClassAux a (z + 1)
      - ((l : ℝ) : ℂ)) / (z + 1))
    (((fun z : ℂ => z + 1) ⁻¹' zeroFreeSet q) ∩ {(-1 : ℂ)}ᶜ)
    (Real.log 4 + 4 + 1)
    (Complex.measurable_ofReal.comp
      ((hmeas.div measurable_id).sub measurable_const))
    (fun t ht => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hSbdd t ht)
    hUopen hUmem hgdiff hrep
  -- descend to the real integral and extract
  have hre := (Complex.continuous_re.tendsto _).comp hNewman
  have hreal : Tendsto (fun X : ℝ =>
      ∫ t in Set.Ioc (1 : ℝ) X, (psiRes a t / t - l) / t) atTop
      (nhds (((fun z => (vonMangoldt.LFunctionResidueClassAux a (z + 1)
        - ((l : ℝ) : ℂ)) / (z + 1)) 0).re)) := by
    refine hre.congr fun X => ?_
    simp only [Function.comp_apply]
    have hcast : ∫ t in Set.Ioc (1 : ℝ) X,
        ((psiRes a t / t - l : ℝ) : ℂ) / (t : ℂ)
        = ((∫ t in Set.Ioc (1 : ℝ) X, (psiRes a t / t - l) / t : ℝ) : ℂ) := by
      rw [← _root_.integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      push_cast
      ring
    rw [hcast, Complex.ofReal_re]
  refine tendsto_div_of_monotone_of_integral_tendsto hl0
    (fun x y _ hxy => psiRes_mono a hxy) (psiRes_nonneg a 1) ?_ hreal
  -- local integrability of the extraction integrand
  intro c b hc hcb
  refine Integrable.mono' (integrable_const (Real.log 4 + 4 + 1))
    ((((hmeas.div measurable_id).sub measurable_const).div
      measurable_id).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht1 : 1 ≤ t := le_trans hc ht.1.le
  have htpos : (0 : ℝ) < t := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
  calc |psiRes a t / t - l| / t
      ≤ |psiRes a t / t - l| := div_le_self (abs_nonneg _) ht1
    _ ≤ Real.log 4 + 4 + 1 := hSbdd t ht1

end Analytic
end EuclidsPath
