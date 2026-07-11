import Mathlib
import EuclidsPath.Engine.Step00FareyModeGeometry

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The additive large sieve over the clock frequencies — the wall-contact module

The program's first ESTIMATE-type theorem binding ALL clocks at once on the INCOMPLETE
side: the additive large sieve over the level-1 mode frequencies `j/q`, `q ∈ clocks A`,
`1 ≤ j ≤ q - 1`, with a fully explicit constant.  The large sieve is absent from the
pinned mathlib; everything below is proved from first principles on top of the Farey
spacing layer (`Step00FareyModeGeometry`).

* **Section A** — the exponential-sum frame: `e θ = exp(2πiθ)` on `ℚ`, `expSum`,
  `expKernel`, and the exact bridge to the program's `modeWave` (`expSum_eq_modeWave_sum`).
* **Section B** — the analytic atom: `expKernel_bound`, the Dirichlet-kernel estimate
  `‖∑_{k<K} e(kθ)‖ ≤ 1/(2δ)` for any `δ > 0` below the distance from `θ` to EVERY
  integer — geometric sum + `‖1 - e(θ)‖ = 2|sin πθ| ≥ 4δ` (Jordan's inequality).
* **Section C** — the Schur/row-sum large sieve `large_sieve_v0`:
  `∑_r ‖expSum a K θ_r‖² ≤ (K + maxRowSum A) · ∑_{k<K} ‖a k‖²` with the EXPLICIT
  rational constant `maxRowSum A = ∑_{q' ∈ clocks A} A·q'·H(⌊A·q'/2⌋)` (`H` = the
  harmonic number, exact in `ℚ`).  Duality-free classical chain: `T = ∑ a_k conj(b_k)`,
  Cauchy–Schwarz, and the Gram row-sum bound organized by the Farey classes `m` of
  `Step00FareyModeGeometry` (each admissible class once per ordered clock pair).
* **Section D** — the program corollary `mode_mass_large_sieve`: the total level-1 mode
  mass over ALL clocks at once, bounded on every incomplete window `k < K`.
* **Section E** — the saturation anatomy: `level_wall_*` (the same method one level up
  meets spacing `~A⁻⁴`, so its constant dwarfs `K ~ A²/6` — kernel witnesses at scale
  `13`) and `universality_blindness` (the bound is quantified over ALL coefficient
  sequences, hence verbatim under Selberg foils: definitionally parity-blind).
* **Section F** — the per-clock exact Parseval `clock_parseval` (character
  orthogonality), the selftest anchor of the harness stage s4.

## DISCLOSURE (read this before anything else)

This module proves an ESTIMATE, not an identity — the first of its genus in the program
— and states its own saturation honestly.  The bound is nontrivial (Section D compares
it against the trivial `#modes · K` bound), but it is a Type-I/linear-genus estimate:
Section E proves in theorem form that it holds for every coefficient sequence, so it
cannot see the parity wall; and that the same method at level 2 (denominators `q·q'`),
where the conspiracy of L52 lives, is trivial — its constant exceeds the ceiling window
already at scale `13`.  No claim of wall progress is made: the wall is TOUCHED (an
incomplete-side quantitative law now exists), not moved.

v1 (Gallagher `2πK + 2A²` via the Sobolev/integral route) is NOT attempted here: TODO
disclosure — the interval-integral plumbing is deferred; v0 is self-sufficient, with the
explicit harmonic-number constant carried everywhere.
-/

namespace EuclidsPath
namespace LargeSieve

open EuclidsPath.StrikeFourier
open EuclidsPath.FareyModeGeometry

/-! ### Section A0 — the objects -/

/-- `e θ = exp(2πiθ)` at a rational frequency: the additive character of the frequency
    circle, realized directly through `Complex.exp` so that frequencies of MIXED clock
    moduli can be subtracted freely (the bridge back to the per-clock `stdAddChar`
    waves is `modeWave_eq_e`). -/
noncomputable def e (θ : ℚ) : ℂ :=
  Complex.exp ((2 * Real.pi * (θ : ℝ) : ℝ) * Complex.I)

/-- The incomplete exponential sum of the coefficients `a` over the window `k < K` at
    frequency `θ`: `∑_{k<K} a k · e(kθ)`. -/
noncomputable def expSum (a : ℕ → ℂ) (K : ℕ) (θ : ℚ) : ℂ :=
  ∑ k ∈ Finset.range K, a k * e ((k : ℚ) * θ)

/-- The Dirichlet kernel of the window: `∑_{k<K} e(kθ)` — the Gram-matrix entry of the
    mode system at frequency difference `θ`. -/
noncomputable def expKernel (K : ℕ) (θ : ℚ) : ℂ :=
  ∑ k ∈ Finset.range K, e ((k : ℚ) * θ)

/-- The level-1 mode labels of scale `A`: the pairs `(q, j)` with `q ∈ clocks A` and
    `1 ≤ j ≤ q - 1` — the frequency set of the large sieve. -/
def level1Modes (A : ℕ) : Finset (ℕ × ℕ) :=
  ((clocks A) ×ˢ Finset.Ioo 0 A).filter fun p => p.2 < p.1

/-- The frequency of a mode label: `(q, j) ↦ j/q ∈ ℚ`. -/
def freq (p : ℕ × ℕ) : ℚ := (p.2 : ℚ) / p.1

/-- **The explicit large-sieve constant** (exact in `ℚ`): `maxRowSum A =
    ∑_{q' ∈ clocks A} A·q'·H(⌊A·q'/2⌋)` where `H` is mathlib's `harmonic`.  This is the
    uniform Gram row-sum bound delivered by the Farey-class organization: for any mode
    `(q, j)`, the row of off-diagonal kernel norms against clock `q'` is at most
    `q·q'·H(⌊q·q'/2⌋) ≤ A·q'·H(⌊A·q'/2⌋)`.  Morally `≲ A³·log A`; kept in exact
    harmonic-number form — no asymptotic claim is made or needed. -/
def maxRowSum (A : ℕ) : ℚ :=
  ∑ q' ∈ clocks A, (A : ℚ) * q' * harmonic (A * q' / 2)

theorem mem_level1Modes {A : ℕ} {p : ℕ × ℕ} :
    p ∈ level1Modes A ↔ p.1 ∈ clocks A ∧ 1 ≤ p.2 ∧ p.2 < p.1 := by
  unfold level1Modes
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioo]
  constructor
  · rintro ⟨⟨hq, hj⟩, hlt⟩
    exact ⟨hq, by omega, hlt⟩
  · rintro ⟨hq, hj1, hlt⟩
    have hA := (mem_clocks.mp hq).2.2
    exact ⟨⟨hq, by omega, by omega⟩, hlt⟩

/-- Iterated-sum form of a `level1Modes` sum: first the clock, then the mode label. -/
theorem sum_level1Modes {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ × ℕ → M) :
    ∑ p ∈ level1Modes A, f p = ∑ q ∈ clocks A, ∑ j ∈ Finset.Ioo 0 q, f (q, j) := by
  unfold level1Modes
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hA := (mem_clocks.mp hq).2.2
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ioo]
  omega

/-! ### Section A — the algebra of `e` and the bridge to the program waves -/

theorem e_zero : e 0 = 1 := by
  unfold e
  norm_num

theorem e_add (θ θ' : ℚ) : e (θ + θ') = e θ * e θ' := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_e (θ : ℚ) : ‖e θ‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_e (θ : ℚ) : (starRingEnd ℂ) (e θ) = e (-θ) := by
  have hmul : e θ * e (-θ) = 1 := by
    rw [← e_add]
    norm_num [e_zero]
  rw [← Complex.inv_eq_conj (norm_e θ)]
  exact inv_eq_of_mul_eq_one_right hmul

/-- `e` at a nonnegative-integer multiple is the power: the geometric-ratio form. -/
theorem e_nat_mul (k : ℕ) (θ : ℚ) : e ((k : ℚ) * θ) = e θ ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e` kills the integers: the frequency circle is `ℚ/ℤ`. -/
theorem e_intCast (n : ℤ) : e (n : ℚ) = 1 := by
  unfold e
  have h : ((2 * Real.pi * ((n : ℚ) : ℝ) : ℝ) : ℂ) * Complex.I
      = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- `e θ ≠ 1` for `θ` bounded away from every integer — the nondegeneracy input of the
    closed geometric sum. -/
theorem e_ne_one {θ δ : ℚ} (hδ : 0 < δ) (hlow : ∀ n : ℤ, δ ≤ |θ - (n : ℚ)|) :
    e θ ≠ 1 := by
  intro h
  unfold e at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hI : ((2 * Real.pi * (θ : ℝ) : ℝ) : ℂ) * Complex.I
      = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have hre : (2 * Real.pi * (θ : ℝ) : ℝ) = (n : ℝ) * (2 * Real.pi) := by
    have h2 := mul_right_cancel₀ Complex.I_ne_zero hI
    exact_mod_cast h2
  have hθn : (θ : ℝ) = (n : ℝ) := by
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpi
    linarith
  have hθnQ : θ = (n : ℚ) := by
    exact_mod_cast hθn
  have := hlow n
  rw [hθnQ, sub_self, abs_zero] at this
  exact absurd this (not_le.mpr hδ)

/-- Norm-symmetry of the kernel: `‖expKernel K (-θ)‖ = ‖expKernel K θ‖` — the kernel at
    the mirrored frequency is the conjugate. -/
theorem norm_expKernel_neg (K : ℕ) (θ : ℚ) :
    ‖expKernel K (-θ)‖ = ‖expKernel K θ‖ := by
  have hconj : expKernel K (-θ) = (starRingEnd ℂ) (expKernel K θ) := by
    unfold expKernel
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_e]
    congr 1
    ring
  rw [hconj, Complex.norm_conj]

/-- The kernel at the diagonal: `expKernel K 0 = K`. -/
theorem expKernel_zero (K : ℕ) : expKernel K 0 = (K : ℂ) := by
  unfold expKernel
  have h : ∀ k ∈ Finset.range K, e ((k : ℚ) * 0) = 1 := fun k _ => by
    rw [mul_zero, e_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range]
  simp

/-- **The bridge to the program waves.**  The level-1 wave of clock `q` at mode `j`,
    evaluated at the integer `k`, IS `e(k·(j/q))`: the guarded `stdAddChar` object of
    `Step00StrikeFourier` and the direct `Complex.exp` frame of this module agree. -/
theorem modeWave_eq_e {q : ℕ} (hq : q ≠ 0) (j k : ℕ) :
    modeWave q j k = e ((k : ℚ) * ((j : ℚ) / q)) := by
  haveI : NeZero q := ⟨hq⟩
  rw [modeWave_def]
  have hcast : (j : ZMod q) * (k : ZMod q) = (((j * k : ℕ) : ℤ) : ZMod q) := by
    push_cast
    ring
  rw [hcast, ZMod.stdAddChar_coe]
  unfold e
  congr 1
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hq0R : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  push_cast
  field_simp

/-- The exponential-sum frame captures the mode-mass object: `expSum` at the level-1
    frequency `j/q` is the windowed wave sum of the program. -/
theorem expSum_eq_modeWave_sum {q : ℕ} (hq : q ≠ 0) (a : ℕ → ℂ) (K j : ℕ) :
    expSum a K ((j : ℚ) / q) = ∑ k ∈ Finset.range K, a k * modeWave q j k := by
  unfold expSum
  exact Finset.sum_congr rfl fun k _ => by rw [modeWave_eq_e hq]

/-! ### Section B — the analytic atom: the Dirichlet kernel bound -/

/-- The sine floor: a frequency keeping distance `≥ δ` from EVERY integer has
    `|sin(πθ)| ≥ 2δ`.  Route: reduce to the nearest-integer representative
    `t = θ - round θ` (`|t| ≤ 1/2`, `|t| ≥ δ`), where `|sin(πθ)| = |sin(πt)|` by
    `π`-antiperiodicity, and apply Jordan's inequality `(2/π)·x ≤ sin x` on `[0, π/2]`
    (`Real.mul_le_sin`) at `x = π|t|`. -/
theorem two_mul_dist_le_abs_sin {θ δ : ℚ} (hδ : 0 < δ)
    (hlow : ∀ n : ℤ, δ ≤ |θ - (n : ℚ)|) :
    2 * (δ : ℝ) ≤ |Real.sin (Real.pi * (θ : ℝ))| := by
  have hpi := Real.pi_pos
  set t : ℚ := θ - round θ with ht
  have habs2 : |t| ≤ 1 / 2 := abs_sub_round θ
  have hδt : δ ≤ |t| := hlow (round θ)
  -- `|sin(πθ)| = |sin(πt)|`
  have hshift : Real.sin (Real.pi * (θ : ℝ))
      = (-1 : ℝ) ^ (round θ : ℤ) * Real.sin (Real.pi * (t : ℝ)) := by
    have harg : Real.pi * (θ : ℝ) = Real.pi * (t : ℝ) + (round θ : ℤ) * Real.pi := by
      push_cast [ht]
      ring
    rw [harg, Real.sin_add_int_mul_pi, mul_comm]
  have habs_eq : |Real.sin (Real.pi * (θ : ℝ))| = |Real.sin (Real.pi * (t : ℝ))| := by
    rw [hshift, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [habs_eq]
  -- `|sin(πt)| = sin(π|t|)` for `|t| ≤ 1/2`
  have habsR : |(t : ℝ)| ≤ 1 / 2 := by
    have h2 : ((|t| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr habs2
    rw [Rat.cast_abs] at h2
    norm_num at h2
    exact h2
  have hsin_abs : Real.sin (Real.pi * |(t : ℝ)|) ≤ |Real.sin (Real.pi * (t : ℝ))| := by
    rcases le_or_gt 0 (t : ℝ) with hsign | hsign
    · rw [abs_of_nonneg hsign]
      exact le_abs_self _
    · rw [abs_of_neg hsign, mul_neg, Real.sin_neg]
      exact neg_le_abs _
  -- Jordan at `x = π|t|`
  have hjordan := Real.mul_le_sin (x := Real.pi * |(t : ℝ)|)
    (by positivity) (by nlinarith [abs_nonneg (t : ℝ)])
  have h2t : 2 / Real.pi * (Real.pi * |(t : ℝ)|) = 2 * |(t : ℝ)| := by
    field_simp
  have hδtR : (δ : ℝ) ≤ |(t : ℝ)| := by
    exact_mod_cast hδt
  calc 2 * (δ : ℝ) ≤ 2 * |(t : ℝ)| := by linarith
    _ = 2 / Real.pi * (Real.pi * |(t : ℝ)|) := h2t.symm
    _ ≤ Real.sin (Real.pi * |(t : ℝ)|) := hjordan
    _ ≤ |Real.sin (Real.pi * (t : ℝ))| := hsin_abs

/-- **The Dirichlet kernel bound (the analytic atom).**  A frequency `θ` keeping
    distance at least `δ > 0` from every integer has
    `‖∑_{k<K} e(kθ)‖ ≤ 1/(2δ)` — closed geometric sum (`geom_sum_eq`), numerator
    `‖e(θ)^K - 1‖ ≤ 2`, denominator `‖e(θ) - 1‖ = 2|sin(πθ)| ≥ 4δ` (the sine floor).
    The constant `1/(2δ)` is the exact yield of this chain: nothing is hidden. -/
theorem expKernel_bound {θ δ : ℚ} (hδ : 0 < δ)
    (hlow : ∀ n : ℤ, δ ≤ |θ - (n : ℚ)|) (K : ℕ) :
    ‖expKernel K θ‖ ≤ 1 / (2 * (δ : ℝ)) := by
  have hδR : (0 : ℝ) < (δ : ℚ) := by exact_mod_cast hδ
  have hne := e_ne_one hδ hlow
  have hgeom : expKernel K θ = (e θ ^ K - 1) / (e θ - 1) := by
    unfold expKernel
    rw [Finset.sum_congr rfl fun k _ => e_nat_mul k θ]
    exact geom_sum_eq hne K
  have hnum : ‖e θ ^ K - 1‖ ≤ 2 := by
    calc ‖e θ ^ K - 1‖ ≤ ‖e θ ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_pow, norm_e, one_pow, norm_one]; norm_num
  have hden : 4 * (δ : ℝ) ≤ ‖e θ - 1‖ := by
    have hform : e θ = Complex.exp (Complex.I * ((2 * Real.pi * (θ : ℝ) : ℝ) : ℂ)) := by
      unfold e
      rw [mul_comm]
    rw [hform, Complex.norm_exp_I_mul_ofReal_sub_one]
    have harg : (2 * Real.pi * (θ : ℝ)) / 2 = Real.pi * (θ : ℝ) := by ring
    rw [harg, Real.norm_eq_abs, abs_mul, abs_two]
    have := two_mul_dist_le_abs_sin hδ hlow
    linarith
  have hden0 : (0 : ℝ) < ‖e θ - 1‖ := by linarith
  rw [hgeom, norm_div]
  calc ‖e θ ^ K - 1‖ / ‖e θ - 1‖ ≤ 2 / (4 * (δ : ℝ)) :=
        div_le_div₀ (by norm_num) hnum (by linarith) hden
    _ = 1 / (2 * (δ : ℝ)) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]
        ring

/-! ### Section C1 — the Farey-class spacing data of a mode pair

The row-sum bound of the large sieve is organized by the Farey classes of
`Step00FareyModeGeometry`: the frequency difference of two level-1 modes is
`crossNum/(q·q')`, its class representative `m = crossNum mod q·q'` measures the exact
circle distance (`classRep_spacing`), never vanishes on genuine pairs
(`classRep_pos`, via `crossNum_shift_ne_zero`), and is INJECTIVE along every row
(`classRep_row_injective` — the row face of `crossterm_class_injective`), so each row
sums over DISTINCT classes: no sorting argument is needed. -/

/-- The Farey-class representative of the ordered mode pair `(q, j), (q', j')`: the
    `ℕ`-representative in `[0, q·q')` of `crossNum q q' j j' mod (q·q')`. -/
def classRep (q q' j j' : ℕ) : ℕ :=
  ((crossNum q q' j j') % ((q : ℤ) * q')).toNat

theorem classRep_lt {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') (j j' : ℕ) :
    classRep q q' j j' < q * q' := by
  have hN : (0 : ℤ) < (q : ℤ) * q' := by positivity
  have h1 := Int.emod_nonneg (crossNum q q' j j') hN.ne'
  have h2 := Int.emod_lt_of_pos (crossNum q q' j j') hN
  have hcast : ((q * q' : ℕ) : ℤ) = (q : ℤ) * q' := by push_cast; ring
  unfold classRep
  omega

/-- On a genuine pair of level-1 modes the class representative never vanishes — the
    nonvanishing kernel `crossNum_shift_ne_zero` of the Farey module, read at the
    division representative. -/
theorem classRep_pos {q q' j j' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) :
    0 < classRep q q' j j' := by
  have hN : (0 : ℤ) < (q : ℤ) * q' := by
    have := hq.pos
    have := hq'.pos
    positivity
  have h1 := Int.emod_nonneg (crossNum q q' j j') hN.ne'
  have hshift := crossNum_shift_ne_zero hq hq' hj1 hjq hj'1 hj'q' hpair
    ((crossNum q q' j j') / ((q : ℤ) * q'))
  have hmod : crossNum q q' j j' % ((q : ℤ) * q') ≠ 0 := by
    rw [Int.emod_def]
    intro h0
    exact hshift (by linear_combination h0)
  unfold classRep
  omega

/-- **The exact spacing floor of a mode pair.**  For EVERY integer `n`, the frequency
    difference `j/q - j'/q'` keeps distance at least `min(m, N-m)/N` from `n`, where
    `N = q·q'` and `m = classRep`: the class representative measures the circle
    distance of the pair.  (When `m = 0` the statement is trivial; `classRep_pos`
    excludes that case on genuine pairs.) -/
theorem classRep_spacing {q q' : ℕ} (hq0 : 0 < q) (hq'0 : 0 < q') (j j' : ℕ) (n : ℤ) :
    ((min (classRep q q' j j') (q * q' - classRep q q' j j') : ℕ) : ℚ)
        / ((q : ℚ) * q')
      ≤ |(j : ℚ) / q - (j' : ℚ) / q' - (n : ℚ)| := by
  set c : ℤ := crossNum q q' j j' with hc
  set m : ℕ := classRep q q' j j' with hm
  have hN : (0 : ℤ) < (q : ℤ) * q' := by positivity
  have hcast : ((q * q' : ℕ) : ℤ) = (q : ℤ) * q' := by push_cast; ring
  have hmlt : m < q * q' := classRep_lt hq0 hq'0 j j'
  have h1 := Int.emod_nonneg c hN.ne'
  have htn : ((m : ℕ) : ℤ) = c % ((q : ℤ) * q') := by
    rw [hm]
    unfold classRep
    rw [← hc]
    exact Int.toNat_of_nonneg h1
  -- the ℤ floor: `min(m, N-m) ≤ |c - n·N|`
  have key : ((min m (q * q' - m) : ℕ) : ℤ) ≤ |c - n * ((q : ℤ) * q')| := by
    have hdm := Int.mul_ediv_add_emod c ((q : ℤ) * q')
    set t : ℤ := c / ((q : ℤ) * q') - n with htdef
    have hval : c - n * ((q : ℤ) * q') = (m : ℤ) + ((q : ℤ) * q') * t := by
      rw [htdef, htn]
      linear_combination hdm.symm
    have hminle : ((min m (q * q' - m) : ℕ) : ℤ) ≤ (m : ℤ) ∧
        ((min m (q * q' - m) : ℕ) : ℤ) ≤ (q : ℤ) * q' - m := by
      constructor
      · exact_mod_cast Nat.cast_le.mpr (min_le_left _ _)
      · have := min_le_right m (q * q' - m)
        omega
    obtain ⟨hle1, hle2⟩ := hminle
    rcases le_or_gt 0 t with hsign | hsign
    · have hNt : 0 ≤ ((q : ℤ) * q') * t := mul_nonneg hN.le hsign
      rw [hval, abs_of_nonneg (by positivity)]
      linarith
    · have hNt : ((q : ℤ) * q') * t ≤ ((q : ℤ) * q') * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) hN.le
      have hneg : (m : ℤ) + ((q : ℤ) * q') * t < 0 := by
        have : (m : ℤ) < (q : ℤ) * q' := by omega
        linarith
      rw [hval, abs_of_neg hneg]
      linarith
  -- descend to `ℚ`
  have hden : (0 : ℚ) < (q : ℚ) * q' := by positivity
  have hdelta : (j : ℚ) / q - (j' : ℚ) / q' - (n : ℚ)
      = ((c - n * ((q : ℤ) * q') : ℤ) : ℚ) / ((q : ℚ) * q') := by
    rw [hc, freq_sub_eq j j' hq0 hq'0]
    push_cast
    rw [sub_div, mul_div_cancel_right₀ _ hden.ne']
  rw [hdelta, abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
  exact_mod_cast key

/-- **Row injectivity of the class representative.**  With the left mode `(q, j)` and
    the clock `q'` fixed, distinct labels `j'` land on distinct representatives — the
    row face of `crossterm_class_injective` (`Step00FareyModeGeometry`), restated in
    the representative normal form the row-sum bound consumes.  Same-clock rows
    (`q' = q`) are covered by the same CRT arithmetic. -/
theorem classRep_row_injective {q q' j j'₁ j'₂ : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hj'₁ : j'₁ < q') (hj'₂ : j'₂ < q')
    (heq : classRep q q' j j'₁ = classRep q q' j j'₂) : j'₁ = j'₂ := by
  have hN : (0 : ℤ) < (q : ℤ) * q' := by
    have := hq.pos
    have := hq'.pos
    positivity
  have h1 := Int.emod_nonneg (crossNum q q' j j'₁) hN.ne'
  have h2 := Int.emod_nonneg (crossNum q q' j j'₂) hN.ne'
  have hmodeq : crossNum q q' j j'₁ % ((q : ℤ) * q')
      = crossNum q q' j j'₂ % ((q : ℤ) * q') := by
    have hcongr := congrArg (fun x : ℕ => (x : ℤ)) heq
    simp only [classRep] at hcongr
    rwa [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hcongr
  have hdvd : (q : ℤ) * q' ∣ ((j'₂ : ℤ) - j'₁) * q := by
    have hdiff : ((q : ℤ) * q') ∣ crossNum q q' j j'₁ - crossNum q q' j j'₂ :=
      Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmodeq, sub_self, Int.zero_emod])
    have hform : crossNum q q' j j'₁ - crossNum q q' j j'₂ = ((j'₂ : ℤ) - j'₁) * q := by
      unfold crossNum
      ring
    rwa [hform] at hdiff
  set d : ℤ := (j'₂ : ℤ) - j'₁ with hd
  have habs : |d| < (q' : ℤ) := by
    rw [abs_lt]
    constructor <;> [skip; skip] <;> omega
  rcases eq_or_ne q q' with rfl | hne
  · -- same clock: `q² ∣ d·q` forces `q ∣ d`
    obtain ⟨k, hk⟩ := hdvd
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.pos.ne'
    have hdq : d = (q : ℤ) * k := by
      have hcancel : d * (q : ℤ) = ((q : ℤ) * k) * q := by linear_combination hk
      exact mul_right_cancel₀ hq0 hcancel
    have hzero : d = 0 := Int.eq_zero_of_abs_lt_dvd ⟨k, hdq⟩ habs
    omega
  · -- distinct clocks: `q' ∣ d·q` and `q' ∤ q` force `q' ∣ d`
    have hdvd' : (q' : ℤ) ∣ d * q := dvd_trans (dvd_mul_left (q' : ℤ) q) hdvd
    rcases (Nat.prime_iff_prime_int.mp hq').dvd_mul.mp hdvd' with h | h
    · have hzero : d = 0 := Int.eq_zero_of_abs_lt_dvd h habs
      omega
    · have hd' : q' ∣ q := Int.natCast_dvd_natCast.mp h
      exact absurd ((Nat.prime_dvd_prime_iff_eq hq' hq).mp hd').symm hne

/-- **The per-pair Gram bound.**  On a genuine pair of level-1 modes the kernel norm at
    the frequency difference is at most `N/(2·min(m, N-m))` with `N = q·q'`,
    `m = classRep`: the analytic atom of Section B evaluated at the exact Farey-class
    spacing floor of Section C1. -/
theorem gram_pair_bound {q q' j j' : ℕ} (K : ℕ) (hq : q.Prime) (hq' : q'.Prime)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) :
    ‖expKernel K ((j : ℚ) / q - (j' : ℚ) / q')‖
      ≤ ((q * q' : ℕ) : ℝ)
        / (2 * ((min (classRep q q' j j') (q * q' - classRep q q' j j') : ℕ) : ℝ)) := by
  set m : ℕ := classRep q q' j j' with hm
  have hmpos : 0 < m := classRep_pos hq hq' hj1 hjq hj'1 hj'q' hpair
  have hmlt : m < q * q' := classRep_lt hq.pos hq'.pos j j'
  have hminpos : 0 < min m (q * q' - m) := by omega
  set δ : ℚ := ((min m (q * q' - m) : ℕ) : ℚ) / ((q : ℚ) * q') with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    have h1 : (0 : ℚ) < ((min m (q * q' - m) : ℕ) : ℚ) := by exact_mod_cast hminpos
    have h2 : (0 : ℚ) < (q : ℚ) * q' := by
      have := hq.pos
      have := hq'.pos
      positivity
    positivity
  have hlow : ∀ n : ℤ, δ ≤ |(j : ℚ) / q - (j' : ℚ) / q' - (n : ℚ)| := fun n =>
    classRep_spacing hq.pos hq'.pos j j' n
  have h := expKernel_bound hδ hlow K
  have hδR : ((δ : ℚ) : ℝ)
      = ((min m (q * q' - m) : ℕ) : ℝ) / ((q * q' : ℕ) : ℝ) := by
    rw [hδdef]
    push_cast
    ring
  have hmR : (0 : ℝ) < ((min m (q * q' - m) : ℕ) : ℝ) := by exact_mod_cast hminpos
  have hNR : (0 : ℝ) < ((q * q' : ℕ) : ℝ) := by
    have := Nat.mul_pos hq.pos hq'.pos
    exact_mod_cast this
  calc ‖expKernel K ((j : ℚ) / q - (j' : ℚ) / q')‖ ≤ 1 / (2 * ((δ : ℚ) : ℝ)) := h
    _ = ((q * q' : ℕ) : ℝ)
        / (2 * ((min m (q * q' - m) : ℕ) : ℝ)) := by
        rw [hδR]
        field_simp

/-! ### Section C2 — the harmonic row sum -/

theorem harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n :=
  Finset.sum_nonneg fun i _ => by positivity

theorem harmonic_mono {m n : ℕ} (h : m ≤ n) : harmonic m ≤ harmonic n := by
  unfold harmonic
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/-- The harmonic number in `Ico`-form: `H(n) = ∑_{m=1}^{n} 1/m`. -/
theorem harmonic_eq_sum_Ico (n : ℕ) :
    harmonic n = ∑ m ∈ Finset.Ico 1 (n + 1), ((m : ℕ) : ℚ)⁻¹ := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hrange : n + 1 - 1 = n := by omega
  rw [hrange]
  unfold harmonic
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm i 1]

/-- **The full Farey-class sum.**  `∑_{m=1}^{N-1} 1/min(m, N-m) ≤ 2·H(⌊N/2⌋)`: split
    at `⌊N/2⌋`; the lower half is exactly `H(⌊N/2⌋)`, the reflected upper half is
    `H(N-1-⌊N/2⌋) ≤ H(⌊N/2⌋)`.  (For odd `N` — every `N = q·q'` here is odd — the
    value is exactly `2·H((N-1)/2)`; only the `≤` is consumed downstream.) -/
theorem sum_invMin_le (N : ℕ) :
    ∑ m ∈ Finset.Ico 1 N, ((min m (N - m) : ℕ) : ℚ)⁻¹ ≤ 2 * harmonic (N / 2) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hempty : Finset.Ico 1 N = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    have := harmonic_nonneg (N / 2)
    linarith
  · set s : ℕ := N / 2 with hs
    have hsplit := Finset.sum_Ico_consecutive
      (f := fun m => ((min m (N - m) : ℕ) : ℚ)⁻¹)
      (by omega : 1 ≤ s + 1) (by omega : s + 1 ≤ N)
    rw [← hsplit]
    -- lower half: `min = m`, exactly the harmonic number
    have hlow : ∑ m ∈ Finset.Ico 1 (s + 1), ((min m (N - m) : ℕ) : ℚ)⁻¹
        = harmonic s := by
      have hmin : ∀ m ∈ Finset.Ico 1 (s + 1),
          ((min m (N - m) : ℕ) : ℚ)⁻¹ = ((m : ℕ) : ℚ)⁻¹ := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        have hminEq : min m (N - m) = m := by omega
        rw [hminEq]
      rw [Finset.sum_congr rfl hmin, harmonic_eq_sum_Ico]
    -- upper half: `min = N - m`, the reflected harmonic number
    have hupp : ∑ m ∈ Finset.Ico (s + 1) N, ((min m (N - m) : ℕ) : ℚ)⁻¹
        ≤ harmonic s := by
      have hmin : ∀ m ∈ Finset.Ico (s + 1) N,
          ((min m (N - m) : ℕ) : ℚ)⁻¹ = ((N - m : ℕ) : ℚ)⁻¹ := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        have hminEq : min m (N - m) = N - m := by omega
        rw [hminEq]
      rw [Finset.sum_congr rfl hmin, Finset.sum_Ico_eq_sum_range]
      set T : ℕ := N - (s + 1) with hT
      have hrefl : ∑ i ∈ Finset.range T, ((N - (s + 1 + i) : ℕ) : ℚ)⁻¹
          = harmonic T := by
        have hcongr : ∀ i ∈ Finset.range T,
            ((N - (s + 1 + i) : ℕ) : ℚ)⁻¹
              = (fun i => ((i + 1 : ℕ) : ℚ)⁻¹) (T - 1 - i) := by
          intro i hi
          rw [Finset.mem_range] at hi
          simp only
          have harg : N - (s + 1 + i) = T - 1 - i + 1 := by omega
          rw [harg]
        rw [Finset.sum_congr rfl hcongr,
          Finset.sum_range_reflect (fun i => ((i + 1 : ℕ) : ℚ)⁻¹) T]
        rfl
      rw [hrefl]
      exact harmonic_mono (by omega)
    linarith

/-- **The row-clock bound.**  Fix a left mode `(q, j)` and a right clock `q'`; sum the
    per-pair Gram bounds over any label set `S ⊆ [1, q'-1]` avoiding the diagonal.
    The class representatives of the row are DISTINCT (`classRep_row_injective`) and
    nonzero (`classRep_pos`), so the row relaxes to the full class sum
    `(N/2)·∑_{m=1}^{N-1} 1/min(m, N-m) ≤ N·H(⌊N/2⌋)`, `N = q·q'`: every admissible
    Farey class pays at most once — the class organization of
    `Step00FareyModeGeometry` replacing any sorting argument. -/
theorem row_clock_bound {q q' : ℕ} (K : ℕ) (hq : q.Prime) (hq' : q'.Prime)
    {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo 0 q') (hdiag : ∀ j' ∈ S, (q, j) ≠ (q', j')) :
    ∑ j' ∈ S, ‖expKernel K ((j : ℚ) / q - (j' : ℚ) / q')‖
      ≤ ((q * q' : ℕ) : ℝ) * ((harmonic (q * q' / 2) : ℚ) : ℝ) := by
  set N : ℕ := q * q' with hN
  have hbounds : ∀ j' ∈ S, 1 ≤ j' ∧ j' ≤ q' - 1 := by
    intro j' hj'
    have := Finset.mem_Ioo.mp (hS hj')
    omega
  -- per-pair bounds, then pull the constant out
  have hstep1 : ∑ j' ∈ S, ‖expKernel K ((j : ℚ) / q - (j' : ℚ) / q')‖
      ≤ ∑ j' ∈ S, ((N : ℕ) : ℝ) / 2
          * ((min (classRep q q' j j') (N - classRep q q' j j') : ℕ) : ℝ)⁻¹ := by
    refine Finset.sum_le_sum fun j' hj' => ?_
    obtain ⟨hj'1, hj'q'⟩ := hbounds j' hj'
    have h := gram_pair_bound K hq hq' hj1 hjq hj'1 hj'q' (hdiag j' hj')
    calc ‖expKernel K ((j : ℚ) / q - (j' : ℚ) / q')‖
        ≤ ((N : ℕ) : ℝ)
          / (2 * ((min (classRep q q' j j') (N - classRep q q' j j') : ℕ) : ℝ)) := h
      _ = ((N : ℕ) : ℝ) / 2
          * ((min (classRep q q' j j') (N - classRep q q' j j') : ℕ) : ℝ)⁻¹ := by
          rw [div_mul_eq_div_div]
          rw [div_eq_mul_inv]
  -- the row relaxes to the full class sum
  have hinj : Set.InjOn (fun j' => classRep q q' j j') ↑S := by
    intro x hx y hy hxy
    obtain ⟨hx1, hxq'⟩ := hbounds x (Finset.mem_coe.mp hx)
    obtain ⟨hy1, hyq'⟩ := hbounds y (Finset.mem_coe.mp hy)
    exact classRep_row_injective hq hq' (by omega) (by omega) hxy
  have hstep2 : ∑ j' ∈ S,
      ((min (classRep q q' j j') (N - classRep q q' j j') : ℕ) : ℝ)⁻¹
      ≤ ∑ m ∈ Finset.Ico 1 N, ((min m (N - m) : ℕ) : ℝ)⁻¹ := by
    calc ∑ j' ∈ S, ((min (classRep q q' j j') (N - classRep q q' j j') : ℕ) : ℝ)⁻¹
        = ∑ m ∈ S.image (fun j' => classRep q q' j j'),
            ((min m (N - m) : ℕ) : ℝ)⁻¹ :=
          (Finset.sum_image (f := fun m : ℕ => ((min m (N - m) : ℕ) : ℝ)⁻¹)
            hinj).symm
      _ ≤ ∑ m ∈ Finset.Ico 1 N, ((min m (N - m) : ℕ) : ℝ)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by positivity
          intro m hm
          rw [Finset.mem_image] at hm
          obtain ⟨j', hj', rfl⟩ := hm
          obtain ⟨hj'1, hj'q'⟩ := hbounds j' hj'
          rw [Finset.mem_Ico]
          exact ⟨classRep_pos hq hq' hj1 hjq hj'1 hj'q' (hdiag j' hj'),
            classRep_lt hq.pos hq'.pos j j'⟩
  -- the class sum is the harmonic bound (proved in ℚ, cast to ℝ)
  have hstep3 : ∑ m ∈ Finset.Ico 1 N, ((min m (N - m) : ℕ) : ℝ)⁻¹
      ≤ 2 * ((harmonic (N / 2) : ℚ) : ℝ) := by
    have hq_le := sum_invMin_le N
    have hcast : ((∑ m ∈ Finset.Ico 1 N, ((min m (N - m) : ℕ) : ℚ)⁻¹ : ℚ) : ℝ)
        = ∑ m ∈ Finset.Ico 1 N, ((min m (N - m) : ℕ) : ℝ)⁻¹ := by
      push_cast
      rfl
    have h2 := (Rat.cast_le (K := ℝ)).mpr hq_le
    rw [hcast] at h2
    calc ∑ m ∈ Finset.Ico 1 N, ((min m (N - m) : ℕ) : ℝ)⁻¹
        ≤ ((2 * harmonic (N / 2) : ℚ) : ℝ) := h2
      _ = 2 * ((harmonic (N / 2) : ℚ) : ℝ) := by push_cast; ring
  -- assemble
  have hNnn : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg N
  calc ∑ j' ∈ S, ‖expKernel K ((j : ℚ) / q - (j' : ℚ) / q')‖
      ≤ ∑ j' ∈ S, ((N : ℕ) : ℝ) / 2
          * ((min (classRep q q' j j') (N - classRep q q' j j') : ℕ) : ℝ)⁻¹ := hstep1
    _ = ((N : ℕ) : ℝ) / 2 * ∑ j' ∈ S,
          ((min (classRep q q' j j') (N - classRep q q' j j') : ℕ) : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ ((N : ℕ) : ℝ) / 2 * (2 * ((harmonic (N / 2) : ℚ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hstep2 hstep3) (by positivity)
    _ = ((N : ℕ) : ℝ) * ((harmonic (N / 2) : ℚ) : ℝ) := by ring

/-- **THE GRAM ROW-SUM BOUND.**  For every mode `r` of the level-1 system, the full
    row of kernel norms is at most `K + maxRowSum A`: the diagonal contributes exactly
    `K` (`expKernel_zero`), each clock row at most `q·q'·H(⌊q·q'/2⌋)`, lifted
    monotonically into the uniform explicit constant `∑_{q'} A·q'·H(⌊A·q'/2⌋)`. -/
theorem gram_row_bound {A : ℕ} {r : ℕ × ℕ} (hr : r ∈ level1Modes A) (K : ℕ) :
    ∑ r' ∈ level1Modes A, ‖expKernel K (freq r - freq r')‖
      ≤ (K : ℝ) + ((maxRowSum A : ℚ) : ℝ) := by
  obtain ⟨q, j⟩ := r
  obtain ⟨hqA, hj1P, hjqP⟩ := mem_level1Modes.mp hr
  have hj1 : 1 ≤ j := hj1P
  have hjlt : j < q := hjqP
  have hjq : j ≤ q - 1 := by omega
  obtain ⟨hq, h5, hqleA⟩ := mem_clocks.mp hqA
  rw [sum_level1Modes]
  -- per-clock target: the uniform summand of `maxRowSum`, plus `K` at the own clock
  have hclock : ∀ q' ∈ clocks A,
      ∑ j' ∈ Finset.Ioo 0 q', ‖expKernel K (freq (q, j) - freq (q', j'))‖
        ≤ (A : ℝ) * q' * ((harmonic (A * q' / 2) : ℚ) : ℝ)
          + (if q' = q then (K : ℝ) else 0) := by
    intro q' hq'A
    obtain ⟨hq', h5', hq'leA⟩ := mem_clocks.mp hq'A
    have hfreq : ∀ j' : ℕ, freq (q, j) - freq (q', j')
        = (j : ℚ) / q - (j' : ℚ) / q' := fun j' => rfl
    have hmono : ((q * q' : ℕ) : ℝ) * ((harmonic (q * q' / 2) : ℚ) : ℝ)
        ≤ (A : ℝ) * q' * ((harmonic (A * q' / 2) : ℚ) : ℝ) := by
      have h1 : ((q * q' : ℕ) : ℝ) ≤ (A : ℝ) * q' := by
        push_cast
        have : (q : ℝ) ≤ A := by exact_mod_cast hqleA
        have hq'nn : (0 : ℝ) ≤ q' := Nat.cast_nonneg q'
        nlinarith
      have h2 : ((harmonic (q * q' / 2) : ℚ) : ℝ)
          ≤ ((harmonic (A * q' / 2) : ℚ) : ℝ) := by
        have hmul : q * q' ≤ A * q' := Nat.mul_le_mul hqleA (le_refl q')
        have hdiv : q * q' / 2 ≤ A * q' / 2 := Nat.div_le_div_right hmul
        exact_mod_cast harmonic_mono hdiv
      have h3 : (0 : ℝ) ≤ ((harmonic (q * q' / 2) : ℚ) : ℝ) := by
        have := harmonic_nonneg (q * q' / 2)
        exact_mod_cast this
      have h4 : (0 : ℝ) ≤ ((q * q' : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    rcases eq_or_ne q' q with heq | hne
    · -- own clock: diagonal `K` + off-diagonal row
      subst heq
      rw [if_pos rfl]
      have hjmem : j ∈ Finset.Ioo 0 q' := Finset.mem_Ioo.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hjmem]
      have hdiagval : ‖expKernel K (freq (q', j) - freq (q', j))‖ = (K : ℝ) := by
        rw [sub_self, expKernel_zero, Complex.norm_natCast]
      have hrow := row_clock_bound K hq hq hj1 hjq ((Finset.Ioo 0 q').erase j)
        (Finset.erase_subset _ _)
        (fun j' hj' => by
          have hne' := Finset.ne_of_mem_erase hj'
          intro hcontra
          exact hne' (by injection hcontra with h1 h2; omega))
      have hrow' : ∑ j' ∈ (Finset.Ioo 0 q').erase j,
          ‖expKernel K (freq (q', j) - freq (q', j'))‖
          ≤ ((q' * q' : ℕ) : ℝ) * ((harmonic (q' * q' / 2) : ℚ) : ℝ) := by
        calc ∑ j' ∈ (Finset.Ioo 0 q').erase j,
            ‖expKernel K (freq (q', j) - freq (q', j'))‖
            = ∑ j' ∈ (Finset.Ioo 0 q').erase j,
              ‖expKernel K ((j : ℚ) / q' - (j' : ℚ) / q')‖ :=
              Finset.sum_congr rfl fun j' _ => by rw [hfreq]
          _ ≤ _ := hrow
      linarith [hdiagval, hrow', hmono]
    · -- other clocks: pure off-diagonal row
      rw [if_neg hne, add_zero]
      have hrow := row_clock_bound K hq hq' hj1 hjq (Finset.Ioo 0 q')
        (subset_refl _)
        (fun j' _ => by
          intro hcontra
          exact hne (by injection hcontra with h1 h2; omega))
      calc ∑ j' ∈ Finset.Ioo 0 q', ‖expKernel K (freq (q, j) - freq (q', j'))‖
          = ∑ j' ∈ Finset.Ioo 0 q', ‖expKernel K ((j : ℚ) / q - (j' : ℚ) / q')‖ :=
            Finset.sum_congr rfl fun j' _ => by rw [hfreq]
        _ ≤ ((q * q' : ℕ) : ℝ) * ((harmonic (q * q' / 2) : ℚ) : ℝ) := hrow
        _ ≤ _ := hmono
  -- assemble over the clocks
  calc ∑ q' ∈ clocks A, ∑ j' ∈ Finset.Ioo 0 q',
        ‖expKernel K (freq (q, j) - freq (q', j'))‖
      ≤ ∑ q' ∈ clocks A, ((A : ℝ) * q' * ((harmonic (A * q' / 2) : ℚ) : ℝ)
          + (if q' = q then (K : ℝ) else 0)) := Finset.sum_le_sum hclock
    _ = (∑ q' ∈ clocks A, (A : ℝ) * q' * ((harmonic (A * q' / 2) : ℚ) : ℝ))
        + ∑ q' ∈ clocks A, (if q' = q then (K : ℝ) else 0) := by
        rw [Finset.sum_add_distrib]
    _ = ((maxRowSum A : ℚ) : ℝ) + (K : ℝ) := by
        congr 1
        · unfold maxRowSum
          push_cast
          rfl
        · rw [Finset.sum_ite_eq' (clocks A) q (fun _ => (K : ℝ)), if_pos hqA]
    _ = (K : ℝ) + ((maxRowSum A : ℚ) : ℝ) := by ring

/-! ### Section C3 — the large sieve (the duality-free Schur chain)

`T := ∑_r ‖S_r‖²` is written as `∑_k a_k · conj(b_k)` with `b_k := ∑_r S_r · e(-kθ_r)`;
Cauchy–Schwarz gives `T² ≤ ‖a‖²·∑_k ‖b_k‖²`; expanding `∑_k ‖b_k‖²` reorganizes it into
the Gram quadratic form, bounded by `(K + maxRowSum A)·T` through the row-sum bound of
C2; cancelling one factor of `T` delivers the sieve.  The classical chain, with no
duality principle needed. -/

/-- `e θ · conj(e θ') = e(θ - θ')`. -/
theorem e_mul_conj (θ θ' : ℚ) : e θ * (starRingEnd ℂ) (e θ') = e (θ - θ') := by
  rw [conj_e, ← e_add]
  congr 1
  ring

/-- `z · conj z` is the squared norm, as a real cast. -/
theorem mul_conj_self (z : ℂ) : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

/-- `conj z · z` is the squared norm, as a real cast. -/
theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]
  exact mul_conj_self z

theorem maxRowSum_nonneg (A : ℕ) : 0 ≤ maxRowSum A :=
  Finset.sum_nonneg fun q' _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg A) (Nat.cast_nonneg q'))
      (harmonic_nonneg _)

/-- **THE LARGE SIEVE, v0 (the shipping theorem).**  For EVERY coefficient sequence
    `a`, every window length `K`, and every scale `A`:

    `∑_{q ∈ clocks A} ∑_{j=1}^{q-1} ‖∑_{k<K} a_k e(k·j/q)‖² ≤ (K + maxRowSum A)·∑_{k<K} ‖a_k‖²`

    with the EXPLICIT constant `maxRowSum A = ∑_{q' ∈ clocks A} A·q'·H(⌊A·q'/2⌋)`
    (exact in `ℚ`).  This is the program's first estimate-type theorem binding ALL
    clocks at once on the incomplete side: the total level-1 mode mass of any window
    of `K` consecutive integers is controlled by `K` plus the harmonic row constant.
    Proof: the duality-free chain `T = ∑_k a_k conj(b_k)` → Cauchy–Schwarz →
    Gram row-sum (Schur) bound → cancel `T`. -/
theorem large_sieve_v0 (A K : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ level1Modes A, ‖expSum a K (freq r)‖ ^ 2
      ≤ ((K : ℝ) + ((maxRowSum A : ℚ) : ℝ)) * ∑ k ∈ Finset.range K, ‖a k‖ ^ 2 := by
  classical
  set R := level1Modes A with hR
  set B : ℝ := (K : ℝ) + ((maxRowSum A : ℚ) : ℝ) with hB
  set b : ℕ → ℂ := fun k => ∑ r ∈ R, expSum a K (freq r)
    * (starRingEnd ℂ) (e ((k : ℚ) * freq r)) with hb
  set T : ℝ := ∑ r ∈ R, ‖expSum a K (freq r)‖ ^ 2 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hna0 : 0 ≤ ∑ k ∈ Finset.range K, ‖a k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hBnn : 0 ≤ B := by
    rw [hB]
    have h1 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have h2 : (0 : ℝ) ≤ ((maxRowSum A : ℚ) : ℝ) := by
      exact_mod_cast maxRowSum_nonneg A
    linarith
  -- conjugate of `b k`
  have hconjb : ∀ k : ℕ, (starRingEnd ℂ) (b k)
      = ∑ r ∈ R, (starRingEnd ℂ) (expSum a K (freq r)) * e ((k : ℚ) * freq r) := by
    intro k
    rw [hb]
    simp only
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, Complex.conj_conj]
  -- identity (i): `T = ∑_k a_k conj(b_k)`
  have hTid : ((T : ℝ) : ℂ) = ∑ k ∈ Finset.range K, a k * (starRingEnd ℂ) (b k) := by
    calc ((T : ℝ) : ℂ)
        = ∑ r ∈ R, ((‖expSum a K (freq r)‖ ^ 2 : ℝ) : ℂ) := by
          rw [hT]
          push_cast
          rfl
      _ = ∑ r ∈ R, (starRingEnd ℂ) (expSum a K (freq r)) * expSum a K (freq r) :=
          Finset.sum_congr rfl fun r _ => (conj_mul_self _).symm
      _ = ∑ r ∈ R, ∑ k ∈ Finset.range K,
            (starRingEnd ℂ) (expSum a K (freq r)) * (a k * e ((k : ℚ) * freq r)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [show expSum a K (freq r)
            = ∑ k ∈ Finset.range K, a k * e ((k : ℚ) * freq r) from rfl,
            Finset.mul_sum]
      _ = ∑ k ∈ Finset.range K, ∑ r ∈ R,
            (starRingEnd ℂ) (expSum a K (freq r)) * (a k * e ((k : ℚ) * freq r)) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.range K, a k * (starRingEnd ℂ) (b k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hconjb k, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
  -- identity (iv): `∑_k ‖b_k‖²` is the Gram quadratic form
  have hnbid : ((∑ k ∈ Finset.range K, ‖b k‖ ^ 2 : ℝ) : ℂ)
      = ∑ r ∈ R, ∑ r' ∈ R, expSum a K (freq r)
          * (starRingEnd ℂ) (expSum a K (freq r'))
          * expKernel K (freq r' - freq r) := by
    have hbk2 : ∀ k ∈ Finset.range K, ((‖b k‖ ^ 2 : ℝ) : ℂ)
        = ∑ r ∈ R, ∑ r' ∈ R, expSum a K (freq r)
            * (starRingEnd ℂ) (expSum a K (freq r'))
            * e ((k : ℚ) * (freq r' - freq r)) := by
      intro k _
      rw [← mul_conj_self (b k), hconjb k]
      conv_lhs => rw [hb]
      simp only
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
      have he : e ((k : ℚ) * freq r') * (starRingEnd ℂ) (e ((k : ℚ) * freq r))
          = e ((k : ℚ) * (freq r' - freq r)) := by
        rw [e_mul_conj]
        congr 1
        ring
      calc expSum a K (freq r) * (starRingEnd ℂ) (e ((k : ℚ) * freq r))
            * ((starRingEnd ℂ) (expSum a K (freq r')) * e ((k : ℚ) * freq r'))
          = expSum a K (freq r) * (starRingEnd ℂ) (expSum a K (freq r'))
            * (e ((k : ℚ) * freq r') * (starRingEnd ℂ) (e ((k : ℚ) * freq r))) := by
            ring
        _ = expSum a K (freq r) * (starRingEnd ℂ) (expSum a K (freq r'))
            * e ((k : ℚ) * (freq r' - freq r)) := by rw [he]
    calc ((∑ k ∈ Finset.range K, ‖b k‖ ^ 2 : ℝ) : ℂ)
        = ∑ k ∈ Finset.range K, ((‖b k‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      _ = ∑ k ∈ Finset.range K, ∑ r ∈ R, ∑ r' ∈ R, expSum a K (freq r)
            * (starRingEnd ℂ) (expSum a K (freq r'))
            * e ((k : ℚ) * (freq r' - freq r)) := Finset.sum_congr rfl hbk2
      _ = ∑ r ∈ R, ∑ k ∈ Finset.range K, ∑ r' ∈ R, expSum a K (freq r)
            * (starRingEnd ℂ) (expSum a K (freq r'))
            * e ((k : ℚ) * (freq r' - freq r)) := Finset.sum_comm
      _ = ∑ r ∈ R, ∑ r' ∈ R, ∑ k ∈ Finset.range K, expSum a K (freq r)
            * (starRingEnd ℂ) (expSum a K (freq r'))
            * e ((k : ℚ) * (freq r' - freq r)) :=
          Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r ∈ R, ∑ r' ∈ R, expSum a K (freq r)
            * (starRingEnd ℂ) (expSum a K (freq r'))
            * expKernel K (freq r' - freq r) := by
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
          rw [show expKernel K (freq r' - freq r)
            = ∑ k ∈ Finset.range K, e ((k : ℚ) * (freq r' - freq r)) from rfl,
            Finset.mul_sum]
  -- the Schur bound on the quadratic form
  have hrow_left : ∀ r ∈ R,
      ∑ r' ∈ R, ‖expKernel K (freq r' - freq r)‖ ≤ B := by
    intro r hr
    have h := gram_row_bound (hR ▸ hr) K
    rw [hB]
    calc ∑ r' ∈ R, ‖expKernel K (freq r' - freq r)‖
        = ∑ r' ∈ R, ‖expKernel K (freq r - freq r')‖ := by
          refine Finset.sum_congr rfl fun r' _ => ?_
          rw [show freq r' - freq r = -(freq r - freq r') by ring, norm_expKernel_neg]
      _ ≤ (K : ℝ) + ((maxRowSum A : ℚ) : ℝ) := hR ▸ h
  have hrow_right : ∀ r' ∈ R,
      ∑ r ∈ R, ‖expKernel K (freq r' - freq r)‖ ≤ B := by
    intro r' hr'
    have h := gram_row_bound (hR ▸ hr') K
    rw [hB]
    exact hR ▸ h
  have hnb_le : ∑ k ∈ Finset.range K, ‖b k‖ ^ 2 ≤ B * T := by
    have hnb0 : 0 ≤ ∑ k ∈ Finset.range K, ‖b k‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have h1 : ∑ k ∈ Finset.range K, ‖b k‖ ^ 2
        = ‖((∑ k ∈ Finset.range K, ‖b k‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnb0]
    rw [h1, hnbid]
    calc ‖∑ r ∈ R, ∑ r' ∈ R, expSum a K (freq r)
          * (starRingEnd ℂ) (expSum a K (freq r'))
          * expKernel K (freq r' - freq r)‖
        ≤ ∑ r ∈ R, ∑ r' ∈ R, ‖expSum a K (freq r)‖ * ‖expSum a K (freq r')‖
            * ‖expKernel K (freq r' - freq r)‖ := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun r _ => ?_)
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun r' _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ ∑ r ∈ R, ∑ r' ∈ R,
            (‖expSum a K (freq r)‖ ^ 2 + ‖expSum a K (freq r')‖ ^ 2) / 2
            * ‖expKernel K (freq r' - freq r)‖ := by
          refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun r' _ => ?_
          have hamgm : ‖expSum a K (freq r)‖ * ‖expSum a K (freq r')‖
              ≤ (‖expSum a K (freq r)‖ ^ 2 + ‖expSum a K (freq r')‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖expSum a K (freq r)‖ - ‖expSum a K (freq r')‖)]
          exact mul_le_mul_of_nonneg_right hamgm (norm_nonneg _)
      _ = (∑ r ∈ R, ∑ r' ∈ R, ‖expSum a K (freq r)‖ ^ 2
              * ‖expKernel K (freq r' - freq r)‖ / 2)
          + ∑ r ∈ R, ∑ r' ∈ R, ‖expSum a K (freq r')‖ ^ 2
              * ‖expKernel K (freq r' - freq r)‖ / 2 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r' _ => ?_
          ring
      _ ≤ B / 2 * T + B / 2 * T := by
          have hfirst : ∑ r ∈ R, ∑ r' ∈ R, ‖expSum a K (freq r)‖ ^ 2
              * ‖expKernel K (freq r' - freq r)‖ / 2 ≤ B / 2 * T := by
            calc ∑ r ∈ R, ∑ r' ∈ R, ‖expSum a K (freq r)‖ ^ 2
                  * ‖expKernel K (freq r' - freq r)‖ / 2
                = ∑ r ∈ R, ‖expSum a K (freq r)‖ ^ 2 / 2
                    * ∑ r' ∈ R, ‖expKernel K (freq r' - freq r)‖ := by
                  refine Finset.sum_congr rfl fun r _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun r' _ => ?_
                  ring
              _ ≤ ∑ r ∈ R, ‖expSum a K (freq r)‖ ^ 2 / 2 * B := by
                  refine Finset.sum_le_sum fun r hr => ?_
                  exact mul_le_mul_of_nonneg_left (hrow_left r hr) (by positivity)
              _ = B / 2 * T := by
                  rw [hT, ← Finset.sum_mul, ← Finset.sum_div]
                  ring
          have hsecond : ∑ r ∈ R, ∑ r' ∈ R, ‖expSum a K (freq r')‖ ^ 2
              * ‖expKernel K (freq r' - freq r)‖ / 2 ≤ B / 2 * T := by
            calc ∑ r ∈ R, ∑ r' ∈ R, ‖expSum a K (freq r')‖ ^ 2
                  * ‖expKernel K (freq r' - freq r)‖ / 2
                = ∑ r' ∈ R, ∑ r ∈ R, ‖expSum a K (freq r')‖ ^ 2
                    * ‖expKernel K (freq r' - freq r)‖ / 2 := Finset.sum_comm
              _ = ∑ r' ∈ R, ‖expSum a K (freq r')‖ ^ 2 / 2
                    * ∑ r ∈ R, ‖expKernel K (freq r' - freq r)‖ := by
                  refine Finset.sum_congr rfl fun r' _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun r _ => ?_
                  ring
              _ ≤ ∑ r' ∈ R, ‖expSum a K (freq r')‖ ^ 2 / 2 * B := by
                  refine Finset.sum_le_sum fun r' hr' => ?_
                  exact mul_le_mul_of_nonneg_left (hrow_right r' hr') (by positivity)
              _ = B / 2 * T := by
                  rw [hT, ← Finset.sum_mul, ← Finset.sum_div]
                  ring
          linarith
      _ = B * T := by ring
  -- the endgame: Cauchy–Schwarz and cancellation
  have hTU : T ≤ ∑ k ∈ Finset.range K, ‖a k‖ * ‖b k‖ := by
    calc T = ‖((T : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
      _ = ‖∑ k ∈ Finset.range K, a k * (starRingEnd ℂ) (b k)‖ := by rw [hTid]
      _ ≤ ∑ k ∈ Finset.range K, ‖a k * (starRingEnd ℂ) (b k)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range K, ‖a k‖ * ‖b k‖ :=
          Finset.sum_congr rfl fun k _ => by rw [norm_mul, Complex.norm_conj]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K)
    (fun k => ‖a k‖) (fun k => ‖b k‖)
  rcases eq_or_lt_of_le hT0 with hT0' | hTpos
  · rw [← hT0']
    exact mul_nonneg hBnn hna0
  · have hchain : T * T ≤ (B * ∑ k ∈ Finset.range K, ‖a k‖ ^ 2) * T := by
      have hU0 : 0 ≤ ∑ k ∈ Finset.range K, ‖a k‖ * ‖b k‖ := le_trans hT0 hTU
      calc T * T ≤ (∑ k ∈ Finset.range K, ‖a k‖ * ‖b k‖)
            * (∑ k ∈ Finset.range K, ‖a k‖ * ‖b k‖) := mul_le_mul hTU hTU hT0 hU0
        _ = (∑ k ∈ Finset.range K, ‖a k‖ * ‖b k‖) ^ 2 := (sq _).symm
        _ ≤ (∑ k ∈ Finset.range K, ‖a k‖ ^ 2)
            * ∑ k ∈ Finset.range K, ‖b k‖ ^ 2 := hCS
        _ ≤ (∑ k ∈ Finset.range K, ‖a k‖ ^ 2) * (B * T) :=
            mul_le_mul_of_nonneg_left hnb_le hna0
        _ = (B * ∑ k ∈ Finset.range K, ‖a k‖ ^ 2) * T := by ring
    exact le_of_mul_le_mul_right hchain hTpos

/-! ### Section D — the program corollary: total level-1 mode mass -/

/-- **THE MODE-MASS LARGE SIEVE (the program corollary).**  The total level-1 mode
    mass over ALL clocks at once, on ANY window of `K` consecutive integers:

    `∑_{q ∈ clocks A} ∑_{j=1}^{q-1} ‖∑_{k<K} a_k · modeWave q j k‖²
       ≤ (K + maxRowSum A) · ∑_{k<K} ‖a_k‖²`

    — the first proven nontrivial bound on an incomplete window object in the program.
    HONEST COMPARISON: the trivial bound (per-mode Cauchy–Schwarz, no interference) is
    `#modes · K · ∑‖a‖²` with `#modes = ∑_q (q-1) ~ A²/(2 ln A)`; at the ceiling window
    `K ~ A²/6` the trivial constant is `~A⁴/(12 ln A)` while `K + maxRowSum A` is
    `~A³`-shaped (`maxRowSum A = ∑_{q'} A·q'·H(⌊A·q'/2⌋)`, morally `≲ A³·log A`) — a
    genuine `~A/log`-factor of cancellation captured across ALL clock pairs
    simultaneously.  The classical optimal shape `K + O(A²)` (Gallagher) is NOT claimed:
    the Schur route pays a harmonic-log factor, disclosed, exact, in `ℚ`.  What this
    does NOT do: see Section E — the estimate is parity-blind and dies one level below
    the L52 conspiracy layer. -/
theorem mode_mass_large_sieve (A K : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ clocks A, ∑ j ∈ Finset.Ioo 0 q,
        ‖∑ k ∈ Finset.range K, a k * modeWave q j k‖ ^ 2
      ≤ ((K : ℝ) + ((maxRowSum A : ℚ) : ℝ)) * ∑ k ∈ Finset.range K, ‖a k‖ ^ 2 := by
  have hbridge : ∑ q ∈ clocks A, ∑ j ∈ Finset.Ioo 0 q,
      ‖∑ k ∈ Finset.range K, a k * modeWave q j k‖ ^ 2
      = ∑ r ∈ level1Modes A, ‖expSum a K (freq r)‖ ^ 2 := by
    rw [sum_level1Modes A (fun r => ‖expSum a K (freq r)‖ ^ 2)]
    refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun j hj => ?_
    have hq0 : q ≠ 0 := by
      have := (mem_clocks.mp hq).2.1
      omega
    rw [show freq (q, j) = (j : ℚ) / q from rfl, expSum_eq_modeWave_sum hq0]
  rw [hbridge]
  exact large_sieve_v0 A K a

/-! ### Section E — the saturation anatomy (theorem-form disclosures)

Two honest walls, stated as theorems where a theorem is available and as kernel
witnesses where the general statement would be vacuous dressing.

**The level wall.**  The sieve of Section C lives on the LEVEL-1 frequencies `j/q`
with spacing floor `1/A²`.  The engine decomposition's conspiracy (ledger L52) lives
at levels 2–3 — frequencies `m/(q·q')` with denominators up to `A²` and spacing as
fine as `~1/A⁴`.  There the SAME method must pay `1/(2δ) ~ A⁴` per off-diagonal pair
against a ceiling window of only `K ~ A²/6` — the constant dwarfs the window and the
bound goes trivial exactly one level below the conspiracy.  Kernel witnesses at scale
`13`: `8/143` and `5/91` are genuine level-2 mode frequencies (`143 = 11·13`,
`91 = 7·13`, unimodular pair `7·8 - 11·5 = 1`), at distance `1/1001` — BELOW the
level-1 floor `1/169`, with per-pair kernel cost `1001/2 > 29 = ⌈13²/6⌉`.

**Universality blindness.**  `large_sieve_v0` is quantified over ALL coefficient
sequences: it holds VERBATIM for the Selberg-foil weighted sequences `(1 ± λ)·a`
(`universality_blindness` is literally an instance).  An estimate of this genus
cannot distinguish the twin-bearing configuration from its parity foils —
definitionally parity-blind, the exact reason Type-I machinery alone cannot break
the wall (L38 lineage; compare the DISCLOSURE blocks of `Step00StrikeFourier` and
`Step00WindowDispersion`). -/

/-- Level-2 witness (scale `13`): the level-2 frequencies `8/143` and `5/91`
    (denominators `11·13` and `7·13`, both products of two clocks of scale `13`) sit
    at distance exactly `1/1001` — a Farey-adjacent level-2 pair
    (`7·8 - 11·5 = 1`). -/
theorem level_wall_spacing : |(8 : ℚ) / 143 - 5 / 91| = 1 / 1001 := by norm_num

/-- The witness spacing is BELOW the level-1 floor `1/A² = 1/169` of scale `13`: the
    level-2 layer is strictly finer than everything the level-1 sieve resolves. -/
theorem level_wall_below_floor : (1 : ℚ) / 1001 < 1 / (13 * 13) := by norm_num

/-- The method's per-pair cost at the witness spacing exceeds the ceiling window: the
    kernel bound pays `1/(2δ) = 1001/2 > 29 = ⌈13²/6⌉ = K`.  One single off-diagonal
    level-2 pair already costs more than the whole diagonal — the Schur constant at
    level 2 is trivial at the wall's own window length. -/
theorem level_wall_cost_exceeds_ceiling : (29 : ℚ) < 1 / (2 * (1 / 1001)) := by
  norm_num

/-- **Universality blindness (theorem form).**  The large sieve holds verbatim for
    ANY reweighted sequence `k ↦ w k · a k` — in particular for the Selberg foils
    `(1 ± λ)`-weighted sequences: the proof term IS `large_sieve_v0` applied to the
    product sequence.  Estimates quantified over all coefficients are definitionally
    parity-blind: this inequality alone can never see which configuration carries
    twins. -/
theorem universality_blindness (A K : ℕ) (w a : ℕ → ℂ) :
    ∑ r ∈ level1Modes A, ‖expSum (fun k => w k * a k) K (freq r)‖ ^ 2
      ≤ ((K : ℝ) + ((maxRowSum A : ℚ) : ℝ))
        * ∑ k ∈ Finset.range K, ‖w k * a k‖ ^ 2 :=
  large_sieve_v0 A K fun k => w k * a k

/-! ### Section F — the per-clock exact Parseval (the selftest anchor)

The exact identity the large sieve degrades gracefully from: over ONE clock `q`, with
the FULL frequency set `j = 0, …, q-1` (including the trivial mode), the mode mass is
EXACTLY `q` times the residue-class mass — character orthogonality, no inequality.
Summing the naive per-clock identity over clocks loses a factor `#clocks` on the
diagonal; the large sieve of Section C recovers the loss on the nontrivial modes at
the price of the harmonic constant.  This identity anchors the harness stage s4. -/

/-- The window residue fiber of the clock `q`: the `k < K` with `k ≡ c (mod q)`. -/
def resFiber (q K : ℕ) (c : ZMod q) : Finset ℕ :=
  (Finset.range K).filter fun k => (Nat.cast k : ZMod q) = c

/-- Conjugation of the standard character negates the argument (local reproof of the
    `Step00WindowDispersion` private lemma, kept private there). -/
theorem conj_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  have hmul : (ZMod.stdAddChar x : ℂ) * ZMod.stdAddChar (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hqx : q • x = 0 := by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hpow : (ZMod.stdAddChar x : ℂ) ^ q = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, hqx, AddChar.map_zero_eq_one]
  have hnorm : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow (NeZero.ne q)
  rw [← Complex.inv_eq_conj hnorm]
  exact inv_eq_of_mul_eq_one_right hmul

/-- **The per-clock exact Parseval identity.**  For every clock modulus `q`, window
    `K`, and coefficients `a`:

    `∑_{j mod q} ‖∑_{k<K} a_k ψ(jk)‖² = q · ∑_{c mod q} ‖∑_{k<K, k≡c (q)} a_k‖²`

    (full-frequency form, `j = 0` included; `ψ = ZMod.stdAddChar`).  Exact identity by
    character orthogonality (`AddChar.sum_mulShift`): the per-clock mode mass IS the
    residue mass, scaled by `q`.  The naive summation of this identity over all clocks
    proves nothing about the joint system — the interference between clocks is exactly
    what the large sieve's row-sum constant controls. -/
theorem clock_parseval (q : ℕ) [NeZero q] (a : ℕ → ℂ) (K : ℕ) :
    ∑ j : ZMod q, ‖∑ k ∈ Finset.range K, a k * ZMod.stdAddChar (j * (k : ZMod q))‖ ^ 2
      = (q : ℝ) * ∑ c : ZMod q, ‖∑ k ∈ resFiber q K c, a k‖ ^ 2 := by
  classical
  -- fiber decomposition: `S j = ∑_c ψ(jc) · A_c`
  have hfiber : ∀ j : ZMod q,
      ∑ k ∈ Finset.range K, a k * ZMod.stdAddChar (j * (k : ZMod q))
        = ∑ c : ZMod q, ZMod.stdAddChar (j * c) * ∑ k ∈ resFiber q K c, a k := by
    intro j
    rw [← Finset.sum_fiberwise (Finset.range K) (fun k => (Nat.cast k : ZMod q))
      (fun k => a k * ZMod.stdAddChar (j * (k : ZMod q)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show resFiber q K c
      = (Finset.range K).filter (fun k => (Nat.cast k : ZMod q) = c) from rfl,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkc : (Nat.cast k : ZMod q) = c := (Finset.mem_filter.mp hk).2
    rw [← hkc]
    ring
  -- the ℂ-level identity by orthogonality
  have hkey : ∑ j : ZMod q,
      (∑ k ∈ Finset.range K, a k * ZMod.stdAddChar (j * (k : ZMod q)))
        * (starRingEnd ℂ) (∑ k ∈ Finset.range K,
            a k * ZMod.stdAddChar (j * (k : ZMod q)))
      = (q : ℂ) * ∑ c : ZMod q, (∑ k ∈ resFiber q K c, a k)
          * (starRingEnd ℂ) (∑ k ∈ resFiber q K c, a k) := by
    calc ∑ j : ZMod q,
        (∑ k ∈ Finset.range K, a k * ZMod.stdAddChar (j * (k : ZMod q)))
          * (starRingEnd ℂ) (∑ k ∈ Finset.range K,
              a k * ZMod.stdAddChar (j * (k : ZMod q)))
        = ∑ j : ZMod q, ∑ c : ZMod q, ∑ c' : ZMod q,
            (ZMod.stdAddChar (j * c) * ∑ k ∈ resFiber q K c, a k)
            * ((starRingEnd ℂ) (ZMod.stdAddChar (j * c') : ℂ)
              * (starRingEnd ℂ) (∑ k ∈ resFiber q K c', a k)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hfiber j, map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
          rw [map_mul (starRingEnd ℂ)]
      _ = ∑ c : ZMod q, ∑ c' : ZMod q,
            ((∑ k ∈ resFiber q K c, a k)
              * (starRingEnd ℂ) (∑ k ∈ resFiber q K c', a k))
            * ∑ j : ZMod q, ZMod.stdAddChar (j * (c - c')) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hchar : (ZMod.stdAddChar (j * c) : ℂ)
              * (starRingEnd ℂ) (ZMod.stdAddChar (j * c') : ℂ)
              = ZMod.stdAddChar (j * (c - c')) := by
            rw [conj_stdAddChar, ← AddChar.map_add_eq_mul]
            congr 1
            ring
          calc (ZMod.stdAddChar (j * c) * ∑ k ∈ resFiber q K c, a k)
              * ((starRingEnd ℂ) (ZMod.stdAddChar (j * c') : ℂ)
                * (starRingEnd ℂ) (∑ k ∈ resFiber q K c', a k))
              = ((∑ k ∈ resFiber q K c, a k)
                * (starRingEnd ℂ) (∑ k ∈ resFiber q K c', a k))
                * ((ZMod.stdAddChar (j * c) : ℂ)
                  * (starRingEnd ℂ) (ZMod.stdAddChar (j * c') : ℂ)) := by ring
            _ = _ := by rw [hchar]
      _ = ∑ c : ZMod q, ∑ c' : ZMod q,
            ((∑ k ∈ resFiber q K c, a k)
              * (starRingEnd ℂ) (∑ k ∈ resFiber q K c', a k))
            * (if c - c' = 0 then (q : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
          congr 1
          rw [AddChar.sum_mulShift (c - c') (ZMod.isPrimitive_stdAddChar q)]
          split_ifs with h
          · rw [ZMod.card]
          · norm_num
      _ = ∑ c : ZMod q, ((∑ k ∈ resFiber q K c, a k)
            * (starRingEnd ℂ) (∑ k ∈ resFiber q K c, a k)) * (q : ℂ) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          have hterm : ∀ c' : ZMod q,
              ((∑ k ∈ resFiber q K c, a k)
                * (starRingEnd ℂ) (∑ k ∈ resFiber q K c', a k))
              * (if c - c' = 0 then (q : ℂ) else 0)
              = if c' = c then
                  ((∑ k ∈ resFiber q K c, a k)
                    * (starRingEnd ℂ) (∑ k ∈ resFiber q K c', a k)) * (q : ℂ)
                else 0 := by
            intro c'
            rcases eq_or_ne c' c with rfl | hne
            · rw [if_pos (sub_self c'), if_pos rfl]
            · rw [if_neg (fun h0 => hne (sub_eq_zero.mp h0).symm), if_neg hne,
                mul_zero]
          rw [Finset.sum_congr rfl fun c' _ => hterm c',
            Finset.sum_ite_eq' Finset.univ c, if_pos (Finset.mem_univ c)]
      _ = (q : ℂ) * ∑ c : ZMod q, (∑ k ∈ resFiber q K c, a k)
            * (starRingEnd ℂ) (∑ k ∈ resFiber q K c, a k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
  -- descend to `ℝ`
  have hcast1 : ((∑ j : ZMod q,
      ‖∑ k ∈ Finset.range K, a k * ZMod.stdAddChar (j * (k : ZMod q))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j : ZMod q,
          (∑ k ∈ Finset.range K, a k * ZMod.stdAddChar (j * (k : ZMod q)))
            * (starRingEnd ℂ) (∑ k ∈ Finset.range K,
                a k * ZMod.stdAddChar (j * (k : ZMod q))) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.ofReal_pow]
    exact (mul_conj_self _).symm
  have hcast2 : (((q : ℝ)
      * ∑ c : ZMod q, ‖∑ k ∈ resFiber q K c, a k‖ ^ 2 : ℝ) : ℂ)
      = (q : ℂ) * ∑ c : ZMod q, (∑ k ∈ resFiber q K c, a k)
          * (starRingEnd ℂ) (∑ k ∈ resFiber q K c, a k) := by
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Complex.ofReal_pow]
    exact (mul_conj_self _).symm
  have hfinal := hcast1.trans (hkey.trans hcast2.symm)
  exact_mod_cast hfinal

/-! ### Kernel anchor of the constant

The exact `ℚ`-value of the shipping constant at the wall scale `13`, kernel-checked:
the harness stage s4 byte-checks its independently computed `Fraction` against this
literal (STOP on mismatch). -/

/-- `maxRowSum 13 = 65·H(32) + 91·H(45) + 143·H(71) + 169·H(84)`, exactly:
    `≈ 2204.2136` — against `K = ⌈13²/6⌉ = 29`.  The constant is honest about its own
    size: at the wall scale the harmonic row constant, not the window, dominates. -/
theorem maxRowSum_13 :
    maxRowSum 13 = 342332647440426240579477769343529818239
      / 155308287585455802788347505848114800 := by
  rw [maxRowSum, show clocks 13 = {5, 7, 11, 13} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [harmonic]
  rw [show (13 * 5 / 2 : ℕ) = 32 from rfl, show (13 * 7 / 2 : ℕ) = 45 from rfl,
    show (13 * 11 / 2 : ℕ) = 71 from rfl, show (13 * 13 / 2 : ℕ) = 84 from rfl]
  norm_num [Finset.sum_range_succ]

/-! ### Axiom audit

Recorded output of the block below (this pass) — ALL eighteen audited declarations:

    large_sieve_v0, mode_mass_large_sieve, universality_blindness, clock_parseval,
    expKernel_bound, gram_pair_bound, gram_row_bound, row_clock_bound,
    classRep_spacing, classRep_row_injective, sum_invMin_le,
    two_mul_dist_le_abs_sin, modeWave_eq_e, expSum_eq_modeWave_sum,
    level_wall_spacing, level_wall_below_floor, level_wall_cost_exceeds_ceiling,
    maxRowSum_13
                                    -- [propext, Classical.choice, Quot.sound]

No `sorryAx`, no `native_decide` (`Lean.ofReduceBool`), no repo axiom
(`step00FirstCause`): the module is green under the standard triple. -/

#print axioms large_sieve_v0
#print axioms mode_mass_large_sieve
#print axioms universality_blindness
#print axioms clock_parseval
#print axioms expKernel_bound
#print axioms gram_pair_bound
#print axioms gram_row_bound
#print axioms row_clock_bound
#print axioms classRep_spacing
#print axioms classRep_row_injective
#print axioms sum_invMin_le
#print axioms two_mul_dist_le_abs_sin
#print axioms modeWave_eq_e
#print axioms expSum_eq_modeWave_sum
#print axioms level_wall_spacing
#print axioms level_wall_below_floor
#print axioms level_wall_cost_exceeds_ceiling
#print axioms maxRowSum_13

end LargeSieve
end EuclidsPath
