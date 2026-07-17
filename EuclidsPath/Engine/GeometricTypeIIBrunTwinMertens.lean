/-
  GeometricTypeIIBrunTwinMertens — THE MERTENS INPUT DISCHARGED: the named
  hypothesis of the stage-4a rate is a THEOREM of the pin, with explicit
  constant `C = 9`:

      ∏_{p ∈ sievePrimes z} (1 − 2/p)  ≤  9 / log²z        (all z ≥ 2)

  — and therefore the Brun rate is UNCONDITIONAL:

      twins(N)  ≤  9·N/log²z + 3^z + z/6 + 1               (all N, all z ≥ 2).

  ORIGIN.  Autonomous continuation (the named remaining step of stage 4a).
  Design adversarially verified (Mertens pre-pass) with the SQUARING ROUTE
  replacing the classical log/exp chain:
    * the pin's FINITE Euler geometric identity
      (`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`)
      gives `∏_{p≤z}(1 − 1/p)⁻¹ = Σ_{(z+1)-smooth} 1/m ≥ Σ_{n≤z} 1/n = harmonic z`
      — a finite-`z` identity, no `s > 1` truncation issue;
    * the pin's harmonic LOWER bound (`log_add_one_le_harmonic`) turns this into
      `∏_{p≤z}(1 − 1/p) ≤ 1/log z`;
    * peeling `p = 2, 3` EXACTLY (`(1−1/2)(1−1/3) = 1/3`) gives
      `∏_{sievePrimes z}(1 − 1/p) ≤ 3/log z`;
    * **THE SQUARING TRICK**: `1 − 2/p ≤ (1 − 1/p)²` pointwise (the difference
      is EXACTLY `1/p²`), so the twin product is at most the square:
      `∏(1 − 2/p) ≤ (3/log z)² = 9/log²z` — no `−log(1−x) ≤ x + x²` apparatus,
      no `Σ1/p²` bound, no exp-monotonicity glue.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `sum_Icc_inv_le_prod_primesBelow` — the finite Euler expansion dominates
      the harmonic sum;
    * `prod_primesBelow_le_inv_log` — `∏_{p≤z}(1 − 1/p) ≤ 1/log z`;
    * `sievePrimes_prod_inv_eq` — the exact `p = 2, 3` peel (factor 3);
    * `sievePrimes_prod_le_nine_div_log_sq` — **THE DISCHARGE**: the stage-4a
      hypothesis `hM` at `C = 9`, byte-compatible;
    * `twin_count_log_rate_unconditional` — **THE UNCONDITIONAL RATE** displayed
      above (prose reading: `z ≈ ½·log N` gives `twins(N) = O(N/(log log N)²)`,
      the crude Brun rate; the true rate is stage 4b, not claimed).

  NUMERIC GROUNDING (Mertens pre-pass): the full chain verified at
  `z ∈ {2,…,10⁵}`; `sup_z [∏(1−2/p)·log²z] = 2.4967` (at `z = 88788`) — `C = 9`
  holds with 3.6× margin; the structural slack is the Euler-vs-Mertens gap
  (`1/log z` vs `e^{−γ}/log z`, squared `2.84 < 9`).

  DISCLOSURES (mandatory reading before quoting):
    * The constant 9 is NOT optimal (the truth is `4e^{−2γ} ≈ 1.26`); optimality
      is not claimed and not needed — any constant closes stage 4a.
    * STILL NOT THE TWIN CONJECTURE — upper bounds only; Brun structurally blind
      to the parity wall.  No registered target (CRE, SemiprimeShortRestriction,
      HigherConductorDispersion, LowFreqRootCoherence, OneWingTarget) touched:
      NOT a §110 event.
    * Stage 4b (the true `N(log log N)²/log²N` via truncation + the dormant
      esymm tail) remains named and unclaimed.
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIBrunTwinRate

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### The inverse-cast monoid hom and the finite Euler expansion -/

/-- `n ↦ (n : ℝ)⁻¹` as a monoid hom (valid at 0 since `(0:ℝ)⁻¹ = 0`). -/
private noncomputable def invCastHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' m n := by
    push_cast
    rw [mul_inv]

@[simp]
private theorem invCastHom_apply (n : ℕ) : invCastHom n = (n : ℝ)⁻¹ := rfl

private theorem invCastHom_norm_lt_one {p : ℕ} (hp : p.Prime) :
    ‖invCastHom p‖ < 1 := by
  rw [invCastHom_apply, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ)⁻¹)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- **The finite Euler expansion dominates the harmonic sum**:
    `Σ_{n≤z} 1/n ≤ ∏_{p≤z} (1 − 1/p)⁻¹` — every `n ≤ z` is `(z+1)`-smooth. -/
theorem sum_Icc_inv_le_prod_primesBelow (z : ℕ) :
    ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹
      ≤ ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  obtain ⟨-, hsum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := invCastHom) (fun {p} hp => invCastHom_norm_lt_one hp) (z + 1)
  have hind : HasSum
      (Set.indicator ((z + 1).smoothNumbers) (⇑invCastHom))
      (∏ p ∈ (z + 1).primesBelow, (1 - invCastHom p)⁻¹) :=
    hasSum_subtype_iff_indicator.mp hsum
  have hle := sum_le_hasSum (Finset.Icc 1 z)
    (fun i _ => Set.indicator_nonneg
      (fun a _ => by simp only [invCastHom_apply]; positivity) i) hind
  have heval : ∑ n ∈ Finset.Icc 1 z,
      Set.indicator ((z + 1).smoothNumbers) (⇑invCastHom) n
      = ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹ := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
    rw [Set.indicator_of_mem
      (Nat.mem_smoothNumbers_of_lt (by omega) (by omega))]
    rfl
  calc ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹
      = ∑ n ∈ Finset.Icc 1 z,
          Set.indicator ((z + 1).smoothNumbers) (⇑invCastHom) n := heval.symm
    _ ≤ ∏ p ∈ (z + 1).primesBelow, (1 - invCastHom p)⁻¹ := hle
    _ = ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
        simp only [invCastHom_apply]

/-- `log z ≤ ∏_{p≤z}(1 − 1/p)⁻¹` (harmonic lower bound + the expansion). -/
theorem log_le_prod_primesBelow_inv (z : ℕ) (hz : 2 ≤ z) :
    Real.log z ≤ ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have h1 : Real.log z ≤ Real.log (z + 1) := by
    refine Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) ?_
    exact_mod_cast Nat.le_succ z
  have h2 := log_add_one_le_harmonic z
  have h3 : ((harmonic z : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
  have h4 := sum_Icc_inv_le_prod_primesBelow z
  have h2' : Real.log (z + 1) ≤ ((harmonic z : ℚ) : ℝ) := by
    exact_mod_cast h2
  linarith

/-- `∏_{p≤z}(1 − 1/p) ≤ 1/log z`. -/
theorem prod_primesBelow_le_inv_log (z : ℕ) (hz : 2 ≤ z) :
    ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹) ≤ (Real.log z)⁻¹ := by
  have hlog : (0 : ℝ) < Real.log z :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have h := log_le_prod_primesBelow_inv z hz
  rw [Finset.prod_inv_distrib] at h
  have hinv := inv_anti₀ hlog h
  rwa [inv_inv] at hinv

/-! ### The exact `p = 2, 3` peel -/

/-- `sievePrimes z` is `primesBelow (z+1)` with `{2, 3}` removed (`z ≥ 3`). -/
theorem sievePrimes_eq_sdiff (z : ℕ) :
    sievePrimes z = (z + 1).primesBelow \ ({2, 3} : Finset ℕ) := by
  ext p
  simp only [sievePrimes, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_sdiff, Nat.mem_primesBelow, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h5, hle⟩, hp⟩
    exact ⟨⟨by omega, hp⟩, by omega⟩
  · rintro ⟨⟨hlt, hp⟩, h23⟩
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    refine ⟨⟨?_, by omega⟩, hp⟩
    omega

/-- The exact peel: `∏_{sievePrimes z}(1 − 1/p) = 3·∏_{p≤z}(1 − 1/p)`. -/
theorem sievePrimes_prod_inv_eq {z : ℕ} (hz : 3 ≤ z) :
    ∏ p ∈ sievePrimes z, (1 - (p : ℝ)⁻¹)
      = 3 * ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹) := by
  have hsub : ({2, 3} : Finset ℕ) ⊆ (z + 1).primesBelow := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · subst h
      exact Nat.mem_primesBelow.mpr ⟨by omega, by norm_num⟩
    · rw [Finset.mem_singleton] at h
      subst h
      exact Nat.mem_primesBelow.mpr ⟨by omega, by norm_num⟩
  have hsdiff := Finset.prod_sdiff (f := fun p : ℕ => (1 - (p : ℝ)⁻¹)) hsub
  have hpair : ∏ p ∈ ({2, 3} : Finset ℕ), (1 - (p : ℝ)⁻¹) = 3⁻¹ := by
    rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]
    norm_num
  rw [sievePrimes_eq_sdiff z]
  have hkey : (∏ p ∈ (z + 1).primesBelow \ ({2, 3} : Finset ℕ),
      (1 - (p : ℝ)⁻¹)) * (3 : ℝ)⁻¹
      = ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹) := by
    rw [← hpair]
    exact hsdiff
  have h30 : (3 : ℝ) ≠ 0 := by norm_num
  linear_combination 3 * hkey

/-! ### The discharge and the unconditional rate -/

/-- **THE DISCHARGE** — the stage-4a Mertens hypothesis is a theorem at `C = 9`:
    `∏_{p ∈ sievePrimes z}(1 − 2/p) ≤ 9/log²z` for all `z ≥ 2`.  The squaring
    trick `1 − 2/p ≤ (1 − 1/p)²` (difference exactly `1/p²`) reduces everything
    to the single-power Euler bound. -/
theorem sievePrimes_prod_le_nine_div_log_sq :
    ∀ z : ℕ, 2 ≤ z →
      ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ)) ≤ 9 / (Real.log z) ^ 2 := by
  intro z hz
  have hlog : (0 : ℝ) < Real.log z :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  by_cases hz3 : 3 ≤ z
  · -- the squaring trick
    have hsq : ∀ p ∈ sievePrimes z,
        (1 - 2 / (p : ℝ)) ≤ (1 - (p : ℝ)⁻¹) ^ 2 := by
      intro p hp
      have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast sievePrimes_five_le hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hdiv : (2 : ℝ) / p = 2 * (p : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
      rw [hdiv]
      nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
    have hnn : ∀ p ∈ sievePrimes z, (0 : ℝ) ≤ 1 - 2 / (p : ℝ) := by
      intro p hp
      have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast sievePrimes_five_le hp
      have : 2 / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith
    have hstep1 : ∏ p ∈ sievePrimes z, (1 - 2 / (p : ℝ))
        ≤ ∏ p ∈ sievePrimes z, (1 - (p : ℝ)⁻¹) ^ 2 :=
      Finset.prod_le_prod hnn hsq
    rw [Finset.prod_pow] at hstep1
    have hnn1 : (0 : ℝ) ≤ ∏ p ∈ sievePrimes z, (1 - (p : ℝ)⁻¹) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast sievePrimes_five_le hp
      have hinv : (p : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        linarith
      linarith
    have hstep2 : ∏ p ∈ sievePrimes z, (1 - (p : ℝ)⁻¹)
        ≤ 3 * (Real.log z)⁻¹ := by
      rw [sievePrimes_prod_inv_eq hz3]
      exact mul_le_mul_of_nonneg_left (prod_primesBelow_le_inv_log z hz)
        (by norm_num)
    have hstep3 : (∏ p ∈ sievePrimes z, (1 - (p : ℝ)⁻¹)) ^ 2
        ≤ (3 * (Real.log z)⁻¹) ^ 2 :=
      pow_le_pow_left₀ hnn1 hstep2 2
    have hfinal : (3 * (Real.log z)⁻¹) ^ 2 = 9 / (Real.log z) ^ 2 := by
      field_simp
      ring
    linarith
  · -- z = 2: the sieve product is empty
    have hz2 : z = 2 := by omega
    subst hz2
    have hempty : sievePrimes 2 = ∅ := by
      unfold sievePrimes
      rw [Finset.Icc_eq_empty (by omega)]
      rfl
    rw [hempty, Finset.prod_empty]
    have hlog1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this
      exact_mod_cast this
    rw [one_le_div (by positivity)]
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have hsq : Real.log ((2 : ℕ) : ℝ) ^ 2 ≤ 1 := by
      rw [hcast]
      nlinarith [hlog1, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    linarith

/-- **THE UNCONDITIONAL BRUN RATE**: for ALL `N` and ALL `z ≥ 2`,
    `twins(N) ≤ 9·N/log²z + 3^z + z/6 + 1` — the stage-4a conditional theorem
    with its Mertens input discharged.  (Prose: `z ≈ ½·log N` yields
    `O(N/(log log N)²)`; the true Brun rate is stage 4b, not claimed.) -/
theorem twin_count_log_rate_unconditional (N z : ℕ) (hz : 2 ≤ z) :
    (((Finset.Icc 1 N).filter fun m =>
        (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      ≤ 9 / (Real.log z) ^ 2 * N + (3 : ℝ) ^ z + ((z : ℝ) / 6 + 1) :=
  twin_count_log_rate sievePrimes_prod_le_nine_div_log_sq N z hz

/-! ### Axiom audit -/

#print axioms sum_Icc_inv_le_prod_primesBelow
#print axioms prod_primesBelow_le_inv_log
#print axioms sievePrimes_prod_inv_eq
#print axioms sievePrimes_prod_le_nine_div_log_sq
#print axioms twin_count_log_rate_unconditional

end TypeII
end Geometric
end EuclidsPath
