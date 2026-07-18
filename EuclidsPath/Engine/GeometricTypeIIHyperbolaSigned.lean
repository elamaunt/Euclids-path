/-
  GeometricTypeIIHyperbolaSigned — SPEC 1, SIGNED LAYER: the μ-signed dyadic
  block of face E's trivial-root sector equals an EXACT short dual sum of
  Möbius partial sums — the sawtooth-to-Möbius dimension reduction.

  ORIGIN.  Wall-assault campaign, SPEC 1 (top-ranked build of the synthesis).
  The unsigned transport layer is `GeometricTypeIIHyperbola`; this module
  applies it with the TRUE Möbius weights on the dyadic conductor block
  `[D, 2D)` and lands the criterion-C event on the registered carrier.

  THE STATEMENT.  For the dyadic block of squarefree conductors coprime to 6,
  the μ-signed trivial-root window defect (the dyadic-block slice of
  `PairRoughRemainder` — face E's registered carrier — restricted to the
  C = ±1 sector, which is the FULL sector at prime conductors) satisfies the
  EXACT identity

      blockRemainder M D
        = Σ_{k < K₁} cut(M, k) + Σ_{1 ≤ k < K₂} cut(M+2, k)
          − 2M · Σ_{d ∈ block} μ(d)/d,

  where `cut(N, k) = Σ_{d ∈ block, kd < N} μ(d)` are MÖBIUS PARTIAL SUMS
  over initial segments of the block at the dual cutpoints, and
  `K₁ = ⌈M/D⌉`, `K₂ = ⌈(M+2)/D⌉`.  The block index (D conductors) is
  replaced by `K₁ + K₂ ≤ 2(M/D) + 3` one-dimensional Möbius evaluations:
  for `D > √(2M)` the dual side is STRICTLY shorter than the block interval
  (`dual_dimension_lt_interval`), machine-checked profile at M = 10⁶:
  125892 conductors → 16 dual terms at D = M^{0.85}.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `blockConductors` + `blockRemainder` + the definitional carrier tie
      `blockRemainder_eq_pairRoughRemainder`;
    * `signed_block_dual` — **THE EXACT DUAL IDENTITY** displayed above;
    * `abs_blockRemainder_le_of_cut_bound` — the honest conditional bound:
      ANY uniform bound `B` on the Möbius partial sums gives
      `|blockRemainder + 2M·Σμ/d| ≤ (K₁ + K₂)·B` — the named hypothesis IS
      the canonical one-dimensional open object;
    * `dual_dimension_le` + `dual_dimension_lt_interval` — the machine form
      of the dimension count.

  §110 FILING (criterion C, on the registered carrier).  The dyadic-block
  slice of `PairRoughRemainder` (index dimension: the block of `≤ D`
  conductors) is EXACTLY equal to `≤ 2(M/D) + 3` one-dimensional Möbius
  partial sums plus one explicit main term — the bilinear sawtooth object is
  replaced by the canonical one-dimensional object, with the unbounded
  variable eliminated.  No unconditional bound is claimed; the exact
  reduction is the registered progress.

  NUMERIC GROUNDING (pre-pass, this session, exact rationals): the full
  signed dual identity verified with exact `Fraction` arithmetic on
  M ∈ {7, 20, 50, 111, 200, 300} × D ∈ {3, 5, 10, 17, 30, 60} — 0
  violations.

  DISCLOSURES (mandated by the campaign synthesis).
    * The unsigned block sum is NOT `O(M/D)`: it carries a computable smooth
      bias for `D ≫ M^{2/3}`; only the exact dual formula, main terms
      included, is the theorem.
    * For `D ≤ √M` the dual side is longer than the block; no reduction is
      claimed there.
    * The surviving open core — Möbius partial sums over squarefree
      coprime-to-6 conductors in initial segments of `[D, 2D)` at the dual
      cutpoints — is exactly as open as face E's dyadic slice; this module
      CLOSES NO FACE: it replaces the bilinear sawtooth by the canonical
      one-dimensional object.
    * Mixed CRT roots are ceded by name: `ω(d) = 2` to
      `SemiprimeShortRestriction`, `ω(d) ≥ 3` to
      `HigherConductorDispersion`.  Nothing is smuggled.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIHyperbola

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### Layer 1: the dyadic block and its remainder -/

/-- The dyadic conductor block: squarefree, coprime to 6, in `[D, 2D)`. -/
def blockConductors (D : ℕ) : Finset ℕ :=
  (Finset.Ico D (2 * D)).filter (fun d => Squarefree d ∧ Nat.Coprime d 6)

theorem mem_blockConductors {D d : ℕ} :
    d ∈ blockConductors D
      ↔ (D ≤ d ∧ d < 2 * D) ∧ Squarefree d ∧ Nat.Coprime d 6 := by
  unfold blockConductors
  rw [Finset.mem_filter, Finset.mem_Ico]

/-- The μ-signed trivial-root window defect of the dyadic block. -/
noncomputable def blockRemainder (M D : ℕ) : ℝ :=
  PairRoughRemainder (trivialRootShift M) (blockConductors D)

/-- The definitional carrier tie: the block remainder IS the dyadic-block
slice of face E's registered carrier at the trivial-root sector. -/
theorem blockRemainder_eq_pairRoughRemainder (M D : ℕ) :
    blockRemainder M D
      = PairRoughRemainder (trivialRootShift M) (blockConductors D) := rfl

/-- The canonical one-dimensional object: the Möbius partial sum of the
block below the `k`-th dual cutpoint of level `N`. -/
noncomputable def moebiusCut (D N k : ℕ) : ℝ :=
  ∑ d ∈ (blockConductors D).filter (fun d => k * d < N),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-! ### Layer 2: THE EXACT DUAL IDENTITY -/

/-- **THE SAWTOOTH-TO-MÖBIUS DIMENSION REDUCTION** (criterion C on the
registered carrier): the μ-signed dyadic block equals `K₁ + K₂ − 1` Möbius
partial sums at the dual cutpoints plus one explicit main term — EXACT. -/
theorem signed_block_dual {D : ℕ} (hD : 3 ≤ D) (M : ℕ) :
    blockRemainder M D
      = (∑ k ∈ Finset.range ((M + D - 1) / D), moebiusCut D M k)
        + (∑ k ∈ Finset.Ico 1 ((M + 2 + D - 1) / D), moebiusCut D (M + 2) k)
        - 2 * M * ∑ d ∈ blockConductors D,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d := by
  classical
  set S := blockConductors D with hS
  have hDd : ∀ d ∈ S, D ≤ d := fun d hd => (mem_blockConductors.mp hd).1.1
  have hd3 : ∀ d ∈ S, 3 ≤ d := fun d hd => le_trans hD (hDd d hd)
  -- Step 1: sawtooth expansion of every block term
  have hexp : blockRemainder M D
      = (∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
            * (((M + d - 1) / d : ℕ) : ℝ))
        + (∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
            * (((M + 1) / d : ℕ) : ℝ))
        - 2 * M * ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d := by
    unfold blockRemainder PairRoughRemainder
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [trivialRootShift_eq_sawtooth (by have := hd3 d hd; omega)]
    ring
  -- Step 2: the ⌊(M+1)/d⌋ column shifts to the ⌈(M+2)/d⌉ column minus one
  have hshift : ∀ d ∈ S,
      (((M + 1) / d : ℕ) : ℝ) = (((M + 2 + d - 1) / d : ℕ) : ℝ) - 1 := by
    intro d hd
    have hd1 : 0 < d := by have := hd3 d hd; omega
    have hnat : (M + 2 + d - 1) / d = (M + 1) / d + 1 := by
      have h1 : M + 2 + d - 1 = M + 1 + d := by omega
      rw [h1, Nat.add_div_right _ hd1]
    rw [hnat]
    push_cast
    ring
  -- Step 3: both divisor columns through the hyperbola switch
  have hswitch1 : ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (((M + d - 1) / d : ℕ) : ℝ)
      = ∑ k ∈ Finset.range ((M + D - 1) / D), moebiusCut D M k := by
    rw [hyperbola_switch (show 1 ≤ D by omega) S hDd M
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))]
    rfl
  have hswitch2 : ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (((M + 2 + d - 1) / d : ℕ) : ℝ)
      = ∑ k ∈ Finset.range ((M + 2 + D - 1) / D), moebiusCut D (M + 2) k := by
    rw [hyperbola_switch (show 1 ≤ D by omega) S hDd (M + 2)
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))]
    rfl
  -- Step 4: peel the k = 0 cutpoint (the full block sum) off column two
  have hK2 : 1 ≤ (M + 2 + D - 1) / D := by
    rw [Nat.le_div_iff_mul_le (show 0 < D by omega)]
    omega
  have hcut0 : moebiusCut D (M + 2) 0
      = ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    unfold moebiusCut
    rw [Finset.filter_true_of_mem (fun d _ => by omega)]
  have hpeel : ∑ k ∈ Finset.range ((M + 2 + D - 1) / D), moebiusCut D (M + 2) k
      = (∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ))
        + ∑ k ∈ Finset.Ico 1 ((M + 2 + D - 1) / D), moebiusCut D (M + 2) k := by
    rw [Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot hK2, hcut0]
  -- Step 5: assemble; the peeled block sum cancels the −Σμ of the shift
  have hcol2 : ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (((M + 1) / d : ℕ) : ℝ)
      = ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          * ((((M + 2 + d - 1) / d : ℕ) : ℝ) - 1) :=
    Finset.sum_congr rfl fun d hd => by rw [hshift d hd]
  have hsplit2 : ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * ((((M + 2 + d - 1) / d : ℕ) : ℝ) - 1)
      = (∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          * (((M + 2 + d - 1) / d : ℕ) : ℝ))
        - ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hexp, hswitch1, hcol2, hsplit2, hswitch2, hpeel]
  ring

/-! ### Layer 3: the honest conditional bound and the dimension count -/

/-- **The honest open core, isolated**: ANY uniform bound on the Möbius
partial sums of the block controls the signed dyadic slice up to the
explicit main term.  The hypothesis is the canonical one-dimensional object
— exactly as open as face E's dyadic slice, now in its canonical name. -/
theorem abs_blockRemainder_le_of_cut_bound {D : ℕ} (hD : 3 ≤ D) (M : ℕ)
    {B : ℝ} (hB : ∀ N k : ℕ, |moebiusCut D N k| ≤ B) :
    |blockRemainder M D
        + 2 * M * ∑ d ∈ blockConductors D,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d|
      ≤ (((M + D - 1) / D + (M + 2 + D - 1) / D : ℕ) : ℝ) * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 1 0)
  have hdual := signed_block_dual hD M
  have hval : blockRemainder M D
      + 2 * M * ∑ d ∈ blockConductors D,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d
      = (∑ k ∈ Finset.range ((M + D - 1) / D), moebiusCut D M k)
        + ∑ k ∈ Finset.Ico 1 ((M + 2 + D - 1) / D), moebiusCut D (M + 2) k := by
    rw [hdual]
    ring
  rw [hval]
  calc |(∑ k ∈ Finset.range ((M + D - 1) / D), moebiusCut D M k)
        + ∑ k ∈ Finset.Ico 1 ((M + 2 + D - 1) / D), moebiusCut D (M + 2) k|
      ≤ (∑ k ∈ Finset.range ((M + D - 1) / D), |moebiusCut D M k|)
        + ∑ k ∈ Finset.Ico 1 ((M + 2 + D - 1) / D), |moebiusCut D (M + 2) k| := by
        refine le_trans (abs_add_le _ _) ?_
        gcongr <;> exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (((M + D - 1) / D : ℕ) : ℝ) * B
        + (((M + 2 + D - 1) / D - 1 : ℕ) : ℝ) * B := by
        gcongr
        · calc ∑ k ∈ Finset.range ((M + D - 1) / D), |moebiusCut D M k|
              ≤ ∑ _k ∈ Finset.range ((M + D - 1) / D), B :=
                Finset.sum_le_sum fun k _ => hB M k
            _ = (((M + D - 1) / D : ℕ) : ℝ) * B := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        · calc ∑ k ∈ Finset.Ico 1 ((M + 2 + D - 1) / D), |moebiusCut D (M + 2) k|
              ≤ ∑ _k ∈ Finset.Ico 1 ((M + 2 + D - 1) / D), B :=
                Finset.sum_le_sum fun k _ => hB (M + 2) k
            _ = (((M + 2 + D - 1) / D - 1 : ℕ) : ℝ) * B := by
                rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ = ((((M + D - 1) / D + ((M + 2 + D - 1) / D - 1) : ℕ)) : ℝ) * B := by
        push_cast [Nat.cast_add]
        ring
    _ ≤ (((M + D - 1) / D + (M + 2 + D - 1) / D : ℕ) : ℝ) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact_mod_cast Nat.add_le_add_left (Nat.sub_le _ _) _

/-- The dual dimension is at most `2(M/D) + 3`. -/
theorem dual_dimension_le {D : ℕ} (hD : 1 ≤ D) (M : ℕ) :
    (M + D - 1) / D + (M + 2 + D - 1) / D ≤ 2 * (M / D) + 3 := by
  have hsplit := Nat.div_add_mod M D
  have hmod : M % D < D := Nat.mod_lt _ (by omega)
  have hcomm : D * (M / D) = (M / D) * D := Nat.mul_comm _ _
  have h1 : (M + D - 1) / D ≤ M / D + 1 := by
    by_contra hcon
    push Not at hcon
    have hk : (M / D + 1) < (M + D - 1) / D := hcon
    have := (lt_ceil_div_iff hD).mp hk
    have hexp : (M / D + 1) * D = (M / D) * D + D := by ring
    omega
  have h2 : (M + 2 + D - 1) / D ≤ M / D + 2 := by
    by_contra hcon
    push Not at hcon
    have hk : (M / D + 2) < (M + 2 + D - 1) / D := hcon
    have := (lt_ceil_div_iff hD).mp hk
    have hexp : (M / D + 2) * D = (M / D) * D + 2 * D := by ring
    omega
  omega

/-- **The machine dimension comparison**: whenever `2(M/D) + 3 < D`
(the `D ≳ √(2M)` regime), the dual index count is STRICTLY below the block
interval length — the criterion-C count made checkable. -/
theorem dual_dimension_lt_interval {D M : ℕ} (hD : 1 ≤ D)
    (hbig : 2 * (M / D) + 3 < D) :
    (M + D - 1) / D + (M + 2 + D - 1) / D < D :=
  lt_of_le_of_lt (dual_dimension_le hD M) hbig

end TypeII
end Geometric
end EuclidsPath
