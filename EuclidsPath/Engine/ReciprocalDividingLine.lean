/-
  ReciprocalDividingLine — sharpening `universal_engine_dividing_line`.

  The engine is realized on ℝ (`perpetualEngine_on_real`, the descent (1/2)ⁿ → 0)
  and forbidden on the well-founded ℕ (`no_perpetual_engine_on_nat`). Here is WHY the
  ℝ-side cannot be "pressed" for an arithmetic conclusion (e.g. the infinitude of
  twin centres): the continuum descent lives in the GAPS, never on the ℕ-skeleton.

  Two green bridges (standard triple; NO `step00FirstCause`; taint unchanged). Both
  are HONEST RELABELLINGS: they recast the observation, they do NOT prove anything
  about primes.

    • `strictAnti_meets_nat_finitely` — a strictly-antitone, bounded-below real
      sequence takes natural-number values only finitely often. The ℝ-engine
      descends through non-integers; the ℕ-skeleton is met finitely.
    • `twinCenters_accumulate_at_zero_iff_infinite` — 0 is a limit point of the
      inverted twin centres {1/m} IFF there are infinitely many twin centres. The
      inversion m ↦ 1/m is a biconditional relabelling of ZERO arithmetic content;
      it carries the taint of NOTHING (proved over an opaque predicate), so it is
      green — and it is provably NOT a proof of the twin conjecture, only its
      restatement in ℝ-topology.
-/
import EuclidsPath.Engine.UniversalEngine
import EuclidsPath.Engine.Residuals
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace EuclidsPath.ReciprocalDividingLine

open EuclidsPath.UniversalEngine

/-- **The engine descends through the gaps, not the ℕ-skeleton.** A strictly-antitone
    real sequence bounded below takes natural-number values only finitely often:
    those values would be an infinite strictly-decreasing set of naturals inside a
    bounded interval. This is `no_perpetual_engine_on_nat` in analytic dress — the
    reason the ℝ-realized engine (`perpetualEngine_on_real`) cannot be pressed for an
    ℕ-conclusion. -/
theorem strictAnti_meets_nat_finitely
    (a : ℕ → ℝ) (ha : StrictAnti a) (L : ℝ) (hL : ∀ n, L ≤ a n) :
    {n | ∃ k : ℕ, a n = (k : ℝ)}.Finite := by
  have hsub : a '' {n | ∃ k : ℕ, a n = (k : ℝ)}
      ⊆ (Nat.cast : ℕ → ℝ) '' Set.Iic ⌊a 0⌋₊ := by
    rintro x ⟨n, ⟨k, hk⟩, rfl⟩
    have h0 : a n ≤ a 0 := ha.antitone (Nat.zero_le n)
    have hk0 : (0 : ℝ) ≤ a 0 := le_trans (by rw [hk]; positivity) h0
    exact ⟨k, by rw [Set.mem_Iic, Nat.le_floor_iff hk0, ← hk]; exact h0, hk.symm⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset ((Set.finite_Iic _).image _) hsub) ha.injective.injOn

/-- **The reciprocal accumulation equivalence.** Zero is a limit point of the inverted
    twin centres `{1/m : TwinCenterZ m}` if and only if there are infinitely many twin
    centres. HONEST SCOPE: this is a RELABELLING, not progress — both directions are
    proved with no number theory (over the opaque predicate `TwinCenterZ`), so the
    ℝ-limit-point statement carries EXACTLY the content of the open arithmetic one and
    no more. It is green precisely because it is an equivalence, importing no taint. -/
theorem twinCenters_accumulate_at_zero_iff_infinite :
    (0 : ℝ) ∈ closure {x : ℝ | ∃ m, EuclidsPath.Residuals.TwinCenterZ m ∧ x = 1 / (m : ℝ)}
      ↔ {m | EuclidsPath.Residuals.TwinCenterZ m}.Infinite := by
  constructor
  · intro hcl
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have hXfin : {x : ℝ | ∃ m, EuclidsPath.Residuals.TwinCenterZ m ∧ x = 1 / (m : ℝ)}.Finite := by
      refine Set.Finite.subset (Set.Finite.image (fun m : ℕ => 1 / (m : ℝ)) hfin) ?_
      rintro x ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    rw [hXfin.isClosed.closure_eq] at hcl
    obtain ⟨m, hm, h0⟩ := hcl
    have hpos : (0 : ℝ) < 1 / (m : ℝ) := by
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; exact absurd hm.1 (by decide)
        · exact h
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      positivity
    rw [← h0] at hpos
    exact lt_irrefl 0 hpos
  · intro hinf
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    obtain ⟨m, hm_mem, hm_gt⟩ := hinf.exists_gt N
    have hεm : 1 / ε < (m : ℝ) := lt_trans hN (by exact_mod_cast hm_gt)
    have hm_pos : (0 : ℝ) < (m : ℝ) := lt_trans (by positivity) hεm
    refine ⟨1 / (m : ℝ), ⟨m, hm_mem, rfl⟩, ?_⟩
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity), div_lt_iff₀ hm_pos,
      mul_comm]
    rwa [div_lt_iff₀ hε] at hεm

#print axioms strictAnti_meets_nat_finitely
#print axioms twinCenters_accumulate_at_zero_iff_infinite

end EuclidsPath.ReciprocalDividingLine
