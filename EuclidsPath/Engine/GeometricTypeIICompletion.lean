/-
  GeometricTypeIICompletion — the exact completion apparatus of the SHORT restriction (§55 core).

  ORIGIN (parity_wall Prime-Chaos session dossier §52 / §55). The wall lives in short intervals.
  The classical bridge from complete to incomplete sums is COMPLETION: the short sum of any
  `f : ZMod q → ℂ` over `m < M` equals `(1/q) Σ_h W_M(h) F(h)`, where `W_M(h) = Σ_{m<M} ψ(−hm)`
  is the interval Fourier weight and `F` the complete transform.  The weight obeys the EXACT
  geometric-telescope law `W_M(h)(ψ(−h) − 1) = ψ(−hM) − 1` (so `‖W_M(h)‖ · ‖ψ(−h) − 1‖ ≤ 2` — the
  algebraic form of the §55 kernel bound `min(M, q/‖h‖)`, with no sine estimates), and the EXACT
  Parseval identity `Σ_h ‖W_M(h)‖² = qM` for `M ≤ q`.  Specializing `f` to the indicator of the
  CRT-root set `{C : C² = 1}` produces the exact per-q Fourier form of the SHORT root-count
  remainder — the literal §55 object — and a per-q Cauchy–Schwarz bound `√(2M)` at prime modulus.

  WHAT IS PROVED (std axioms, no sorry, no new axioms; ALL exact identities / visibility lemmas):
    * `interval_completion` — the exact completion identity (all `q`, ALL `M`, any `f`);
    * `interval_weight_geom` / `interval_weight_bound` — the geometric kernel law and
      `‖W_M(h)‖·‖ψ(−h)−1‖ ≤ 2`, plus the trivial `‖W_M(h)‖ ≤ M`;
    * `interval_parseval` — `Σ_h ‖W_M(h)‖² = qM` EXACTLY, for `M ≤ q` (necessary: for `M > q`
      classes repeat and the sum strictly exceeds `qM`);
    * `rootFourier_parseval` — `Σ_h ‖S_q(h)‖² = q·#{C : C² = 1}` (the general-q §53 second moment);
    * `root_remainder_fourier` — `q·(short root count) = M·|R| + Σ_{h≠0} W_M(h)·S_q(h)` EXACTLY;
    * `root_remainder_prime_bound` — at prime `p`, `M ≤ p`: the short-interval root-count remainder
      is `≤ √(2M)` in absolute value.

  DISCLOSURE (the wall is NOT moved, renamed, or hidden):
    * Summing the per-q bounds in absolute value over `q ∣ P(z)` is USELESS (the dossier's
      `3^{π(z)}`-term blow-up); the open object is the SIGNED coherent low-frequency sum over `q` —
      residual E (`LowFreqRootCoherence`) — which nothing in this module touches, weakens, or renames.
    * For prime `q` the per-q Cauchy–Schwarz bound `√(2M)` is WORSE than the trivial bound `2`
      obtained by counting the two roots directly (for every `M > 2`); it is recorded only to
      display the completed Fourier structure and is NOT a criterion-B summability gain.
    * The completion identity, the geometric kernel bound, Parseval, and the per-q Fourier form of
      the short root-count remainder are exact restatements — visibility lemmas, not progress on
      residuals C/D/E or `CRE`.  This module introduces ZERO new open `Prop`s; every new `def` is a
      named structural object (a kernel / a completed remainder form), NOT a target and NOT a bound.
    * Nothing here proves twins; the wall is localized, not defeated. twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIRoots

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The interval Fourier weight and complete orthogonality -/

/-- The interval Fourier weight `W_M(h) = Σ_{m<M} ψ(−h·m)` — a named structural object (a kernel),
    NOT a target and NOT a bound. -/
noncomputable def intervalWeight (q : ℕ) [NeZero q] (M : ℕ) (h : ZMod q) : ℂ :=
  ∑ m ∈ Finset.range M, ZMod.stdAddChar (-(h * (m : ZMod q)))

/-- Complete orthogonality: `Σ_h ψ(h·x) = q·[x = 0]` (any modulus). -/
private theorem char_sum_shift {q : ℕ} [NeZero q] (x : ZMod q) :
    ∑ h : ZMod q, ZMod.stdAddChar (h * x) = if x = 0 then (q : ℂ) else 0 := by
  have hs := AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q)
  rw [hs]
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos hx, ZMod.card]
  · rw [if_neg hx, if_neg hx]
    exact Nat.cast_zero

/-- `‖ψ(x)‖ = 1` for the standard character. -/
private theorem stdAddChar_norm {q : ℕ} [NeZero q] (x : ZMod q) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- `conj ψ(x) = ψ(−x)` for the standard character. -/
private theorem stdAddChar_conj {q : ℕ} [NeZero q] (x : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hinv : ZMod.stdAddChar (-x) = (ZMod.stdAddChar x)⁻¹ := AddChar.map_neg_eq_inv _ x
  rw [hinv, ← Complex.inv_eq_conj (stdAddChar_norm x)]

/-! ## The exact completion identity (all q, ALL M) -/

/-- **The completion identity (§55 core).** The SHORT sum of any `f : ZMod q → ℂ` over `m < M`
    equals the complete Fourier-weighted sum: `Σ_{m<M} f(m) = (1/q) Σ_h W_M(h) F(h)`, with
    `F(h) = Σ_n f(n) ψ(h·n)`.  Exact for ALL `M` (including `M > q`). -/
theorem interval_completion (q M : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ m ∈ Finset.range M, f ((m : ZMod q))
      = (q : ℂ)⁻¹ * ∑ h : ZMod q,
          intervalWeight q M h * (∑ n : ZMod q, f n * ZMod.stdAddChar (h * n)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have key : ∑ h : ZMod q,
      intervalWeight q M h * (∑ n : ZMod q, f n * ZMod.stdAddChar (h * n))
      = (q : ℂ) * ∑ m ∈ Finset.range M, f ((m : ZMod q)) := by
    have expand : ∀ h : ZMod q,
        intervalWeight q M h * (∑ n : ZMod q, f n * ZMod.stdAddChar (h * n))
          = ∑ m ∈ Finset.range M, ∑ n : ZMod q,
              f n * ZMod.stdAddChar (h * (n - (m : ZMod q))) := by
      intro h
      unfold intervalWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      have hmul : ZMod.stdAddChar (-(h * (m : ZMod q))) * ZMod.stdAddChar (h * n)
          = ZMod.stdAddChar (h * (n - (m : ZMod q))) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      calc ZMod.stdAddChar (-(h * (m : ZMod q))) * (f n * ZMod.stdAddChar (h * n))
          = f n * (ZMod.stdAddChar (-(h * (m : ZMod q))) * ZMod.stdAddChar (h * n)) := by ring
        _ = f n * ZMod.stdAddChar (h * (n - (m : ZMod q))) := by rw [hmul]
    rw [Finset.sum_congr rfl (fun h _ => expand h), Finset.sum_comm]
    have inner : ∀ m ∈ Finset.range M,
        ∑ h : ZMod q, ∑ n : ZMod q, f n * ZMod.stdAddChar (h * (n - (m : ZMod q)))
          = (q : ℂ) * f ((m : ZMod q)) := by
      intro m _
      rw [Finset.sum_comm]
      have hterm : ∀ n : ZMod q,
          ∑ h : ZMod q, f n * ZMod.stdAddChar (h * (n - (m : ZMod q)))
            = f n * (if n - (m : ZMod q) = 0 then (q : ℂ) else 0) := by
        intro n
        rw [← Finset.mul_sum, char_sum_shift]
      rw [Finset.sum_congr rfl (fun n _ => hterm n)]
      have hsingle : ∀ n : ZMod q,
          f n * (if n - (m : ZMod q) = 0 then (q : ℂ) else 0)
            = if n = (m : ZMod q) then f n * (q : ℂ) else 0 := by
        intro n
        by_cases hn : n = (m : ZMod q)
        · rw [if_pos hn, if_pos (by rw [hn, sub_self])]
        · rw [if_neg hn, if_neg (fun hc => hn (by linear_combination hc)), mul_zero]
      rw [Finset.sum_congr rfl (fun n _ => hsingle n),
        Finset.sum_ite_eq' Finset.univ ((m : ZMod q)) (fun n => f n * (q : ℂ))]
      rw [if_pos (Finset.mem_univ _)]
      ring
    rw [Finset.sum_congr rfl inner, ← Finset.mul_sum]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]

/-! ## The geometric kernel law (§55, algebraic form — no sine estimates) -/

/-- The weight is a geometric sum of the ratio `ψ(−h)`. -/
private theorem intervalWeight_eq_geom (q M : ℕ) [NeZero q] (h : ZMod q) :
    intervalWeight q M h = ∑ m ∈ Finset.range M, (ZMod.stdAddChar (-h)) ^ m := by
  unfold intervalWeight
  apply Finset.sum_congr rfl
  intro m _
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- **The geometric kernel law (§55).** `W_M(h)·(ψ(−h) − 1) = ψ(−hM) − 1` — the exact telescoping
    identity behind `min(M, q/‖h‖)`, valid for all `h` (both sides vanish at `ψ(−h) = 1`). -/
theorem interval_weight_geom (q M : ℕ) [NeZero q] (h : ZMod q) :
    intervalWeight q M h * (ZMod.stdAddChar (-h) - 1)
      = ZMod.stdAddChar (-(h * (M : ZMod q))) - 1 := by
  rw [intervalWeight_eq_geom, geom_sum_mul]
  congr 1
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- **The kernel bound (§55, algebraic form).** `‖W_M(h)‖ · ‖ψ(−h) − 1‖ ≤ 2`: away from the zero
    frequency the weight is small exactly inversely to the frequency's distance from `1`. -/
theorem interval_weight_bound (q M : ℕ) [NeZero q] (h : ZMod q) :
    ‖intervalWeight q M h‖ * ‖ZMod.stdAddChar (-h) - 1‖ ≤ 2 := by
  rw [← norm_mul, interval_weight_geom]
  calc ‖ZMod.stdAddChar (-(h * (M : ZMod q))) - 1‖
      ≤ ‖ZMod.stdAddChar (-(h * (M : ZMod q)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [stdAddChar_norm, norm_one]; norm_num

/-- The trivial weight bound `‖W_M(h)‖ ≤ M`. -/
theorem interval_weight_trivial (q M : ℕ) [NeZero q] (h : ZMod q) :
    ‖intervalWeight q M h‖ ≤ M := by
  unfold intervalWeight
  calc ‖∑ m ∈ Finset.range M, ZMod.stdAddChar (-(h * (m : ZMod q)))‖
      ≤ ∑ m ∈ Finset.range M, ‖ZMod.stdAddChar (-(h * (m : ZMod q)))‖ := norm_sum_le _ _
    _ = ∑ _m ∈ Finset.range M, (1 : ℝ) :=
        Finset.sum_congr rfl fun m _ => stdAddChar_norm _
    _ = M := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]

/-! ## The exact Parseval identities (M ≤ q) -/

/-- Pointwise: `z · conj z` is the squared norm, as a complex number. -/
private theorem mul_conj_eq_norm_sq (z : ℂ) :
    z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Interval Parseval (§55).** `Σ_h ‖W_M(h)‖² = q·M` EXACTLY, for `M ≤ q`.  (The hypothesis is
    necessary: for `M > q` residue classes repeat and the sum strictly exceeds `qM`.) -/
theorem interval_parseval (q M : ℕ) [NeZero q] (hMq : M ≤ q) :
    ∑ h : ZMod q, ‖intervalWeight q M h‖ ^ 2 = (q : ℝ) * M := by
  have key : ∑ h : ZMod q, (intervalWeight q M h) * (starRingEnd ℂ) (intervalWeight q M h)
      = (q : ℂ) * M := by
    have expand : ∀ h : ZMod q,
        (intervalWeight q M h) * (starRingEnd ℂ) (intervalWeight q M h)
          = ∑ m ∈ Finset.range M, ∑ m' ∈ Finset.range M,
              ZMod.stdAddChar (h * ((m' : ZMod q) - (m : ZMod q))) := by
      intro h
      unfold intervalWeight
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m' _
      rw [stdAddChar_conj, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [Finset.sum_congr rfl (fun h _ => expand h), Finset.sum_comm]
    have inner : ∀ m ∈ Finset.range M,
        ∑ h : ZMod q, ∑ m' ∈ Finset.range M,
            ZMod.stdAddChar (h * ((m' : ZMod q) - (m : ZMod q)))
          = (q : ℂ) := by
      intro m hm
      rw [Finset.sum_comm]
      have hterm : ∀ m' ∈ Finset.range M,
          ∑ h : ZMod q, ZMod.stdAddChar (h * ((m' : ZMod q) - (m : ZMod q)))
            = if (m' : ZMod q) = (m : ZMod q) then (q : ℂ) else 0 := by
        intro m' _
        rw [char_sum_shift]
        by_cases he : (m' : ZMod q) = (m : ZMod q)
        · rw [if_pos (by rw [he, sub_self]), if_pos he]
        · rw [if_neg (fun hc => he (by linear_combination hc)), if_neg he]
      rw [Finset.sum_congr rfl hterm]
      have huniq : ∀ m' ∈ Finset.range M,
          (if (m' : ZMod q) = (m : ZMod q) then (q : ℂ) else 0)
            = if m' = m then (q : ℂ) else 0 := by
        intro m' hm'
        by_cases he : m' = m
        · rw [if_pos he, if_pos (by rw [he])]
        · rw [if_neg he]
          have hne : (m' : ZMod q) ≠ (m : ZMod q) := by
            intro hc
            have hmod : m' % q = m % q := (ZMod.natCast_eq_natCast_iff m' m q).mp hc
            have h2 : m' % q = m' :=
              Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hm') hMq)
            have h3 : m % q = m :=
              Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hm) hMq)
            omega
          rw [if_neg hne]
      rw [Finset.sum_congr rfl huniq,
        Finset.sum_ite_eq' (Finset.range M) m (fun _ => (q : ℂ)), if_pos hm]
    rw [Finset.sum_congr rfl inner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hcast : ((∑ h : ZMod q, ‖intervalWeight q M h‖ ^ 2 : ℝ) : ℂ) = ((q : ℝ) * M : ℝ) := by
    push_cast
    rw [← key]
    apply Finset.sum_congr rfl
    intro h _
    rw [mul_conj_eq_norm_sq]
    push_cast
    ring
  exact_mod_cast hcast

/-! ## The CRT-root Fourier transform at general modulus (§53) -/

/-- The Fourier transform of the CRT-root set `{C : C² = 1}` at modulus `q` — a named structural
    object, NOT a target and NOT a bound (cf. `rootSum` for the prime-pair form and
    `PairRoughRemainder` for the signed global object). -/
noncomputable def rootFourier (q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ C ∈ Finset.univ.filter (fun C : ZMod q => C ^ 2 = 1), ZMod.stdAddChar (h * C)

/-- **Root Parseval (§53, general q).** `Σ_h ‖S_q(h)‖² = q·#{C : C² = 1}` — the complete second
    moment of the root transform, at ANY modulus. -/
theorem rootFourier_parseval (q : ℕ) [NeZero q] :
    ∑ h : ZMod q, ‖rootFourier q h‖ ^ 2
      = (q : ℝ) * (Finset.univ.filter (fun C : ZMod q => C ^ 2 = 1)).card := by
  set R : Finset (ZMod q) := Finset.univ.filter (fun C : ZMod q => C ^ 2 = 1) with hR
  have key : ∑ h : ZMod q, (rootFourier q h) * (starRingEnd ℂ) (rootFourier q h)
      = (q : ℂ) * R.card := by
    have expand : ∀ h : ZMod q,
        (rootFourier q h) * (starRingEnd ℂ) (rootFourier q h)
          = ∑ C ∈ R, ∑ C' ∈ R, ZMod.stdAddChar (h * (C - C')) := by
      intro h
      unfold rootFourier
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C' _
      rw [stdAddChar_conj, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [Finset.sum_congr rfl (fun h _ => expand h), Finset.sum_comm]
    have inner : ∀ C ∈ R,
        ∑ h : ZMod q, ∑ C' ∈ R, ZMod.stdAddChar (h * (C - C')) = (q : ℂ) := by
      intro C hC
      rw [Finset.sum_comm]
      have hterm : ∀ C' ∈ R,
          ∑ h : ZMod q, ZMod.stdAddChar (h * (C - C'))
            = if C' = C then (q : ℂ) else 0 := by
        intro C' _
        rw [char_sum_shift]
        by_cases he : C' = C
        · rw [if_pos (by rw [he, sub_self]), if_pos he]
        · rw [if_neg (fun hc => he (by linear_combination -hc)), if_neg he]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' R C (fun _ => (q : ℂ)), if_pos hC]
    rw [Finset.sum_congr rfl inner, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcast : ((∑ h : ZMod q, ‖rootFourier q h‖ ^ 2 : ℝ) : ℂ) = ((q : ℝ) * R.card : ℝ) := by
    push_cast
    rw [← key]
    apply Finset.sum_congr rfl
    intro h _
    rw [mul_conj_eq_norm_sq]
    push_cast
    ring
  exact_mod_cast hcast

/-! ## The exact per-q Fourier form of the SHORT root-count remainder (§55) -/

/-- **The short root-count remainder, completed (§55).** EXACT identity at any modulus, any `M`:
    `q · #{m < M : m² ≡ 1} = M · #{C : C² = 1} + Σ_{h≠0} W_M(h) · S_q(h)`.
    The left side is the SHORT count; the first right term is the expected main term; the
    `h ≠ 0` sum is the literal per-q low-frequency remainder of residual E. -/
theorem root_remainder_fourier (q M : ℕ) [NeZero q] :
    (q : ℂ) * (((Finset.range M).filter (fun (m : ℕ) => ((m : ZMod q)) ^ 2 = 1)).card : ℂ)
      = (M : ℂ) * ((Finset.univ.filter (fun C : ZMod q => C ^ 2 = 1)).card : ℂ)
        + ∑ h ∈ Finset.univ.erase (0 : ZMod q), intervalWeight q M h * rootFourier q h := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  -- completion applied to the root indicator
  have hcomp := interval_completion q M (fun n => if n ^ 2 = 1 then (1 : ℂ) else 0)
  -- the transform of the indicator is rootFourier
  have hF : ∀ h : ZMod q,
      (∑ n : ZMod q, (if n ^ 2 = 1 then (1 : ℂ) else 0) * ZMod.stdAddChar (h * n))
        = rootFourier q h := by
    intro h
    unfold rootFourier
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ^ 2 = 1
    · rw [if_pos hn, if_pos hn, one_mul]
    · rw [if_neg hn, if_neg hn, zero_mul]
  -- the short sum of the indicator is the short count
  have hshort : ∑ m ∈ Finset.range M, (if ((m : ZMod q)) ^ 2 = 1 then (1 : ℂ) else 0)
      = (((Finset.range M).filter (fun (m : ℕ) => ((m : ZMod q)) ^ 2 = 1)).card : ℂ) := by
    rw [Finset.sum_boole]
  simp only [hF] at hcomp
  rw [hshort] at hcomp
  -- split off h = 0
  have hsplit : ∑ h : ZMod q, intervalWeight q M h * rootFourier q h
      = intervalWeight q M 0 * rootFourier q 0
        + ∑ h ∈ Finset.univ.erase (0 : ZMod q), intervalWeight q M h * rootFourier q h :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod q))).symm
  have hW0 : intervalWeight q M 0 = (M : ℂ) := by
    unfold intervalWeight
    have hz : ∀ m : ℕ, ZMod.stdAddChar (-((0 : ZMod q) * (m : ZMod q))) = 1 := by
      intro m
      rw [zero_mul, neg_zero, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl (fun m _ => hz m), Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.card_range]
  have hS0 : rootFourier q 0
      = ((Finset.univ.filter (fun C : ZMod q => C ^ 2 = 1)).card : ℂ) := by
    unfold rootFourier
    have hz : ∀ C ∈ Finset.univ.filter (fun C : ZMod q => C ^ 2 = 1),
        ZMod.stdAddChar ((0 : ZMod q) * C) = 1 := by
      intro C _
      rw [zero_mul, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl hz, Finset.sum_const, nsmul_eq_mul, mul_one]
  calc (q : ℂ) * (((Finset.range M).filter (fun (m : ℕ) => ((m : ZMod q)) ^ 2 = 1)).card : ℂ)
      = (q : ℂ) * ((q : ℂ)⁻¹ * ∑ h : ZMod q, intervalWeight q M h * rootFourier q h) := by
        rw [← hcomp]
    _ = ∑ h : ZMod q, intervalWeight q M h * rootFourier q h := by
        rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
    _ = (M : ℂ) * ((Finset.univ.filter (fun C : ZMod q => C ^ 2 = 1)).card : ℂ)
        + ∑ h ∈ Finset.univ.erase (0 : ZMod q), intervalWeight q M h * rootFourier q h := by
        rw [hsplit, hW0, hS0]

/-! ## The prime case: |R| = 2 and the per-q bound -/

private theorem two_ne_zero_zmodq {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) : (2 : ZMod p) ≠ 0 := by
  have : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
  simpa using this

/-- At an odd prime the root set is exactly `{1, −1}`: cardinality `2`. -/
theorem rootFourier_card_prime {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    (Finset.univ.filter (fun C : ZMod p => C ^ 2 = 1)).card = 2 := by
  have h2 := two_ne_zero_zmodq hp2
  have hset : Finset.univ.filter (fun C : ZMod p => C ^ 2 = 1) = {(1 : ZMod p), -1} := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hC
      have hfac : (C - 1) * (C + 1) = 0 := by linear_combination hC
      rcases mul_eq_zero.mp hfac with h | h
      · left; linear_combination h
      · right; linear_combination h
    · rintro (rfl | rfl)
      · rw [one_pow]
      · rw [neg_one_sq]
  rw [hset]
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  intro hmem
  rw [Finset.mem_singleton] at hmem
  exact h2 (by linear_combination hmem)

/-- **The per-q remainder bound at prime modulus (§55, `M ≤ p`).** The short root-count remainder
    is `≤ √(2M)`: completion + Cauchy–Schwarz + the two Parseval identities.  RECORDED FOR THE
    STRUCTURE ONLY: for prime `p` this is WORSE than the trivial bound `2` whenever `M > 2` — it
    is NOT a criterion-B gain, and summing per-q absolute bounds over `q` is the known dead end;
    the signed low-frequency coherence (residual E) is untouched. -/
theorem root_remainder_prime_bound {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {M : ℕ} (hMp : M ≤ p) :
    |(((Finset.range M).filter (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ)
        - 2 * M / p| ≤ Real.sqrt (2 * M) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := (Fact.out : p.Prime).pos
    exact_mod_cast this
  -- the exact identity, real form
  have hid := root_remainder_fourier p M
  rw [rootFourier_card_prime hp2] at hid
  -- bound the h ≠ 0 tail
  have htail : ‖∑ h ∈ Finset.univ.erase (0 : ZMod p),
      intervalWeight p M h * rootFourier p h‖ ≤ (p : ℝ) * Real.sqrt (2 * M) := by
    have hCS : (∑ h ∈ Finset.univ.erase (0 : ZMod p),
        ‖intervalWeight p M h‖ * ‖rootFourier p h‖) ^ 2
        ≤ (∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖ ^ 2)
          * ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖rootFourier p h‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hWsum : ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖ ^ 2
        ≤ (p : ℝ) * M := by
      calc ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖ ^ 2
          ≤ ∑ h : ZMod p, ‖intervalWeight p M h‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun h _ _ => sq_nonneg _)
        _ = (p : ℝ) * M := interval_parseval p M hMp
    have hSsum : ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖rootFourier p h‖ ^ 2
        ≤ (p : ℝ) * 2 := by
      calc ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖rootFourier p h‖ ^ 2
          ≤ ∑ h : ZMod p, ‖rootFourier p h‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun h _ _ => sq_nonneg _)
        _ = (p : ℝ) * 2 := by rw [rootFourier_parseval, rootFourier_card_prime hp2]; norm_num
    have hnorm : ‖∑ h ∈ Finset.univ.erase (0 : ZMod p),
        intervalWeight p M h * rootFourier p h‖
        ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p),
            ‖intervalWeight p M h‖ * ‖rootFourier p h‖ := by
      calc ‖∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * rootFourier p h‖
          ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h * rootFourier p h‖ :=
            norm_sum_le _ _
        _ = ∑ h ∈ Finset.univ.erase (0 : ZMod p),
              ‖intervalWeight p M h‖ * ‖rootFourier p h‖ :=
            Finset.sum_congr rfl fun h _ => norm_mul _ _
    -- combine: X ≤ √(pM)·√(2p) = p·√(2M)
    have hXnn : (0 : ℝ) ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p),
        ‖intervalWeight p M h‖ * ‖rootFourier p h‖ :=
      Finset.sum_nonneg fun h _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hprod : (∑ h ∈ Finset.univ.erase (0 : ZMod p),
        ‖intervalWeight p M h‖ * ‖rootFourier p h‖) ^ 2
        ≤ ((p : ℝ) * M) * ((p : ℝ) * 2) := by
      calc (∑ h ∈ Finset.univ.erase (0 : ZMod p),
          ‖intervalWeight p M h‖ * ‖rootFourier p h‖) ^ 2
          ≤ (∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖ ^ 2)
            * ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖rootFourier p h‖ ^ 2 := hCS
        _ ≤ ((p : ℝ) * M) * ((p : ℝ) * 2) := by
            apply mul_le_mul hWsum hSsum
              (Finset.sum_nonneg fun h _ => sq_nonneg _)
              (by positivity)
    have hval : ((p : ℝ) * M) * ((p : ℝ) * 2) = ((p : ℝ) * Real.sqrt (2 * M)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (M:ℝ))]
      ring
    rw [hval] at hprod
    have hX : ∑ h ∈ Finset.univ.erase (0 : ZMod p),
        ‖intervalWeight p M h‖ * ‖rootFourier p h‖ ≤ (p : ℝ) * Real.sqrt (2 * M) := by
      have hYnn : (0 : ℝ) ≤ (p : ℝ) * Real.sqrt (2 * M) := by positivity
      have h3 := Real.sqrt_le_sqrt hprod
      rwa [Real.sqrt_sq hXnn, Real.sqrt_sq hYnn] at h3
    linarith [hnorm, hX]
  -- convert the complex identity into the real remainder bound
  have hre : ((p : ℝ) * ((((Finset.range M).filter
        (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ)) - 2 * M : ℝ)
      = ((p : ℝ) * (((Finset.range M).filter
          (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ) - 2 * M) := rfl
  have hcx : (((p : ℝ) * (((Finset.range M).filter
        (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ) - 2 * M : ℝ) : ℂ)
      = ∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * rootFourier p h := by
    push_cast
    linear_combination hid
  have habs : |(p : ℝ) * (((Finset.range M).filter
        (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ) - 2 * M|
      ≤ (p : ℝ) * Real.sqrt (2 * M) := by
    have h1 : |(p : ℝ) * (((Finset.range M).filter
          (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ) - 2 * M|
        = ‖(((p : ℝ) * (((Finset.range M).filter
            (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ) - 2 * M : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1, hcx]
    exact htail
  -- divide by p
  have hdiv : (((Finset.range M).filter (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ)
      - 2 * M / p
      = ((p : ℝ) * (((Finset.range M).filter
          (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ) - 2 * M) / p := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hppos, div_le_iff₀ hppos]
  calc |(p : ℝ) * (((Finset.range M).filter
        (fun (m : ℕ) => ((m : ZMod p)) ^ 2 = 1)).card : ℝ) - 2 * M|
      ≤ (p : ℝ) * Real.sqrt (2 * M) := habs
    _ = Real.sqrt (2 * M) * p := by ring

end TypeII
end Geometric
end EuclidsPath
