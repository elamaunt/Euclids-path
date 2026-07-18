/-
  Engine/GeometricTypeIIMoebiusSegment — STAGE M5-B: the honest face-E
  COROLLARY of the Mertens cancellation.

  The M5-A cancellation `M(x) = o(x)` transfers to the coprime-to-6
  restricted Möbius sums by two FIXED-DEPTH unrolls (the 2-layer and the
  3-layer, each a finite telescope of scaled full sums — no analytic
  machinery), hence to the block cut sums `moebiusCut D N k` UNIFORMLY
  in `(N, k)` (each cut is a difference of at most two endpoint
  evaluations at scales `≤ 2D`), hence through the EXACT dual identity
  (`signed_block_dual`, criterion C) to the dyadic-block slice of face
  E's registered carrier:

      ∀ ε > 0, eventually in D:  ∀ M ≥ D,
        |blockRemainder M D + main term| ≤ 21·ε·M.

  DISCLOSURES (mandated, verbatim frame).
    * FACE E IS NOT CLOSED.  This is o(M) WITHOUT power saving, on the
      TRIVIAL-ROOT sector, and the EXPLICIT MAIN TERM
      `2M·Σ_{d ∈ block} μ(d)/d` REMAINS on the left: the corollary
      controls the dual fluctuation, not the face-E carrier itself.
      Face E's content — the μ-signed aggregation across incommensurable
      moduli in SHORT windows with power saving — is untouched; the
      registered disclosure of `GeometricTypeIIHyperbolaSigned` stands
      verbatim (mixed CRT roots remain ceded by name).
    * EVENTUAL in `D`, not effective.
    * No face touched, NOT a §110 event.  The twin sorry
      (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Engine.GeometricTypeIIHyperbolaSigned
import EuclidsPath.Analytic.MoebiusFromLiouville

set_option maxHeartbeats 3200000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open ArithmeticFunction Finset Filter
open scoped BigOperators

/-! ### The restricted Mertens sums -/

/-- The full Mertens sum `M(y)`. -/
noncomputable def mertensM (y : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 y, moebius n

/-- The odd-restricted Mertens sum. -/
noncomputable def mertensOdd (y : ℕ) : ℤ :=
  ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n)), moebius n

/-- The coprime-to-6 Mertens sum. -/
noncomputable def mertensC6 (y : ℕ) : ℤ :=
  ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n)), moebius n

/-! ### Trivial bounds -/

theorem abs_moebius_le_one_int (n : ℕ) : |moebius n| ≤ (1 : ℤ) := by
  by_cases hsf : Squarefree n
  · rw [moebius_apply_of_squarefree hsf]
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [moebius_eq_zero_of_not_squarefree hsf]
    norm_num

theorem abs_moebius_sum_le (s : Finset ℕ) :
    |∑ n ∈ s, moebius n| ≤ (s.card : ℤ) := by
  calc |∑ n ∈ s, moebius n| ≤ ∑ n ∈ s, |moebius n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ s, (1 : ℤ) :=
        Finset.sum_le_sum fun n _ => abs_moebius_le_one_int n
    _ = (s.card : ℤ) := by rw [Finset.sum_const]; simp

theorem abs_mertensM_le (y : ℕ) : |mertensM y| ≤ (y : ℤ) := by
  refine le_trans (abs_moebius_sum_le _) ?_
  have h1 : (Finset.Icc 1 y).card = y := by rw [Nat.card_Icc]; omega
  rw [h1]

theorem abs_mertensOdd_le (y : ℕ) : |mertensOdd y| ≤ (y : ℤ) := by
  refine le_trans (abs_moebius_sum_le _) ?_
  have h1 : ((Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n))).card ≤ y := by
    calc ((Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n))).card
        ≤ (Finset.Icc 1 y).card := Finset.card_filter_le _ _
      _ = y := by rw [Nat.card_Icc]; omega
  exact_mod_cast h1

theorem abs_mertensC6_le (y : ℕ) : |mertensC6 y| ≤ (y : ℤ) := by
  refine le_trans (abs_moebius_sum_le _) ?_
  have h1 : ((Finset.Icc 1 y).filter
      (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n))).card ≤ y := by
    calc ((Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n))).card
        ≤ (Finset.Icc 1 y).card := Finset.card_filter_le _ _
      _ = y := by rw [Nat.card_Icc]; omega
  exact_mod_cast h1

/-! ### The two vanishing/negation laws -/

theorem moebius_two_mul_even {e : ℕ} (he : 2 ∣ e) :
    moebius (2 * e) = 0 := by
  refine moebius_eq_zero_of_not_squarefree ?_
  intro hsf
  obtain ⟨f, rfl⟩ := he
  have h4 : 2 * 2 ∣ 2 * (2 * f) := ⟨f, by ring⟩
  have := hsf 2 h4
  rw [Nat.isUnit_iff] at this
  omega

theorem moebius_two_mul_odd {e : ℕ} (he : ¬(2 ∣ e)) :
    moebius (2 * e) = -moebius e := by
  have hco : Nat.Coprime 2 e :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr he
  rw [isMultiplicative_moebius.map_mul_of_coprime hco,
    moebius_apply_prime Nat.prime_two]
  ring

theorem moebius_three_mul_div {e : ℕ} (he : 3 ∣ e) :
    moebius (3 * e) = 0 := by
  refine moebius_eq_zero_of_not_squarefree ?_
  intro hsf
  obtain ⟨f, rfl⟩ := he
  have h9 : 3 * 3 ∣ 3 * (3 * f) := ⟨f, by ring⟩
  have := hsf 3 h9
  rw [Nat.isUnit_iff] at this
  omega

theorem moebius_three_mul_ndvd {e : ℕ} (he : ¬(3 ∣ e)) :
    moebius (3 * e) = -moebius e := by
  have hco : Nat.Coprime 3 e :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr he
  rw [isMultiplicative_moebius.map_mul_of_coprime hco,
    moebius_apply_prime Nat.prime_three]
  ring

/-! ### The recursion identities -/

/-- The 2-layer step: `M_odd(y) = M(y) + M_odd(y/2)`. -/
theorem mertensOdd_rec (y : ℕ) :
    mertensOdd y = mertensM y + mertensOdd (y / 2) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 y) (fun n => 2 ∣ n) (fun n => moebius n)
  have hreindex : ∑ n ∈ (Finset.Icc 1 y).filter (fun n => 2 ∣ n),
      moebius n = ∑ e ∈ Finset.Icc 1 (y / 2), moebius (2 * e) := by
    refine Finset.sum_nbij' (i := fun n => n / 2) (j := fun e => 2 * e)
      ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, hdvd⟩ := hn
      rw [Finset.mem_Icc]
      obtain ⟨e, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left e (by norm_num)]
      constructor
      · omega
      · rw [Nat.le_div_iff_mul_le (by norm_num)]
        omega
    · intro e he
      rw [Finset.mem_Icc] at he
      rw [Finset.mem_filter, Finset.mem_Icc]
      rw [Nat.le_div_iff_mul_le (by norm_num)] at he
      exact ⟨⟨by omega, by omega⟩, ⟨e, rfl⟩⟩
    · intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨e, rfl⟩ := hn.2
      rw [Nat.mul_div_cancel_left e (by norm_num)]
    · intro e _
      rw [Nat.mul_div_cancel_left e (by norm_num)]
    · intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨e, rfl⟩ := hn.2
      rw [Nat.mul_div_cancel_left e (by norm_num)]
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 (y / 2)) (fun e => 2 ∣ e) (fun e => moebius (2 * e))
  have hzero : ∑ e ∈ (Finset.Icc 1 (y / 2)).filter (fun e => 2 ∣ e),
      moebius (2 * e) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rw [Finset.mem_filter] at he
    exact moebius_two_mul_even he.2
  have hneg : ∑ e ∈ (Finset.Icc 1 (y / 2)).filter (fun e => ¬(2 ∣ e)),
      moebius (2 * e) = -mertensOdd (y / 2) := by
    unfold mertensOdd
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_filter] at he
    exact moebius_two_mul_odd he.2
  have h1 : ∑ n ∈ (Finset.Icc 1 y).filter (fun n => 2 ∣ n), moebius n
      = -mertensOdd (y / 2) := by
    rw [hreindex, ← hsplit2, hzero, hneg]
    ring
  have hOdd_def : mertensOdd y
      = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n)), moebius n := rfl
  have hM_def : mertensM y = ∑ n ∈ Finset.Icc 1 y, moebius n := rfl
  linarith [hsplit, h1, hOdd_def, hM_def]

/-- The 3-layer step: `C6(y) = M_odd(y) + C6(y/3)`. -/
theorem mertensC6_rec (y : ℕ) :
    mertensC6 y = mertensOdd y + mertensC6 (y / 3) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n))) (fun n => 3 ∣ n)
    (fun n => moebius n)
  have hff1 : ((Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n))).filter
      (fun n => ¬(3 ∣ n))
      = (Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n)) := by
    rw [Finset.filter_filter]
  have hreindex : ∑ n ∈ ((Finset.Icc 1 y).filter
      (fun n => ¬(2 ∣ n))).filter (fun n => 3 ∣ n), moebius n
      = ∑ e ∈ (Finset.Icc 1 (y / 3)).filter (fun e => ¬(2 ∣ e)),
          moebius (3 * e) := by
    refine Finset.sum_nbij' (i := fun n => n / 3) (j := fun e => 3 * e)
      ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨h1, h2⟩, hodd⟩, hdvd⟩ := hn
      rw [Finset.mem_filter, Finset.mem_Icc]
      obtain ⟨e, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left e (by norm_num)]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le (by norm_num)]
        omega
      · intro h2e
        exact hodd (Dvd.dvd.mul_left h2e 3)
    · intro e he
      rw [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨h1, h2⟩, hodd⟩ := he
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
      rw [Nat.le_div_iff_mul_le (by norm_num)] at h2
      refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ⟨e, rfl⟩⟩
      intro hdvd
      rcases (Nat.Coprime.dvd_of_dvd_mul_left
        (by norm_num : Nat.Coprime 2 3) hdvd) with h2e
      exact hodd h2e
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_filter] at hn
      obtain ⟨e, rfl⟩ := hn.2
      rw [Nat.mul_div_cancel_left e (by norm_num)]
    · intro e _
      rw [Nat.mul_div_cancel_left e (by norm_num)]
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_filter] at hn
      obtain ⟨e, rfl⟩ := hn.2
      rw [Nat.mul_div_cancel_left e (by norm_num)]
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 (y / 3)).filter (fun e => ¬(2 ∣ e))) (fun e => 3 ∣ e)
    (fun e => moebius (3 * e))
  have hzero : ∑ e ∈ ((Finset.Icc 1 (y / 3)).filter
      (fun e => ¬(2 ∣ e))).filter (fun e => 3 ∣ e), moebius (3 * e) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rw [Finset.mem_filter] at he
    exact moebius_three_mul_div he.2
  have hneg : ∑ e ∈ ((Finset.Icc 1 (y / 3)).filter
      (fun e => ¬(2 ∣ e))).filter (fun e => ¬(3 ∣ e)), moebius (3 * e)
      = -mertensC6 (y / 3) := by
    unfold mertensC6
    rw [← Finset.sum_neg_distrib]
    have hset : ((Finset.Icc 1 (y / 3)).filter
        (fun e => ¬(2 ∣ e))).filter (fun e => ¬(3 ∣ e))
        = (Finset.Icc 1 (y / 3)).filter
            (fun e => ¬(2 ∣ e) ∧ ¬(3 ∣ e)) := by
      rw [Finset.filter_filter]
    rw [hset]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_filter] at he
    exact moebius_three_mul_ndvd he.2.2
  have h1 : ∑ n ∈ ((Finset.Icc 1 y).filter
      (fun n => ¬(2 ∣ n))).filter (fun n => 3 ∣ n), moebius n
      = -mertensC6 (y / 3) := by
    rw [hreindex, ← hsplit2, hzero, hneg]
    ring
  have hC6_def : mertensC6 y
      = ∑ n ∈ (Finset.Icc 1 y).filter
          (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n)), moebius n := rfl
  have hOdd_def : mertensOdd y
      = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬(2 ∣ n)), moebius n := rfl
  rw [← hff1] at hC6_def
  linarith [hsplit, h1, hC6_def, hOdd_def]

/-! ### The fixed-depth unrolls -/

theorem mertensOdd_unroll (y J : ℕ) :
    mertensOdd y = (∑ j ∈ Finset.range J, mertensM (y / 2 ^ j))
      + mertensOdd (y / 2 ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [ih, Finset.sum_range_succ, mertensOdd_rec (y / 2 ^ J)]
    have hdd : y / 2 ^ J / 2 = y / 2 ^ (J + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [hdd]
    ring

theorem mertensC6_unroll (y J : ℕ) :
    mertensC6 y = (∑ j ∈ Finset.range J, mertensOdd (y / 3 ^ j))
      + mertensC6 (y / 3 ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [ih, Finset.sum_range_succ, mertensC6_rec (y / 3 ^ J)]
    have hdd : y / 3 ^ J / 3 = y / 3 ^ (J + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [hdd]
    ring

/-! ### The geometric caps and the eventual bound -/

theorem geom_sum_le_inv_one_sub {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, r ^ j ≤ 1 / (1 - r) := by
  rw [geom_sum_eq (by linarith) J]
  have hne : (0 : ℝ) < 1 - r := by linarith
  have heq : (r ^ J - 1) / (r - 1) = (1 - r ^ J) / (1 - r) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  rw [heq, div_le_div_iff₀ hne hne]
  have hrJ : (0 : ℝ) ≤ r ^ J := by positivity
  nlinarith

/-- All-scale linear cap for `M` from the M5-A cancellation:
`|M(u)| ≤ ε·u + K` for EVERY `u` (the threshold is absorbed into `K`). -/
theorem mertensM_linear_cap {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℕ, |(mertensM u : ℝ)| ≤ ε * u + K := by
  have hev := Metric.tendsto_nhds.mp
    EuclidsPath.Analytic.moebius_partialSum_tendsto ε hε
  obtain ⟨U, hU⟩ := eventually_atTop.mp hev
  refine ⟨max U 0 + 1, by positivity, fun u => ?_⟩
  have hcast : ((mertensM u : ℤ) : ℝ)
      = ∑ n ∈ Finset.Icc 1 u, (moebius n : ℝ) := by
    unfold mertensM
    push_cast
    rfl
  rcases le_or_gt ((u : ℝ)) (max U 0 + 1) with hle | hgt
  · have h1 := abs_mertensM_le u
    have h1R : |(mertensM u : ℝ)| ≤ (u : ℝ) := by exact_mod_cast h1
    have h2 : (0 : ℝ) ≤ ε * u := by positivity
    linarith
  · have huU : U ≤ (u : ℝ) := by
      have := le_max_left U 0
      linarith
    have hu0 : (0 : ℝ) < (u : ℝ) := by
      have := le_max_right U 0
      linarith
    have h := hU (u : ℝ) huU
    rw [Real.dist_eq, sub_zero, Nat.floor_natCast] at h
    rw [abs_div, abs_of_pos hu0, div_lt_iff₀ hu0] at h
    rw [hcast]
    have h2 : (0 : ℝ) ≤ max U 0 + 1 := by positivity
    calc |∑ n ∈ Finset.Icc 1 u, (moebius n : ℝ)| ≤ ε * u := le_of_lt h
      _ ≤ ε * u + (max U 0 + 1) := by linarith

/-- **The coprime-to-6 Mertens cancellation**: `C6(y) = o(y)` —
eventual linear bound at every slack. -/
theorem mertensC6_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, |(mertensC6 y : ℝ)| ≤ ε * y := by
  -- fixed depth J: 2^{-J} small
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ε / 24 from by positivity)
    (show (1 : ℝ) / 2 < 1 from by norm_num)
  obtain ⟨K, hK0, hM⟩ := mertensM_linear_cap
    (show (0 : ℝ) < ε / 9 from by positivity)
  -- the odd layer, all scales
  have hOdd : ∀ u : ℕ, |(mertensOdd u : ℝ)|
      ≤ (2 * (ε / 9) + (1 / 2) ^ J) * u + J * K := by
    intro u
    have hunroll := mertensOdd_unroll u J
    have hcast : (mertensOdd u : ℝ)
        = (∑ j ∈ Finset.range J, ((mertensM (u / 2 ^ j) : ℤ) : ℝ))
          + ((mertensOdd (u / 2 ^ J) : ℤ) : ℝ) := by
      rw [hunroll]
      push_cast
      ring
    rw [hcast]
    have hdivcast : ∀ j : ℕ, ((u / 2 ^ j : ℕ) : ℝ) ≤ (u : ℝ) * (1 / 2) ^ j := by
      intro j
      have h1 : ((u / 2 ^ j : ℕ) : ℝ) ≤ (u : ℝ) / ((2 ^ j : ℕ) : ℝ) :=
        Nat.cast_div_le
      have h2 : ((2 ^ j : ℕ) : ℝ) = 2 ^ j := by push_cast; rfl
      rw [h2] at h1
      calc ((u / 2 ^ j : ℕ) : ℝ) ≤ (u : ℝ) / 2 ^ j := h1
        _ = (u : ℝ) * (1 / 2) ^ j := by
            rw [div_pow, one_pow]
            ring
    have hterms : ∀ j ∈ Finset.range J,
        |((mertensM (u / 2 ^ j) : ℤ) : ℝ)|
          ≤ ε / 9 * ((u : ℝ) * (1 / 2) ^ j) + K := by
      intro j _
      calc |((mertensM (u / 2 ^ j) : ℤ) : ℝ)|
          ≤ ε / 9 * ((u / 2 ^ j : ℕ) : ℝ) + K := hM _
        _ ≤ ε / 9 * ((u : ℝ) * (1 / 2) ^ j) + K := by
            have := hdivcast j
            have h9 : (0 : ℝ) ≤ ε / 9 := by positivity
            nlinarith
    have htail : |((mertensOdd (u / 2 ^ J) : ℤ) : ℝ)|
        ≤ (u : ℝ) * (1 / 2) ^ J := by
      have h1 := abs_mertensOdd_le (u / 2 ^ J)
      have h1R : |((mertensOdd (u / 2 ^ J) : ℤ) : ℝ)|
          ≤ ((u / 2 ^ J : ℕ) : ℝ) := by
        have h2 : ((|mertensOdd (u / 2 ^ J)| : ℤ) : ℝ)
            ≤ (((u / 2 ^ J : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr h1
        rw [Int.cast_abs] at h2
        push_cast at h2 ⊢
        exact h2
      exact le_trans h1R (hdivcast J)
    calc |(∑ j ∈ Finset.range J, ((mertensM (u / 2 ^ j) : ℤ) : ℝ))
          + ((mertensOdd (u / 2 ^ J) : ℤ) : ℝ)|
        ≤ (∑ j ∈ Finset.range J, |((mertensM (u / 2 ^ j) : ℤ) : ℝ)|)
          + |((mertensOdd (u / 2 ^ J) : ℤ) : ℝ)| := by
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑ j ∈ Finset.range J,
            (ε / 9 * ((u : ℝ) * (1 / 2) ^ j) + K))
          + (u : ℝ) * (1 / 2) ^ J :=
          add_le_add (Finset.sum_le_sum hterms) htail
      _ = ε / 9 * (u : ℝ) * (∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j)
          + J * K + (u : ℝ) * (1 / 2) ^ J := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ ε / 9 * (u : ℝ) * 2 + J * K + (u : ℝ) * (1 / 2) ^ J := by
          have hg := geom_sum_le_inv_one_sub
            (show (0 : ℝ) ≤ 1 / 2 from by norm_num)
            (show (1 : ℝ) / 2 < 1 from by norm_num) J
          have h2 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
          rw [h2] at hg
          have h9u : (0 : ℝ) ≤ ε / 9 * (u : ℝ) := by positivity
          nlinarith
      _ = (2 * (ε / 9) + (1 / 2) ^ J) * u + J * K := by ring
  -- the coprime-6 layer, all scales
  have hC6 : ∀ y : ℕ, |(mertensC6 y : ℝ)|
      ≤ (3 * (ε / 9) + (3 / 2) * (1 / 2) ^ J + (1 / 3) ^ J) * y
        + (J + 1) * (J * K) := by
    intro y
    have hunroll := mertensC6_unroll y J
    have hcast : (mertensC6 y : ℝ)
        = (∑ j ∈ Finset.range J, ((mertensOdd (y / 3 ^ j) : ℤ) : ℝ))
          + ((mertensC6 (y / 3 ^ J) : ℤ) : ℝ) := by
      rw [hunroll]
      push_cast
      ring
    rw [hcast]
    have hdivcast : ∀ j : ℕ, ((y / 3 ^ j : ℕ) : ℝ) ≤ (y : ℝ) * (1 / 3) ^ j := by
      intro j
      have h1 : ((y / 3 ^ j : ℕ) : ℝ) ≤ (y : ℝ) / ((3 ^ j : ℕ) : ℝ) :=
        Nat.cast_div_le
      have h2 : ((3 ^ j : ℕ) : ℝ) = 3 ^ j := by push_cast; rfl
      rw [h2] at h1
      calc ((y / 3 ^ j : ℕ) : ℝ) ≤ (y : ℝ) / 3 ^ j := h1
        _ = (y : ℝ) * (1 / 3) ^ j := by
            rw [div_pow, one_pow]
            ring
    have hterms : ∀ j ∈ Finset.range J,
        |((mertensOdd (y / 3 ^ j) : ℤ) : ℝ)|
          ≤ (2 * (ε / 9) + (1 / 2) ^ J) * ((y : ℝ) * (1 / 3) ^ j)
            + J * K := by
      intro j _
      calc |((mertensOdd (y / 3 ^ j) : ℤ) : ℝ)|
          ≤ (2 * (ε / 9) + (1 / 2) ^ J) * ((y / 3 ^ j : ℕ) : ℝ)
            + J * K := hOdd _
        _ ≤ (2 * (ε / 9) + (1 / 2) ^ J) * ((y : ℝ) * (1 / 3) ^ j)
            + J * K := by
            have h1 := hdivcast j
            have h2 : (0 : ℝ) ≤ 2 * (ε / 9) + (1 / 2) ^ J := by positivity
            nlinarith
    have htail : |((mertensC6 (y / 3 ^ J) : ℤ) : ℝ)|
        ≤ (y : ℝ) * (1 / 3) ^ J := by
      have h1 := abs_mertensC6_le (y / 3 ^ J)
      have h1R : |((mertensC6 (y / 3 ^ J) : ℤ) : ℝ)|
          ≤ ((y / 3 ^ J : ℕ) : ℝ) := by
        have h2 : ((|mertensC6 (y / 3 ^ J)| : ℤ) : ℝ)
            ≤ (((y / 3 ^ J : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr h1
        rw [Int.cast_abs] at h2
        push_cast at h2 ⊢
        exact h2
      exact le_trans h1R (hdivcast J)
    calc |(∑ j ∈ Finset.range J, ((mertensOdd (y / 3 ^ j) : ℤ) : ℝ))
          + ((mertensC6 (y / 3 ^ J) : ℤ) : ℝ)|
        ≤ (∑ j ∈ Finset.range J, |((mertensOdd (y / 3 ^ j) : ℤ) : ℝ)|)
          + |((mertensC6 (y / 3 ^ J) : ℤ) : ℝ)| := by
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑ j ∈ Finset.range J,
            ((2 * (ε / 9) + (1 / 2) ^ J) * ((y : ℝ) * (1 / 3) ^ j)
              + J * K))
          + (y : ℝ) * (1 / 3) ^ J :=
          add_le_add (Finset.sum_le_sum hterms) htail
      _ = (2 * (ε / 9) + (1 / 2) ^ J) * (y : ℝ)
            * (∑ j ∈ Finset.range J, ((1 : ℝ) / 3) ^ j)
          + J * (J * K) + (y : ℝ) * (1 / 3) ^ J := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ (2 * (ε / 9) + (1 / 2) ^ J) * (y : ℝ) * (3 / 2)
          + J * (J * K) + (y : ℝ) * (1 / 3) ^ J := by
          have hg := geom_sum_le_inv_one_sub
            (show (0 : ℝ) ≤ 1 / 3 from by norm_num)
            (show (1 : ℝ) / 3 < 1 from by norm_num) J
          have h2 : (1 : ℝ) / (1 - 1 / 3) = 3 / 2 := by norm_num
          rw [h2] at hg
          have hcoef : (0 : ℝ) ≤ (2 * (ε / 9) + (1 / 2) ^ J) * (y : ℝ) := by
            positivity
          nlinarith
      _ ≤ (3 * (ε / 9) + (3 / 2) * (1 / 2) ^ J + (1 / 3) ^ J) * y
          + (J + 1) * (J * K) := by
          have hJK : (0 : ℝ) ≤ J * K := by positivity
          nlinarith [Nat.cast_nonneg (α := ℝ) y]
  -- assemble the eventual statement
  have hcoef : (3 : ℝ) * (ε / 9) + (3 / 2) * (1 / 2) ^ J + (1 / 3) ^ J
      ≤ ε / 3 + ε / 8 := by
    have h13 : ((1 : ℝ) / 3) ^ J ≤ ((1 : ℝ) / 2) ^ J :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) J
    have h3 : (3 : ℝ) * (ε / 9) = ε / 3 := by ring
    nlinarith [hJ]
  have hconst : ∀ᶠ y : ℕ in atTop,
      ((J : ℝ) + 1) * (J * K) ≤ ε / 2 * y := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ ((J : ℝ) + 1) * (J * K) from
      by positivity) with heq | hlt
    · filter_upwards [eventually_ge_atTop 0] with y _
      have : (0 : ℝ) ≤ ε / 2 * y := by positivity
      linarith [heq.symm]
    · have hquot : (0 : ℝ) < ε / 2 := by positivity
      obtain ⟨Y, hY⟩ := exists_nat_ge (((J : ℝ) + 1) * (J * K) / (ε / 2))
      filter_upwards [eventually_ge_atTop Y] with y hy
      have hyR : (((J : ℝ) + 1) * (J * K)) / (ε / 2) ≤ (y : ℝ) := by
        calc (((J : ℝ) + 1) * (J * K)) / (ε / 2) ≤ (Y : ℝ) := hY
          _ ≤ (y : ℝ) := by exact_mod_cast hy
      rw [div_le_iff₀ hquot] at hyR
      linarith [hyR]
  filter_upwards [hconst] with y hy
  calc |(mertensC6 y : ℝ)|
      ≤ (3 * (ε / 9) + (3 / 2) * (1 / 2) ^ J + (1 / 3) ^ J) * y
        + (J + 1) * (J * K) := hC6 y
    _ ≤ (ε / 3 + ε / 8) * y + ε / 2 * y := by
        have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ ≤ ε * y := by
        have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg _
        nlinarith

/-! ### The window transfer to the block cut sums -/

theorem coprime_six_iff (d : ℕ) :
    Nat.Coprime d 6 ↔ ¬(2 ∣ d) ∧ ¬(3 ∣ d) := by
  rw [show (6 : ℕ) = 2 * 3 from by norm_num, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨h2, h3⟩
    constructor
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (Nat.coprime_comm.mp h2)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Nat.coprime_comm.mp h3)
  · rintro ⟨h2, h3⟩
    constructor
    · exact Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
    · exact Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)

/-- The coprime-6 window sum as a difference of endpoint evaluations. -/
theorem mertensC6_window {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    ∑ n ∈ (Finset.Icc a b).filter (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n)), moebius n
      = mertensC6 b - mertensC6 (a - 1) := by
  have hunion : Finset.Icc 1 b
      = Finset.Icc 1 (a - 1) ∪ Finset.Icc a b := by
    ext n
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (a - 1)) (Finset.Icc a b) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    rw [Finset.mem_Icc] at hn hn'
    omega
  have hsum : mertensC6 b
      = mertensC6 (a - 1)
        + ∑ n ∈ (Finset.Icc a b).filter
            (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n)), moebius n := by
    unfold mertensC6
    rw [hunion, Finset.filter_union, Finset.sum_union
      (Finset.disjoint_filter_filter hdisj)]
  linarith [hsum]

/-- Every cut of the dyadic block is a two-endpoint window: uniformity
over `(N, k)` is free. -/
theorem moebiusCut_eq_window (D N k : ℕ) (hD : 1 ≤ D) :
    ∃ b : ℕ, D - 1 ≤ b ∧ b ≤ 2 * D - 1 ∧
      moebiusCut D N k = ((mertensC6 b - mertensC6 (D - 1) : ℤ) : ℝ) := by
  -- Step 1: identify the cut set with an interval (three regimes)
  have hcut : ∃ b : ℕ, D - 1 ≤ b ∧ b ≤ 2 * D - 1 ∧
      (blockConductors D).filter (fun d => k * d < N)
        = (Finset.Icc D b).filter
            (fun d => Squarefree d ∧ Nat.Coprime d 6) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨D - 1, le_refl _, by omega, ?_⟩
      rw [Finset.filter_false_of_mem (fun d _ => by omega),
        show Finset.Icc D (D - 1) = ∅ from Finset.Icc_eq_empty (by omega),
        Finset.filter_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨2 * D - 1, by omega, le_refl _, ?_⟩
      rw [Finset.filter_true_of_mem (fun d _ => by omega)]
      unfold blockConductors
      congr 1
      ext d
      rw [Finset.mem_Ico, Finset.mem_Icc]
      omega
    · refine ⟨max (D - 1) (min (2 * D - 1) ((N - 1) / k)), le_max_left _ _,
        by omega, ?_⟩
      unfold blockConductors
      rw [Finset.filter_filter]
      ext d
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ico,
        Finset.mem_Icc]
      have hchar : k * d < N ↔ d ≤ (N - 1) / k := by
        rw [Nat.le_div_iff_mul_le hk, Nat.mul_comm k d]
        omega
      constructor
      · rintro ⟨⟨h1, h2⟩, hsc, hlt⟩
        rw [hchar] at hlt
        exact ⟨⟨h1, by omega⟩, hsc⟩
      · rintro ⟨⟨h1, h2⟩, hsc⟩
        have hle : d ≤ (N - 1) / k := by omega
        rw [← hchar] at hle
        exact ⟨⟨h1, by omega⟩, hsc, hle⟩
  obtain ⟨b, hb1, hb2, hset⟩ := hcut
  refine ⟨b, hb1, hb2, ?_⟩
  unfold moebiusCut
  rw [hset]
  -- Step 2: drop the squarefree constraint (μ vanishes off it)
  have hdrop : ∑ d ∈ (Finset.Icc D b).filter
      (fun d => Squarefree d ∧ Nat.Coprime d 6),
        ((moebius d : ℤ) : ℝ)
      = ∑ d ∈ (Finset.Icc D b).filter
          (fun d => ¬(2 ∣ d) ∧ ¬(3 ∣ d)), ((moebius d : ℤ) : ℝ) := by
    have hstep1 : (Finset.Icc D b).filter
        (fun d => Squarefree d ∧ Nat.Coprime d 6)
        = ((Finset.Icc D b).filter
            (fun d => ¬(2 ∣ d) ∧ ¬(3 ∣ d))).filter Squarefree := by
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun d _ => ?_
      rw [coprime_six_iff]
      constructor
      · rintro ⟨hsf, hcop⟩
        exact ⟨hcop, hsf⟩
      · rintro ⟨hcop, hsf⟩
        exact ⟨hsf, hcop⟩
    rw [hstep1]
    refine Finset.sum_filter_of_ne fun d _ hne => ?_
    by_contra hsf
    rw [moebius_eq_zero_of_not_squarefree hsf] at hne
    simp at hne
  rw [hdrop]
  have hwin := mertensC6_window (a := D) (b := b) hD (by omega)
  have hcast : ∑ d ∈ (Finset.Icc D b).filter
      (fun d => ¬(2 ∣ d) ∧ ¬(3 ∣ d)), ((moebius d : ℤ) : ℝ)
      = ((∑ d ∈ (Finset.Icc D b).filter
          (fun d => ¬(2 ∣ d) ∧ ¬(3 ∣ d)), moebius d : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hcast, hwin]

/-- All-scale linear cap for `C6`. -/
theorem mertensC6_linear_cap {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℕ, |(mertensC6 y : ℝ)| ≤ ε * y + K := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (mertensC6_eventually hε)
  refine ⟨(Y : ℝ), Nat.cast_nonneg _, fun y => ?_⟩
  rcases le_or_gt Y y with hle | hgt
  · have h1 := hY y hle
    have h2 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg _
    linarith
  · have h1 := abs_mertensC6_le y
    have h1R : |(mertensC6 y : ℝ)| ≤ (y : ℝ) := by
      have h2 : ((|mertensC6 y| : ℤ) : ℝ) ≤ ((y : ℤ) : ℝ) :=
        Int.cast_le.mpr h1
      rw [Int.cast_abs] at h2
      push_cast at h2 ⊢
      exact h2
    have h2 : (y : ℝ) ≤ (Y : ℝ) := by exact_mod_cast le_of_lt hgt
    have h3 : (0 : ℝ) ≤ ε * y := by positivity
    linarith

/-- **THE UNIFORM CUT BOUND**: eventually in `D`, EVERY Möbius cut of
the dyadic block is `≤ 4εD` — uniformly in `(N, k)`. -/
theorem moebiusCut_uniform_bound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ N k : ℕ, |moebiusCut D N k| ≤ 4 * ε * D := by
  obtain ⟨K, hK0, hC6⟩ := mertensC6_linear_cap hε
  have hDbig : ∀ᶠ D : ℕ in atTop, 2 * K ≤ ε * D := by
    obtain ⟨Y, hY⟩ := exists_nat_ge (2 * K / ε)
    filter_upwards [eventually_ge_atTop Y] with D hD
    have h1 : 2 * K / ε ≤ (D : ℝ) := by
      calc 2 * K / ε ≤ (Y : ℝ) := hY
        _ ≤ (D : ℝ) := by exact_mod_cast hD
    rw [div_le_iff₀ hε] at h1
    linarith
  filter_upwards [eventually_ge_atTop 1, hDbig] with D hD1 hDK
  intro N k
  obtain ⟨b, hb1, hb2, heq⟩ := moebiusCut_eq_window D N k hD1
  rw [heq]
  have hbD : (b : ℝ) ≤ 2 * D := by
    have : b ≤ 2 * D := by omega
    exact_mod_cast this
  have hD1R : ((D - 1 : ℕ) : ℝ) ≤ (D : ℝ) := by
    have : D - 1 ≤ D := by omega
    exact_mod_cast this
  have hsplit : ((mertensC6 b - mertensC6 (D - 1) : ℤ) : ℝ)
      = (mertensC6 b : ℝ) - (mertensC6 (D - 1) : ℝ) := by
    push_cast
    ring
  rw [hsplit]
  calc |(mertensC6 b : ℝ) - (mertensC6 (D - 1) : ℝ)|
      ≤ |(mertensC6 b : ℝ)| + |(mertensC6 (D - 1) : ℝ)| :=
        abs_sub _ _
    _ ≤ (ε * b + K) + (ε * ((D - 1 : ℕ) : ℝ) + K) :=
        add_le_add (hC6 b) (hC6 (D - 1))
    _ ≤ ε * (2 * D) + ε * D + 2 * K := by nlinarith
    _ ≤ 4 * ε * D := by nlinarith

/-- **THE FACE-E COROLLARY (M5)** — the dyadic-block slice of the
registered carrier is `o(M)` up to its EXPLICIT main term: for every
`ε > 0`, eventually in `D`, for EVERY `M ≥ D`

    `|blockRemainder M D + 2M·Σ_{d ∈ block} μ(d)/d| ≤ 21·ε·M`.

DISCLOSURES (mandated): FACE E IS NOT CLOSED — no power saving, the
main term REMAINS on the left, the trivial-root sector only; the
μ-signed short-window aggregation across incommensurable moduli (face
E's registered content) is untouched; mixed CRT roots stay ceded.
NOT a §110 event.  twin sorry untouched. -/
theorem abs_blockRemainder_add_main_eventual {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ M : ℕ, D ≤ M →
      |blockRemainder M D
          + 2 * M * ∑ d ∈ blockConductors D,
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d|
        ≤ 21 * ε * M := by
  filter_upwards [moebiusCut_uniform_bound hε, eventually_ge_atTop 3]
    with D hcut hD3
  intro M hDM
  have hbound := abs_blockRemainder_le_of_cut_bound hD3 M
    (B := 4 * ε * D) (fun N k => hcut N k)
  refine le_trans hbound ?_
  have hdim := dual_dimension_le (by omega : 1 ≤ D) M
  have hdimR : (((M + D - 1) / D + (M + 2 + D - 1) / D : ℕ) : ℝ)
      ≤ ((2 * (M / D) + 3 : ℕ) : ℝ) := by exact_mod_cast hdim
  have hB0 : (0 : ℝ) ≤ 4 * ε * D := by positivity
  have hMD : ((M / D : ℕ) : ℝ) * D ≤ (M : ℝ) := by
    have h1 : (M / D) * D ≤ M := Nat.div_mul_le_self M D
    exact_mod_cast h1
  have hDM_R : (D : ℝ) ≤ (M : ℝ) := by exact_mod_cast hDM
  calc (((M + D - 1) / D + (M + 2 + D - 1) / D : ℕ) : ℝ) * (4 * ε * D)
      ≤ ((2 * (M / D) + 3 : ℕ) : ℝ) * (4 * ε * D) :=
        mul_le_mul_of_nonneg_right hdimR hB0
    _ = 8 * ε * (((M / D : ℕ) : ℝ) * D) + 12 * ε * D := by
        push_cast
        ring
    _ ≤ 8 * ε * M + 12 * ε * M := by
        have h1 : 8 * ε * (((M / D : ℕ) : ℝ) * D) ≤ 8 * ε * M := by
          have h8 : (0 : ℝ) ≤ 8 * ε := by positivity
          nlinarith
        have h2 : 12 * ε * (D : ℝ) ≤ 12 * ε * M := by
          have h12 : (0 : ℝ) ≤ 12 * ε := by positivity
          nlinarith
        linarith
    _ ≤ 21 * ε * M := by
        have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
        nlinarith

end TypeII
end Geometric
end EuclidsPath
