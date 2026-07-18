/-
  GeometricTypeIIHyperbola — SPEC 1, UNSIGNED LAYER: the sawtooth form of the
  trivial-root window defect, and the HYPERBOLA SWITCH that converts a
  dyadic-block divisor sum into a short dual sum.

  ORIGIN.  Wall-assault campaign, top-ranked build (SPEC 1 of the synthesis):
  face E (`LowFreqRootCoherence`) lives on the μ-signed aggregation of
  CRT-root window defects across conductors.  On the TRIVIAL-ROOT sector
  (the classes C = ±1 — the FULL root set at prime conductors), the defect
  of one conductor is an exact SAWTOOTH in `⌈M/d⌉` and `⌊(M+1)/d⌋`; and a
  dyadic block of such divisor terms equals, by the classical hyperbola
  double count, an EXACT dual sum with ~M/D terms.  For `D > √M` the dual
  is SHORTER than the block: the dimension of the block slice drops from
  `D` (conductors) to `⌈(M+D−1)/D⌉`-scale (cutpoints).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `count_res_one` / `count_res_neg_one` — exact progression counts on
      `[1, M]`: the class `1 (mod d)` has `(M+d−1)/d = ⌈M/d⌉` members, the
      class `−1 (mod d)` has `(M+1)/d` members (explicit bijections);
    * `trivialRootShift` + `trivialRootShift_eq_sawtooth` — the C = ±1
      sector of the machine root shift is the exact sawtooth
      `(M+d−1)/d + (M+1)/d − 2M/d`;
    * `trivialRootShift_eq_zero_of_dvd` — full periods have zero defect
      (the block object is pure short-window content);
    * `natRoots_prime` + `rootShift_eq_trivial_of_prime` — **THE
      PRIME-SLICE PIN**: at prime conductors `p ≥ 5` the trivial-root
      sector IS the full machine referent (`rootShift = trivialRootShift`);
      mixed roots exist only at composite conductors and are ceded by name
      to faces C/D;
    * `filter_mul_lt_eq_range` — the switch atom: `{k < K : kd < N}` is the
      initial segment `range ((N+d−1)/d)`;
    * `hyperbola_switch` — **THE SWITCH**: for any weights `w` on a block
      `S` with `D ≤ d` for `d ∈ S`,
      `Σ_{d∈S} w(d)·((N+d−1)/d) = Σ_{k<(N+D−1)/D} Σ_{d∈S, kd<N} w(d)` —
      EXACT, the Dirichlet hyperbola double count with the unbounded
      variable eliminated.

  NUMERIC GROUNDING (pre-pass, this session, exact rationals): count
  formulas and sawtooth exhaustive on d ≤ 40, M ≤ 200 — 0 violations;
  switch identity exhaustive on N ≤ 300, seven block sizes, random signed
  weights — 0 violations; dual-dimension profile at M = 10⁶:
  block ~1995/15848/125892 conductors vs dual ~1004/128/16 terms at
  D = M^{0.55}/M^{0.7}/M^{0.85}.

  DISCLOSURES.
    * Identities, not estimates: nothing here bounds a signed sum.  The
      signed consequences (the μ-weighted block reduction and its honest
      open core) live in the sibling `GeometricTypeIIHyperbolaSigned`.
    * For `D ≤ √M` the dual side is LONGER than the block; no reduction is
      claimed there.
    * The parity wall's faces are untouched; this is the exact-transport
      layer of a criterion-C filing made in the signed module.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIMachineEnergy

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### Layer 0: the ceiling-division atom -/

/-- The switch atom: `t < ⌈N/d⌉` iff the `t`-th lattice row is below the
hyperbola. -/
theorem lt_ceil_div_iff {d t N : ℕ} (hd : 1 ≤ d) :
    t < (N + d - 1) / d ↔ t * d < N := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (show 0 < d by omega),
    add_one_mul]
  omega

/-- The floor atom for the `−1` class: `t < ⌊(M+1)/d⌋` iff
`d·t + (d−1) ≤ M`. -/
theorem lt_floor_succ_iff {d t M : ℕ} (hd : 1 ≤ d) :
    t < (M + 1) / d ↔ t * d + d ≤ M + 1 := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (show 0 < d by omega),
    add_one_mul]

/-! ### Layer 1: exact progression counts on `[1, M]` -/

/-- The class `1 (mod d)` on `[1, M]` has exactly `(M + d − 1)/d = ⌈M/d⌉`
members. -/
theorem count_res_one {d : ℕ} (hd : 2 ≤ d) (M : ℕ) :
    ((Finset.Icc 1 M).filter fun m => m % d = 1).card = (M + d - 1) / d := by
  rw [← Finset.card_range ((M + d - 1) / d)]
  refine Finset.card_nbij' (fun m => m / d) (fun t => d * t + 1) ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨_, hmM⟩, hmr⟩ := hm
    have hsplit := Nat.div_add_mod m d
    rw [hmr] at hsplit
    have hcomm : d * (m / d) = (m / d) * d := Nat.mul_comm d (m / d)
    rw [Finset.mem_coe, Finset.mem_range]
    show m / d < (M + d - 1) / d
    rw [lt_ceil_div_iff (show 1 ≤ d by omega)]
    omega
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_range,
      lt_ceil_div_iff (show 1 ≤ d by omega)] at ht
    have hcomm : d * t = t * d := Nat.mul_comm d t
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    show (1 ≤ d * t + 1 ∧ d * t + 1 ≤ M) ∧ (d * t + 1) % d = 1
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, hmr⟩ := hm
    have hsplit := Nat.div_add_mod m d
    rw [hmr] at hsplit
    show d * (m / d) + 1 = m
    exact hsplit
  · intro t _
    show (d * t + 1) / d = t
    rw [Nat.mul_add_div (show 0 < d by omega),
      Nat.div_eq_of_lt (show 1 < d by omega), add_zero]

/-- The class `−1 (mod d)` on `[1, M]` has exactly `(M + 1)/d` members. -/
theorem count_res_neg_one {d : ℕ} (hd : 2 ≤ d) (M : ℕ) :
    ((Finset.Icc 1 M).filter fun m => m % d = d - 1).card = (M + 1) / d := by
  rw [← Finset.card_range ((M + 1) / d)]
  refine Finset.card_nbij' (fun m => m / d) (fun t => d * t + (d - 1))
    ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨_, hmM⟩, hmr⟩ := hm
    have hsplit := Nat.div_add_mod m d
    rw [hmr] at hsplit
    have hcomm : d * (m / d) = (m / d) * d := Nat.mul_comm d (m / d)
    rw [Finset.mem_coe, Finset.mem_range]
    show m / d < (M + 1) / d
    rw [lt_floor_succ_iff (show 1 ≤ d by omega)]
    omega
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_range,
      lt_floor_succ_iff (show 1 ≤ d by omega)] at ht
    have hcomm : d * t = t * d := Nat.mul_comm d t
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    show (1 ≤ d * t + (d - 1) ∧ d * t + (d - 1) ≤ M)
      ∧ (d * t + (d - 1)) % d = d - 1
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, hmr⟩ := hm
    have hsplit := Nat.div_add_mod m d
    rw [hmr] at hsplit
    show d * (m / d) + (d - 1) = m
    exact hsplit
  · intro t _
    show (d * t + (d - 1)) / d = t
    rw [Nat.mul_add_div (show 0 < d by omega),
      Nat.div_eq_of_lt (show d - 1 < d by omega), add_zero]

/-! ### Layer 2: the trivial-root sector and its sawtooth -/

/-- The trivial-root (C = ±1) sector of the machine root shift. -/
noncomputable def trivialRootShift (M d : ℕ) : ℝ :=
  rootClassDefect M d 1 + rootClassDefect M d (d - 1)

/-- **THE SAWTOOTH**: the trivial-root defect of one conductor is the exact
elementary expression `⌈M/d⌉ + ⌊(M+1)/d⌋ − 2M/d`. -/
theorem trivialRootShift_eq_sawtooth {d : ℕ} (hd : 2 ≤ d) (M : ℕ) :
    trivialRootShift M d
      = (((M + d - 1) / d : ℕ) : ℝ) + (((M + 1) / d : ℕ) : ℝ)
        - 2 * M / d := by
  unfold trivialRootShift rootClassDefect
  rw [count_res_one hd, count_res_neg_one hd]
  ring

/-- Full periods carry zero trivial-root defect: the block object is pure
short-window content. -/
theorem trivialRootShift_eq_zero_of_dvd {d M : ℕ} (hd : 2 ≤ d)
    (hdvd : d ∣ M) : trivialRootShift M d = 0 := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [trivialRootShift_eq_sawtooth hd]
  have h1 : (d * c + d - 1) / d = c := by
    have : d * c + d - 1 = d * c + (d - 1) := by omega
    rw [this, Nat.mul_add_div (by omega : 0 < d),
      Nat.div_eq_of_lt (by omega : d - 1 < d), add_zero]
  have h2 : (d * c + 1) / d = c := by
    rw [Nat.mul_add_div (by omega : 0 < d),
      Nat.div_eq_of_lt (by omega : 1 < d), add_zero]
  rw [h1, h2]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ### Layer 3: the prime-slice pin -/

/-- At a prime conductor `p ≥ 5` the square roots of unity are exactly
`{1, p−1}`. -/
theorem natRoots_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    natRoots p = {1, p - 1} := by
  have : NeZero p := ⟨by omega⟩
  ext v
  rw [mem_natRoots, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hvp, hsq⟩
    -- transport to ZMod p and factor x² − 1
    have : Fact p.Prime := ⟨hp⟩
    have hcast : ((v * v : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hsq
    push_cast at hcast
    have hfact : ((v : ZMod p)) = 1 ∨ ((v : ZMod p)) = -1 :=
      mul_self_eq_one_iff.mp hcast
    rcases hfact with h | h
    · left
      have h1 : ((1 : ℕ) : ZMod p) = ((v : ℕ) : ZMod p) := by
        rw [h]; push_cast; ring
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hvp] at this
      omega
    · right
      have hm1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
        push_cast [Nat.cast_sub (show 1 ≤ p by omega)]
        rw [ZMod.natCast_self]
        ring
      have h1 : ((p - 1 : ℕ) : ZMod p) = ((v : ℕ) : ZMod p) := by
        rw [hm1, h]
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hvp] at this
      omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, rfl⟩
    · refine ⟨by omega, ?_⟩
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
      have hexp : (q + 2 - 1) * (q + 2 - 1) = (q + 2) * q + 1 := by
        have h1 : q + 2 - 1 = q + 1 := by omega
        rw [h1]
        ring
      rw [hexp, Nat.mul_add_mod]

/-- **THE PRIME-SLICE PIN**: at prime conductors `p ≥ 5` the trivial-root
sector IS the full machine referent. -/
theorem rootShift_eq_trivial_of_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (M : ℕ) : rootShift M p = trivialRootShift M p := by
  unfold rootShift
  rw [natRoots_prime hp hp5]
  rw [Finset.sum_insert (by
    rw [Finset.mem_singleton]
    omega), Finset.sum_singleton]
  rfl

/-! ### Layer 4: the hyperbola switch -/

/-- The lattice rows below the hyperbola form an initial segment. -/
theorem filter_mul_lt_eq_range {d N K : ℕ} (hd : 1 ≤ d)
    (hK : (N + d - 1) / d ≤ K) :
    (Finset.range K).filter (fun k => k * d < N)
      = Finset.range ((N + d - 1) / d) := by
  ext k
  rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨_, hkd⟩
    exact (lt_ceil_div_iff hd).mpr hkd
  · intro hk
    exact ⟨by omega, (lt_ceil_div_iff hd).mp hk⟩

/-- Ceiling division is antitone in the divisor (block-uniform cutoff). -/
theorem ceil_div_le_of_le {d D N : ℕ} (hD : 1 ≤ D) (hDd : D ≤ d) :
    (N + d - 1) / d ≤ (N + D - 1) / D := by
  by_contra hcon
  push Not at hcon
  set k := (N + D - 1) / D with hk
  have hk_lt : k < (N + d - 1) / d := hcon
  have hkd : k * d < N := (lt_ceil_div_iff (by omega)).mp hk_lt
  have hkD : k * D ≤ k * d := Nat.mul_le_mul_left k hDd
  have : k < (N + D - 1) / D := (lt_ceil_div_iff hD).mpr (by omega)
  omega

/-- **THE HYPERBOLA SWITCH**: a block divisor sum equals the exact short
dual sum — the Dirichlet double count of `{(k,d) : kd < N}` with the
unbounded variable eliminated. -/
theorem hyperbola_switch {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ d ∈ S, D ≤ d) (N : ℕ) (w : ℕ → ℝ) :
    ∑ d ∈ S, w d * (((N + d - 1) / d : ℕ) : ℝ)
      = ∑ k ∈ Finset.range ((N + D - 1) / D),
          ∑ d ∈ S.filter (fun d => k * d < N), w d := by
  set K := (N + D - 1) / D with hK
  have hterm : ∀ d ∈ S,
      w d * (((N + d - 1) / d : ℕ) : ℝ)
        = ∑ k ∈ Finset.range K, (if k * d < N then w d else 0) := by
    intro d hd
    have hd1 : 1 ≤ d := le_trans hD (hS d hd)
    rw [← Finset.sum_filter,
      filter_mul_lt_eq_range hd1 (ceil_div_le_of_le hD (hS d hd)),
      Finset.sum_const, nsmul_eq_mul, mul_comm, Finset.card_range]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_filter]

end TypeII
end Geometric
end EuclidsPath
