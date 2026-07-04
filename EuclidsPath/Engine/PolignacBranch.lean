/-
  PolignacBranch — Polignac in the grid: cousins (p, p+4) and sexy primes (p, p+6).

  The 6m±1 grid encodes small even gaps between primes > 3:
    * gap 2 (twins)   — ONE center m: pair (6m−1, 6m+1);
    * gap 4 (cousins) — ADJACENT centers, DIFFERENT sides:
      pair (6m+1, 6m+5), where 6m+5 = 6(m+1)−1 — the minus-side of center m+1;
    * gap 6 (sexy)    — ADJACENT centers, SAME side:
      (6m−1, 6(m+1)−1 = 6m+5) on the minus-side, or
      (6m+1, 6(m+1)+1 = 6m+7) on the plus-side.

  Polignac's conjecture (in particular for gaps 4 and 6) is OPEN. The Hardy–Littlewood
  heuristic predicts infinitely many pairs in each class — a sign IN FAVOUR,
  but NOT a proof.

  ⚠️ MAIN HONESTY: no implication twins ⇄ cousins/sexy is asserted here
  in either direction (marker
  NoTwinsToPolignacImplicationClaimed). Open problems are not resolved.

  WHAT IS PROVED (standard axioms, no sorry):
    * cousin_upper_eq_minusSide — embedding into the program's language: the upper cousin —
      is the minus-side of the NEXT center, 6m+5 = 6(m+1)−1;
    * cousin_mod_six — classification: the lower member of a cousin pair p > 3 always
      lies on the PLUS-side (p % 6 = 1);
    * cousin_instances, sexy_instances — concrete pairs: cousins (7,11),
      (13,17), (19,23); sexy (5,11), (11,17), (7,13);
    * cousinLowersInfinite_of_unbounded, sexyLowersInfinite_of_unbounded —
      conditional bridges "unboundedness of centers ⟹ infinitely many pairs"
      (same form as `twinLowersInfinite_of_mersenneTwins` in MersenneBranch);
    * constellation_of_adjacent_twinCenters — two ADJACENT twin-centers simultaneously yield
      cousins and both kinds of sexy pairs (m = 1: constellation 5, 7, 11, 13).
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.PolignacBranch

open EuclidsPath

/-! ## Cousins: gap 4 — adjacent centers, different sides -/

/-- Cousin-center: `m` defines the cousin pair `(6m+1, 6m+5)` — the plus-side of center
    `m` and the minus-side of center `m+1` (see `cousin_upper_eq_minusSide`). -/
def IsCousinCenter (m : ℕ) : Prop := (6 * m + 1).Prime ∧ (6 * m + 5).Prime

/-- The set of lower members of cousin pairs `(p, p+4)`. -/
def CousinLowers : Set ℕ := { p | p.Prime ∧ (p + 4).Prime }

/-- **EMBEDDING INTO THE PROGRAM'S LANGUAGE (proved):** the upper cousin `6m+5` is the
    MINUS-side of the next center: `6m+5 = 6(m+1) − 1`. A cousin pair is
    a cross-pair of adjacent centers. -/
theorem cousin_upper_eq_minusSide (m : ℕ) : 6 * m + 5 = 6 * (m + 1) - 1 := by
  omega

/-- **CLASSIFICATION (proved):** the lower member of a cousin pair `p > 3` always
    lies on the PLUS-side of the grid: `p % 6 = 1`. Otherwise (when `p % 6 = 5`)
    the number `p + 4` would be divisible by 3. -/
theorem cousin_mod_six {p : ℕ} (hp : p.Prime) (hp4 : (p + 4).Prime)
    (h3 : 3 < p) : p % 6 = 1 := by
  have h2 : ¬ (2 ∣ p) := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 2 h with h' | h' <;> omega
  have h3' : ¬ (3 ∣ p) := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 h with h' | h' <;> omega
  have hcases : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases hcases with h | h
  · exact h
  · exfalso
    have hdvd : 3 ∣ p + 4 := ⟨(p + 4) / 3, by omega⟩
    have heq : 3 = p + 4 :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp4).mp hdvd
    omega

/-- Concrete cousin-centers: `m = 1` gives `(7, 11)`, `m = 2` — `(13, 17)`,
    `m = 3` — `(19, 23)`. -/
theorem cousin_instances :
    IsCousinCenter 1 ∧ IsCousinCenter 2 ∧ IsCousinCenter 3 := by
  unfold IsCousinCenter
  norm_num

/-- Unboundedness of cousin-centers (named input: the gap-4 case of Polignac's
    conjecture; OPEN, not derived from anything here). -/
def CousinCentersUnbounded : Prop := ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsCousinCenter m

/-- **CONDITIONAL BRIDGE (proved):** unboundedness of cousin-centers ⟹
    infinitely many cousin pairs. Pure grid repackaging, no new number theory;
    same form as `twinLowersInfinite_of_mersenneTwins`. -/
theorem cousinLowersInfinite_of_unbounded (H : CousinCentersUnbounded) :
    CousinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨m, hgt, h1, h2⟩ := H B
  have hmem : (6 * m + 1) ∈ CousinLowers := by
    show (6 * m + 1).Prime ∧ (6 * m + 1 + 4).Prime
    refine ⟨h1, ?_⟩
    have hstep : 6 * m + 1 + 4 = 6 * m + 5 := by omega
    rw [hstep]
    exact h2
  have hBlt : B < 6 * m + 1 := by omega
  exact absurd (hB hmem) (not_le.mpr hBlt)

/-! ## Sexy primes: gap 6 — adjacent centers, same side -/

/-- Sexy pair on the MINUS-side: `(6m−1, 6m+5)` — the minus-sides of centers
    `m` and `m+1`. -/
def IsSexyMinusPair (m : ℕ) : Prop := (6 * m - 1).Prime ∧ (6 * m + 5).Prime

/-- Sexy pair on the PLUS-side: `(6m+1, 6m+7)` — the plus-sides of centers
    `m` and `m+1`. -/
def IsSexyPlusPair (m : ℕ) : Prop := (6 * m + 1).Prime ∧ (6 * m + 7).Prime

/-- Sexy-center: `m` carries a sexy pair on at least one side. -/
def IsSexyCenter (m : ℕ) : Prop := IsSexyMinusPair m ∨ IsSexyPlusPair m

/-- The set of lower members of sexy pairs `(p, p+6)`. -/
def SexyLowers : Set ℕ := { p | p.Prime ∧ (p + 6).Prime }

/-- **SIDE PRESERVATION (proved):** a shift by 6 does not change the residue modulo 6 —
    a sexy pair always lies on the SAME side of the grid. -/
theorem sexy_preserves_side {p : ℕ} (_hp : p.Prime) (_h3 : 3 < p) :
    (p + 6) % 6 = p % 6 := by
  omega

/-- Concrete sexy pairs: minus-side `m = 1` gives `(5, 11)`, `m = 2` —
    `(11, 17)`; plus-side `m = 1` gives `(7, 13)`. -/
theorem sexy_instances :
    IsSexyMinusPair 1 ∧ IsSexyMinusPair 2 ∧ IsSexyPlusPair 1 := by
  unfold IsSexyMinusPair IsSexyPlusPair
  norm_num

/-- Unboundedness of sexy-centers (named input: the gap-6 case of Polignac's
    conjecture; OPEN, not derived from anything here). -/
def SexyCentersUnbounded : Prop := ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsSexyCenter m

/-- **CONDITIONAL BRIDGE (proved):** unboundedness of sexy-centers ⟹
    infinitely many sexy pairs. For the minus-side, primality of `6m − 1`
    yields `1 ≤ m` (otherwise in ℕ we would have `6·0 − 1 = 0` — not prime),
    which guards all rewrites involving truncated subtraction. -/
theorem sexyLowersInfinite_of_unbounded (H : SexyCentersUnbounded) :
    SexyLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨m, hgt, hcen⟩ := H B
  rcases hcen with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- minus-side: lower member 6m − 1
    have hm1 : 1 ≤ m := by
      have := h1.two_le
      omega
    have hmem : (6 * m - 1) ∈ SexyLowers := by
      show (6 * m - 1).Prime ∧ (6 * m - 1 + 6).Prime
      refine ⟨h1, ?_⟩
      have hstep : 6 * m - 1 + 6 = 6 * m + 5 := by omega
      rw [hstep]
      exact h2
    have hBlt : B < 6 * m - 1 := by omega
    exact absurd (hB hmem) (not_le.mpr hBlt)
  · -- plus-side: lower member 6m + 1
    have hmem : (6 * m + 1) ∈ SexyLowers := by
      show (6 * m + 1).Prime ∧ (6 * m + 1 + 6).Prime
      refine ⟨h1, ?_⟩
      have hstep : 6 * m + 1 + 6 = 6 * m + 7 := by omega
      rw [hstep]
      exact h2
    have hBlt : B < 6 * m + 1 := by omega
    exact absurd (hB hmem) (not_le.mpr hBlt)

/-- Plumbing: unboundedness of the minus-side is sufficient. -/
theorem sexyUnbounded_of_minus
    (H : ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsSexyMinusPair m) : SexyCentersUnbounded := by
  intro N
  obtain ⟨m, hlt, hpair⟩ := H N
  exact ⟨m, hlt, Or.inl hpair⟩

/-- Plumbing: unboundedness of the plus-side is sufficient. -/
theorem sexyUnbounded_of_plus
    (H : ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsSexyPlusPair m) : SexyCentersUnbounded := by
  intro N
  obtain ⟨m, hlt, hpair⟩ := H N
  exact ⟨m, hlt, Or.inr hpair⟩

/-! ## Constellation: two adjacent twin-centers -/

/-- **CONSTELLATION (proved):** two ADJACENT twin-centers `m` and `m+1` yield
    everything at once: cousins at `m` and both sexy pairs at `m`. For `m = 1` this is the
    constellation `5, 7, 11, 13` — cousins `(7, 11)`, sexy `(5, 11)` and `(7, 13)`. -/
theorem constellation_of_adjacent_twinCenters {m : ℕ}
    (h1 : IsTwinCenter m) (h2 : IsTwinCenter (m + 1)) :
    IsCousinCenter m ∧ IsSexyMinusPair m ∧ IsSexyPlusPair m := by
  obtain ⟨hm_lo, hm_hi⟩ := h1
  obtain ⟨hm1_lo, hm1_hi⟩ := h2
  have e1 : 6 * (m + 1) - 1 = 6 * m + 5 := by omega
  have e2 : 6 * (m + 1) + 1 = 6 * m + 7 := by omega
  rw [e1] at hm1_lo
  rw [e2] at hm1_hi
  exact ⟨⟨hm_hi, hm1_lo⟩, ⟨hm_lo, hm1_lo⟩, ⟨hm_hi, hm1_hi⟩⟩

/-! ## Honesty -/

/-- **HONESTY (coverage):** no implication `twins ⇄ cousins/sexy`
    is asserted here in either direction. Polignac's conjecture for
    gaps 4 and 6 and the twin prime conjecture are INDEPENDENT open problems;
    the bridges proved above are conditional (named input: unboundedness of centers) and
    do not resolve any open problems. -/
abbrev NoTwinsToPolignacImplicationClaimed : Prop := True

theorem noTwinsToPolignacImplicationClaimed :
    NoTwinsToPolignacImplicationClaimed := trivial

#print axioms cousin_mod_six
#print axioms cousinLowersInfinite_of_unbounded
#print axioms sexyLowersInfinite_of_unbounded
#print axioms constellation_of_adjacent_twinCenters

end EuclidsPath.PolignacBranch
