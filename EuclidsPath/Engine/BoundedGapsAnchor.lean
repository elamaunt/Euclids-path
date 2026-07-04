/-
  BoundedGapsAnchor — anchor of bounded gaps: Zhang 2013 / Maynard–Tao 2014.

  ┌─────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER. WHAT IS GREEN HERE AND WHAT IS HONESTLY RED.        │
  └─────────────────────────────────────────────────────────────────────────┘

  Yitang Zhang (2013) proved: there exists B < 70 000 000 such that infinitely
  many pairs of consecutive primes have gap ≤ B. Maynard and Tao (2014,
  independently; Polymath8b) lowered the bar to B = 246. This is the BEST
  unconditional result of humanity on the road to twins (B = 2). NOT ONE of
  these results is formalised: mathlib v4.31 has neither Zhang's theorem nor
  Maynard–Tao, nor even the Goldston–Pintz–Yıldırım method. The strongest thing
  mathlib actually gives about gaps is Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`): there is a prime in (n, 2n]. But that
  is a gap of order p ITSELF, not a constant B — from Bertrand to bounded gaps
  is a century of analytic number theory (BV-theorem, GPY/Maynard sieves).
  Therefore the entry here is a named RED def-anchor `BoundedGaps B`,
  NOT a theorem, NOT sorry, NOT an axiom.

  🔴 RED INPUTS (named, derived from nowhere):
   · `BoundedGaps B` — "infinitely many prime pairs with gap ≤ B";
   · `ZhangAnchor`      = BoundedGaps 70000000 (Zhang 2013);
   · `MaynardTaoAnchor` = BoundedGaps 246      (Maynard–Tao 2014, Polymath8b).

  🟢 GREEN BRIDGES (machine-proven, std axioms):
   · `boundedGaps_mono` — monotonicity in B: relaxing the bar is free;
   · `zhangAnchor_of_maynardTao` — 246 ⟹ 70 000 000 (instance of monotonicity);
   · `boundedGaps_two_iff_twins` — THE MAIN GOAL-RENAMING AUDIT
     (mirror of `offCriticalBridge_iff_RH`): the anchor at edge B = 2 IS
     EQUIVALENT TO infinitely many twins (`TwinLowers.Infinite` from Step00).
     Accepting `BoundedGaps 2` = accepting twins: this is a word-for-word
     renaming of the hypothesis, and we expose it machine-wise via an iff-theorem,
     not hide it;
   · `boundedGaps_two_iff_unbounded_twins` — the same equivalence in the
     standalone formulation "∀ N ∃ p > N: p and p+2 are prime";
   · `boundedGaps_four_twins_or_cousins`, `boundedGaps_six_polignac_trichotomy`
     — the PolignacBranch grid: for gap ≤ 4 at least one of the classes
     {twins, cousins} is infinite; for ≤ 6 — at least one of {twins, cousins, sexy}.
     This is the formal shadow of the REAL corollary of Maynard–Tao: from B = 246
     at least ONE gap class d ≤ 246 is infinite — but WHICH one is unknown;
     the disjunction is irreducible.

  ⚠️ THE MAIN HONESTY: the descent from B = 246 to B = 2 is OPEN mathematics.
  `MaynardTaoAnchor` does NOT entail twins: from "infinitely many gaps ≤ 246"
  no green means can derive "infinitely many gaps ≤ 2" —
  monotonicity works UPWARD in B, not downward. Marker:
  `NoDescentFrom246To2Claimed`. What mathematics MUST exhibit for the descent:
  a level of distribution of primes beyond Bombieri–Vinogradov (the
  Elliott–Halberstam conjecture gives B = 12, generalised EH — B = 6, Polymath8b),
  and below 6 sieves hit Selberg's parity problem — B = 2 does not fall even
  under GEH; an idea of a different kind is needed. Mathlib v4.31 has NONE of
  this: no Bombieri–Vinogradov, no Selberg sieve in the required strength, not
  a single proof_wanted about bounded gaps.

  THIS IS NOT A SOLUTION TO THE TWIN PRIME CONJECTURE AND NOT A GÖDELIAN ARGUMENT.
  The anchor is an honest docking point: if external mathematics supplies
  `BoundedGaps 2`, the green bridge immediately closes the Step00 goal.

  No sorry, no admit, no native_decide, no new axiom; the quarantine
  (CausalClosureAxiom) is NOT imported. The green load-bearing declarations are
  the standard triple propext / Classical.choice / Quot.sound.
  The repository taint count (taint 47) is NOT changed by this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BoundedGapsAnchor.lean
    → zero errors.

  Kinship: EuclidsPath/Engine/PolignacBranch.lean (6m±1 grid, cousins/sexy),
  EuclidsPath/Step00_Overview.lean (`TwinLowers`, `IsTwinPair`).
-/
import Mathlib
import EuclidsPath.Engine.PolignacBranch

set_option autoImplicit false

namespace EuclidsPath.BoundedGapsAnchor

open EuclidsPath EuclidsPath.PolignacBranch

/-! ### 🔴 Red inputs: named anchors, NOT theorems -/

/-- **🔴 RED INPUT — anchor of bounded gaps.** "Infinitely many prime pairs
    with gap ≤ B": above any `N` there exist primes `p < q ≤ p + B`.

    Known to humanity (outside mathlib): Zhang 2013 gives `B = 70 000 000`,
    Maynard–Tao 2014 (and Polymath8b) — `B = 246`. NEITHER of these values
    is formalised: mathlib v4.31 about gaps knows only Bertrand's postulate
    (`Nat.exists_prime_lt_and_le_two_mul`) — gap ≤ p, growing, NOT a constant.
    The twin prime conjecture is exactly `BoundedGaps 2` (see the audit
    `boundedGaps_two_iff_twins`). Here the predicate is only NAMED. -/
def BoundedGaps (B : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B

/-- **🔴 Zhang anchor (2013):** infinitely many gaps ≤ 70 000 000.
    Proved by humanity, NOT formalised; here — only a name. -/
def ZhangAnchor : Prop := BoundedGaps 70000000

/-- **🔴 Maynard–Tao anchor (2014, Polymath8b):** infinitely many gaps
    ≤ 246. The best unconditional result; NOT formalised; here — only a name.
    ⚠️ Does NOT entail twins: the descent 246 → 2 is open mathematics
    (see `NoDescentFrom246To2Claimed`). -/
def MaynardTaoAnchor : Prop := BoundedGaps 246

/-! ### 🟢 Green bridges -/

/-- **🟢 Monotonicity in the bar (proved):** relaxing B is free — the same
    witness pair passes under a higher bar. Works only UPWARD in B;
    there is no reverse direction (descent) and none is claimed. -/
theorem boundedGaps_mono {B B2 : ℕ} (h : B ≤ B2) (H : BoundedGaps B) :
    BoundedGaps B2 := by
  intro N
  obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H N
  exact ⟨p, q, hN, hp, hq, hlt, by omega⟩

/-- **🟢 246 ⟹ 70 000 000 (proved):** the Maynard–Tao anchor entails the Zhang
    anchor — an instance of monotonicity. Historically the arrow went the other
    way (Zhang first, then strengthening), logically — this way. -/
theorem zhangAnchor_of_maynardTao (H : MaynardTaoAnchor) : ZhangAnchor :=
  boundedGaps_mono (by norm_num) H

/-- **🟢 Plumbing (proved):** infiniteness of `TwinLowers` ⟺ unboundedness of
    the lesser members of twin pairs, "∀ N ∃ p > N: p and p+2 are prime".
    A cheap bridge between the repo form (Step00) and the standalone formulation. -/
theorem twinLowers_infinite_iff_unbounded :
    TwinLowers.Infinite ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime := by
  constructor
  · intro H N
    obtain ⟨p, hmem, hlt⟩ := H.exists_gt N
    have hpair : IsTwinPair p := hmem
    exact ⟨p, hlt, hpair.1, hpair.2⟩
  · intro H
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, hlt, hp, hp2⟩ := H C
    have hmem : p ∈ TwinLowers := show IsTwinPair p from ⟨hp, hp2⟩
    exact absurd (hC hmem) (not_le.mpr hlt)

/-- **🟢 THE MAIN GOAL-RENAMING AUDIT (proved; mirror of
    `offCriticalBridge_iff_RH`):** the anchor at edge `B = 2` IS EQUIVALENT TO
    infinitely many twins. Accepting `BoundedGaps 2` = accepting twins:
    a word-for-word renaming of the Step00 hypothesis, exposed machine-wise.

    Forward: above `max C 2` both primes are odd; from `p < q ≤ p + 2` the gap
    `q − p ∈ {1, 2}`, but `q = p + 1` is even and > 2 — not prime; what remains
    is `q = p + 2` — a twin pair. Backward: the twin pair itself is the
    witness for gap 2. -/
theorem boundedGaps_two_iff_twins : BoundedGaps 2 ↔ TwinLowers.Infinite := by
  constructor
  · intro H
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H (max C 2)
    have hp2 : 2 < p := lt_of_le_of_lt (le_max_right C 2) hN
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hq_eq : q = p + 2 := by
      rcases (by omega : q = p + 1 ∨ q = p + 2) with h | h
      · exfalso
        have hdvd : 2 ∣ q := by omega
        rcases hq.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega
      · exact h
    have hmem : p ∈ TwinLowers := show IsTwinPair p from ⟨hp, hq_eq ▸ hq⟩
    have hCp : C < p := lt_of_le_of_lt (le_max_left C 2) hN
    exact absurd (hC hmem) (not_le.mpr hCp)
  · intro H N
    obtain ⟨p, hlt, hp, hp2⟩ := twinLowers_infinite_iff_unbounded.mp H N
    exact ⟨p, p + 2, hlt, hp, hp2, by omega, le_refl _⟩

/-- **🟢 The same equivalence in the standalone formulation (proved):**
    `BoundedGaps 2` ⟺ "∀ N ∃ p > N: p and p+2 are prime" — without reference
    to the repo set, for external docking. -/
theorem boundedGaps_two_iff_unbounded_twins :
    BoundedGaps 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime :=
  boundedGaps_two_iff_twins.trans twinLowers_infinite_iff_unbounded

/-! ### 🟢 Polignac grid: disjunctive corollaries of small bars

  The formal shadow of the real corollary of Maynard–Tao: from `BoundedGaps 246`
  at least ONE gap class `d ≤ 246` is infinite, but WHICH one is unknown.
  Here the same for bars 4 and 6 via the PolignacBranch classes. The disjunction
  is irreducible: choosing a disjunct = solving an open problem. -/

/-- **🟢 Bar 4 ⟹ twins OR cousins (proved):** above 2 both primes are odd,
    gap ≤ 4 means `q = p + 2` or `q = p + 4`; the union `TwinLowers ∪ CousinLowers`
    is infinite, hence at least one class is infinite. Which one — the anchor
    does NOT reveal. -/
theorem boundedGaps_four_twins_or_cousins (H : BoundedGaps 4) :
    TwinLowers.Infinite ∨ CousinLowers.Infinite := by
  have hunion : (TwinLowers ∪ CousinLowers).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H (max C 2)
    have hp2 : 2 < p := lt_of_le_of_lt (le_max_right C 2) hN
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
    have hmem : p ∈ TwinLowers ∪ CousinLowers := by
      rcases (by omega : q = p + 2 ∨ q = p + 4) with h | h
      · exact Set.mem_union_left _ (show IsTwinPair p from ⟨hp, h ▸ hq⟩)
      · exact Set.mem_union_right _ ⟨hp, h ▸ hq⟩
    have hCp : C < p := lt_of_le_of_lt (le_max_left C 2) hN
    exact absurd (hC hmem) (not_le.mpr hCp)
  exact Set.infinite_union.mp hunion

/-- **🟢 Bar 6 ⟹ Polignac trichotomy (proved):** gap ≤ 6 between odd primes
    is 2, 4, or 6; at least one of the classes {twins, cousins, sexy} is infinite.
    A miniature of the Maynard–Tao corollary: for `B = 246` the same holds with
    123 even classes — and NOT ONE is chosen. -/
theorem boundedGaps_six_polignac_trichotomy (H : BoundedGaps 6) :
    TwinLowers.Infinite ∨ CousinLowers.Infinite ∨ SexyLowers.Infinite := by
  have hunion : (TwinLowers ∪ (CousinLowers ∪ SexyLowers)).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨C, hC⟩
    obtain ⟨p, q, hN, hp, hq, hlt, hle⟩ := H (max C 2)
    have hp2 : 2 < p := lt_of_le_of_lt (le_max_right C 2) hN
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
    have hmem : p ∈ TwinLowers ∪ (CousinLowers ∪ SexyLowers) := by
      rcases (by omega : q = p + 2 ∨ q = p + 4 ∨ q = p + 6) with h | h | h
      · exact Set.mem_union_left _ (show IsTwinPair p from ⟨hp, h ▸ hq⟩)
      · exact Set.mem_union_right _ (Set.mem_union_left _ ⟨hp, h ▸ hq⟩)
      · exact Set.mem_union_right _ (Set.mem_union_right _ ⟨hp, h ▸ hq⟩)
    have hCp : C < p := lt_of_le_of_lt (le_max_left C 2) hN
    exact absurd (hC hmem) (not_le.mpr hCp)
  rcases Set.infinite_union.mp hunion with h | h
  · exact Or.inl h
  · exact Or.inr (Set.infinite_union.mp h)

/-! ### Honesty -/

/-- **HONESTY (scope):** the descent from `B = 246` to `B = 2` is NOT claimed
    here and follows from nowhere: monotonicity `boundedGaps_mono` works only
    upward in the bar. `MaynardTaoAnchor` does NOT entail twins. What mathematics
    must exhibit for the descent: a level of distribution of primes beyond
    Bombieri–Vinogradov (Elliott–Halberstam gives B = 12, generalised EH —
    B = 6; below 6 sieves are blocked by Selberg's parity problem). None of this
    is in mathlib v4.31. -/
abbrev NoDescentFrom246To2Claimed : Prop := True

theorem noDescentFrom246To2Claimed : NoDescentFrom246To2Claimed := trivial

#print axioms boundedGaps_mono
#print axioms zhangAnchor_of_maynardTao
#print axioms twinLowers_infinite_iff_unbounded
#print axioms boundedGaps_two_iff_twins
#print axioms boundedGaps_two_iff_unbounded_twins
#print axioms boundedGaps_four_twins_or_cousins
#print axioms boundedGaps_six_polignac_trichotomy
#print axioms noDescentFrom246To2Claimed

end EuclidsPath.BoundedGapsAnchor
