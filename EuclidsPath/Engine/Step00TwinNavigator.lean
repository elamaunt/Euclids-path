import EuclidsPath.Engine.Step00WitnessChainKernel
import EuclidsPath.Engine.Step00PhaseCoverKernel
import EuclidsPath.Engine.GenealogyBasins
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Twin navigator — the path/defect dichotomy and certified navigation below proven ceilings

This pass formalises the user directive of the ordered-exponent assault: "we do not need
to FIND the path to the next twin — we need to prove that a path EXISTS; and if it does
not exist, there must be a DEFECT."  The formal object is the **window verdict**
(`windowVerdict`): for every window `(k, k+g]` below the sieve ceiling
(`6(k+g)+1 < A²`), EITHER the window contains a twin center, OR every offset of the
window is struck by a clock `≤ A` — the latter is `CoverDefect`, a certified,
per-instance kernel-checkable object that is EXACTLY the SAT side of the phase-cover
solver of `Step00PhaseCoverKernel` (`coverDefect_iff_phaseCover`, `coverDefect_demo_37`).

Contents, in dependency order:

* **Drainage disclosure** (`drainage_downhill`): the genealogical drainage of
  `GenealogyBasins` is strictly downhill, so the NEXT twin is never reachable through
  the repacking drainage — graph search toward the next twin is a dead channel by
  construction; navigation lives on the center line.  This motivates the scan-based
  navigator below.
* **The dichotomy** (`windowVerdict`, `verdict_exclusive`, `no_long_defect_5` …
  `no_long_defect_37`): path-or-defect, exclusivity of the horns above the scale, the
  honest overlap example at the boundary, and the ten kernel scales at which long
  defects are REFUTED on all of ℕ.
* **The navigator** (`nextTwinAux` / `nextTwin`): a clock-list-parameterised bounded
  scan with full partial correctness (`nextTwin_clean`, `nextTwin_twin`), the scan-
  completeness lemma `cleanListB_complete` (the converse of the repo's
  `clean_of_cleanListB` soundness), and conditional totality
  (`nextTwin_isSome_of_cleanGapBound`).  Clock lists are always passed explicitly and
  never computed from `A` — mathlib primality instances are kernel-opaque.
* **The enumerator** (`twinSeq`): the `Nat.find` least-witness iterate of the green
  escalation `twinCenters_unbounded_of_twinJacobsthalCofinal`; strictly monotone, starts
  at the first twin center (`twinSeq_zero : twinSeq H 0 = 1`, the pair `(5,7)`), and —
  the crown — provably enumerates ALL twin centers in order (`twinSeq_surj`), conditional
  only on the named wall `TwinJacobsthalBoundCofinal`.  (A `ScaleOracle`-style computable
  variant that recomputes clock lists per scale would be a possible second layer; it is
  not built here.)
* **The packaging disclosure** (`navigator_iff_unbounded_twins`): navigator totality is
  EQUIVALENT to twin infinitude (`TwinLowers.Infinite`) — the navigator is a REPACKAGING
  of the goal, not progress toward it.

## Anti-vocabulary

Navigation / scanning / sorting vocabulary in this module carries NO new arithmetic
content: `nextTwin` is a bounded linear scan, `twinSeq` is `Nat.find` bookkeeping, and
the packaging iff shows navigator totality IS twin infinitude.  The only fuel above the
ten certified scales is the named wall (`TwinJacobsthalBound` / its cofinal weakening);
below the proven ceilings everything is unconditional and kernel-backed.
`twin_prime_conjecture` stays untouched.
-/

namespace EuclidsPath
namespace TwinNavigator

open EuclidsPath.Residuals
open EuclidsPath.CleanGraph
open EuclidsPath.TwinJacobsthalWall
open EuclidsPath.Genealogy
open EuclidsPath.WitnessChainKernel (cleanListB clean_of_cleanListB)
open EuclidsPath.PhaseCoverKernel (CoverClock coveredB dvd_wing_minus dvd_wing_plus
  allStruckB)

/-! ### Section 1 — the drainage is downhill: the next twin is unreachable through it -/

/-- A peel step is strictly downhill with NO height side condition: for `m ≥ 2` this is
    `Genealogy.peelStep_lt`; for `m ≤ 1` the step equation `6m − ε = p(6t + δ)` is
    impossible outright (`p ≥ 5` and `6t + δ ≥ 5` force the right side `≥ 25`, the left
    side is `≤ 7`). -/
theorem peelStep_lt_unconditional {m t : ℕ} (h : PeelStep m t) : t < m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exfalso
    obtain ⟨ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩ := h
    have hp5' : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
    have hwing : (5 : ℤ) ≤ 6 * (t : ℤ) + δ := by
      rcases hδ with rfl | rfl <;> omega
    have h25 : (5 : ℤ) * 5 ≤ (p : ℤ) * (6 * (t : ℤ) + δ) :=
      mul_le_mul hp5' hwing (by norm_num) (Int.natCast_nonneg p)
    rw [← heq] at h25
    rcases hε with rfl | rfl <;> omega
  · exact peelStep_lt hm h

/-- Everything peel-reachable from `m` sits at or below `m`: the drainage only descends. -/
theorem peelReach_le {m n : ℕ} (h : Relation.ReflTransGen PeelStep m n) : n ≤ m := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans (Nat.le_of_lt (peelStep_lt_unconditional hbc)) ih

/--
  **DISCLOSURE (honesty theorem): the genealogy drainage cannot navigate to the next
  twin.**  Every `PeelStep` strictly decreases the center
  (`peelStep_lt_unconditional`), so every node peel-reachable from `m` is `≤ m`
  (`peelReach_le`) — a twin center strictly above `m` is UNREACHABLE from `m`'s drainage
  by construction.  (The twin hypothesis is carried only to state the claim in the form
  the search channel would need; the obstruction is purely order-theoretic and holds for
  every target above `m`.)

  This closes the "graph search toward the next twin" channel: the repacking drainage of
  `GenealogyBasins` (`canonicalPeel` / `grave`, and the deflection idiom
  `twinFree_descent_exit`) only ever certifies twins BELOW the start.  Navigation toward
  the NEXT twin lives on the center line `m, m+1, m+2, …` — which is exactly the
  scan-based navigator of Section 3.
-/
theorem drainage_downhill {m w : ℕ} (hmw : m < w) (hw : TwinCenterZ w) :
    ¬ Relation.ReflTransGen PeelStep m w :=
  fun h => absurd (peelReach_le h) (by omega)

/-! ### Section 2 — the window verdict: a path exists XOR a defect exists

The user's dichotomy, made formal.  `CoverDefect A k g` says the whole window `(k, k+g]`
is struck — every offset is killed by some clock `≤ A`.  Below the sieve ceiling the
verdict is total (`windowVerdict`), above the scale it is exclusive
(`verdict_exclusive`), and at the ten kernel scales long defects are refuted on all of ℕ
(`no_long_defect_*`). -/

/-- Every offset in the window `(k, k+g]` is struck by some clock `≤ A`: no clean center
    anywhere in the window.  This is the formal DEFECT object of the dichotomy — and it
    is exactly the SAT-side pattern of `Step00PhaseCoverKernel`
    (`coverDefect_iff_phaseCover`, `coverDefect_of_allStruck`). -/
def CoverDefect (A k g : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ g → ¬ Clean A (k + j)

/--
  **THE WINDOW VERDICT (green, unconditional): below the ceiling, a path exists or a
  defect exists.**  For any window `(k, k+g]` with `6(k+g)+1 < A²`, EITHER the window
  contains a twin center, OR `CoverDefect A k g` holds.  Classical case split on whether
  some offset is clean; a clean offset below the ceiling is a twin by `sink_is_twin`
  (mirroring `twin_gap_below_wall`).

  We do not need to FIND the path — we prove one exists, or we hold a defect.  Both horns
  are finitely checkable per instance.  (Adaptation note: `sink_is_twin` needs neither
  `1 ≤ k` nor primality of `A` — the offset `j ≥ 1` already puts the wings at `≥ 5`, and
  the ceiling hypothesis carries the entire sieve-horizon content — so this statement
  drops both side conditions the pass sketch carried.)
-/
theorem windowVerdict {A k g : ℕ} (hceil : 6 * (k + g) + 1 < A * A) :
    (∃ m, k < m ∧ m ≤ k + g ∧ TwinCenterZ m) ∨ CoverDefect A k g := by
  by_cases hex : ∃ j, 1 ≤ j ∧ j ≤ g ∧ Clean A (k + j)
  · obtain ⟨j, hj1, hjg, hclean⟩ := hex
    exact Or.inl ⟨k + j, by omega, by omega,
      sink_is_twin (by omega) (by omega) (by omega) (by omega) hclean⟩
  · right
    intro j hj1 hjg hclean
    exact hex ⟨j, hj1, hjg, hclean⟩

/--
  **Exclusivity above the scale: the two horns cannot both hold.**  If every wing in the
  window exceeds `A` (`A < 6(k+1) − 1`, the smallest wing of the window), then a twin
  center in the window is automatically `Clean A` — a prime wing `> A` has no prime
  divisor `≤ A` — contradicting `CoverDefect` at its offset.

  The guard is NECESSARY: below the scale the horns can overlap — see
  `verdict_overlap_at_boundary` right below.
-/
theorem verdict_exclusive {A k g : ℕ} (hA : A < 6 * (k + 1) - 1)
    (htw : ∃ m, k < m ∧ m ≤ k + g ∧ TwinCenterZ m) :
    ¬ CoverDefect A k g := by
  rintro hdef
  obtain ⟨m, hkm, hmg, hm⟩ := htw
  have hclean : Clean A m := by
    intro q hq hqA hor
    have hq2 := hq.two_le
    rcases hor with hd | hd
    · rcases hm.1.eq_one_or_self_of_dvd q hd with h1 | hself <;> omega
    · rcases hm.2.eq_one_or_self_of_dvd q hd with h1 | hself <;> omega
  have hstruck := hdef (m - k) (by omega) (by omega)
  rw [show k + (m - k) = m from by omega] at hstruck
  exact hstruck hclean

/-- The boundary overlap, kernel-checked: `m = 1` is a twin center (wings `5, 7`) AND it
    is struck at scale `A = 7` (both wings are themselves clocks `≤ 7`). -/
example : TwinCenterZ 1 ∧ ¬ Clean 7 1 := by decide

/--
  **The honest overlap example at the boundary.**  For the window `(0, 1]` at scale
  `A = 7` BOTH horns of the verdict hold: `m = 1` is a twin center in the window, and
  the window is simultaneously a full `CoverDefect` (the wing `5` of `m = 1` is struck
  by the clock `5 ≤ 7`).  The exclusivity guard fails here — `7 < 6·(0+1) − 1 = 5` is
  false — which is exactly why `verdict_exclusive` carries it: below the scale, a twin's
  own wings can be clocks, so "struck" does not preclude "twin".
-/
theorem verdict_overlap_at_boundary : TwinCenterZ 1 ∧ CoverDefect 7 0 1 := by
  refine ⟨GenealogyBasins.twinCenterZ_one, ?_⟩
  intro j hj1 hjle hclean
  have hj : j = 1 := by omega
  subst hj
  exact hclean 5 (by norm_num) (by norm_num) (Or.inl (by norm_num))

/-- A clean-gap bound refutes every defect of the same length: the clean center that
    `CleanGapBound A G` plants in `(k, k+G]` is an unstruck offset. -/
theorem no_long_defect_of_cleanGapBound {A G : ℕ} (h : CleanGapBound A G) (k : ℕ) :
    ¬ CoverDefect A k G := by
  intro hdef
  obtain ⟨m, h1, h2, h3⟩ := h k
  have hstruck := hdef (m - k) (by omega) (by omega)
  rw [show k + (m - k) = m from by omega] at hstruck
  exact hstruck h3

/-! #### No long defects at the ten kernel scales

Each instance consumes an existing machine-proved gap bound: `A ∈ {5, 7, 11, 13}` from
the one-period certificates of `Step00TwinJacobsthalWall`, `A ∈ {17, …, 37}` from the
phase-cover UNSAT gates of `Step00PhaseCoverKernel`.  Reading: at scale `A`, NO window
of length `G(A)` anywhere in ℕ is a full defect — defects at these scales are provably
SHORTER than the certified gap. -/

/-- No defect of length 2 at scale 5 (`G(5) = 2`, kernel-exact). -/
theorem no_long_defect_5 : ∀ k, ¬ CoverDefect 5 k 2 :=
  no_long_defect_of_cleanGapBound cleanGapBound_5

/-- No defect of length 5 at scale 7 (`G(7) = 5`, kernel-exact). -/
theorem no_long_defect_7 : ∀ k, ¬ CoverDefect 7 k 5 :=
  no_long_defect_of_cleanGapBound cleanGapBound_7

/-- No defect of length 7 at scale 11 (`G(11) = 7`, kernel-exact). -/
theorem no_long_defect_11 : ∀ k, ¬ CoverDefect 11 k 7 :=
  no_long_defect_of_cleanGapBound cleanGapBound_11

/-- No defect of length 11 at scale 13 (`G(13) = 11`, kernel-exact). -/
theorem no_long_defect_13 : ∀ k, ¬ CoverDefect 13 k 11 :=
  no_long_defect_of_cleanGapBound cleanGapBound_13

/-- No defect of length 18 at scale 17 (`G(17) = 18`, phase-cover kernel gate). -/
theorem no_long_defect_17 : ∀ k, ¬ CoverDefect 17 k 18 :=
  no_long_defect_of_cleanGapBound PhaseCoverKernel.cleanGapBound_17

/-- No defect of length 25 at scale 19 (`G(19) = 25`, phase-cover kernel gate). -/
theorem no_long_defect_19 : ∀ k, ¬ CoverDefect 19 k 25 :=
  no_long_defect_of_cleanGapBound PhaseCoverKernel.cleanGapBound_19

/-- No defect of length 34 at scale 23 (`G(23) = 34`, phase-cover kernel gate). -/
theorem no_long_defect_23 : ∀ k, ¬ CoverDefect 23 k 34 :=
  no_long_defect_of_cleanGapBound PhaseCoverKernel.cleanGapBound_23

/-- No defect of length 43 at scale 29 (`G(29) = 43`, phase-cover kernel gate). -/
theorem no_long_defect_29 : ∀ k, ¬ CoverDefect 29 k 43 :=
  no_long_defect_of_cleanGapBound PhaseCoverKernel.cleanGapBound_29

/-- No defect of length 58 at scale 31 (`G(31) = 58`, phase-cover kernel gate). -/
theorem no_long_defect_31 : ∀ k, ¬ CoverDefect 31 k 58 :=
  no_long_defect_of_cleanGapBound PhaseCoverKernel.cleanGapBound_31

/-- No defect of length 88 at scale 37 (`G(37) = 88`, phase-cover kernel gate). -/
theorem no_long_defect_37 : ∀ k, ¬ CoverDefect 37 k 88 :=
  no_long_defect_of_cleanGapBound PhaseCoverKernel.cleanGapBound_37

/-! #### The defect IS the phase cover

`CoverDefect` is exactly the covering pattern of `Step00PhaseCoverKernel`: an offset `j`
is struck by clock `q` iff `q` covers `j` at the phase `(−k) mod q` induced by the window
start.  The transport lemmas below replicate the (private) `phase_cancel`/`offset_phase`
arithmetic of that module and add the converse direction, giving the clean iff
`coverDefect_iff_phaseCover` against the self-contained covering Prop `PhaseCoverAll`.
Instantiating `C` with the kernel clock tables (`smallClocks ++ bigs37`, etc.) makes the
match with the kernel's `coveredB`-based machinery DEFINITIONAL — same `coveredB`, same
phase convention `t_q = (−k) mod q` as `cleanGapBound_of_unsatCover`. -/

/-- Every offset of the window `(k, k+g]` is covered by some listed clock at the phase
    induced by the window start `k` — the self-contained phase-cover Prop. -/
def PhaseCoverAll (C : List CoverClock) (k g : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ g →
    ∃ p ∈ C, coveredB p.1 p.2 ((p.1 - k % p.1) % p.1) j = true

/-- `(−k) mod q` cancels `k` mod `q` (replica of the kernel-private `phase_cancel`). -/
private theorem phase_cancel' {q : ℕ} (k : ℕ) (hq : 0 < q) :
    ((q - k % q) % q + k) ≡ 0 [MOD q] := by
  have hmlt : k % q < q := Nat.mod_lt _ hq
  calc (q - k % q) % q + k
      ≡ (q - k % q) + k [MOD q] := Nat.ModEq.add_right k (Nat.mod_modEq _ _)
    _ ≡ (q - k % q) + k % q [MOD q] := Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
    _ = q := Nat.sub_add_cancel hmlt.le
    _ ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl

/-- Center congruence to offset phase (replica of the kernel-private `offset_phase`):
    `k + o ≡ a (mod q)` transports to `o ≡ t_k + a (mod q)`, `t_k = (−k) mod q`. -/
private theorem offset_phase' {q k o a : ℕ} (hq : 0 < q)
    (h : (k + o) % q = a % q) : o % q = ((q - k % q) % q + a) % q := by
  have hc : ((q - k % q) % q + k) ≡ 0 [MOD q] := phase_cancel' k hq
  have h2 : (q - k % q) % q + a + k ≡ a [MOD q] := by
    calc (q - k % q) % q + a + k
        = a + ((q - k % q) % q + k) := by ring
      _ ≡ a + 0 [MOD q] := Nat.ModEq.add_left a hc
      _ = a := by ring
  have h3 : o + k ≡ (q - k % q) % q + a + k [MOD q] := by
    have ho : o + k ≡ a [MOD q] := by
      show (o + k) % q = a % q
      rw [Nat.add_comm o k]
      exact h
    exact ho.trans h2.symm
  exact Nat.ModEq.add_right_cancel' k h3

/-- Offset phase back to center congruence (the converse transport). -/
private theorem covered_phase {q k o a : ℕ} (hq : 0 < q)
    (h : o % q = ((q - k % q) % q + a) % q) : (k + o) % q = a % q := by
  have hc : ((q - k % q) % q + k) ≡ 0 [MOD q] := phase_cancel' k hq
  calc (k + o)
      ≡ k + ((q - k % q) % q + a) [MOD q] := Nat.ModEq.add_left k h
    _ = ((q - k % q) % q + k) + a := by ring
    _ ≡ 0 + a [MOD q] := Nat.ModEq.add_right a hc
    _ = a := by ring

/-- Residue `i6` on the center forces a strike on the minus wing (converse of
    `dvd_wing_minus`). -/
private theorem wing_minus_of_residue {q i6 m : ℕ} (hinv : 6 * i6 % q = 1)
    (hq1 : 1 < q) (hm : 1 ≤ m) (hr : m % q = i6 % q) : q ∣ 6 * m - 1 := by
  have e1 : 6 * m ≡ 6 * i6 [MOD q] := Nat.ModEq.mul_left 6 hr
  have e2 : 6 * i6 ≡ 1 [MOD q] := by
    show 6 * i6 % q = 1 % q
    rw [hinv, Nat.mod_eq_of_lt hq1]
  have e3 : (1 : ℕ) ≡ 6 * m [MOD q] := (e1.trans e2).symm
  exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ 6 * m)).mp e3

/-- Residue `q − i6` on the center forces a strike on the plus wing (converse of
    `dvd_wing_plus`; the divisibility `q ∣ 6(q − i6) + 1` replays the arithmetic inside
    `dvd_wing_plus`). -/
private theorem wing_plus_of_residue {q i6 m : ℕ} (hi : i6 < q)
    (hinv : 6 * i6 % q = 1) (hr : m % q = (q - i6) % q) : q ∣ 6 * m + 1 := by
  have hdm := Nat.div_add_mod (6 * i6) q
  rw [hinv] at hdm
  have hd2 : q ∣ 6 * (q - i6) + 1 := by
    have he2 : 6 * (q - i6) + 1 = 6 * q - q * (6 * i6 / q) := by omega
    rw [he2]
    exact Nat.dvd_sub (Dvd.intro 6 (by ring)) (Dvd.intro _ rfl)
  have e1 : 6 * m + 1 ≡ 6 * (q - i6) + 1 [MOD q] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 6 hr)
  have e2 : 6 * (q - i6) + 1 ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hd2
  exact Nat.modEq_zero_iff_dvd.mp (e1.trans e2)

/-- A cover of offset `j` at the induced phase strikes a wing of the center `k + j`. -/
private theorem struck_of_covered {q i6 k j : ℕ} (h5 : 5 ≤ q) (hi : i6 < q)
    (hinv : 6 * i6 % q = 1) (hkj : 1 ≤ k + j)
    (hcb : coveredB q i6 ((q - k % q) % q) j = true) :
    q ∣ 6 * (k + j) - 1 ∨ q ∣ 6 * (k + j) + 1 := by
  have hq0 : 0 < q := by omega
  simp only [coveredB, Bool.or_eq_true, beq_iff_eq] at hcb
  rcases hcb with hcb | hcb
  · exact Or.inl (wing_minus_of_residue hinv (by omega) hkj (covered_phase hq0 hcb))
  · exact Or.inr (wing_plus_of_residue hi hinv (covered_phase hq0 hcb))

/--
  **The defect IS the phase cover.**  Over a clock table `C` carrying every prime of
  `[5, A]` with its `6⁻¹` witness (the exact side conditions of
  `cleanGapBound_of_unsatCover`), the window defect `CoverDefect A k g` holds iff every
  offset of `(k, k+g]` is covered at the phase tuple induced by the window start
  (`PhaseCoverAll C k g`).  Forward: an unclean offset yields a striking prime — the
  clocks `2, 3` never strike wings (`omega`), and a striking clock `≥ 5` covers the
  offset through `dvd_wing_minus` / `dvd_wing_plus` plus the phase transport.  Backward:
  a cover of the offset strikes a wing (`struck_of_covered`), refuting cleanliness.

  So the two certificate families of `Step00PhaseCoverKernel` speak EXACTLY about
  `CoverDefect`: the UNSAT gates (`Uncoverable`, through `cleanGapBound_*` and
  `no_long_defect_*`) refute all long defects, and the SAT runs (`allStruckB`, through
  `coverDefect_of_allStruck`) certify concrete maximal ones.
-/
theorem coverDefect_iff_phaseCover {A k g : ℕ} {C : List CoverClock}
    (hsc : ∀ p ∈ C, p.1.Prime ∧ 5 ≤ p.1 ∧ p.1 ≤ A ∧ p.2 < p.1 ∧ 6 * p.2 % p.1 = 1)
    (hcov : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → q ∈ C.map Prod.fst) :
    CoverDefect A k g ↔ PhaseCoverAll C k g := by
  constructor
  · intro hdef j hj1 hjg
    have hnc := hdef j hj1 hjg
    have hex : ∃ q : ℕ, q.Prime ∧ q ≤ A ∧
        (q ∣ (6 * (k + j) - 1) ∨ q ∣ (6 * (k + j) + 1)) := by
      by_contra hno
      apply hnc
      intro q hq hqA hor
      exact hno ⟨q, hq, hqA, hor⟩
    obtain ⟨q, hq, hqA, hor⟩ := hex
    rcases Nat.lt_or_ge q 5 with h5 | h5
    · exfalso
      have h2 := hq.two_le
      interval_cases q
      · rcases hor with hd | hd <;> omega
      · rcases hor with hd | hd <;> omega
      · exact absurd hq (by norm_num)
    · obtain ⟨p, hpmem, hpq⟩ := List.mem_map.mp (hcov q hq h5 hqA)
      obtain ⟨hqp, h5p, hAp, hip, hinvp⟩ := hsc p hpmem
      rw [hpq] at hqp h5p hAp hip hinvp
      refine ⟨p, hpmem, ?_⟩
      rw [hpq]
      simp only [coveredB, Bool.or_eq_true, beq_iff_eq]
      rcases hor with hd | hd
      · exact Or.inl (offset_phase' (by omega)
          (dvd_wing_minus hqp h5p hinvp (by omega) hd))
      · exact Or.inr (offset_phase' (by omega)
          (dvd_wing_plus hqp h5p hip hinvp hd))
  · intro hps j hj1 hjg hclean
    obtain ⟨p, hpmem, hcb⟩ := hps j hj1 hjg
    obtain ⟨hqp, h5p, hAp, hip, hinvp⟩ := hsc p hpmem
    exact hclean p.1 hqp hAp (struck_of_covered h5p hip hinvp (by omega) hcb)

/-- A kernel-verified struck run is a certified defect: the SAT-side bridge (the
    `CoverDefect` mirror of `not_cleanGapBound_of_struck`). -/
theorem coverDefect_of_allStruck {A r len : ℕ} {C : List CoverClock}
    (hsc : ∀ p ∈ C, p.1.Prime ∧ p.1 ≤ A)
    (h : allStruckB C r len = true) : CoverDefect A r len := by
  intro j hj1 hjlen hclean
  have hall := List.all_eq_true.mp h (j - 1) (List.mem_range.mpr (by omega))
  have hall' :
      (C.any fun p =>
        ((6 * (r + 1 + (j - 1)) - 1) % p.1 == 0) ||
          ((6 * (r + 1 + (j - 1)) + 1) % p.1 == 0)) = true := hall
  rw [show r + 1 + (j - 1) = r + j from by omega] at hall'
  obtain ⟨p, hp, hstrike⟩ := List.any_eq_true.mp hall'
  obtain ⟨hpr, hpA⟩ := hsc p hp
  rw [Bool.or_eq_true] at hstrike
  rcases hstrike with hs | hs
  · exact hclean p.1 hpr hpA (Or.inl (Nat.dvd_of_mod_eq_zero (by simpa using hs)))
  · exact hclean p.1 hpr hpA (Or.inr (Nat.dvd_of_mod_eq_zero (by simpa using hs)))

/-- **Kernel demo: a certified MAXIMAL defect at scale 37.**  The SAT witness of
    `Step00PhaseCoverKernel` (`allStruck_37`, an explicit run of 87 struck centers after
    `r = 1145973108145`, kernel-verified by trial division) is exactly a `CoverDefect`
    of length `G(37) − 1 = 87` — one short of the length that `no_long_defect_37`
    refutes everywhere.  The dichotomy's defect horn, inhabited by a concrete literal. -/
theorem coverDefect_demo_37 : CoverDefect 37 1145973108145 87 :=
  coverDefect_of_allStruck (by decide) PhaseCoverKernel.allStruck_37

/-- The same demo at scale 17 (`allStruck_17`: 17 struck centers after `r = 117`) —
    small enough to cross-check against the navigator's `none` verdict below. -/
theorem coverDefect_demo_17 : CoverDefect 17 117 17 :=
  coverDefect_of_allStruck (by decide) PhaseCoverKernel.allStruck_17

/-! ### Section 3 — the navigator: a clock-list-parameterised bounded scan

Three layers: the fuelled scan `nextTwinAux`, the window front-end `nextTwin`, and the
correctness stack.  The clock list `qs` is ALWAYS passed explicitly — never computed
from `A` — because mathlib primality instances are kernel-opaque and the whole point is
that `cleanListB` folds are kernel-cheap.  Soundness of the scan test is the repo's
`clean_of_cleanListB`; the genuinely NEW lemma is the completeness direction
`cleanListB_complete` (a clean center never fails the fold), which is what turns a
`none` verdict into knowledge and a `CleanGapBound` into totality. -/

/-- The fuelled scan: try centers `m, m+1, …` (at most `fuel` of them), return the first
    one that passes the `cleanListB` fold. -/
def nextTwinAux (qs : List ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, m => if cleanListB qs m then some m else nextTwinAux qs fuel (m + 1)

/-- The navigator: scan the window `(t, t+g]` for the first center clean along `qs`. -/
def nextTwin (qs : List ℕ) (t g : ℕ) : Option ℕ :=
  nextTwinAux qs g (t + 1)

/-- A `some` answer of the scan is in range and passes the fold. -/
theorem nextTwinAux_spec {qs : List ℕ} :
    ∀ (fuel : ℕ) {s m : ℕ}, nextTwinAux qs fuel s = some m →
      s ≤ m ∧ m < s + fuel ∧ cleanListB qs m = true := by
  intro fuel
  induction fuel with
  | zero => intro s m h; simp [nextTwinAux] at h
  | succ fuel ih =>
      intro s m h
      simp only [nextTwinAux] at h
      by_cases hcl : cleanListB qs s = true
      · rw [if_pos hcl] at h
        cases h
        exact ⟨le_rfl, by omega, hcl⟩
      · rw [if_neg hcl] at h
        obtain ⟨h1, h2, h3⟩ := ih h
        exact ⟨by omega, by omega, h3⟩

/-- A `none` answer certifies that EVERY center of the scanned range fails the fold. -/
theorem nextTwinAux_none {qs : List ℕ} :
    ∀ (fuel : ℕ) {s : ℕ}, nextTwinAux qs fuel s = none →
      ∀ j, j < fuel → cleanListB qs (s + j) = false := by
  intro fuel
  induction fuel with
  | zero => intro s _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ fuel ih =>
      intro s h j hj
      simp only [nextTwinAux] at h
      by_cases hcl : cleanListB qs s = true
      · rw [if_pos hcl] at h
        simp at h
      · rw [if_neg hcl] at h
        have hf : cleanListB qs s = false := by
          cases hb : cleanListB qs s
          · rfl
          · exact absurd hb hcl
        cases j with
        | zero => simpa using hf
        | succ j =>
            have hstep := ih h j (by omega)
            rwa [show s + 1 + j = s + (j + 1) from by omega] at hstep

/-- **Completeness of the fold test** — the one genuinely new lemma of this file (the
    repo only had soundness, `clean_of_cleanListB`): when every listed clock is a prime
    `≤ A`, a `Clean A` center PASSES the fold.  `Clean` forbids each `q ∈ qs` from
    dividing either wing, so both `%`-tests are nonzero. -/
theorem cleanListB_complete {A m : ℕ} {qs : List ℕ}
    (hside : ∀ q ∈ qs, q.Prime ∧ q ≤ A) (h : Clean A m) :
    cleanListB qs m = true := by
  simp only [cleanListB, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq]
  intro q hq
  obtain ⟨hqp, hqA⟩ := hside q hq
  constructor
  · intro h0
    exact h q hqp hqA (Or.inl (Nat.dvd_of_mod_eq_zero h0))
  · intro h0
    exact h q hqp hqA (Or.inr (Nat.dvd_of_mod_eq_zero h0))

/-- **Partial correctness of the navigator**: with the clock list covering the primes of
    `[5, A]` (the same coverage side condition `clean_of_cleanListB` consumes), a `some`
    answer is a `Clean A` center inside the window `(t, t+g]`. -/
theorem nextTwin_clean {A t g m : ℕ} {qs : List ℕ}
    (hcov : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → q ∈ qs)
    (h : nextTwin qs t g = some m) :
    t < m ∧ m ≤ t + g ∧ Clean A m := by
  obtain ⟨h1, h2, h3⟩ := nextTwinAux_spec g (h : nextTwinAux qs g (t + 1) = some m)
  exact ⟨by omega, by omega, clean_of_cleanListB (by omega) hcov h3⟩

/-- **Twin upgrade below the ceiling**: when the whole window additionally sits under
    the sieve horizon (`6(t+g)+1 < A²`), the navigator's answer is a TWIN center
    (`sink_is_twin`, mirroring `twin_gap_below_wall`). -/
theorem nextTwin_twin {A t g m : ℕ} {qs : List ℕ}
    (hcov : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → q ∈ qs)
    (hceil : 6 * (t + g) + 1 < A * A)
    (h : nextTwin qs t g = some m) :
    t < m ∧ m ≤ t + g ∧ TwinCenterZ m := by
  obtain ⟨h1, h2, h3⟩ := nextTwin_clean hcov h
  exact ⟨h1, h2, sink_is_twin (by omega) (by omega) (by omega) (by omega) h3⟩

/-- **Conditional totality**: a `CleanGapBound A g` (with the clock list inside the
    scale, so completeness applies) forces the navigator to answer `some` on every
    window of length `g`.  The bound plants a clean center in the window; by
    `cleanListB_complete` it passes the fold; a `none` scan would have declared it
    failing (`nextTwinAux_none`) — contradiction. -/
theorem nextTwin_isSome_of_cleanGapBound {A g : ℕ} {qs : List ℕ}
    (hside : ∀ q ∈ qs, q.Prime ∧ q ≤ A)
    (hbound : CleanGapBound A g) (t : ℕ) :
    (nextTwin qs t g).isSome = true := by
  obtain ⟨m, h1, h2, h3⟩ := hbound t
  cases hres : nextTwin qs t g with
  | some m' => rfl
  | none =>
      exfalso
      have hnone :=
        nextTwinAux_none g (hres : nextTwinAux qs g (t + 1) = none)
          (m - (t + 1)) (by omega)
      rw [show t + 1 + (m - (t + 1)) = m from by omega] at hnone
      rw [cleanListB_complete hside h3] at hnone
      exact Bool.noConfusion hnone

/-- Navigator demo (kernel-checkable): from `t = 16`, window length `11` (the certified
    `G(13) = 11`), the clocks of scale 13 point at `m = 17` — the twin pair
    `(101, 103)`. -/
example : nextTwin [5, 7, 11, 13] 16 11 = some 17 := by decide

/-- Navigator demo, `none` shape: the window after `k = 117` at scale 17 is the
    certified defect `coverDefect_demo_17` (`allStruck_17`), and the navigator's scan
    verdict agrees — no center of `(117, 134]` passes the scale-17 fold. -/
example : nextTwin [5, 7, 11, 13, 17] 117 17 = none := by decide

/-! ### Section 4 — the enumerator: least-witness twin sequence under the wall

`twinSeq H n` iterates `Nat.find` over the green escalation
`twinCenters_unbounded_of_twinJacobsthalCofinal H : ∀ M0, ∃ m, M0 < m ∧ TwinCenterZ m` —
no `Classical.choice`-extraction: `Nat.find` picks the LEAST witness, which is what makes
the enumerator canonical and (the crown) surjective onto all twin centers. -/

/-- The least-witness twin enumerator, conditional on the cofinal wall: `twinSeq H 0` is
    the least twin center above `0`, and `twinSeq H (n+1)` the least one above
    `twinSeq H n`.  (`TwinCenterZ` is decidable through the `GenealogyBasins` instance,
    so `Nat.find` applies.) -/
def twinSeq (H : TwinJacobsthalBoundCofinal) : ℕ → ℕ
  | 0 => Nat.find (twinCenters_unbounded_of_twinJacobsthalCofinal H 0)
  | n + 1 => Nat.find (twinCenters_unbounded_of_twinJacobsthalCofinal H (twinSeq H n))

theorem twinSeq_zero_def (H : TwinJacobsthalBoundCofinal) :
    twinSeq H 0 = Nat.find (twinCenters_unbounded_of_twinJacobsthalCofinal H 0) := rfl

theorem twinSeq_succ_def (H : TwinJacobsthalBoundCofinal) (n : ℕ) :
    twinSeq H (n + 1) =
      Nat.find (twinCenters_unbounded_of_twinJacobsthalCofinal H (twinSeq H n)) := rfl

/-- Every enumerator value is a twin center. -/
theorem twinSeq_twin (H : TwinJacobsthalBoundCofinal) (n : ℕ) :
    TwinCenterZ (twinSeq H n) := by
  cases n with
  | zero =>
      rw [twinSeq_zero_def]
      exact (Nat.find_spec (twinCenters_unbounded_of_twinJacobsthalCofinal H 0)).2
  | succ n =>
      rw [twinSeq_succ_def]
      exact (Nat.find_spec
        (twinCenters_unbounded_of_twinJacobsthalCofinal H (twinSeq H n))).2

/-- Each step strictly climbs. -/
theorem twinSeq_lt (H : TwinJacobsthalBoundCofinal) (n : ℕ) :
    twinSeq H n < twinSeq H (n + 1) := by
  rw [twinSeq_succ_def]
  exact (Nat.find_spec
    (twinCenters_unbounded_of_twinJacobsthalCofinal H (twinSeq H n))).1

/-- The enumerator is strictly monotone. -/
theorem twinSeq_strictMono (H : TwinJacobsthalBoundCofinal) :
    StrictMono (twinSeq H) :=
  strictMono_nat_of_lt_succ (twinSeq_lt H)

/-- The enumerator grows at least linearly: `n ≤ twinSeq H n`. -/
theorem le_twinSeq (H : TwinJacobsthalBoundCofinal) : ∀ n : ℕ, n ≤ twinSeq H n
  | 0 => Nat.zero_le _
  | n + 1 => by
      have h1 := le_twinSeq H n
      have h2 := twinSeq_lt H n
      omega

/-- The enumerator starts at the FIRST twin center: `twinSeq H 0 = 1`, the pair `(5, 7)`
    (`Nat.find_eq_iff`: `m = 1` is a twin, and `m = 0` is above nothing). -/
theorem twinSeq_zero (H : TwinJacobsthalBoundCofinal) : twinSeq H 0 = 1 := by
  rw [twinSeq_zero_def, Nat.find_eq_iff]
  refine ⟨⟨Nat.one_pos, GenealogyBasins.twinCenterZ_one⟩, ?_⟩
  rintro n hn ⟨hn0, -⟩
  omega

/--
  **The crown: least-witness completeness of the enumerator.**  Every twin center
  `m ≥ 1` is hit: `twinSeq H n = m` for some `n` — the enumerator provably enumerates
  ALL twin centers in increasing order, conditional only on the named wall.  Proof: take
  the least index `N` with `m ≤ twinSeq H N` (exists since `n ≤ twinSeq H n`); `N ≠ 0`
  when `m > 1` (as `twinSeq H 0 = 1`), and at `N = n + 1` minimality gives
  `twinSeq H n < m`, so `m` satisfies the `Nat.find` predicate of step `n + 1` and
  `Nat.find_min'` pins `twinSeq H (n+1) ≤ m ≤ twinSeq H (n+1)`.
-/
theorem twinSeq_surj (H : TwinJacobsthalBoundCofinal) {m : ℕ} (hm1 : 1 ≤ m)
    (htw : TwinCenterZ m) : ∃ n : ℕ, twinSeq H n = m := by
  rcases eq_or_lt_of_le hm1 with heq | hlt
  · exact ⟨0, by rw [twinSeq_zero]; omega⟩
  · have hex : ∃ k : ℕ, m ≤ twinSeq H k := ⟨m, le_twinSeq H m⟩
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · exfalso
        have hspec := Nat.find_spec hex
        rw [h0, twinSeq_zero] at hspec
        omega
      · exact ⟨Nat.find hex - 1, by omega⟩
    have hupper : m ≤ twinSeq H (n + 1) := by
      have hspec := Nat.find_spec hex
      rwa [hn] at hspec
    have hlower : twinSeq H n < m := by
      have hmin : ¬ m ≤ twinSeq H n := Nat.find_min hex (by omega)
      omega
    have hfind_le : twinSeq H (n + 1) ≤ m := by
      rw [twinSeq_succ_def]
      exact Nat.find_min'
        (twinCenters_unbounded_of_twinJacobsthalCofinal H (twinSeq H n)) ⟨hlower, htw⟩
    exact ⟨n + 1, by omega⟩

/-! ### Section 5 — the packaging disclosure: the navigator is the goal -/

/--
  **DISCLOSURE: navigator totality ⟺ unbounded twins.**  "The navigator always finds a
  next twin" (`∀ t, ∃ m, t < m ∧ TwinCenterZ m` — the Prop that unconditional totality
  of `nextTwin` at every horizon would produce, and exactly what `twinSeq` consumes) is
  EQUIVALENT to the repo's canonical goal form `TwinLowers.Infinite`.  Forward:
  `infinite_of_unbounded_centers` (each high center donates its lower wing).  Backward:
  an unbounded twin-lower above `6t + 5` is `6m − 1` for a twin center `m > t`
  (`twinCenter_of_twinLower`).

  Honest reading: this iff shows the navigator is a REPACKAGING of twin infinitude, not
  progress toward it.  The only fuel above the certified scales is the named wall
  (`TwinJacobsthalBound` / `TwinJacobsthalBoundCofinal`); the module's actual content is
  the window dichotomy and certified navigation BELOW the proven ceilings.
  `twin_prime_conjecture` stays untouched.
-/
theorem navigator_iff_unbounded_twins :
    (∀ t : ℕ, ∃ m : ℕ, t < m ∧ TwinCenterZ m) ↔ TwinLowers.Infinite := by
  constructor
  · intro h
    exact infinite_of_unbounded_centers h
  · intro H t
    obtain ⟨p, hpmem, hpgt⟩ :=
      GeometryFront.twinLowers_unbounded_of_infinite H (6 * t + 5)
    have hp : IsTwinPair p := hpmem
    obtain ⟨m, hm1, htw, hpm⟩ := GeometryFront.twinCenter_of_twinLower hp (by omega)
    exact ⟨m, by omega, htw⟩

end TwinNavigator
end EuclidsPath

/-
  ### Machine honesty (recorded `#print axioms` output)

  Checked against this exact file with `lake env lean` (scratch `#print axioms` block,
  removed after recording); every declaration sits under the standard axioms only — no
  `sorryAx`, no `step00FirstCause`, no `Lean.ofReduceBool`/`Lean.trustCompiler`
  (`native_decide` is not used anywhere in this file):

  * `peelStep_lt_unconditional`            — `[propext, Classical.choice, Quot.sound]`
  * `peelReach_le`                         — `[propext, Classical.choice, Quot.sound]`
  * `drainage_downhill`                    — `[propext, Classical.choice, Quot.sound]`
  * `windowVerdict`                        — `[propext, Classical.choice, Quot.sound]`
  * `verdict_exclusive`                    — `[propext, Quot.sound]`
  * `verdict_overlap_at_boundary`          — `[propext, Classical.choice, Quot.sound]`
  * `no_long_defect_of_cleanGapBound`      — `[propext, Quot.sound]`
  * `no_long_defect_5` … `no_long_defect_37`
                                           — `[propext, Classical.choice, Quot.sound]`
  * `coverDefect_iff_phaseCover`           — `[propext, Classical.choice, Quot.sound]`
  * `coverDefect_of_allStruck`             — `[propext, Quot.sound]`
  * `coverDefect_demo_37` / `_17`          — `[propext, Classical.choice, Quot.sound]`
  * `nextTwinAux_spec` / `nextTwinAux_none` — `[propext, Quot.sound]`
  * `cleanListB_complete`                  — `[propext, Quot.sound]`
  * `nextTwin_clean` / `nextTwin_twin`     — `[propext, Classical.choice, Quot.sound]`
  * `nextTwin_isSome_of_cleanGapBound`     — `[propext, Quot.sound]`
  * `twinSeq_zero_def` / `twinSeq_succ_def` / `twinSeq_twin` / `twinSeq_lt` /
    `twinSeq_strictMono` / `le_twinSeq` / `twinSeq_zero` / `twinSeq_surj`
                                           — `[propext, Classical.choice, Quot.sound]`
  * `navigator_iff_unbounded_twins`        — `[propext, Classical.choice, Quot.sound]`

  The three `decide` examples (the boundary overlap and the two navigator demos) are
  kernel-checked in place; all `decide` obligations of this file are sub-second — the
  heaviest is the 17-center window scan of the `none` demo.
-/
