import EuclidsPath.Engine.GenealogyForest
import EuclidsPath.Engine.Step00PackingGeometry

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Grave structure — the descent sinks welded to every geometric layer (all green)

A **grave** is a descent sink of the genealogical forest: a center with nothing to peel,
i.e. `Genealogy.IsRoot`.  This file deliberately introduces NO new `Grave` definition —
the root predicate IS the grave, and `Genealogy.root_iff_twin` already identifies the
graves with the twins.  What this file adds is the weld between that sink structure and
the layers built independently of it: the gain layer (`wingGain`), the packing model
(`Repackable`), the sign layer (`wingSign`), the phase laws of the two-engine
oscillation, and the boundary exits of the concrete Step00 graph.

## Contents (no `sorry`, no new axiom, no `native_decide`)

* `TwinCenterZ.one_le` — a twin center is positive (the `m = 0` degeneracy is impossible:
  in ℕ the left side `6·0 − 1 = 0` is not prime);
* `grave_iff_gainZero` / `grave_iff_collision` — the grave in gain and packing vocabulary.
  DISCLOSURE: pointwise twin restatement chains, zero new content;
* `descent_reaches_grave` — every center `m ≥ 1` descends to a grave `t ≤ m` carrying its
  layer certificates: gain zero and sign `+1`;
* `balanced_window_has_grave` — the counting bridge lands on a grave vertex of the window;
* `grave_strike_avoidance` — a grave center out of a clock's reach sits on NEITHER strike
  phase: prime wings force any striking clock to equal a wing;
* `grave_boundary_exit` — the ℕ-truncation exit through the zero point (artifact, disclosed);
* `strike_exit_below` — a GENUINE strike exit strictly below a clean center: the inverse
  phase `((6 : ZMod q)⁻¹).val` is a real boundary target;
* `grave_exit_control` — the assembled exit-control package of a grave center.

## Honest reading

Everything here is pointwise or downhill.  The equivalences are vocabulary welds (house
DISCLOSURE rule), the descent only ever certifies a grave AT OR BELOW its start, and no
statement multiplies the graves.  `twin_prime_conjecture` stays untouched.
-/

namespace EuclidsPath
namespace GraveStructure

open EuclidsPath.Residuals
open EuclidsPath.CleanGraph
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.GeometryFront
open EuclidsPath.GradedWindowComplex
open EuclidsPath.OrderedExponent
open EuclidsPath.GainLayer
open EuclidsPath.TwoEngineOscillation
open EuclidsPath.PackingGeometry

/-! ### Section 1 — positivity of twin centers and the grave equivalences -/

/-- A twin center is positive: at `m = 0` the left side `6·0 − 1 = 0` (in ℕ) is not
    prime, so `TwinCenterZ 0` is impossible. -/
theorem TwinCenterZ.one_le {m : ℕ} (h : TwinCenterZ m) : 1 ≤ m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  subst hm0
  have h2 := h.1.two_le
  omega

/-- **The grave in gain vocabulary.**  DISCLOSURE (house rule): this is the pointwise twin
    restatement chain grave = root ⟺ twin (`Genealogy.root_iff_twin`) ⟺ gain zero
    (`wingGain_eq_zero_iff`) — vocabulary weld between the forest and the gain layer,
    zero new content. -/
theorem grave_iff_gainZero {m : ℕ} (hm : 1 ≤ m) :
    Genealogy.IsRoot m ↔ wingGain m = (0, 0) :=
  (Genealogy.root_iff_twin hm).trans (wingGain_eq_zero_iff hm).symm

/-- **The grave in packing vocabulary.**  DISCLOSURE: pointwise chain grave = root ⟺ twin
    (`Genealogy.root_iff_twin`) ⟺ collision (`twin_collision`, whose center conjunct is
    free) — the packing dressing of the same twin predicate, recorded as vocabulary,
    not progress. -/
theorem grave_iff_collision {m : ℕ} (hm : 1 ≤ m) :
    Genealogy.IsRoot m ↔
      Repackable (6 * m) ∧ ¬ Repackable (6 * m - 1) ∧ ¬ Repackable (6 * m + 1) :=
  (Genealogy.root_iff_twin hm).trans (twin_collision hm)

/-! ### Section 2 — descent and counting land on graves -/

/-- **Descent reaches a grave**, and the grave carries all its layer certificates: every
    center `m ≥ 1` descends to a root `t ≤ m` that is gain-zero and sign-plus.  Downhill
    only — the grave is at or below `m` (the honest boundary of `descent_reaches_twin`);
    this multiplies no graves. -/
theorem descent_reaches_grave (m : ℕ) (hm : 1 ≤ m) :
    ∃ t : ℕ, t ≤ m ∧ 1 ≤ t ∧ Genealogy.IsRoot t ∧
      wingGain t = (0, 0) ∧ wingSign t = 1 := by
  obtain ⟨t, hle, h1, hroot⟩ := Genealogy.descent_reaches_root m hm
  have htwin : TwinCenterZ t := (Genealogy.root_iff_twin h1).mp hroot
  exact ⟨t, hle, h1, hroot, (wingGain_eq_zero_iff h1).mpr htwin, wingSign_of_twin htwin⟩

/-- **A balanced window contains a grave vertex**: the counting bridge
    (`balanced_window_has_twin`) rewritten in root-and-sign vocabulary — two survivors
    plus gain balance certify a grave among the survivor indices. -/
theorem balanced_window_has_grave {A : ℕ} {W : Finset State} (hA : 2 ≤ A)
    (h2 : 2 ≤ (survivors A W).card) (hbal : GainBalanced A W) :
    ∃ m ∈ survivorIdx A W, Genealogy.IsRoot m ∧ wingSign m = 1 := by
  obtain ⟨m, hmem, htwin⟩ := balanced_window_has_twin hA h2 hbal
  have hm1 : 1 ≤ m := TwinCenterZ.one_le htwin
  exact ⟨m, hmem, (Genealogy.root_iff_twin hm1).mpr htwin, wingSign_of_twin htwin⟩

/-! ### Section 3 — phase laws at a grave -/

/-- Local re-derivation (the upstream originals are `private`): `6 ≠ 0` in `ZMod q`
    for a prime clock `q ≥ 5`. -/
private theorem six_ne_zero {q : ℕ} [Fact q.Prime] (h5 : 5 ≤ q) : (6 : ZMod q) ≠ 0 := by
  have hq : q.Prime := Fact.out
  intro h
  have hdvd : q ∣ 6 := by
    have := (ZMod.natCast_eq_zero_iff 6 q).mp (by exact_mod_cast h)
    exact this
  have := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases q
  · exact absurd hdvd (by norm_num)
  · exact absurd hq (by norm_num)

/-- **Strike avoidance at a grave**: a clock `q ≥ 5` strictly below the left wing of a
    root center sits on NEITHER strike phase.  Both wings of a grave are prime
    (`Genealogy.root_iff_twin`), so a strike (`strike_phase_left/right`) would force the
    clock to divide a prime wing, hence to EQUAL it — contradicting `q < 6m − 1 < 6m + 1`. -/
theorem grave_strike_avoidance {q m : ℕ} [Fact q.Prime] (h5 : 5 ≤ q) (hm : 1 ≤ m)
    (hq : q < 6 * m - 1) (hroot : Genealogy.IsRoot m) :
    (m : ZMod q) ≠ (6 : ZMod q)⁻¹ ∧ (m : ZMod q) ≠ -(6 : ZMod q)⁻¹ := by
  have htwin : TwinCenterZ m := (Genealogy.root_iff_twin hm).mp hroot
  constructor
  · intro hphase
    have hdvd : q ∣ 6 * m - 1 := (strike_phase_left h5 hm).mpr hphase
    rcases htwin.1.eq_one_or_self_of_dvd q hdvd with h1 | hself
    · omega
    · omega
  · intro hphase
    have hdvd : q ∣ 6 * m + 1 := (strike_phase_right h5 hm).mpr hphase
    rcases htwin.2.eq_one_or_self_of_dvd q hdvd with h1 | hself
    · omega
    · omega

/-! ### Section 4 — boundary exits out of a clean center -/

/-- **The ℕ-truncation exit.**  DISCLOSURE (artifact, disclosed loudly): from ANY clean
    center every clock `q ≤ A` exits through the zero point, because
    `sideValue minus 0 = 6·0 − 1 = 0` in ℕ and `q ∣ 0`.  This is the grave-of-zero
    geometry of `GeometryFront` (honest boundary 3 there), NOT an arithmetic strike —
    the genuine strike exit is `strike_exit_below`. -/
theorem grave_boundary_exit {A M0 q m : ℕ} (hq : q.Prime) (hqA : q ≤ A) (hm : 1 ≤ m)
    (hclean : Clean A m) :
    State.defect 0 q Side.minus ∈ outTargets A M0 (State.center m) := by
  show State.defect 0 q Side.minus ∈ cleanTargets A m ∪ boundaryTargets A m
  exact Finset.mem_union.mpr (Or.inr (mem_boundaryTargets.mpr
    ⟨hclean, 0, q, Side.minus, by omega, hq, hqA, zeroPoint_absorbs_all_divisors q, rfl⟩))

/-- **A genuine strike exit strictly below**: for a clean center `m` above the clock
    (`q + 1 ≤ m`), the inverse phase `n = ((6 : ZMod q)⁻¹).val` is a real boundary target
    `defect n q minus` with `1 ≤ n < m` — the clock's actual strike row
    (`strike_phase_left` read backwards through the value map), not the ℕ-artifact of
    `grave_boundary_exit`. -/
theorem strike_exit_below {A M0 q m : ℕ} [Fact q.Prime] (h5 : 5 ≤ q) (hqA : q ≤ A)
    (hm : 1 ≤ m) (hclean : Clean A m) (hqm : q + 1 ≤ m) :
    ∃ n : ℕ, 1 ≤ n ∧ n < m ∧
      State.defect n q Side.minus ∈ outTargets A M0 (State.center m) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have h6 : (6 : ZMod q) ≠ 0 := six_ne_zero h5
  have hinv : (6 : ZMod q)⁻¹ ≠ 0 := inv_ne_zero h6
  have hn0 : ((6 : ZMod q)⁻¹).val ≠ 0 := fun h0 => hinv ((ZMod.val_eq_zero _).mp h0)
  have hn1 : 1 ≤ ((6 : ZMod q)⁻¹).val := Nat.one_le_iff_ne_zero.mpr hn0
  have hnq : ((6 : ZMod q)⁻¹).val < q := ZMod.val_lt _
  have hnm : ((6 : ZMod q)⁻¹).val < m := by omega
  have hcast : ((((6 : ZMod q)⁻¹).val : ℕ) : ZMod q) = (6 : ZMod q)⁻¹ :=
    ZMod.natCast_zmod_val _
  have hdvd : q ∣ sideValue Side.minus ((6 : ZMod q)⁻¹).val :=
    (strike_phase_left h5 hn1).mpr hcast
  refine ⟨((6 : ZMod q)⁻¹).val, hn1, hnm, ?_⟩
  show State.defect ((6 : ZMod q)⁻¹).val q Side.minus ∈
    cleanTargets A m ∪ boundaryTargets A m
  exact Finset.mem_union.mpr (Or.inr (mem_boundaryTargets.mpr
    ⟨hclean, ((6 : ZMod q)⁻¹).val, q, Side.minus, hnm, hq, hqA, hdvd, rfl⟩))

/-! ### Section 5 — the assembled exit control of a grave center -/

/-- **Exit control at a grave.**  DISCLOSURE: an assembly of existing greens, and the
    three disjointness conjuncts hold for ALL centers, not only graves
    (`support_renewal_succ` / `wing_idxSupport_disjoint` are unconditional).
    A grave center has: (a) no peel exit (it is a root); (b) for every clock `q ≤ A` the
    ℕ-truncation boundary exit through the zero point; (c) totally renewed supports — the
    left wing, the stable center and the right wing pairwise share no prime direction;
    (d) the positive sign certificate `wingSign m = 1 ≠ 0`. -/
theorem grave_exit_control {A M0 m : ℕ} (hm : 1 ≤ m) (hroot : Genealogy.IsRoot m)
    (hclean : Clean A m) :
    (¬ ∃ t : ℕ, Genealogy.PeelStep m t) ∧
    (∀ q : ℕ, q.Prime → q ≤ A →
      State.defect 0 q Side.minus ∈ outTargets A M0 (State.center m)) ∧
    Disjoint (idxSupport (6 * m - 1)) (idxSupport (6 * m)) ∧
    Disjoint (idxSupport (6 * m)) (idxSupport (6 * m + 1)) ∧
    Disjoint (idxSupport (6 * m - 1)) (idxSupport (6 * m + 1)) ∧
    wingSign m = 1 ∧ wingSign m ≠ 0 := by
  have htwin : TwinCenterZ m := (Genealogy.root_iff_twin hm).mp hroot
  have hLC : Disjoint (idxSupport (6 * m - 1)) (idxSupport (6 * m)) := by
    have h := support_renewal_succ (6 * m - 1)
    have he : 6 * m - 1 + 1 = 6 * m := by omega
    rwa [he] at h
  exact ⟨hroot, fun q hq hqA => grave_boundary_exit hq hqA hm hclean, hLC,
    support_renewal_succ (6 * m), wing_idxSupport_disjoint hm,
    wingSign_of_twin htwin, wingSign_ne_zero m⟩

end GraveStructure
end EuclidsPath

/-!
### Machine honesty (recorded `#print axioms` output)

Checked against the built module (scratch run, `lake env lean`); every declaration of this
file sits under the standard axioms only — no `sorry`, no `step00FirstCause`:

* `TwinCenterZ.one_le` — `[propext, Quot.sound]`
* `grave_iff_gainZero` — `[propext, Classical.choice, Quot.sound]`
* `grave_iff_collision` — `[propext, Classical.choice, Quot.sound]`
* `descent_reaches_grave` — `[propext, Classical.choice, Quot.sound]`
* `balanced_window_has_grave` — `[propext, Classical.choice, Quot.sound]`
* `grave_strike_avoidance` — `[propext, Classical.choice, Quot.sound]`
* `grave_boundary_exit` — `[propext, Classical.choice, Quot.sound]`
* `strike_exit_below` — `[propext, Classical.choice, Quot.sound]`
* `grave_exit_control` — `[propext, Classical.choice, Quot.sound]`
-/
