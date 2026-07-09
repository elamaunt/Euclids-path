import EuclidsPath.Engine.GeometryFront
import EuclidsPath.Engine.Step00GradedKilledBoundary

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Graded window complex — the killed-boundary sector split, exact laws (all green)

The relative-index census (tools/relindex_harness.py, ledger L13–L16) REFUTED the structural
reading of the constant `−5`: no natural quotient of the ornament window complex is constant in
the horizon — `gaussBonnet_cone3 = −5` is an isolated calibration point of one small cone, and
the `relIndex_computed : relIndex = -5` field of `RelativeCurvatureCertificate` is NOMINAL (the
certificate is logically equivalent to survivor existence — which is how the graded route of
`Step00GradedKilledBoundary` legitimately inhabits it), not the value of a structural invariant.

What the census found INSTEAD, and this file proves green:

* **Sector split** (`eulerChar_sector_split`): on any window, `χ = relIndexStruct + killedEuler`
  — the Euler characteristic decomposes into a survivor-relative part and the killed subcomplex.
* **The absorber horizon is invisible to the relative index** (`relIndexStruct_m0_invariant`,
  census law L15, now a theorem): `relIndexStruct = V_S − E_SS − E_SK − E_KS` contains no `M0`
  because ALL `M0`-dependence of the ornament graph (absorb edges, absorber cells) lives inside
  the killed sector.  This is the true content the `−5` decree was groping at: relativization
  kills the horizon-dependence exactly — but the residual index is apex-dependent, not constant.
* **The survivor sector is a complete transitive tournament** (`survivor_out_full`,
  `eSS_eq_choose_two`, census law L14): on a forward-closed window every ordered pair of clean
  centers carries exactly one clean edge, so `E_SS = C(V_S, 2)` exactly and the survivor-sector
  index is the explicit quadratic `V_S − C(V_S,2) − (E_SK + E_KS)` — the measured quadratic law.
* Kernel calibration on `cone3`: `relIndexStruct 5 4 cone3 = -7`, `killedEuler 5 4 cone3 = 2`,
  recovering `χ = −5`; and the invariance theorem specializes to concrete horizons.

Honest status: everything here is green counting on finite windows.  It does NOT construct a
matching or estimate; it fixes the CORRECT parametrization for the assault (Line B of the plan):
invariance in `M0` is proved, constancy in the apex is refuted, the apex law is quadratic via
the tournament.
-/

namespace EuclidsPath
namespace GradedWindowComplex

open EuclidsPath.CleanGraph
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.GeometryFront

/-! ### The sector split: survivor cells vs killed cells -/

/-- A survivor cell: a clean center.  Everything else (defects, absorbers, non-clean centers)
    is a killed cell. -/
def IsSurvivor (A : ℕ) : State → Prop
  | State.center m => Clean A m
  | State.defect _ _ _ => False
  | State.absorber _ => False

instance survivorDecidable (A : ℕ) (v : State) : Decidable (IsSurvivor A v) :=
  match v with
  | State.center m => inferInstanceAs (Decidable (Clean A m))
  | State.defect _ _ _ => isFalse (fun h => h)
  | State.absorber _ => isFalse (fun h => h)

/-- Survivor cells of a window. -/
def survivors (A : ℕ) (W : Finset State) : Finset State := W.filter (fun v => IsSurvivor A v)

/-- Killed cells of a window. -/
def killedCells (A : ℕ) (W : Finset State) : Finset State :=
  W.filter (fun v => ¬ IsSurvivor A v)

theorem card_survivors_add_card_killed (A : ℕ) (W : Finset State) :
    (survivors A W).card + (killedCells A W).card = W.card :=
  Finset.filter_card_add_filter_neg_card_eq_card (fun v => IsSurvivor A v)

/-! ### Sector edge counts -/

/-- Edges from `v` into the survivor part of `W`. -/
def outIntoSurvivors (A M0 : ℕ) (W : Finset State) (v : State) : ℕ :=
  ((outTargets A M0 v ∩ W).filter (fun w => IsSurvivor A w)).card

/-- Edges from `v` into the killed part of `W`. -/
def outIntoKilled (A M0 : ℕ) (W : Finset State) (v : State) : ℕ :=
  ((outTargets A M0 v ∩ W).filter (fun w => ¬ IsSurvivor A w)).card

theorem outInto_split (A M0 : ℕ) (W : Finset State) (v : State) :
    outIntoSurvivors A M0 W v + outIntoKilled A M0 W v
      = (outTargets A M0 v ∩ W).card :=
  Finset.filter_card_add_filter_neg_card_eq_card (fun w => IsSurvivor A w)

/-- `E_SS`: survivor → survivor edges. -/
def eSS (A M0 : ℕ) (W : Finset State) : ℕ :=
  (survivors A W).sum (outIntoSurvivors A M0 W)

/-- `E_SK`: survivor → killed edges. -/
def eSK (A M0 : ℕ) (W : Finset State) : ℕ :=
  (survivors A W).sum (outIntoKilled A M0 W)

/-- `E_KS`: killed → survivor edges (peel edges landing on clean centers). -/
def eKS (A M0 : ℕ) (W : Finset State) : ℕ :=
  (killedCells A W).sum (outIntoSurvivors A M0 W)

/-- `E_KK`: killed → killed edges. -/
def eKK (A M0 : ℕ) (W : Finset State) : ℕ :=
  (killedCells A W).sum (outIntoKilled A M0 W)

/-- The four sector counts exhaust the induced edges. -/
theorem inducedEdges_sector_split (A M0 : ℕ) (W : Finset State) :
    eSS A M0 W + eSK A M0 W + (eKS A M0 W + eKK A M0 W) = inducedEdges A M0 W := by
  have hS : eSS A M0 W + eSK A M0 W
      = (survivors A W).sum (fun v => (outTargets A M0 v ∩ W).card) := by
    rw [eSS, eSK, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => outInto_split A M0 W v
  have hK : eKS A M0 W + eKK A M0 W
      = (killedCells A W).sum (fun v => (outTargets A M0 v ∩ W).card) := by
    rw [eKS, eKK, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => outInto_split A M0 W v
  rw [hS, hK, inducedEdges]
  exact Finset.sum_filter_add_sum_filter_not W (fun v => IsSurvivor A v) _

/-! ### The structural relative index and the killed Euler characteristic -/

/-- **The structural relative index**: survivor cells minus all survivor-incident edges.
    By `relIndexStruct_m0_invariant` below it does not depend on the absorber horizon `M0` —
    the exact content of census law L15. -/
def relIndexStruct (A M0 : ℕ) (W : Finset State) : ℤ :=
  ((survivors A W).card : ℤ) - (eSS A M0 W : ℤ) - (eSK A M0 W : ℤ) - (eKS A M0 W : ℤ)

/-- Euler characteristic of the killed subcomplex. -/
def killedEuler (A M0 : ℕ) (W : Finset State) : ℤ :=
  ((killedCells A W).card : ℤ) - (eKK A M0 W : ℤ)

/-- **Sector split of the Euler characteristic**: `χ(W) = relIndexStruct + killedEuler`.
    Equivalently `relIndexStruct = χ(W) − χ(K)` — the "quotient by the killed boundary". -/
theorem eulerChar_sector_split (A M0 : ℕ) (W : Finset State) :
    eulerChar A M0 W = relIndexStruct A M0 W + killedEuler A M0 W := by
  rw [eulerChar, relIndexStruct, killedEuler, ← inducedEdges_sector_split A M0 W,
    ← card_survivors_add_card_killed A W]
  push_cast
  ring

/-! ### The absorber horizon is invisible to the relative index (census law L15, green) -/

theorem outTargets_center_m0_free (A M0 M0' m : ℕ) :
    outTargets A M0 (State.center m) = outTargets A M0' (State.center m) := rfl

/-- Absorb targets never land in the survivor sector. -/
theorem filter_survivor_absorbTargets (A M0 n : ℕ) (W : Finset State) :
    ((absorbTargets M0 n ∩ W).filter (fun w => IsSurvivor A w)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
  obtain ⟨hva, -⟩ := Finset.mem_inter.mp hv1
  obtain ⟨-, rfl⟩ := mem_absorbTargets.mp hva
  exact hv2

/-- The survivor-targets of a defect are exactly its peel targets in `W` — the `M0`-dependent
    absorb component is filtered out by the sector. -/
theorem defect_outIntoSurvivors (A M0 n q : ℕ) (s : Side) (W : Finset State) :
    outIntoSurvivors A M0 W (State.defect n q s)
      = ((peelTargets n q s ∩ W).filter (fun w => IsSurvivor A w)).card := by
  unfold outIntoSurvivors
  show (((peelTargets n q s ∪ absorbTargets M0 n) ∩ W).filter (fun w => IsSurvivor A w)).card = _
  rw [Finset.union_inter_distrib_right, Finset.filter_union,
    filter_survivor_absorbTargets, Finset.union_empty]

/-- Survivor-target counts do not depend on the horizon, from ANY source vertex. -/
theorem outIntoSurvivors_m0_invariant (A M0 M0' : ℕ) (W : Finset State) (v : State) :
    outIntoSurvivors A M0 W v = outIntoSurvivors A M0' W v := by
  cases v with
  | center m => unfold outIntoSurvivors; rw [outTargets_center_m0_free A M0 M0' m]
  | defect n q s =>
      rw [defect_outIntoSurvivors A M0 n q s W, defect_outIntoSurvivors A M0' n q s W]
  | absorber a => rfl

/-- Killed-target counts from a SURVIVOR source do not depend on the horizon (survivor
    out-edges — clean and boundary — never mention `M0`). -/
theorem outIntoKilled_m0_invariant_of_center (A M0 M0' : ℕ) (W : Finset State) (m : ℕ) :
    outIntoKilled A M0 W (State.center m) = outIntoKilled A M0' W (State.center m) := by
  unfold outIntoKilled
  rw [outTargets_center_m0_free A M0 M0' m]

theorem eSS_m0_invariant (A M0 M0' : ℕ) (W : Finset State) :
    eSS A M0 W = eSS A M0' W :=
  Finset.sum_congr rfl fun v _ => outIntoSurvivors_m0_invariant A M0 M0' W v

theorem eKS_m0_invariant (A M0 M0' : ℕ) (W : Finset State) :
    eKS A M0 W = eKS A M0' W :=
  Finset.sum_congr rfl fun v _ => outIntoSurvivors_m0_invariant A M0 M0' W v

theorem eSK_m0_invariant (A M0 M0' : ℕ) (W : Finset State) :
    eSK A M0 W = eSK A M0' W := by
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨-, hsurv⟩ := Finset.mem_filter.mp hv
  cases v with
  | center m => exact outIntoKilled_m0_invariant_of_center A M0 M0' W m
  | defect n q s => exact absurd hsurv (fun h => h)
  | absorber a => exact absurd hsurv (fun h => h)

/-- **THE HORIZON-INVISIBILITY THEOREM (census law L15, green).**  The structural relative
    index contains no `M0`: every `M0`-dependent cell and edge of the ornament graph lies
    inside the killed sector, and the quotient removes it exactly.  This is the true,
    provable content behind the refuted `−5` decree: relativization kills the
    horizon-dependence — the residue depends on the apex, not on the absorber horizon. -/
theorem relIndexStruct_m0_invariant (A M0 M0' : ℕ) (W : Finset State) :
    relIndexStruct A M0 W = relIndexStruct A M0' W := by
  rw [relIndexStruct, relIndexStruct, eSS_m0_invariant A M0 M0' W,
    eSK_m0_invariant A M0 M0' W, eKS_m0_invariant A M0 M0' W]

/-! ### The survivor tournament (census law L14, green) -/

/-- On a forward-closed window, the survivor out-edges of a clean center `m` inside the window
    are EXACTLY the survivors of smaller index: the survivor sector is a complete transitive
    tournament. -/
theorem survivor_out_full {A M0 : ℕ} {W : Finset State} (hclosed : ForwardClosed A M0 W)
    {m : ℕ} (hm : State.center m ∈ W) (hclean : Clean A m) :
    ((outTargets A M0 (State.center m) ∩ W).filter (fun w => IsSurvivor A w))
      = (survivors A W).filter (fun w => ∃ n, n < m ∧ w = State.center n) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_inter, survivors]
  constructor
  · rintro ⟨⟨hout, hW⟩, hsurv⟩
    refine ⟨⟨hW, hsurv⟩, ?_⟩
    cases w with
    | center n =>
        rcases Finset.mem_union.mp hout with h | h
        · rcases mem_cleanTargets.mp h with ⟨-, n', -, hn', heq⟩
          exact ⟨n', hn', heq⟩
        · rcases mem_boundaryTargets.mp h with ⟨-, n', q', s', -, -, -, -, heq⟩
          exact State.noConfusion heq
    | defect n' q' s' => exact absurd hsurv (fun h => h)
    | absorber a => exact absurd hsurv (fun h => h)
  · rintro ⟨⟨hW, hsurv⟩, n, hn, rfl⟩
    have hcleann : Clean A n := hsurv
    have hout : State.center n ∈ outTargets A M0 (State.center m) :=
      Finset.mem_union.mpr (Or.inl (mem_cleanTargets.mpr ⟨hclean, n, hcleann, hn, rfl⟩))
    exact ⟨⟨hout, hW⟩, hsurv⟩

/-- Center indices of the survivor cells. -/
def survivorIdx (A : ℕ) (W : Finset State) : Finset ℕ :=
  (survivors A W).image (fun v => match v with
    | State.center m => m
    | _ => 0)

theorem card_survivorIdx (A : ℕ) (W : Finset State) :
    (survivorIdx A W).card = (survivors A W).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw hvw
  obtain ⟨-, hv2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
  obtain ⟨-, hw2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
  cases v with
  | center mv =>
      cases w with
      | center mw => simpa using hvw
      | defect n q s => exact absurd hw2 (fun h => h)
      | absorber a => exact absurd hw2 (fun h => h)
  | defect n q s => exact absurd hv2 (fun h => h)
  | absorber a => exact absurd hv2 (fun h => h)

/-- The pair-counting identity: summing "how many below me" over a finite set of naturals
    counts each unordered pair once. -/
theorem sum_count_lt (I : Finset ℕ) :
    ∑ m ∈ I, (I.filter (fun n => n < m)).card = I.card.choose 2 := by
  classical
  induction I using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
      have hnotmem : a ∉ s := fun h => lt_irrefl a (ha a h)
      rw [Finset.sum_insert hnotmem]
      have hterm : ((insert a s).filter (fun n => n < a)).card = s.card := by
        congr 1
        rw [Finset.filter_insert, if_neg (lt_irrefl a)]
        apply Finset.filter_true_of_mem
        intro x hx
        exact ha x hx
      have hrest : ∀ m ∈ s, ((insert a s).filter (fun n => n < m)).card
          = (s.filter (fun n => n < m)).card := by
        intro m hm
        congr 1
        rw [Finset.filter_insert, if_neg (by have := ha m hm; omega)]
      rw [hterm, Finset.sum_congr rfl hrest, ih, Finset.card_insert_of_notMem hnotmem]
      have hchoose : (s.card + 1).choose 2 = s.card + s.card.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      omega

/-- **The tournament law (census law L14, green)**: on a forward-closed window
    `E_SS = C(V_S, 2)` exactly — every unordered pair of survivors carries exactly one
    clean edge (from the larger center to the smaller). -/
theorem eSS_eq_choose_two {A M0 : ℕ} {W : Finset State}
    (hclosed : ForwardClosed A M0 W) :
    eSS A M0 W = (survivors A W).card.choose 2 := by
  classical
  have hstep : ∀ v ∈ survivors A W,
      outIntoSurvivors A M0 W v = ((survivorIdx A W).filter (fun n => n <
        (match v with | State.center m => m | _ => 0))).card := by
    intro v hv
    obtain ⟨hvW, hvS⟩ := Finset.mem_filter.mp hv
    cases v with
    | center m =>
        have hclean : Clean A m := hvS
        unfold outIntoSurvivors
        rw [survivor_out_full hclosed hvW hclean]
        rw [survivorIdx]
        rw [Finset.filter_image]
        rw [Finset.card_image_of_injOn]
        · congr 1
          ext w
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hw, n, hn, rfl⟩
            exact ⟨hw, hn⟩
          · intro ⟨hw, hlt⟩
            obtain ⟨-, hsurv⟩ := Finset.mem_filter.mp hw
            cases w with
            | center n => exact ⟨hw, n, hlt, rfl⟩
            | defect n' q' s' => exact absurd hsurv (fun h => h)
            | absorber a => exact absurd hsurv (fun h => h)
        · intro v hv w hw hvw
          obtain ⟨hv1, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
          obtain ⟨hw1, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
          obtain ⟨-, hv2⟩ := Finset.mem_filter.mp hv1
          obtain ⟨-, hw2⟩ := Finset.mem_filter.mp hw1
          cases v with
          | center mv =>
              cases w with
              | center mw => simpa using hvw
              | defect n q s => exact absurd hw2 (fun h => h)
              | absorber a => exact absurd hw2 (fun h => h)
          | defect n q s => exact absurd hv2 (fun h => h)
          | absorber a => exact absurd hv2 (fun h => h)
    | defect n q s => exact absurd hvS (fun h => h)
    | absorber a => exact absurd hvS (fun h => h)
  rw [eSS, Finset.sum_congr rfl hstep, ← card_survivorIdx A W, ← sum_count_lt (survivorIdx A W)]
  rw [survivorIdx, Finset.sum_image]
  intro v hv w hw hvw
  obtain ⟨-, hv2⟩ := Finset.mem_filter.mp hv
  obtain ⟨-, hw2⟩ := Finset.mem_filter.mp hw
  cases v with
  | center mv =>
      cases w with
      | center mw => simpa using hvw
      | defect n q s => exact absurd hw2 (fun h => h)
      | absorber a => exact absurd hw2 (fun h => h)
  | defect n q s => exact absurd hv2 (fun h => h)
  | absorber a => exact absurd hv2 (fun h => h)

/-! ### Kernel calibration on `cone3` -/

/-- `relIndexStruct` on the calibration cone: `V_S = 2` (centers 3, 2), `E_SS = 1 = C(2,2)`,
    `E_SK = 8` boundary edges, `E_KS = 0` — index `−7`. -/
theorem relIndexStruct_cone3 : relIndexStruct 5 4 cone3 = -7 := by decide

/-- The killed subcomplex of the calibration cone: 7 cells, 5 internal edges — `χ(K) = 2`. -/
theorem killedEuler_cone3 : killedEuler 5 4 cone3 = 2 := by decide

/-- Consistency: the sector split recovers the kernel-checked `χ(cone3) = −5 = −7 + 2`. -/
theorem cone3_sector_consistency :
    eulerChar 5 4 cone3 = relIndexStruct 5 4 cone3 + killedEuler 5 4 cone3 :=
  eulerChar_sector_split 5 4 cone3

/-- The horizon-invisibility theorem, specialized: the calibration cone keeps index `−7`
    at EVERY absorber horizon. -/
theorem relIndexStruct_cone3_all_horizons (M0 : ℕ) :
    relIndexStruct 5 M0 cone3 = -7 := by
  rw [relIndexStruct_m0_invariant 5 M0 4 cone3]
  exact relIndexStruct_cone3

end GradedWindowComplex
end EuclidsPath
