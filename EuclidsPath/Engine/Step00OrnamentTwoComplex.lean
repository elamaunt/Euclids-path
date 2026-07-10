import EuclidsPath.Engine.Step00GradedWindowComplex

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The ornament 2-complex — faces, dimension-2 sector split, horizon invisibility (all green)

Dimension 1 of the ornament complex is topologically trivial (survivor tournament
`eSS_eq_choose_two`, horizon invisibility `relIndexStruct_m0_invariant`).  This file adds the
2-cells and lifts the bookkeeping one dimension up:

* `Face` — directed 2-simplices (`tri u v w`: edges `u→v`, `v→w`, `u→w` of the real step graph)
  and killed squares (`quad m n q q' s s'`: the two boundary exits of a clean center `m` into
  the two defects of a sub-center `n ≤ M0`, closed through the absorber `a_n`);
* `triFaces`/`quadFaces`/`faces` — computed `Finset Face` per window, in the house
  computed-Finset style of `outTargets`;
* **`no_absorber_in_tri`** — the keystone: no triangle contains an absorber (edges into an
  absorber come only from defects, absorbers have no out-edges, and there is no defect→defect
  edge), hence **`triFaces_m0_invariant`**: the triangle layer is horizon-free;
* `quadFaces_mono_m0` — ALL `M0`-dependence of the 2-skeleton is carried by the killed squares,
  monotonically;
* `eulerChar2` and the three-term split `eulerChar2_sector_split`:
  `χ₂ = relIndexStruct2 + killedEuler2 + #quads`, with
  **`relIndexStruct2_m0_invariant`** — census law L15 upgraded to dimension 2;
* the triple-counting laws `card_lt_pairs`/`sum_choose_two_lt`/`card_lt_triples` (the `choose 3`
  analog of the proven `choose 2` tournament law) and their geometric payoff
  **`card_triAllSurv_eq_choose_three`**: on a forward-closed window the all-survivor triangles
  are exactly the 3-chains of the survivor tournament — `C(V_S, 3)` exactly;
* kernel calibration on `cone3` (`by decide`): 4 triangles + 6 squares, `χ₂ = 5`,
  `relIndexStruct2 = −3` at EVERY horizon.

Everything here is deterministic counting — no hypotheses, no `sorry`, standard axioms only.
The gain/twist layer (rank certificates, holonomy, blindness disclosures) lives in the next
files; this one is the cell skeleton they compute on.
-/

namespace EuclidsPath
namespace OrnamentTwoComplex

open EuclidsPath.CleanGraph
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.GeometryFront
open EuclidsPath.GradedWindowComplex

/-! ### Faces -/

/-- A 2-cell of the ornament complex: a directed 2-simplex or a killed square. -/
inductive Face where
  | tri : State → State → State → Face
  | quad : ℕ → ℕ → ℕ → ℕ → Side → Side → Face
  deriving DecidableEq

/-- Numeric key of a defect label, for the canonical ordering of square corners. -/
def sideIdx : Side → ℕ
  | Side.minus => 0
  | Side.plus => 1

def quadKey (q : ℕ) (s : Side) : ℕ := 2 * q + sideIdx s

/-- The directed 2-simplices of the window: `u→v`, `v→w`, `u→w` all real edges, corners in `W`. -/
def triFaces (A M0 : ℕ) (W : Finset State) : Finset Face :=
  ((W ×ˢ W ×ˢ W).filter fun p =>
    p.2.1 ∈ outTargets A M0 p.1 ∧ p.2.2 ∈ outTargets A M0 p.2.1 ∧
      p.2.2 ∈ outTargets A M0 p.1).image fun p => Face.tri p.1 p.2.1 p.2.2

def isCenter : State → Bool
  | State.center _ => true
  | _ => false

def isDefect : State → Bool
  | State.defect _ _ _ => true
  | _ => false

def centerIdx : State → ℕ
  | State.center m => m
  | _ => 0

def defectCenter : State → ℕ
  | State.defect n _ _ => n
  | _ => 0

def centerIdxs (W : Finset State) : Finset ℕ :=
  (W.filter fun v => isCenter v = true).image centerIdx

def defectIdxs (W : Finset State) : Finset ℕ :=
  (W.filter fun v => isDefect v = true).image defectCenter

/-- Legality of a killed square `(center m, defect n q s, absorber n, defect n q' s')`. -/
def QuadLegal (A M0 : ℕ) (W : Finset State) (m n q q' : ℕ) (s s' : Side) : Prop :=
  State.center m ∈ W ∧ State.defect n q s ∈ W ∧ State.defect n q' s' ∈ W ∧
    State.absorber n ∈ W ∧
    Clean A m ∧ n < m ∧ q.Prime ∧ q ≤ A ∧ q ∣ sideValue s n ∧
    q'.Prime ∧ q' ≤ A ∧ q' ∣ sideValue s' n ∧ n ≤ M0 ∧ quadKey q s < quadKey q' s'

instance quadLegalDecidable (A M0 : ℕ) (W : Finset State) (m n q q' : ℕ) (s s' : Side) :
    Decidable (QuadLegal A M0 W m n q q' s s') := by
  unfold QuadLegal
  infer_instance

/-- The killed squares of the window (canonically ordered corner labels). -/
def quadFaces (A M0 : ℕ) (W : Finset State) : Finset Face :=
  ((centerIdxs W ×ˢ defectIdxs W ×ˢ Finset.range (A + 1) ×ˢ Finset.range (A + 1)
      ×ˢ sideFinset ×ˢ sideFinset).filter fun x =>
    QuadLegal A M0 W x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2).image fun x =>
    Face.quad x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

/-- All 2-cells. -/
def faces (A M0 : ℕ) (W : Finset State) : Finset Face :=
  triFaces A M0 W ∪ quadFaces A M0 W

/-- Triangles and squares are distinct constructors, so the union is disjoint. -/
theorem triFaces_disjoint_quadFaces (A M0 : ℕ) (W : Finset State) :
    Disjoint (triFaces A M0 W) (quadFaces A M0 W) := by
  rw [Finset.disjoint_left]
  intro f hf hg
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hg
  exact Face.noConfusion hx

theorem card_faces (A M0 : ℕ) (W : Finset State) :
    (faces A M0 W).card = (triFaces A M0 W).card + (quadFaces A M0 W).card :=
  Finset.card_union_of_disjoint (triFaces_disjoint_quadFaces A M0 W)

/-! ### The keystone: triangles never contain absorbers, hence are horizon-free -/

theorem absorber_not_target_of_center {A M0 m a : ℕ} :
    State.absorber a ∉ outTargets A M0 (State.center m) := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨-, n, -, -, heq⟩ := mem_cleanTargets.mp h
    exact State.noConfusion heq
  · obtain ⟨-, n, q, s, -, -, -, -, heq⟩ := mem_boundaryTargets.mp h
    exact State.noConfusion heq

theorem defect_not_target_of_defect {A M0 n q n' q' : ℕ} {s s' : Side} :
    State.defect n' q' s' ∉ outTargets A M0 (State.defect n q s) := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨t, os, -, -, heq⟩ := mem_peelTargets.mp h
    exact State.noConfusion heq
  · obtain ⟨-, heq⟩ := mem_absorbTargets.mp h
    exact State.noConfusion heq

theorem center_not_target_of_absorber {A M0 a m : ℕ} :
    State.center m ∉ outTargets A M0 (State.absorber a) := fun h =>
  Finset.notMem_empty _ h

/-- Membership of a NON-absorber target in an out-set never depends on the horizon. -/
theorem mem_outTargets_m0_free {A M0 M0' : ℕ} {u w : State}
    (hw : ∀ a, w ≠ State.absorber a) :
    w ∈ outTargets A M0 u ↔ w ∈ outTargets A M0' u := by
  cases u with
  | center m => rw [outTargets_center_m0_free A M0 M0' m]
  | absorber a => rfl
  | defect n q s =>
      show w ∈ peelTargets n q s ∪ absorbTargets M0 n
        ↔ w ∈ peelTargets n q s ∪ absorbTargets M0' n
      simp only [Finset.mem_union]
      have h1 : w ∉ absorbTargets M0 n := fun h => hw n (mem_absorbTargets.mp h).2
      have h2 : w ∉ absorbTargets M0' n := fun h => hw n (mem_absorbTargets.mp h).2
      tauto

/-- **No triangle contains an absorber**, in edge form: an absorber cannot be a source (no
    out-edges); as the final corner it would force two absorb edges from two defects joined
    by a defect→defect edge, which does not exist. -/
theorem no_absorber_of_tri_edges {A M0 : ℕ} {u v w : State}
    (huv : v ∈ outTargets A M0 u) (hvw : w ∈ outTargets A M0 v)
    (huw : w ∈ outTargets A M0 u) :
    (∀ a, u ≠ State.absorber a) ∧ (∀ a, v ≠ State.absorber a) ∧
      (∀ a, w ≠ State.absorber a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [ha] at huv
    exact Finset.notMem_empty _ huv
  · intro a ha
    rw [ha] at hvw
    exact Finset.notMem_empty _ hvw
  · intro a ha
    rw [ha] at huw hvw
    -- w = absorber a: then u→v with u, v both defects over center a — impossible.
    cases u with
    | center m => exact absorber_not_target_of_center huw
    | absorber b => exact Finset.notMem_empty _ huv
    | defect n q s =>
        cases v with
        | center m' =>
            -- v = center: v → absorber impossible
            exact absorber_not_target_of_center hvw
        | absorber b => exact Finset.notMem_empty _ hvw
        | defect n' q' s' => exact defect_not_target_of_defect huv

/-- **No triangle contains an absorber** — face form of `no_absorber_of_tri_edges`. -/
theorem no_absorber_in_tri {A M0 : ℕ} {W : Finset State} {u v w : State}
    (hf : Face.tri u v w ∈ triFaces A M0 W) :
    (∀ a, u ≠ State.absorber a) ∧ (∀ a, v ≠ State.absorber a) ∧
      (∀ a, w ≠ State.absorber a) := by
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hf
  obtain ⟨huv, hvw, huw⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨h1, h2, h3⟩ := Face.tri.inj heq
  subst h1; subst h2; subst h3
  exact no_absorber_of_tri_edges huv hvw huw

/-- The three edges of a triangle never mention the horizon: neither inner corner can be
    an absorber (keystone case analysis), and non-absorber targets are horizon-free. -/
theorem tri_edges_m0_free {A M0 M0' : ℕ} {u v w : State}
    (huv : v ∈ outTargets A M0 u) (hvw : w ∈ outTargets A M0 v)
    (huw : w ∈ outTargets A M0 u) :
    v ∈ outTargets A M0' u ∧ w ∈ outTargets A M0' v ∧ w ∈ outTargets A M0' u := by
  have hv : ∀ a, v ≠ State.absorber a := by
    intro a hva
    rw [hva] at hvw
    exact Finset.notMem_empty _ hvw
  have hw : ∀ a, w ≠ State.absorber a := by
    intro a hwa
    rw [hwa] at huw hvw
    -- w = absorber: reuse the keystone case analysis
    cases u with
    | center m => exact absorber_not_target_of_center huw
    | absorber b => exact Finset.notMem_empty _ huv
    | defect n q s =>
        cases v with
        | center m' => exact absorber_not_target_of_center hvw
        | absorber b => exact Finset.notMem_empty _ hvw
        | defect n' q' s' => exact defect_not_target_of_defect huv
  exact ⟨(mem_outTargets_m0_free hv).mp huv, (mem_outTargets_m0_free hw).mp hvw,
    (mem_outTargets_m0_free hw).mp huw⟩

/-- **The triangle layer is horizon-free.** -/
theorem triFaces_m0_invariant (A M0 M0' : ℕ) (W : Finset State) :
    triFaces A M0 W = triFaces A M0' W := by
  unfold triFaces
  congr 1
  apply Finset.filter_congr
  intro p hp
  constructor
  · rintro ⟨huv, hvw, huw⟩
    exact tri_edges_m0_free huv hvw huw
  · rintro ⟨huv, hvw, huw⟩
    exact tri_edges_m0_free huv hvw huw

/-- **All horizon-dependence of the 2-skeleton is monotone and lives in the killed squares.** -/
theorem quadFaces_mono_m0 {A M0 M0' : ℕ} (h : M0 ≤ M0') (W : Finset State) :
    quadFaces A M0 W ⊆ quadFaces A M0' W := by
  unfold quadFaces
  apply Finset.image_subset_image
  intro x hx
  obtain ⟨hxmem, hxlegal⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxmem, ?_⟩
  unfold QuadLegal at hxlegal ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hxlegal
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, by omega, h14⟩

/-! ### Dimension-2 Euler characteristic and the three-term sector split -/

/-- Whether all corners of a triangle are survivors / all are killed. -/
def triAllSurv (A : ℕ) : Face → Prop
  | Face.tri u v w => IsSurvivor A u ∧ IsSurvivor A v ∧ IsSurvivor A w
  | Face.quad _ _ _ _ _ _ => False

def triSurvIncident (A : ℕ) : Face → Prop
  | Face.tri u v w => IsSurvivor A u ∨ IsSurvivor A v ∨ IsSurvivor A w
  | Face.quad _ _ _ _ _ _ => False

instance (A : ℕ) (f : Face) : Decidable (triAllSurv A f) := by
  cases f <;> unfold triAllSurv <;> infer_instance

instance (A : ℕ) (f : Face) : Decidable (triSurvIncident A f) := by
  cases f <;> unfold triSurvIncident <;> infer_instance

/-- Euler characteristic of the 2-complex: `V − E + F`. -/
def eulerChar2 (A M0 : ℕ) (W : Finset State) : ℤ :=
  (W.card : ℤ) - (inducedEdges A M0 W : ℤ) + ((faces A M0 W).card : ℤ)

/-- The dimension-2 survivor-relative index: the 1-dimensional one plus the
    survivor-incident triangles. -/
def relIndexStruct2 (A M0 : ℕ) (W : Finset State) : ℤ :=
  relIndexStruct A M0 W + (((triFaces A M0 W).filter (triSurvIncident A)).card : ℤ)

/-- The dimension-2 killed Euler characteristic: killed cells, killed edges, all-killed
    triangles (squares are ledgered separately — they carry the horizon). -/
def killedEuler2 (A M0 : ℕ) (W : Finset State) : ℤ :=
  killedEuler A M0 W + (((triFaces A M0 W).filter (fun f => ¬ triSurvIncident A f)).card : ℤ)

/-- **The three-term split**: `χ₂ = relIndexStruct2 + killedEuler2 + #quads`. -/
theorem eulerChar2_sector_split (A M0 : ℕ) (W : Finset State) :
    eulerChar2 A M0 W
      = relIndexStruct2 A M0 W + killedEuler2 A M0 W + ((quadFaces A M0 W).card : ℤ) := by
  have h1 := eulerChar_sector_split A M0 W
  have h2 : ((triFaces A M0 W).filter (triSurvIncident A)).card
      + ((triFaces A M0 W).filter (fun f => ¬ triSurvIncident A f)).card
      = (triFaces A M0 W).card :=
    Finset.filter_card_add_filter_neg_card_eq_card (triSurvIncident A)
  have h3 := card_faces A M0 W
  rw [eulerChar2, relIndexStruct2, killedEuler2]
  rw [eulerChar] at h1
  push_cast [h3, ← h2]
  linarith

/-- **Census law L15 in dimension 2**: the survivor-relative index of the 2-complex contains
    no horizon.  The 1-dimensional part is `relIndexStruct_m0_invariant`; the triangle part is
    horizon-free by the keystone. -/
theorem relIndexStruct2_m0_invariant (A M0 M0' : ℕ) (W : Finset State) :
    relIndexStruct2 A M0 W = relIndexStruct2 A M0' W := by
  rw [relIndexStruct2, relIndexStruct2, relIndexStruct_m0_invariant A M0 M0' W,
    triFaces_m0_invariant A M0 M0' W]

/-! ### Triple counting: the `choose 3` law -/

/-- Summing `C(#below, 2)` over a finite set of naturals counts its 3-subsets. -/
theorem sum_choose_two_lt (I : Finset ℕ) :
    ∑ m ∈ I, ((I.filter (fun n => n < m)).card).choose 2 = I.card.choose 3 := by
  classical
  induction I using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
      have hnotmem : a ∉ s := fun h => lt_irrefl a (ha a h)
      rw [Finset.sum_insert hnotmem]
      have hterm : ((insert a s).filter (fun n => n < a)).card = s.card := by
        congr 1
        rw [Finset.filter_insert, if_neg (lt_irrefl a)]
        exact Finset.filter_true_of_mem fun x hx => ha x hx
      have hrest : ∀ m ∈ s, (((insert a s).filter (fun n => n < m)).card).choose 2
          = ((s.filter (fun n => n < m)).card).choose 2 := by
        intro m hm
        congr 2
        rw [Finset.filter_insert, if_neg (by have := ha m hm; omega)]
      rw [hterm, Finset.sum_congr rfl hrest, ih, Finset.card_insert_of_notMem hnotmem]
      have hchoose : (s.card + 1).choose 3 = s.card.choose 2 + s.card.choose 3 :=
        Nat.choose_succ_succ s.card 2
      omega

/-- Counting strictly decreasing pairs in `J × J`: the coordinate form of the pair law. -/
theorem card_lt_pairs (J : Finset ℕ) :
    ((J ×ˢ J).filter fun x => x.2 < x.1).card = J.card.choose 2 := by
  classical
  have hmem : ∀ x ∈ (J ×ˢ J).filter (fun x => x.2 < x.1), x.1 ∈ J :=
    fun x hx => (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  have key : ∀ n ∈ J,
      (((J ×ˢ J).filter (fun x => x.2 < x.1)).filter (fun x => x.1 = n)).card
        = (J.filter (fun k => k < n)).card := by
    intro n hn
    have hfiber : ((J ×ˢ J).filter (fun x => x.2 < x.1)).filter (fun x => x.1 = n)
        = {n} ×ˢ (J.filter (fun k => k < n)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        subst h4
        exact ⟨rfl, h2, h3⟩
      · rintro ⟨h4, h2, h3⟩
        subst h4
        exact ⟨⟨⟨hn, h2⟩, h3⟩, rfl⟩
    rw [hfiber, Finset.card_product, Finset.card_singleton, one_mul]
  rw [← sum_count_lt J,
    Finset.card_eq_sum_card_fiberwise (f := fun x : ℕ × ℕ => x.1) (t := J) hmem]
  exact Finset.sum_congr rfl key

/-- Counting strictly decreasing triples in `I × I × I`: fibering over the top corner
    reduces the `choose 3` count to the pair law on each lower window. -/
theorem card_lt_triples (I : Finset ℕ) :
    ((I ×ˢ I ×ˢ I).filter fun x => x.2.2 < x.2.1 ∧ x.2.1 < x.1).card
      = I.card.choose 3 := by
  classical
  have hmem : ∀ x ∈ (I ×ˢ I ×ˢ I).filter (fun x => x.2.2 < x.2.1 ∧ x.2.1 < x.1),
      x.1 ∈ I :=
    fun x hx => (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  have key : ∀ m ∈ I,
      (((I ×ˢ I ×ˢ I).filter (fun x => x.2.2 < x.2.1 ∧ x.2.1 < x.1)).filter
          (fun x => x.1 = m)).card
        = ((I.filter (fun n => n < m)).card).choose 2 := by
    intro m hm
    have hfiber : ((I ×ˢ I ×ˢ I).filter (fun x => x.2.2 < x.2.1 ∧ x.2.1 < x.1)).filter
          (fun x => x.1 = m)
        = {m} ×ˢ (((I.filter (fun n => n < m)) ×ˢ (I.filter (fun n => n < m))).filter
            (fun y => y.2 < y.1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hx1, hx21, hx22⟩, hlt1, hlt2⟩, hxm⟩
        subst hxm
        exact ⟨rfl, ⟨⟨hx21, hlt2⟩, hx22, by omega⟩, hlt1⟩
      · rintro ⟨hxm, ⟨⟨hx21, hlt21⟩, hx22, hlt22⟩, hlt⟩
        subst hxm
        exact ⟨⟨⟨hm, hx21, hx22⟩, hlt, hlt21⟩, rfl⟩
    rw [hfiber, Finset.card_product, Finset.card_singleton, one_mul,
      card_lt_pairs (I.filter (fun n => n < m))]
  rw [← sum_choose_two_lt I,
    Finset.card_eq_sum_card_fiberwise (f := fun x : ℕ × ℕ × ℕ => x.1) (t := I) hmem]
  exact Finset.sum_congr rfl key

/-! ### The survivor-triangle law: all-survivor triangles are 3-chains of the tournament -/

/-- Between two clean centers the ornament edge exists exactly when the index drops:
    the coordinate form of tournament completeness (boundary targets are defects, so the
    edge must be a clean edge, whose members satisfy `b < a`; conversely every clean pair
    with `b < a` carries the clean edge). -/
theorem center_edge_iff {A M0 a b : ℕ} (ha : Clean A a) (hb : Clean A b) :
    State.center b ∈ outTargets A M0 (State.center a) ↔ b < a := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨-, n, -, hn, heq⟩ := mem_cleanTargets.mp h
      have := State.center.inj heq
      omega
    · obtain ⟨-, n, q, s, -, -, -, -, heq⟩ := mem_boundaryTargets.mp h
      exact State.noConfusion heq
  · intro h
    exact Finset.mem_union.mpr (Or.inl (mem_cleanTargets.mpr ⟨ha, b, hb, h, rfl⟩))

/-- The survivor index set in coordinate form: `a ∈ survivorIdx A W` iff `center a` is a
    clean center of the window. -/
theorem mem_survivorIdx {A : ℕ} {W : Finset State} {a : ℕ} :
    a ∈ survivorIdx A W ↔ State.center a ∈ W ∧ Clean A a := by
  constructor
  · intro h
    obtain ⟨v, hv, hva⟩ := Finset.mem_image.mp h
    obtain ⟨hvW, hvS⟩ := Finset.mem_filter.mp hv
    cases v with
    | center m =>
        have hma : m = a := hva
        subst hma
        exact ⟨hvW, hvS⟩
    | defect n q s => exact absurd hvS (fun h => h)
    | absorber b => exact absurd hvS (fun h => h)
  · rintro ⟨hW, hclean⟩
    exact Finset.mem_image.mpr ⟨State.center a,
      Finset.mem_filter.mpr ⟨hW, hclean⟩, rfl⟩

/-- Shape of an all-survivor triangle: three clean centers of the window with strictly
    dropping indices `c < b < a` (the two consecutive edges force the drops via
    `center_edge_iff`). -/
theorem mem_filter_triAllSurv {A M0 : ℕ} {W : Finset State} {f : Face}
    (hf : f ∈ (triFaces A M0 W).filter (triAllSurv A)) :
    ∃ a b c, f = Face.tri (State.center a) (State.center b) (State.center c) ∧
      a ∈ survivorIdx A W ∧ b ∈ survivorIdx A W ∧ c ∈ survivorIdx A W ∧
      c < b ∧ b < a := by
  obtain ⟨hface, hsurv⟩ := Finset.mem_filter.mp hf
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hface
  obtain ⟨u, v, w⟩ := p
  obtain ⟨hpmem, h12, h23, h13⟩ := Finset.mem_filter.mp hp
  obtain ⟨huW, hvwW⟩ := Finset.mem_product.mp hpmem
  obtain ⟨hvW, hwW⟩ := Finset.mem_product.mp hvwW
  have hsurv' : IsSurvivor A u ∧ IsSurvivor A v ∧ IsSurvivor A w := hsurv
  obtain ⟨hsu, hsv, hsw⟩ := hsurv'
  cases u with
  | center a =>
      cases v with
      | center b =>
          cases w with
          | center c =>
              have hca : Clean A a := hsu
              have hcb : Clean A b := hsv
              have hcc : Clean A c := hsw
              exact ⟨a, b, c, rfl,
                mem_survivorIdx.mpr ⟨huW, hca⟩,
                mem_survivorIdx.mpr ⟨hvW, hcb⟩,
                mem_survivorIdx.mpr ⟨hwW, hcc⟩,
                (center_edge_iff hcb hcc).mp h23,
                (center_edge_iff hca hcb).mp h12⟩
          | defect n q s => exact absurd hsw (fun h => h)
          | absorber x => exact absurd hsw (fun h => h)
      | defect n q s => exact absurd hsv (fun h => h)
      | absorber x => exact absurd hsv (fun h => h)
  | defect n q s => exact absurd hsu (fun h => h)
  | absorber x => exact absurd hsu (fun h => h)

/-- **Survivor triangles of a forward-closed window are exactly the 3-chains of the
    tournament**: their count is `C(V_S, 3)` — the `choose 3` upgrade of
    `eSS_eq_choose_two`.  (The stated hypothesis matches the tournament interface; the
    bijection itself reads corner membership directly off `triFaces`.) -/
theorem card_triAllSurv_eq_choose_three {A M0 : ℕ} {W : Finset State}
    (hclosed : ForwardClosed A M0 W) :
    ((triFaces A M0 W).filter (triAllSurv A)).card = (survivors A W).card.choose 3 := by
  classical
  rw [← card_survivorIdx A W, ← card_lt_triples (survivorIdx A W)]
  refine Finset.card_bij (fun f _ => match f with
    | Face.tri u v w => (centerIdx u, centerIdx v, centerIdx w)
    | Face.quad _ _ _ _ _ _ => ((0 : ℕ), (0 : ℕ), (0 : ℕ))) ?_ ?_ ?_
  · intro f hf
    obtain ⟨a, b, c, rfl, ha, hb, hc, hcb, hba⟩ := mem_filter_triAllSurv hf
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hb, hc⟩⟩, hcb, hba⟩
  · intro f₁ hf₁ f₂ hf₂ h
    obtain ⟨a₁, b₁, c₁, rfl, -, -, -, -, -⟩ := mem_filter_triAllSurv hf₁
    obtain ⟨a₂, b₂, c₂, rfl, -, -, -, -, -⟩ := mem_filter_triAllSurv hf₂
    have h1 : a₁ = a₂ := congrArg (fun x : ℕ × ℕ × ℕ => x.1) h
    have h2 : b₁ = b₂ := congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) h
    have h3 : c₁ = c₂ := congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) h
    rw [h1, h2, h3]
  · intro y hy
    obtain ⟨hymem, hy1, hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨ha, hbc⟩ := Finset.mem_product.mp hymem
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    obtain ⟨haW, hca⟩ := mem_survivorIdx.mp ha
    obtain ⟨hbW, hcb⟩ := mem_survivorIdx.mp hb
    obtain ⟨hcW, hcc⟩ := mem_survivorIdx.mp hc
    have hface : Face.tri (State.center y.1) (State.center y.2.1) (State.center y.2.2)
        ∈ (triFaces A M0 W).filter (triAllSurv A) := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_image.mpr
          ⟨(State.center y.1, State.center y.2.1, State.center y.2.2), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩
        · exact Finset.mem_product.mpr ⟨haW, Finset.mem_product.mpr ⟨hbW, hcW⟩⟩
        · exact (center_edge_iff hca hcb).mpr hy2
        · exact (center_edge_iff hcb hcc).mpr hy1
        · exact (center_edge_iff hca hcc).mpr (lt_trans hy1 hy2)
      · exact ⟨hca, hcb, hcc⟩
    exact ⟨_, hface, rfl⟩

/-! ### Kernel calibration on `cone3` -/

set_option maxRecDepth 10000 in
/-- The calibration cone carries exactly 4 triangles: the mixed `(c₃, c₂, defect)` faces
    over the four common defect targets of centers 3 and 2 — as designed. -/
theorem triFaces_cone3_card : (triFaces 5 4 cone3).card = 4 := by decide

set_option maxRecDepth 10000 in
/-- 6 killed squares: for each clean center `m ∈ {3, 2}` the three ordered pairs of the
    grave defects `(0,2,−), (0,3,−), (0,5,−)` close through `absorber 0`. -/
theorem quadFaces_cone3_card : (quadFaces 5 4 cone3).card = 6 := by decide

set_option maxRecDepth 10000 in
/-- `χ₂(cone3) = 9 − 14 + 10 = 5`. -/
theorem eulerChar2_cone3 : eulerChar2 5 4 cone3 = 5 := by decide

set_option maxRecDepth 10000 in
/-- `relIndexStruct2(cone3) = −7 + 4 = −3`: all four triangles are survivor-incident. -/
theorem relIndexStruct2_cone3 : relIndexStruct2 5 4 cone3 = -3 := by decide

/-- Horizon invisibility, calibrated: the dimension-2 relative index of the cone is `−3`
    at EVERY absorber horizon. -/
theorem relIndexStruct2_cone3_all_horizons (M0 : ℕ) :
    relIndexStruct2 5 M0 cone3 = -3 := by
  rw [relIndexStruct2_m0_invariant 5 M0 4 cone3]
  exact relIndexStruct2_cone3

end OrnamentTwoComplex
end EuclidsPath
