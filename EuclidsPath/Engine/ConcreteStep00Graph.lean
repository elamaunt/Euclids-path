/-
  ConcreteStep00Graph — the CONCRETE Step00 graph for the 6m±1 branch (not the abstract σ) + lexicographic height.
  Source: EuclidsPath_concrete_step00_graph_patch + EuclidsPath_step00_lex_height_patch.
  Prose: prose/24_BoundaryDecomp.md (section "The concrete 6m±1 graph and lex-height").

  Builds a real graph: State (center/defect/absorber), inductive RealStep (clean/boundary/peel/absorb)
  with PeelCert arithmetic (6n±1 = q·(6t±1)), Legal via Clean/divisibility. NOT vacuous.
  THE KEY POINT: `lexRank = 3·center + phase` (center=2,defect=1,absorber=0) STRICTLY DROPS on EVERY edge,
  including absorb (where the center is preserved — phase 1→0). The height μ is PROVEN here, not an input.
  Remainder of the bounded package: ledger-projection + ∞-family of defects + collision-resolve. Does NOT close Step00.
-/
import EuclidsPath.Engine.CleanGraph
import EuclidsPath.Engine.BoundaryDefectPayment
import EuclidsPath.Engine.BoundaryLedgerCollision
import EuclidsPath.Engine.LabelledFanIn
import EuclidsPath.Engine.Residuals
import EuclidsPath.Engine.MkNode
import EuclidsPath.Engine.RigidClose
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath
namespace ConcreteStep00Graph

open EuclidsPath.CleanGraph
open EuclidsPath.BoundaryDefectPayment
open EuclidsPath.BoundaryLedgerCollision
open EuclidsPath.LabelledFanIn



/-#############################################################################
  §1. Arithmetic sides and states
#############################################################################-/

/-- Which side of a centre is carrying the obstruction: `6n-1` or `6n+1`. -/
inductive Side where
  | minus
  | plus
deriving DecidableEq

/-- The natural number represented by the chosen side of centre `n`. -/
def sideValue : Side → ℕ → ℕ
  | Side.minus, n => 6 * n - 1
  | Side.plus,  n => 6 * n + 1

/-- Indexing a side inside a finite key. -/
def sideIndex : Side → Fin 2
  | Side.minus => ⟨0, by decide⟩
  | Side.plus  => ⟨1, by decide⟩

/--
Concrete Step00 state space.

`center m` is a clean-core centre candidate.
`defect n q side` is the first material boundary defect: `q ∣ 6n±1`.
`absorber a` is an old endpoint, intended to satisfy `a ≤ M0` under `Legal`.
-/
inductive State where
  | center   : ℕ → State
  | defect   : ℕ → ℕ → Side → State
  | absorber : ℕ → State
deriving DecidableEq

/-- Centre coordinate of a concrete Step00 state. -/
def centerOf : State → ℕ
  | State.center m       => m
  | State.defect n _ _   => n
  | State.absorber a     => a

/--
Concrete legality predicate for the Step00 graph at sieve scale `A` and old
bound `M0`.
-/
def Legal (A M0 : ℕ) : State → Prop
  | State.center m       => Clean A m
  | State.defect n q s   => q.Prime ∧ q ≤ A ∧ q ∣ sideValue s n
  | State.absorber a     => a ≤ M0

/-- Freshness means that the state lies above the old twin bound. -/
def Fresh (M0 : ℕ) (U : State) : Prop := M0 < centerOf U

/-- Old absorbers are exactly absorber states below the old bound. -/
def OldAbsorber (M0 : ℕ) : State → Prop
  | State.absorber a => a ≤ M0
  | _                => False

/-- State-level defect predicate: the state itself is a legal small-prime defect. -/
def Defective (A : ℕ) : State → Prop
  | State.defect n q s => q.Prime ∧ q ≤ A ∧ q ∣ sideValue s n
  | _                  => False

/-- The `SmallPrimeDefect` predicate from the previous patch is carried by every legal defect state. -/
theorem smallPrimeDefect_of_defective {A n q : ℕ} {s : Side}
    (h : Defective A (State.defect n q s)) : SmallPrimeDefect A n := by
  rcases h with ⟨hqPrime, hqA, hdiv⟩
  refine ⟨q, hqPrime, hqA, ?_⟩
  cases s with
  | minus => exact Or.inl hdiv
  | plus  => exact Or.inr hdiv

/-- A legal defect state is exactly a state-level defect. -/
theorem defective_of_legal_defect {A M0 n q : ℕ} {s : Side}
    (h : Legal A M0 (State.defect n q s)) : Defective A (State.defect n q s) := h

/-- A legal defect state is not clean at its centre. -/
theorem not_clean_of_legal_defect {A M0 n q : ℕ} {s : Side}
    (h : Legal A M0 (State.defect n q s)) : ¬ Clean A n := by
  intro hClean
  rcases h with ⟨hqPrime, hqA, hdiv⟩
  have hbad : q ∣ (6 * n - 1) ∨ q ∣ (6 * n + 1) := by
    cases s with
    | minus => exact Or.inl hdiv
    | plus  => exact Or.inr hdiv
  exact hClean q hqPrime hqA hbad

/-#############################################################################
  §2. Real Step00 transitions
#############################################################################-/

/--
An explicit arithmetic old-peel certificate.

This is the part that must eventually be connected to `cofactor_is_center` in the
full arithmetic development: a defect side `6n±1` factors as the defect prime
`q` times a new twin-side `6t±1`, and the resulting centre is smaller.
-/
structure PeelCert (n q t : ℕ) (inSide outSide : Side) : Prop where
  factor : sideValue inSide n = q * sideValue outSide t
  smaller : t < n

/--
Concrete real transition relation for the Step00 boundary graph.
-/
inductive RealStep (A M0 : ℕ) : State → State → Prop
  | clean {m n : ℕ}
      (h : CleanActiveEdge A m n) :
      RealStep A M0 (State.center m) (State.center n)
  | boundary {m n q : ℕ} {s : Side}
      (hmClean : Clean A m)
      (hEdge : ActiveEdge A m n)
      (hqPrime : q.Prime)
      (hqA : q ≤ A)
      (hdiv : q ∣ sideValue s n) :
      RealStep A M0 (State.center m) (State.defect n q s)
  | peel {n q t : ℕ} {inSide outSide : Side}
      (h : PeelCert n q t inSide outSide) :
      RealStep A M0 (State.defect n q inSide) (State.center t)
  | absorb {n q : ℕ} {s : Side}
      (hOld : n ≤ M0) :
      RealStep A M0 (State.defect n q s) (State.absorber n)

/-- Clean active edges become concrete real steps between centre states. -/
theorem realStep_of_cleanActiveEdge {A M0 m n : ℕ}
    (h : CleanActiveEdge A m n) :
    RealStep A M0 (State.center m) (State.center n) :=
  RealStep.clean h

/--
A boundary exit produces an actual legal defect state and a concrete real edge
from the clean centre into that defect state.
-/
theorem boundaryExit_to_defectStep {A M0 m n : ℕ}
    (hExit : BoundaryExit A m n) :
    ∃ q s,
      Legal A M0 (State.center m) ∧
      Legal A M0 (State.defect n q s) ∧
      Defective A (State.defect n q s) ∧
      RealStep A M0 (State.center m) (State.defect n q s) := by
  rcases hExit with ⟨hmClean, hEdge, hnNotClean⟩
  have hSmall : SmallPrimeDefect A n :=
    boundaryExit_has_smallPrimeDefect ⟨hmClean, hEdge, hnNotClean⟩
  rcases hSmall with ⟨q, hqPrime, hqA, hside⟩
  rcases hside with hminus | hplus
  · refine ⟨q, Side.minus, hmClean, ?_, ?_, ?_⟩
    · exact ⟨hqPrime, hqA, hminus⟩
    · exact ⟨hqPrime, hqA, hminus⟩
    · exact RealStep.boundary hmClean hEdge hqPrime hqA hminus
  · refine ⟨q, Side.plus, hmClean, ?_, ?_, ?_⟩
    · exact ⟨hqPrime, hqA, hplus⟩
    · exact ⟨hqPrime, hqA, hplus⟩
    · exact RealStep.boundary hmClean hEdge hqPrime hqA hplus

/-- A centre-to-centre real step strictly decreases the centre coordinate. -/
theorem center_decreases_of_clean_step {A M0 m n : ℕ}
    (h : RealStep A M0 (State.center m) (State.center n)) : n < m := by
  cases h with
  | clean hCleanEdge => exact hCleanEdge.2.2.2

/-- A centre-to-defect boundary step strictly decreases the centre coordinate. -/
theorem center_decreases_of_boundary_step {A M0 m n q : ℕ} {s : Side}
    (h : RealStep A M0 (State.center m) (State.defect n q s)) : n < m := by
  cases h with
  | boundary _ hEdge _ _ _ => exact hEdge.2

/-- An arithmetic peel step strictly decreases the centre coordinate. -/
theorem center_decreases_of_peel_step {A M0 n q t : ℕ} {inSide outSide : Side}
    (h : RealStep A M0 (State.defect n q inSide) (State.center t)) : t < n := by
  cases h with
  | peel hcert => exact hcert.smaller

/-- Absorption lands in an old absorber. -/
theorem oldAbsorber_of_absorb_step {A M0 n q : ℕ} {s : Side}
    (h : RealStep A M0 (State.defect n q s) (State.absorber n)) :
    OldAbsorber M0 (State.absorber n) := by
  cases h with
  | absorb hOld => exact hOld

/-#############################################################################
  §3. Labels, kinds, and finite ledger keys
#############################################################################-/

/-- Bounded natural index used by finite envelopes. -/
noncomputable def boundedIndex (B x : ℕ) : Fin (B + 1) :=
  if h : x ≤ B then ⟨x, Nat.lt_succ_of_le h⟩ else ⟨0, Nat.succ_pos B⟩

/-- A finite envelope for old absorber / small-prime / side data. -/
abbrev LedgerKey (A M0 : ℕ) := Fin (M0 + 1) × Fin (A + 1) × Fin 2

/--
A ledger projection is the real normalized key map.

The type of the key is finite by construction, but the mathematical content is
in choosing a semantically correct `key`.  This file therefore does not bake in a
fake projection as the proof-relevant one.
-/
structure LedgerProjection (A M0 : ℕ) where
  key : State → LedgerKey A M0

/--
A harmless finite envelope key.  It is useful for experiments, but the main
obligations below are parameterized by `LedgerProjection` to avoid pretending
that this default truncation is the real Step00 ledger.
-/
noncomputable def finiteEnvelopeKey (A M0 : ℕ) : State → LedgerKey A M0
  | State.center m       => (boundedIndex M0 m, boundedIndex A 0, sideIndex Side.minus)
  | State.defect n q s   => (boundedIndex M0 n, boundedIndex A q, sideIndex s)
  | State.absorber a     => (boundedIndex M0 a, boundedIndex A 0, sideIndex Side.plus)

/-- A total edge kind classifier compatible with the existing labelled-fan-in API. -/
def edgeKind : State → State → Kind
  | State.center _, State.center _       => Kind.active
  | State.center _, State.defect _ _ _   => Kind.boundary
  | State.defect _ _ _, State.center _   => Kind.oldPeel
  | State.defect _ _ _, State.absorber _ => Kind.oldPeel
  | _, _                                 => Kind.corridor

/-- A finite edge signature envelope: source centre, defect prime, side. -/
abbrev EdgeSig (A M0 : ℕ) := Fin (M0 + 1) × Fin (A + 1) × Fin 2

/--
A simple finite edge signature.  Like `finiteEnvelopeKey`, this is only an
envelope.  Any final proof must justify that the chosen signature is the correct
normal form for the intended collision argument.
-/
noncomputable def edgeSig (A M0 : ℕ) : State → State → EdgeSig A M0
  | State.center m,     State.center _       => (boundedIndex M0 m, boundedIndex A 0, sideIndex Side.minus)
  | State.center _,     State.defect _ q s   => (boundedIndex M0 0, boundedIndex A q, sideIndex s)
  | State.defect n q s, State.center _       => (boundedIndex M0 n, boundedIndex A q, sideIndex s)
  | State.defect n q s, State.absorber _     => (boundedIndex M0 n, boundedIndex A q, sideIndex s)
  | U,                  _                    => (boundedIndex M0 (centerOf U), boundedIndex A 0, sideIndex Side.plus)

/-#############################################################################
  §4. The concrete obligations after the graph has been built
#############################################################################-/

/--
The remaining collision-resolution law, now specialized to the concrete Step00
state space and real transition relation.
-/
abbrev ConcreteLedgerCollisionResolves (A M0 : ℕ) (proj : LedgerProjection A M0) : Prop :=
  BoundaryLedgerCollisionResolves
    (σ := State) (Key := LedgerKey A M0)
    (RealStep A M0) (Legal A M0) (Fresh M0) (Defective A)
    proj.key BoundaryDefectPayment.ImpossiblePayment

/--
An infinite family of actual legal fresh defect states for the concrete graph.

This is the non-vacuity obligation: finite twins must eventually produce a set
`S` satisfying this predicate.  Without such an inhabited infinite family, the
ledger collision branch is vacuous.
-/
abbrev InfiniteFreshDefectFamily (A M0 : ℕ) (S : Set State) : Prop :=
  S.Infinite ∧ ∀ U ∈ S, Fresh M0 U ∧ Defective A U ∧ Legal A M0 U

/--
The concrete graph version of the previously abstract branch theorem.

If the concrete graph has infinitely many fresh legal defect states and the real
ledger projection resolves key collisions, then a legal nonempty cycle exists in
this very graph.  The payment branch is burned by the already-proved
`impossiblePayment_false`.
-/
theorem infinite_fresh_defects_force_concrete_cycle
    {A M0 : ℕ} {S : Set State} (proj : LedgerProjection A M0)
    (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : ConcreteLedgerCollisionResolves A M0 proj) :
    LegalCycle (RealStep A M0) (Legal A M0) := by
  rcases hS with ⟨hInf, hMem⟩
  exact infinite_defect_flows_force_cycle
    (σ := State) (Key := LedgerKey A M0)
    (RealStep := RealStep A M0) (Legal := Legal A M0)
    (Fresh := Fresh M0) (Defective := Defective A)
    (ImpossiblePayment := BoundaryDefectPayment.ImpossiblePayment)
    (S := S) hInf hMem proj.key hResolve
    BoundaryDefectPayment.impossiblePayment_false

/--
With the existing `CycleBridge`, the same concrete cycle gives the current
Euclidean engine proposition.
-/
theorem infinite_fresh_defects_force_concrete_engine
    {A M0 : ℕ} {S : Set State} {EuclideanEngine : Prop}
    (proj : LedgerProjection A M0)
    (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : ConcreteLedgerCollisionResolves A M0 proj)
    (hBridge : CycleBridge (RealStep := RealStep A M0) (Legal A M0) EuclideanEngine) :
    EuclideanEngine := by
  exact hBridge (infinite_fresh_defects_force_concrete_cycle proj hS hResolve)

/--
Under a concrete local height witness, the same package is contradictory.

This is the final anti-vacuum detector for the concrete graph:

  infinite fresh legal defects
  + finite ledger projection
  + collision resolution
  + strict local height
  --------------------------------------------------
  False.
-/
theorem infinite_fresh_defects_impossible_under_concrete_height
    {A M0 : ℕ} {S : Set State}
    (proj : LedgerProjection A M0)
    (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : ConcreteLedgerCollisionResolves A M0 proj)
    (height : State → ℕ)
    (hdrop : ∀ {U V : State}, RealStep A M0 U V → height U < height V) :
    False := by
  exact infinite_defect_flows_impossible_under_height
    (σ := State) (Key := LedgerKey A M0)
    (RealStep := RealStep A M0) (Legal := Legal A M0)
    (Fresh := Fresh M0) (Defective := Defective A)
    (ImpossiblePayment := BoundaryDefectPayment.ImpossiblePayment)
    (S := S) hS.1 hS.2 proj.key hResolve
    BoundaryDefectPayment.impossiblePayment_false height hdrop

/-#############################################################################
  §5. A single package name for the remaining Step00 task
#############################################################################-/

/--
A concrete Step00 package sufficient to collapse the boundary branch.

This is not asserted to exist.  It states exactly what must now be built for the
real `6m±1` programme:

1. a semantically correct finite ledger projection `proj`;
2. an infinite family of actual fresh legal defect states;
3. a local collision-resolution theorem for this concrete graph;
4. a local height witness, if the intended closure is by EPMI/acyclicity.
-/
structure ConcreteStep00CollapsePackage (A M0 : ℕ) where
  proj : LedgerProjection A M0
  S : Set State
  infiniteFreshDefects : InfiniteFreshDefectFamily A M0 S
  collisionResolves : ConcreteLedgerCollisionResolves A M0 proj
  height : State → ℕ
  heightStrict : ∀ {U V : State}, RealStep A M0 U V → height U < height V

/-- Any concrete collapse package gives contradiction. -/
theorem concreteStep00CollapsePackage_false {A M0 : ℕ}
    (P : ConcreteStep00CollapsePackage A M0) : False := by
  exact infinite_fresh_defects_impossible_under_concrete_height
    P.proj P.infiniteFreshDefects P.collisionResolves P.height P.heightStrict

/--
Audit name for the next real construction task.

Compared with the earlier abstract `σ`-based patches, this obligation is now
attached to the concrete `State`, `RealStep`, `Legal`, `Fresh`, and `Defective`
objects above.
-/
abbrev TheConcreteGraphObligation (A M0 : ℕ) : Prop :=
  ∃ P : ConcreteStep00CollapsePackage A M0, True



/-#############################################################################
  §1. Phase refinement of the centre coordinate
#############################################################################-/

/--
Phase of a concrete Step00 state.

The ordering is chosen so that the natural rank

  `3 * centerOf U + phase U`

strictly decreases along same-centre terminal absorption:

  `defect n q side -> absorber n` gives `3n + 0 < 3n + 1`.
-/
def phase : State → ℕ
  | State.center _      => 2
  | State.defect _ _ _  => 1
  | State.absorber _    => 0

/-- The opposite phase used by bounded co-height. -/
def coPhase : State → ℕ
  | State.center _      => 0
  | State.defect _ _ _  => 1
  | State.absorber _    => 2

/--
Unbounded lexicographic rank.  This is the intrinsic local descent coordinate.
It strictly decreases along concrete Step00 edges.
-/
def lexRank (U : State) : ℕ :=
  3 * centerOf U + phase U

/--
Bounded lexicographic co-height.

This has the orientation expected by the existing `cycleBridge_of_height`:
if `RealStep U V`, then `lexCoHeight B U < lexCoHeight B V`, provided both
centres lie under the same explicit bound `B`.
-/
def lexCoHeight (B : ℕ) (U : State) : ℕ :=
  3 * (B - centerOf U) + coPhase U

/-#############################################################################
  §2. The intrinsic descent theorem: no bound needed
#############################################################################-/

/--
The concrete Step00 lexicographic rank strictly decreases along every real edge.

This is the direct formal fix for the absorb-edge obstruction:
`centerOf` is constant on `defect n q side -> absorber n`, but `phase` drops
from `1` to `0`.
-/
theorem lexRank_strict_decrease_on_RealStep
    {A M0 : ℕ} {U V : State}
    (h : RealStep A M0 U V) :
    lexRank V < lexRank U := by
  cases h with
  | clean hCleanEdge =>
      -- `CleanActiveEdge A m n` contains `ActiveEdge A m n`, hence `n < m`.
      have hdesc : _ < _ := hCleanEdge.2.2.2
      dsimp [lexRank, centerOf, phase]
      omega
  | boundary hmClean hEdge hqPrime hqA hdiv =>
      -- Boundary edges also carry the active-edge descent `n < m`.
      have hdesc : _ < _ := hEdge.2
      dsimp [lexRank, centerOf, phase]
      omega
  | peel hcert =>
      -- Arithmetic old-peel exposes the smaller centre `t < n`.
      have hdesc : _ < _ := hcert.smaller
      dsimp [lexRank, centerOf, phase]
      omega
  | absorb hOld =>
      -- The centre is unchanged; the phase supplies the strict drop.
      dsimp [lexRank, centerOf, phase]
      omega

/--
A same-centre absorb edge is exactly the case that the bare centre cannot see,
but `lexRank` does see.
-/
theorem lexRank_strict_on_absorb
    {A M0 n q : ℕ} {s : Side} (hOld : n ≤ M0) :
    lexRank (State.absorber n) < lexRank (State.defect n q s) := by
  exact lexRank_strict_decrease_on_RealStep
    (A := A) (M0 := M0)
    (U := State.defect n q s) (V := State.absorber n)
    (RealStep.absorb hOld)

/-#############################################################################
  §3. Bounded co-height in the direction required by cycleBridge_of_height
#############################################################################-/

/-- Legal plus a visible global centre bound. -/
def BoundedLegal (A M0 B : ℕ) (U : State) : Prop :=
  Legal A M0 U ∧ centerOf U ≤ B

/--
The concrete transition relation restricted to the bounded window.

The existing `cycleBridge_of_height` consumes a bare relation, not a relation plus
separate legal endpoint assumptions.  Therefore the bounded height witness must
be attached to this bounded subgraph rather than to the unrestricted
`RealStep A M0`.
-/
def BoundedRealStep (A M0 B : ℕ) (U V : State) : Prop :=
  RealStep A M0 U V ∧ centerOf U ≤ B ∧ centerOf V ≤ B

/-- Bounded fresh defect family, now with the same explicit bound on every state. -/
abbrev InfiniteBoundedFreshDefectFamily (A M0 B : ℕ) (S : Set State) : Prop :=
  S.Infinite ∧ ∀ U ∈ S, Fresh M0 U ∧ Defective A U ∧ BoundedLegal A M0 B U

/-- Collision-resolution law specialized to bounded legality. -/
abbrev BoundedConcreteLedgerCollisionResolves
    (A M0 B : ℕ) (proj : LedgerProjection A M0) : Prop :=
  BoundaryLedgerCollisionResolves
    (σ := State) (Key := LedgerKey A M0)
    (BoundedRealStep A M0 B) (BoundedLegal A M0 B) (Fresh M0) (Defective A)
    proj.key BoundaryDefectPayment.ImpossiblePayment

/--
Bounded co-height strictly increases along every concrete Step00 edge.

This is the version that can be fed directly to `cycleBridge_of_height`, whose
local-height orientation is `height U < height V` along `RealStep U V`.
The bound hypotheses are explicit; this patch does not pretend that all
concrete states are globally bounded.
-/
theorem lexCoHeight_strict_on_RealStep_of_bounds
    {A M0 B : ℕ} {U V : State}
    (hU : centerOf U ≤ B)
    (hV : centerOf V ≤ B)
    (h : RealStep A M0 U V) :
    lexCoHeight B U < lexCoHeight B V := by
  cases h with
  | clean hCleanEdge =>
      have hdesc : _ < _ := hCleanEdge.2.2.2
      dsimp [lexCoHeight, centerOf, coPhase] at *
      omega
  | boundary hmClean hEdge hqPrime hqA hdiv =>
      have hdesc : _ < _ := hEdge.2
      dsimp [lexCoHeight, centerOf, coPhase] at *
      omega
  | peel hcert =>
      have hdesc : _ < _ := hcert.smaller
      dsimp [lexCoHeight, centerOf, coPhase] at *
      omega
  | absorb hOld =>
      dsimp [lexCoHeight, centerOf, coPhase] at *
      omega

/-- The same bounded co-height theorem for the bounded subgraph relation. -/
theorem lexCoHeight_strict_on_BoundedRealStep
    {A M0 B : ℕ} {U V : State}
    (h : BoundedRealStep A M0 B U V) :
    lexCoHeight B U < lexCoHeight B V := by
  exact lexCoHeight_strict_on_RealStep_of_bounds
    (A := A) (M0 := M0) (B := B)
    h.2.1 h.2.2 h.1

/-#############################################################################
  §4. The bounded branch closes with the new concrete height
#############################################################################-/

/--
If the infinite defect family is bounded and the bounded ledger-collision
resolution is supplied, the bounded branch is contradictory by the concrete
lexicographic co-height.

This is the honest EPMI form: the height is no longer a black box, but the proof
requires a real bound `B` on all legal states involved in the branch.
-/
theorem infinite_bounded_fresh_defects_impossible_by_lexCoHeight
    {A M0 B : ℕ} {S : Set State}
    (proj : LedgerProjection A M0)
    (hS : InfiniteBoundedFreshDefectFamily A M0 B S)
    (hResolve : BoundedConcreteLedgerCollisionResolves A M0 B proj) :
    False := by
  exact infinite_defect_flows_impossible_under_height
    (σ := State) (Key := LedgerKey A M0)
    (RealStep := BoundedRealStep A M0 B)
    (Legal := BoundedLegal A M0 B)
    (Fresh := Fresh M0)
    (Defective := Defective A)
    (ImpossiblePayment := BoundaryDefectPayment.ImpossiblePayment)
    (S := S)
    hS.1 hS.2 proj.key hResolve
    BoundaryDefectPayment.impossiblePayment_false
    (lexCoHeight B)
    (by
      intro U V hStep
      exact lexCoHeight_strict_on_BoundedRealStep
        (A := A) (M0 := M0) (B := B) hStep)

/-#############################################################################
  §5. Named package for the now-explicit bounded Step00 obligation
#############################################################################-/

/--
A bounded concrete Step00 collapse package.

Compared with the previous package, the height witness is no longer a field.
It is supplied by `lexCoHeight B`.  The package must instead provide the real
boundedness of the defect family and the bounded collision-resolution law.
-/
structure BoundedConcreteStep00CollapsePackage (A M0 B : ℕ) where
  proj : LedgerProjection A M0
  S : Set State
  infiniteBoundedFreshDefects : InfiniteBoundedFreshDefectFamily A M0 B S
  collisionResolves : BoundedConcreteLedgerCollisionResolves A M0 B proj

/-- Any bounded concrete package collapses by the explicit lexicographic height. -/
theorem boundedConcreteStep00CollapsePackage_false
    {A M0 B : ℕ} (P : BoundedConcreteStep00CollapsePackage A M0 B) : False := by
  exact infinite_bounded_fresh_defects_impossible_by_lexCoHeight
    P.proj P.infiniteBoundedFreshDefects P.collisionResolves

/--
The remaining concrete obligation after the lexicographic height patch.

The missing work is no longer a mysterious height `μ`: for bounded branches,
`lexCoHeight B` supplies it.  The remaining input is to build an actual bounded
fresh defect family and a concrete bounded ledger-collision resolution law.
-/
abbrev TheBoundedConcreteGraphObligation (A M0 B : ℕ) : Prop :=
  ∃ P : BoundedConcreteStep00CollapsePackage A M0 B, True

/-! ### §6–8. Unconditional (global) acyclicity from lexRank

The decreasing ℕ-rank `lexRank` BY ITSELF forbids cycles (well-founded), without the boundary `B` and without co-height.
Source: EuclidsPath_step00_lexRank_acyclic_patch. The anti-cycle side is discharged GLOBALLY. -/

/-- A rank strictly decreasing along an edge weakly decreases along any path. -/
theorem pathN_rank_le_of_step_decrease
    {α : Type*} {R : α → α → Prop} {rank : α → ℕ}
    (hstep : ∀ {U V : α}, R U V → rank V < rank U) :
    ∀ {n : ℕ} {X Y : α}, PathN R n X Y → rank Y ≤ rank X := by
  intro n
  induction n with
  | zero => intro X Y h; dsimp [PathN] at h; cases h; exact le_rfl
  | succ n ih =>
      intro X Y h
      dsimp [PathN] at h
      rcases h with ⟨Z, hXZ, hZY⟩
      exact Nat.le_trans (ih hZY) (Nat.le_of_lt (hstep hXZ))

/-- A strictly decreasing rank strictly decreases along a NONEMPTY path. -/
theorem pathN_rank_strict_of_pos_of_step_decrease
    {α : Type*} {R : α → α → Prop} {rank : α → ℕ}
    (hstep : ∀ {U V : α}, R U V → rank V < rank U) :
    ∀ {n : ℕ} {X Y : α}, 0 < n → PathN R n X Y → rank Y < rank X := by
  intro n
  cases n with
  | zero => intro X Y hpos _; omega
  | succ n =>
      intro X Y _ hpath
      dsimp [PathN] at hpath
      rcases hpath with ⟨Z, hXZ, hZY⟩
      exact lt_of_le_of_lt (pathN_rank_le_of_step_decrease (R := R) (rank := rank) hstep hZY)
        (hstep hXZ)

/-- A strict ℕ-descent along an edge forbids a nonempty self-path (direct well-founded, without co-height). -/
theorem no_nonemptyPath_of_step_decrease
    {α : Type*} {R : α → α → Prop} {rank : α → ℕ}
    (hstep : ∀ {U V : α}, R U V → rank V < rank U) (W : α) :
    ¬ NonemptyPath R W W := by
  rintro ⟨n, hpos, hPathN⟩
  exact Nat.lt_irrefl (rank W)
    (pathN_rank_strict_of_pos_of_step_decrease (R := R) (rank := rank) hstep hpos hPathN)

/-- **The concrete Step00 graph is acyclic GLOBALLY** (unconditionally, from `lexRank`). -/
theorem no_concrete_nonemptyPath_by_lexRank {A M0 : ℕ} (W : State) :
    ¬ NonemptyPath (RealStep A M0) W W :=
  no_nonemptyPath_of_step_decrease (R := RealStep A M0) (rank := lexRank)
    (fun hStep => lexRank_strict_decrease_on_RealStep hStep) W

/-- No legal cycle in the concrete graph (form for ledger-collision). -/
theorem no_concrete_legalCycle_by_lexRank {A M0 : ℕ} :
    ¬ LegalCycle (RealStep A M0) (Legal A M0) := by
  rintro ⟨W, _hLegal, hPath⟩
  exact no_concrete_nonemptyPath_by_lexRank (A := A) (M0 := M0) W hPath

/-- ∞ fresh defects + collision-resolve ⟹ `False` DIRECTLY from `lexRank` (without the boundary `B`). -/
theorem infinite_fresh_defects_impossible_by_lexRank
    {A M0 : ℕ} {S : Set State}
    (proj : LedgerProjection A M0)
    (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : ConcreteLedgerCollisionResolves A M0 proj) : False :=
  no_concrete_legalCycle_by_lexRank (A := A) (M0 := M0)
    (infinite_fresh_defects_force_concrete_cycle (A := A) (M0 := M0) (S := S) proj hS hResolve)

/-- Unbounded package: without the height field and without `B` (anti-cycle = `lexRank`). -/
structure UnboundedConcreteStep00CollapsePackage (A M0 : ℕ) where
  proj : LedgerProjection A M0
  S : Set State
  infiniteFreshDefects : InfiniteFreshDefectFamily A M0 S
  collisionResolves : ConcreteLedgerCollisionResolves A M0 proj

/-- Any unbounded package collapses by `lexRank`. -/
theorem unboundedConcreteStep00CollapsePackage_false {A M0 : ℕ}
    (P : UnboundedConcreteStep00CollapsePackage A M0) : False :=
  infinite_fresh_defects_impossible_by_lexRank P.proj P.infiniteFreshDefects P.collisionResolves

/-- Remainder after global acyclicity: THREE positive inputs (proj, ∞-family, resolve). -/
abbrev TheUnboundedConcreteGraphObligation (A M0 : ℕ) : Prop :=
  ∃ P : UnboundedConcreteStep00CollapsePackage A M0, True


/-! ### §9. The PROPER unbounded ledger graph (not vacuous: State ∞, Key finite).
Source: EuclidsPath_proper_unbounded_ledger_graph_patch. Replaces the vacuous finite-strict:
pigeonhole on an infinite subset of the UNBOUNDED State → finite ledger-key. -/

namespace ProperUnboundedLedgerGraph

open EuclidsPath.BoundaryLedgerCollision
open EuclidsPath.BoundaryDefectPayment
open EuclidsPath.LabelledFanIn

/-#############################################################################
  §1. Semantic finite ledger projection and quotient graph
#############################################################################-/

/--
A semantic finite ledger projection for the concrete unbounded Step00 graph.

`Key` is the finite ledger vertex type.  It should encode only bounded old data
(absorber slot, side/payment class, normalized finite signature, etc.), not the
unbounded centre or full trace.  The mathematical correctness of that encoding
is not hidden here; it is consumed later as the collision-resolution law.
-/
structure SemanticLedgerProjection (A M0 : ℕ) where
  Key : Type
  finiteKey : Finite Key
  key : State → Key

/-- The finite vertex type of the semantic ledger quotient graph. -/
abbrev Vertex {A M0 : ℕ} (proj : SemanticLedgerProjection A M0) : Type := proj.Key

/-- The vertex type of the semantic ledger quotient graph is finite. -/
instance finiteVertex {A M0 : ℕ} (proj : SemanticLedgerProjection A M0) :
    Finite (Vertex proj) :=
  proj.finiteKey

/--
The finite ledger quotient edge relation.

A ledger edge `K -> L` exists exactly when it is induced by an actual concrete
Step00 edge `U -> V` between legal concrete states whose keys are `K` and `L`.
-/
def LedgerEdge {A M0 : ℕ} (proj : SemanticLedgerProjection A M0)
    (K L : Vertex proj) : Prop :=
  ∃ U V : State,
    Legal A M0 U ∧ Legal A M0 V ∧
    RealStep A M0 U V ∧
    proj.key U = K ∧ proj.key V = L

/-- A small bundled finite graph object for the semantic ledger quotient. -/
structure LedgerQuotientGraph (A M0 : ℕ) where
  proj : SemanticLedgerProjection A M0
  Edge : Vertex proj → Vertex proj → Prop := LedgerEdge proj

/-- The vertices of a ledger quotient graph are finite by construction. -/
instance quotientGraphVertexFinite {A M0 : ℕ} (G : LedgerQuotientGraph A M0) :
    Finite (Vertex G.proj) :=
  G.proj.finiteKey

/-- Every legal concrete real edge projects to a finite ledger edge. -/
theorem ledgerEdge_of_realStep {A M0 : ℕ} (proj : SemanticLedgerProjection A M0)
    {U V : State}
    (hU : Legal A M0 U) (hV : Legal A M0 V)
    (hStep : RealStep A M0 U V) :
    LedgerEdge proj (proj.key U) (proj.key V) := by
  exact ⟨U, V, hU, hV, hStep, rfl, rfl⟩

/--
Membership predicate for a ledger vertex occupied by a concrete fresh legal
defect from a set `S`.
-/
def OccupiedByFreshDefect {A M0 : ℕ} (proj : SemanticLedgerProjection A M0)
    (S : Set State) (K : Vertex proj) : Prop :=
  ∃ U : State,
    U ∈ S ∧ Fresh M0 U ∧ Defective A U ∧ Legal A M0 U ∧ proj.key U = K

/-- Every member of a concrete fresh-defect family occupies its ledger key. -/
theorem occupied_key_of_family_member {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State}
    (hS : InfiniteFreshDefectFamily A M0 S)
    {U : State} (hU : U ∈ S) :
    OccupiedByFreshDefect proj S (proj.key U) := by
  rcases hS with ⟨_hInf, hMem⟩
  rcases hMem U hU with ⟨hFresh, hDef, hLeg⟩
  exact ⟨U, hU, hFresh, hDef, hLeg, rfl⟩

/-#############################################################################
  §2. Non-vacuous pigeonhole on the unbounded concrete state space
#############################################################################-/

/--
The proper pigeonhole statement.

The source set `S` is a subset of the unbounded concrete `State`, and may be
infinite.  The target is only the finite ledger vertex type `proj.Key`.  Thus the
conclusion is a real collision between two distinct concrete states in `S`, not
a vacuous contradiction from finiteness of the state type.
-/
theorem infinite_unbounded_family_forces_ledger_collision
    {A M0 : ℕ} (proj : SemanticLedgerProjection A M0)
    {S : Set State} (hS : InfiniteFreshDefectFamily A M0 S) :
    ∃ U₁ U₂ : State,
      U₁ ≠ U₂ ∧
      U₁ ∈ S ∧ U₂ ∈ S ∧
      Fresh M0 U₁ ∧ Defective A U₁ ∧ Legal A M0 U₁ ∧
      Fresh M0 U₂ ∧ Defective A U₂ ∧ Legal A M0 U₂ ∧
      proj.key U₁ = proj.key U₂ := by
  classical
  letI : Finite proj.Key := proj.finiteKey
  rcases hS with ⟨hInf, hMem⟩
  exact infinite_defect_flows_force_ledger_collision
    (σ := State) (Key := proj.Key)
    (RealStep := RealStep A M0) (Legal := Legal A M0)
    (Fresh := Fresh M0) (Defective := Defective A)
    (S := S) hInf hMem proj.key

/--
A same-ledger-key collision resolution law for the proper unbounded concrete
ledger graph.

This is the local arithmetic obligation for the chosen semantic projection.
Unlike the older fixed-envelope `LedgerProjection`, the key type is allowed to be
any finite type supplied by `proj`.
-/
abbrev SemanticLedgerCollisionResolves
    {A M0 : ℕ} (proj : SemanticLedgerProjection A M0) : Prop :=
  BoundaryLedgerCollisionResolves
    (σ := State) (Key := proj.Key)
    (RealStep A M0) (Legal A M0) (Fresh M0) (Defective A)
    proj.key BoundaryDefectPayment.ImpossiblePayment

/--
The quotient graph plus resolution gives `LegalCycle ∨ ImpossiblePayment`.
This is the exact finite-ledger branch before burning either side.
-/
theorem infinite_unbounded_family_forces_cycle_or_payment
    {A M0 : ℕ} (proj : SemanticLedgerProjection A M0)
    {S : Set State} (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : SemanticLedgerCollisionResolves proj) :
    LegalCycle (RealStep A M0) (Legal A M0) ∨
      BoundaryDefectPayment.ImpossiblePayment := by
  classical
  letI : Finite proj.Key := proj.finiteKey
  rcases hS with ⟨hInf, hMem⟩
  exact infinite_defect_flows_force_cycle_or_payment
    (σ := State) (Key := proj.Key)
    (RealStep := RealStep A M0) (Legal := Legal A M0)
    (Fresh := Fresh M0) (Defective := Defective A)
    (ImpossiblePayment := BoundaryDefectPayment.ImpossiblePayment)
    (S := S) hInf hMem proj.key hResolve

/-#############################################################################
  §3. Strict closure: payment burned, cycles forbidden by `lexRank`
#############################################################################-/

/--
The payment branch is already impossible; therefore a resolved infinite
unbounded fresh-defect family would force a concrete legal cycle.
-/
theorem infinite_unbounded_family_forces_cycle
    {A M0 : ℕ} (proj : SemanticLedgerProjection A M0)
    {S : Set State} (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : SemanticLedgerCollisionResolves proj) :
    LegalCycle (RealStep A M0) (Legal A M0) := by
  classical
  letI : Finite proj.Key := proj.finiteKey
  rcases hS with ⟨hInf, hMem⟩
  exact infinite_defect_flows_force_cycle
    (σ := State) (Key := proj.Key)
    (RealStep := RealStep A M0) (Legal := Legal A M0)
    (Fresh := Fresh M0) (Defective := Defective A)
    (ImpossiblePayment := BoundaryDefectPayment.ImpossiblePayment)
    (S := S) hInf hMem proj.key hResolve
    BoundaryDefectPayment.impossiblePayment_false

/--
Strict closure of the proper unbounded finite-ledger graph.

This is the non-vacuous close:

  infinite concrete fresh defects in unbounded `State`
  + finite semantic ledger projection
  + same-ledger collision resolution
  ----------------------------------------------------
  False

The contradiction is not obtained from finiteness of the state type.  It is
obtained because the finite ledger creates a real same-key collision, resolution
turns it into cycle/payment, payment is impossible, and the concrete graph is
acyclic by the global `lexRank` descent.
-/
theorem proper_unbounded_ledger_graph_closes_strictly
    {A M0 : ℕ} (proj : SemanticLedgerProjection A M0)
    {S : Set State} (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : SemanticLedgerCollisionResolves proj) :
    False := by
  have hCycle : LegalCycle (RealStep A M0) (Legal A M0) :=
    infinite_unbounded_family_forces_cycle proj hS hResolve
  exact no_concrete_legalCycle_by_lexRank
    (A := A) (M0 := M0) hCycle

/--
The same strict closure expressed through the finite quotient graph object.
-/
theorem proper_ledger_quotient_graph_closes_strictly
    {A M0 : ℕ} (G : LedgerQuotientGraph A M0)
    {S : Set State} (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : SemanticLedgerCollisionResolves G.proj) :
    False := by
  exact proper_unbounded_ledger_graph_closes_strictly
    G.proj hS hResolve

/-#############################################################################
  §4. The exact remaining positive package
#############################################################################-/

/--
The correct remaining Step00 package.

This is deliberately not a finite-state package.  The concrete state type remains
unbounded; only the semantic ledger quotient is finite.
-/
structure ProperUnboundedLedgerCollapsePackage (A M0 : ℕ) where
  proj : SemanticLedgerProjection A M0
  S : Set State
  infiniteFreshDefects : InfiniteFreshDefectFamily A M0 S
  collisionResolves : SemanticLedgerCollisionResolves proj

/-- Any proper unbounded ledger collapse package is contradictory. -/
theorem properUnboundedLedgerCollapsePackage_false
    {A M0 : ℕ} (P : ProperUnboundedLedgerCollapsePackage A M0) : False := by
  exact proper_unbounded_ledger_graph_closes_strictly
    P.proj P.infiniteFreshDefects P.collisionResolves

/--
Final audit name for the now-correct graph task.

To close Step00, one must construct a term of this proposition for the actual
`A` and old bound `M0` forced by the finite-twin assumption.  The fields are the
three genuine positive arithmetic inputs; height, acyclicity, and payment are no
longer fields.
-/
abbrev TheProperUnboundedLedgerGraphObligation (A M0 : ℕ) : Prop :=
  ∃ P : ProperUnboundedLedgerCollapsePackage A M0, True


/-! ### §10. Strict audit of the projection Π (anti-cheating: ban on identity-key and hidden center).
Source: EuclidsPath_semantic_ledger_strict_audit_patch. Does not prove soundness of Π —
it machine-forbids cheating projections; all arithmetic is isolated in SemanticLedgerCollisionResolves. -/

namespace StrictLedgerAudit

open EuclidsPath.BoundaryLedgerCollision
open EuclidsPath.BoundaryDefectPayment
open EuclidsPath.LabelledFanIn

/-#############################################################################
  §1. What it means for a key to leak too much information
#############################################################################-/

/--
`proj.key` is state-complete on `S` if equal keys force equal concrete states.

For an infinite family this is impossible for a finite key.  This predicate
therefore detects an illicit `key := identity`-style projection.
-/
def KeyDeterminesStateOn {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) (S : Set State) : Prop :=
  ∀ ⦃U V : State⦄, U ∈ S → V ∈ S → proj.key U = proj.key V → U = V

/--
`proj.key` determines the centre on `S` if equal keys force equal `centerOf`.

This is not always forbidden: many different states may legitimately have the
same old centre.  It becomes forbidden on a family where `centerOf` is injective,
because then centre-completeness implies state-completeness for the collision
created by finite pigeonhole.
-/
def KeyDeterminesCenterOn {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) (S : Set State) : Prop :=
  ∀ ⦃U V : State⦄, U ∈ S → V ∈ S → proj.key U = proj.key V → centerOf U = centerOf V

/-- State-completeness immediately implies centre-completeness. -/
theorem keyDeterminesCenter_of_keyDeterminesState {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) (S : Set State)
    (h : KeyDeterminesStateOn proj S) :
    KeyDeterminesCenterOn proj S := by
  intro U V hU hV hkey
  simpa [h hU hV hkey]

/--
A finite ledger key cannot determine the whole concrete state on an infinite
subset of the unbounded state space.
-/
theorem finite_key_cannot_determine_state_on_infinite {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State}
    (hInf : S.Infinite) :
    ¬ KeyDeterminesStateOn proj S := by
  classical
  intro hDet
  letI : Finite proj.Key := proj.finiteKey
  rcases infinite_set_key_collision
      (σ := State) (Key := proj.Key) (S := S) hInf proj.key with
    ⟨U, V, hU, hV, hne, hkey⟩
  exact hne (hDet hU hV hkey)

/--
If centres are injective on an infinite family, then a finite key cannot even
determine the centre on that family.

This is the formal no-centre-leak check.  It blocks a projection that smuggles
unbounded centre data into a finite key and then makes the collision meaningless.
-/
theorem finite_key_cannot_determine_center_on_center_injective_infinite
    {A M0 : ℕ} (proj : SemanticLedgerProjection A M0) {S : Set State}
    (hInf : S.Infinite)
    (hCenterInj : Set.InjOn centerOf S) :
    ¬ KeyDeterminesCenterOn proj S := by
  classical
  intro hDet
  letI : Finite proj.Key := proj.finiteKey
  rcases infinite_set_key_collision
      (σ := State) (Key := proj.Key) (S := S) hInf proj.key with
    ⟨U, V, hU, hV, hne, hkey⟩
  have hc : centerOf U = centerOf V := hDet hU hV hkey
  have hUV : U = V := hCenterInj hU hV hc
  exact hne hUV

/--
State-completeness is a special forbidden case of the finite-key audit.
-/
theorem no_state_complete_semantic_key_on_family {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State}
    (hS : InfiniteFreshDefectFamily A M0 S) :
    ¬ KeyDeterminesStateOn proj S := by
  exact finite_key_cannot_determine_state_on_infinite proj hS.1

/--
Centre-completeness is forbidden on any infinite fresh-defect family whose
centres are injective.
-/
theorem no_center_complete_semantic_key_on_center_injective_family {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State}
    (hS : InfiniteFreshDefectFamily A M0 S)
    (hCenterInj : Set.InjOn centerOf S) :
    ¬ KeyDeterminesCenterOn proj S := by
  exact finite_key_cannot_determine_center_on_center_injective_infinite
    proj hS.1 hCenterInj

/-#############################################################################
  §2. The genuine same-key collision produced by finite pigeonhole
#############################################################################-/

/--
A concrete same-ledger collision inside an actual infinite fresh-defect family.

This is deliberately a collision in the unbounded concrete `State`, not in a
finite envelope type.
-/
abbrev HasSemanticLedgerCollision {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) (S : Set State) : Prop :=
  ∃ U₁ U₂ : State,
    U₁ ≠ U₂ ∧
    U₁ ∈ S ∧ U₂ ∈ S ∧
    Fresh M0 U₁ ∧ Defective A U₁ ∧ Legal A M0 U₁ ∧
    Fresh M0 U₂ ∧ Defective A U₂ ∧ Legal A M0 U₂ ∧
    proj.key U₁ = proj.key U₂

/--
Every infinite concrete fresh-defect family creates a real same-key collision
for every finite semantic ledger projection proj.
-/
theorem hasSemanticLedgerCollision_of_infinite_family {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State}
    (hS : InfiniteFreshDefectFamily A M0 S) :
    HasSemanticLedgerCollision proj S := by
  exact infinite_unbounded_family_forces_ledger_collision proj hS

/--
The collision is not by itself a proof of Step00.  It is only the counting half.
The arithmetic half is exactly `SemanticLedgerCollisionResolves proj`.
-/
abbrev SemanticSoundnessObligation {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) : Prop :=
  SemanticLedgerCollisionResolves proj

/-#############################################################################
  §3. Bundled audit certificate: what is proved before semantic soundness
#############################################################################-/

/--
The strict audit certificate for a candidate semantic ledger projection proj on a
concrete infinite fresh-defect family `S`.

The certificate records only what is forced by finiteness and infinitude:
there is a real same-key collision, and the key cannot be a hidden identity key.
It does *not* include the collision-resolution law.
-/
structure ProjectionAuditCertificate {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) (S : Set State) where
  family : InfiniteFreshDefectFamily A M0 S
  collision : HasSemanticLedgerCollision proj S
  notStateComplete : ¬ KeyDeterminesStateOn proj S
  notCenterCompleteOnCenterInjective :
    Set.InjOn centerOf S → ¬ KeyDeterminesCenterOn proj S

/--
The audit certificate is obtained for free from an infinite concrete
fresh-defect family and a finite semantic key.  This is still only audit/counting;
it does not close Step00.
-/
theorem projectionAuditCertificate_of_infinite_family {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State}
    (hS : InfiniteFreshDefectFamily A M0 S) :
    ProjectionAuditCertificate proj S := by
  refine ⟨hS, ?_, ?_, ?_⟩
  · exact hasSemanticLedgerCollision_of_infinite_family proj hS
  · exact no_state_complete_semantic_key_on_family proj hS
  · intro hCenterInj
    exact no_center_complete_semantic_key_on_center_injective_family
      proj hS hCenterInj

/--
Adding the missing semantic soundness law to an audit certificate closes the
branch.  This theorem is intentionally separated from the certificate: the audit
layer alone must not pretend to prove the arithmetic collision-resolution law.
-/
theorem projectionAudit_closes_with_semanticSoundness {A M0 : ℕ}
    {proj : SemanticLedgerProjection A M0} {S : Set State}
    (C : ProjectionAuditCertificate proj S)
    (hSound : SemanticSoundnessObligation proj) :
    False := by
  exact proper_unbounded_ledger_graph_closes_strictly
    proj C.family hSound

/--
The exact remaining package after the strict audit.

A term of this structure is the real Step00 arithmetic content for the chosen
scale `A` and old bound `M0`: an audited finite semantic ledger projection, plus
the local semantic collision-resolution law.
-/
structure AuditedSemanticLedgerClosingPackage (A M0 : ℕ) where
  proj : SemanticLedgerProjection A M0
  S : Set State
  audit : ProjectionAuditCertificate proj S
  semanticSoundness : SemanticSoundnessObligation proj

/-- Any fully audited-and-sound semantic ledger package is contradictory. -/
theorem auditedSemanticLedgerClosingPackage_false {A M0 : ℕ}
    (P : AuditedSemanticLedgerClosingPackage A M0) : False := by
  exact projectionAudit_closes_with_semanticSoundness
    P.audit P.semanticSoundness

/-#############################################################################
  §4. Trivial key sanity check: finite does not mean sound
#############################################################################-/

/--
The maximally coarse finite key.  It is useful as a sanity check: finiteness and
collisions are automatic, but semantic soundness is still a real obligation.
-/
noncomputable def unitProjection (A M0 : ℕ) : SemanticLedgerProjection A M0 where
  Key := PUnit
  finiteKey := inferInstance
  key := fun _ => PUnit.unit

/-- The unit projection assigns the same key to all states. -/
theorem unitProjection_key_eq {A M0 : ℕ} (U V : State) :
    (unitProjection A M0).key U = (unitProjection A M0).key V := by
  rfl

/--
Even for `Key := Unit`, closing the branch still requires the explicit semantic
collision-resolution law.  This theorem has that law as a hypothesis on purpose.
-/
theorem unitProjection_closes_only_with_resolution {A M0 : ℕ}
    {S : Set State}
    (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : SemanticSoundnessObligation (unitProjection A M0)) :
    False := by
  exact proper_unbounded_ledger_graph_closes_strictly
    (unitProjection A M0) hS hResolve

/--
For the unit projection, the audit certificate exists for every infinite
fresh-defect family, but this still does not supply semantic soundness.
-/
theorem unitProjection_auditCertificate {A M0 : ℕ}
    {S : Set State}
    (hS : InfiniteFreshDefectFamily A M0 S) :
    ProjectionAuditCertificate (unitProjection A M0) S := by
  exact projectionAuditCertificate_of_infinite_family
    (unitProjection A M0) hS

/-#############################################################################
  §5. Final audit name
#############################################################################-/

/--
The post-audit Step00 obligation.

Compared with the earlier proper unbounded ledger package, this version makes
explicit that proj has passed the finite-key anti-vacuity audit and that the only
remaining unproved mathematical field is semantic collision-resolution.
-/
abbrev TheStrictSemanticLedgerAuditObligation (A M0 : ℕ) : Prop :=
  ∃ P : AuditedSemanticLedgerClosingPackage A M0, True

end StrictLedgerAudit


end ProperUnboundedLedgerGraph



/-! ### §11. Generated-flow formulation of the source (multiplicity preserved).
Source: EuclidsPath_generated_flow_strict_formulation_patch. Pigeonhole on GENEALOGIES
(flow = start + nonempty path + ledger-terminal), not on states — fan-in is not erased. -/

namespace GeneratedFlowFormulation
open EuclidsPath.Residuals


open EuclidsPath.CleanGraph
open EuclidsPath.LabelledFanIn
open EuclidsPath.BoundaryLedgerCollision
open EuclidsPath.BoundaryDefectPayment
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph
open EuclidsPath.Residuals

/-#############################################################################
  §1. Generated flows / genealogies
#############################################################################-/

/--
A generated Step00 flow from a fresh clean centre into the concrete graph.

The field `path` is nonempty.  Therefore the flow is not merely the start state;
it records at least one actual transition in `ConcreteStep00Graph.RealStep`.
-/
structure GeneratedFlow (A M0 : ℕ) where
  start : ℕ
  terminal : State
  steps : ℕ
  nonempty : 0 < steps
  path : PathN (RealStep A M0) steps (State.center start) terminal
  startClean : Clean A start
  startFresh : M0 < start
  terminalLegal : Legal A M0 terminal

/-- The concrete start state of a generated flow. -/
def GeneratedFlow.startState {A M0 : ℕ} (F : GeneratedFlow A M0) : State :=
  State.center F.start

/-- A generated flow is fresh by construction if its start is above `M0`. -/
def FlowFresh {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  M0 < F.start

/-- A generated flow is legal if its terminal is legal; the path is already stored in `F.path`. -/
def FlowLegal {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  Legal A M0 F.terminal

/-- The terminal of the flow is a fresh concrete defect state. -/
def EndsInFreshDefect {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  Fresh M0 F.terminal ∧ Defective A F.terminal ∧ Legal A M0 F.terminal

/-- The terminal of the flow is an old absorber. -/
def EndsInOldAbsorber {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  OldAbsorber M0 F.terminal ∧ Legal A M0 F.terminal

/--
The terminal is ledger-relevant: either a fresh defect or an old absorber.
This is the correct replacement for a bare `Defective` predicate on states.
-/
def HasLedgerTerminal {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  EndsInFreshDefect F ∨ EndsInOldAbsorber F

/--
An admissible generated flow: fresh start, legal terminal, and a terminal that
must be explained by the ledger.
-/
def FlowAdmissible {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  FlowFresh F ∧ FlowLegal F ∧ HasLedgerTerminal F

/-- Every generated flow is fresh at the start by its stored certificate. -/
theorem flowFresh_of_generated {A M0 : ℕ} (F : GeneratedFlow A M0) :
    FlowFresh F :=
  F.startFresh

/-- Every generated flow is legal at the terminal by its stored certificate. -/
theorem flowLegal_of_generated {A M0 : ℕ} (F : GeneratedFlow A M0) :
    FlowLegal F :=
  F.terminalLegal

/--
A family of generated flows.  This is the non-vacuous source object that should
be produced from the finite-twin assumption.
-/
def InfiniteGeneratedFlowFamily (A M0 : ℕ)
    (𝓕 : Set (GeneratedFlow A M0)) : Prop :=
  𝓕.Infinite ∧ ∀ F ∈ 𝓕, FlowAdmissible F

/-- Extract the set of fresh defect terminal states reached by a flow family. -/
def FreshDefectTerminalStates {A M0 : ℕ}
    (𝓕 : Set (GeneratedFlow A M0)) : Set State :=
  {U | ∃ F ∈ 𝓕, F.terminal = U ∧ EndsInFreshDefect F}

/-- Extract the set of old absorber terminal states reached by a flow family. -/
def OldAbsorberTerminalStates {A M0 : ℕ}
    (𝓕 : Set (GeneratedFlow A M0)) : Set State :=
  {U | ∃ F ∈ 𝓕, F.terminal = U ∧ EndsInOldAbsorber F}

/-#############################################################################
  §2. The positive source obligation: finite twins -> generated flows
#############################################################################-/

/-- A concrete old bound: no twin centre exists above `M0`. -/
abbrev TwinBoundAbove (M0 : ℕ) : Prop :=
  ∀ m : ℕ, M0 < m → ¬ TwinCenterZ m

/-- Infinite CRT-clean starts at a fixed sieve scale. -/
abbrev InfiniteCleanStarts (A M0 : ℕ) : Prop :=
  {m : ℕ | M0 < m ∧ Clean A m}.Infinite

/--
The real positive source obligation.

Given a fixed scale `A`, an old twin bound `M0`, infinitely many clean starts,
and no twin centre above `M0`, produce an infinite family of generated Step00
flows.  This is where CRT clean-start supply, clean non-twin peel, and
well-founded termination of the clean descent must be connected.
-/
def TwinBoundForcesInfiniteGeneratedFlows (A M0 : ℕ) : Prop :=
  InfiniteCleanStarts A M0 →
  TwinBoundAbove M0 →
  ∃ 𝓕 : Set (GeneratedFlow A M0), InfiniteGeneratedFlowFamily A M0 𝓕

/--
A more explicit factory form of the same obligation.

It says that every clean start above `M0` has a generated flow, and that the
chosen collection of such flows is infinite.  This form is often easier to audit
than a direct existential family.
-/
structure GeneratedFlowFactory (A M0 : ℕ) where
  flowOf : ∀ m : ℕ, M0 < m → Clean A m → ¬ TwinCenterZ m → GeneratedFlow A M0
  admissible : ∀ m hFresh hClean hNoTwin,
    FlowAdmissible (flowOf m hFresh hClean hNoTwin)
  start_eq : ∀ m hFresh hClean hNoTwin,
    (flowOf m hFresh hClean hNoTwin).start = m

/--
The final source input in compact package form.

This is intentionally only a structure: this patch does not prove it.  It is the
correct target for the arithmetic construction of `S`.
-/
structure GeneratedFlowSourceInput (A M0 : ℕ) where
  cleanStarts : InfiniteCleanStarts A M0
  twinBound : TwinBoundAbove M0
  family : Set (GeneratedFlow A M0)
  infiniteFamily : InfiniteGeneratedFlowFamily A M0 family

/-#############################################################################
  §3. Finite semantic ledger projection on flows
#############################################################################-/

/--
A finite semantic ledger projection whose key is attached to generated flows,
not merely to terminal states.

This is the central correction: if two different clean starts end at the same
terminal state, they remain two different flows.  The finite ledger must explain
the collision of genealogies, not just the collision of final states.
-/
structure SemanticFlowLedgerProjection (A M0 : ℕ) where
  Key : Type
  finiteKey : Finite Key
  keyFlow : GeneratedFlow A M0 → Key

/-- A same-key collision between two generated flows in a family. -/
structure FlowSameKeyCollision {A M0 : ℕ}
    (proj : SemanticFlowLedgerProjection A M0)
    (𝓕 : Set (GeneratedFlow A M0))
    (F₁ F₂ : GeneratedFlow A M0) : Prop where
  distinct : F₁ ≠ F₂
  left_mem : F₁ ∈ 𝓕
  right_mem : F₂ ∈ 𝓕
  left_admissible : FlowAdmissible F₁
  right_admissible : FlowAdmissible F₂
  same_key : proj.keyFlow F₁ = proj.keyFlow F₂

/--
Pure unbounded-to-finite pigeonhole for generated flows.

The source `𝓕` is a set of generated genealogies.  It may be infinite even when
terminal states repeat.  The target is the finite flow-ledger key.
-/
theorem infinite_generated_flows_force_flow_key_collision
    {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0)
    {𝓕 : Set (GeneratedFlow A M0)}
    (h𝓕 : InfiniteGeneratedFlowFamily A M0 𝓕) :
    ∃ F₁ F₂ : GeneratedFlow A M0,
      FlowSameKeyCollision proj 𝓕 F₁ F₂ := by
  classical
  letI : Finite proj.Key := proj.finiteKey
  rcases h𝓕 with ⟨hInf, hMem⟩
  obtain ⟨F₁, F₂, hF₁, hF₂, hne, hkey⟩ :=
    BoundaryLedgerCollision.infinite_set_key_collision
      (σ := GeneratedFlow A M0) (Key := proj.Key)
      (S := 𝓕) hInf proj.keyFlow
  exact ⟨F₁, F₂,
    ⟨hne, hF₁, hF₂, hMem F₁ hF₁, hMem F₂ hF₂, hkey⟩⟩

/-#############################################################################
  §4. Flow-collision resolution: the actual Euclidean-engine wall
#############################################################################-/

/-- The only two resolution alternatives for a generated-flow key collision. -/
abbrev FlowResolutionAlternative (A M0 : ℕ) : Prop :=
  LegalCycle (RealStep A M0) (Legal A M0) ∨
    BoundaryDefectPayment.ImpossiblePayment

/--
No resolution alternative is available for free in the concrete graph:
cycles are forbidden by `lexRank`, and payment is impossible.
-/
theorem no_flowResolutionAlternative (A M0 : ℕ) :
    ¬ FlowResolutionAlternative A M0 := by
  intro h
  rcases h with hCycle | hPayment
  · exact no_concrete_legalCycle_by_lexRank
      (A := A) (M0 := M0) hCycle
  · exact BoundaryDefectPayment.impossiblePayment_false hPayment

/--
Semantic flow-ledger collision resolution.

This is the local arithmetic law that is still missing.  It is stronger and more
precise than a state-level collision law: it compares generated histories.
-/
def SemanticFlowLedgerCollisionResolves
    {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : GeneratedFlow A M0,
    F₁ ≠ F₂ →
    FlowAdmissible F₁ →
    FlowAdmissible F₂ →
    proj.keyFlow F₁ = proj.keyFlow F₂ →
      FlowResolutionAlternative A M0

/-- Projection alone only produces an unresolved collision. -/
def UnresolvedFlowKeyCollision {A M0 : ℕ}
    (proj : SemanticFlowLedgerProjection A M0)
    (𝓕 : Set (GeneratedFlow A M0)) : Prop :=
  (∃ left right : GeneratedFlow A M0, FlowSameKeyCollision proj 𝓕 left right) ∧
    ¬ FlowResolutionAlternative A M0

/--
Every finite flow-ledger projection has an unresolved same-key collision on an
infinite generated-flow family, unless additional arithmetic rules out that
family or supplies a genuine resolution.
-/
theorem infinite_generated_flows_force_unresolved_flow_collision
    {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0)
    {𝓕 : Set (GeneratedFlow A M0)}
    (h𝓕 : InfiniteGeneratedFlowFamily A M0 𝓕) :
    UnresolvedFlowKeyCollision proj 𝓕 := by
  rcases infinite_generated_flows_force_flow_key_collision
      (A := A) (M0 := M0) proj h𝓕 with ⟨F₁, F₂, hCol⟩
  exact ⟨⟨F₁, F₂, hCol⟩, no_flowResolutionAlternative A M0⟩

/--
If semantic collision resolution is supplied, an infinite generated-flow family
forces a resolution alternative.
-/
theorem infinite_generated_flows_force_cycle_or_payment
    {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0)
    {𝓕 : Set (GeneratedFlow A M0)}
    (h𝓕 : InfiniteGeneratedFlowFamily A M0 𝓕)
    (hResolve : SemanticFlowLedgerCollisionResolves proj) :
    FlowResolutionAlternative A M0 := by
  rcases infinite_generated_flows_force_flow_key_collision
      (A := A) (M0 := M0) proj h𝓕 with ⟨F₁, F₂, hCol⟩
  exact hResolve F₁ F₂
    hCol.distinct hCol.left_admissible hCol.right_admissible hCol.same_key

/--
Main strict close for the generated-flow formulation.

The contradiction uses no finite-state vacuity: the source type is the type of
all generated flows, and the finite object is only `proj.Key`.
-/
theorem infinite_generated_flows_impossible_with_resolution
    {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0)
    {𝓕 : Set (GeneratedFlow A M0)}
    (h𝓕 : InfiniteGeneratedFlowFamily A M0 𝓕)
    (hResolve : SemanticFlowLedgerCollisionResolves proj) :
    False := by
  have hAlt : FlowResolutionAlternative A M0 :=
    infinite_generated_flows_force_cycle_or_payment
      (A := A) (M0 := M0) proj h𝓕 hResolve
  exact no_flowResolutionAlternative A M0 hAlt

/--
The no-cheat conclusion for generated flows: a finite projection on flows cannot
itself manufacture the Euclidean engine.  It always produces an unresolved
collision unless the missing semantic law is added.
-/
abbrev FlowProjectionCheatsOn {A M0 : ℕ}
    (proj : SemanticFlowLedgerProjection A M0)
    (𝓕 : Set (GeneratedFlow A M0)) : Prop :=
  UnresolvedFlowKeyCollision proj 𝓕

/-- Every finite flow-ledger projection cheats on an infinite generated-flow family unless extra arithmetic is supplied. -/
theorem every_flow_projection_cheats_on_infinite_family
    {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0)
    {𝓕 : Set (GeneratedFlow A M0)}
    (h𝓕 : InfiniteGeneratedFlowFamily A M0 𝓕) :
    FlowProjectionCheatsOn proj 𝓕 :=
  infinite_generated_flows_force_unresolved_flow_collision proj h𝓕

/-#############################################################################
  §5. The exact remaining Step00 package in generated-flow form
#############################################################################-/

/--
The corrected final positive package.

Compared with the earlier state-family package, the source is now an infinite
family of generated flows, and the key is a finite semantic key on flows.
-/
structure GeneratedFlowStep00Package (A M0 : ℕ) where
  source : GeneratedFlowSourceInput A M0
  proj : SemanticFlowLedgerProjection A M0
  semanticResolution : SemanticFlowLedgerCollisionResolves proj

/-- Any generated-flow Step00 package is contradictory by the already closed branches. -/
theorem generatedFlowStep00Package_false
    {A M0 : ℕ} (P : GeneratedFlowStep00Package A M0) : False := by
  exact infinite_generated_flows_impossible_with_resolution
    P.proj P.source.infiniteFamily P.semanticResolution

/--
The actual generated-flow obligation.

To move Step00, construct this package for the `A` and `M0` produced by the
finite-twin assumption.  The height, cycle, and payment branches are not fields:
they have already been closed by previous patches.
-/
abbrev TheGeneratedFlowStep00Obligation (A M0 : ℕ) : Prop :=
  ∃ P : GeneratedFlowStep00Package A M0, True

/-#############################################################################
  §6. Diagnostic split: terminal states are not the right source object
#############################################################################-/

/--
A family has state-terminal multiplicity if two different flows share the same
terminal state.  This is not a bug; it is exactly the kind of fan-in that a
state-only family would erase.
-/
def TerminalFanIn {A M0 : ℕ}
    (𝓕 : Set (GeneratedFlow A M0)) : Prop :=
  ∃ F₁ F₂ : GeneratedFlow A M0,
    F₁ ∈ 𝓕 ∧ F₂ ∈ 𝓕 ∧ F₁ ≠ F₂ ∧ F₁.terminal = F₂.terminal

/--
If terminal fan-in occurs, then replacing flows by terminal states loses
multiplicity.  This theorem is intentionally only the formal witness of loss:
the equality of terminal states is exactly the erased information.
-/
theorem terminalFanIn_witnesses_state_projection_loss
    {A M0 : ℕ} {𝓕 : Set (GeneratedFlow A M0)}
    (h : TerminalFanIn 𝓕) :
    ∃ F₁ F₂ : GeneratedFlow A M0,
      F₁ ∈ 𝓕 ∧ F₂ ∈ 𝓕 ∧ F₁ ≠ F₂ ∧
      F₁.terminal = F₂.terminal :=
  h


/-! ### Building the source: generated-flow factory from a clean non-twin start (7 bricks).
InfiniteCleanStarts closed by a CONSTRUCTIVE primorial; well-founded flow-builder; cofactor-normalizer
via real 6m±1 arithmetic. Twins reduced to a SINGLE input SemanticExtendedFlowLedgerCollisionResolves. -/
open EuclidsPath.RigidClose
open Classical


/-! #### patch: generated_flow_factory_reduction -/


/-#############################################################################
  §1. From a local flow factory to an infinite generated-flow family
#############################################################################-/

/--
The canonical family of flows produced by a factory from all fresh clean starts
under a fixed twin bound.
-/
def factoryFlowFamily {A M0 : ℕ}
    (G : GeneratedFlowFactory A M0)
    (hTwinBound : TwinBoundAbove M0) : Set (GeneratedFlow A M0) :=
  {F | ∃ (m : ℕ) (hFresh : M0 < m) (hClean : Clean A m),
    F = G.flowOf m hFresh hClean (hTwinBound m hFresh)}

/--
Every member of the factory-produced family is admissible.
-/
theorem factoryFlowFamily_admissible {A M0 : ℕ}
    (G : GeneratedFlowFactory A M0)
    (hTwinBound : TwinBoundAbove M0) :
    ∀ F ∈ factoryFlowFamily G hTwinBound, FlowAdmissible F := by
  intro F hF
  rcases hF with ⟨m, hFresh, hClean, rfl⟩
  exact G.admissible m hFresh hClean (hTwinBound m hFresh)

/--
The factory-produced family is infinite whenever the fresh clean starts are
infinite.  The proof uses the stored equality `F.start = m`, so it preserves
multiplicity at the genealogy level instead of collapsing through terminals.
-/
theorem factoryFlowFamily_infinite {A M0 : ℕ}
    (G : GeneratedFlowFactory A M0)
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    (factoryFlowFamily G hTwinBound).Infinite := by
  classical
  let 𝓕 : Set (GeneratedFlow A M0) := factoryFlowFamily G hTwinBound
  -- If the flow family were finite, then its image under `.start` would be finite.
  intro hFin𝓕
  have hImageFinite : (GeneratedFlow.start '' 𝓕).Finite :=
    hFin𝓕.image GeneratedFlow.start
  -- Every fresh clean start appears as the start of its factory flow.
  have hCleanSubset : {m : ℕ | M0 < m ∧ Clean A m} ⊆ GeneratedFlow.start '' 𝓕 := by
    intro m hm
    let F : GeneratedFlow A M0 :=
      G.flowOf m hm.1 hm.2 (hTwinBound m hm.1)
    refine ⟨F, ?_, ?_⟩
    · exact ⟨m, hm.1, hm.2, rfl⟩
    · dsimp [F]
      exact G.start_eq m hm.1 hm.2 (hTwinBound m hm.1)
  exact hCleanStarts (hImageFinite.subset hCleanSubset)

/--
A local generated-flow factory closes the global source obligation
`TwinBoundForcesInfiniteGeneratedFlows`.
-/
theorem twinBoundForcesInfiniteGeneratedFlows_of_factory {A M0 : ℕ}
    (G : GeneratedFlowFactory A M0) :
    TwinBoundForcesInfiniteGeneratedFlows A M0 := by
  intro hCleanStarts hTwinBound
  refine ⟨factoryFlowFamily G hTwinBound, ?_⟩
  exact ⟨factoryFlowFamily_infinite G hCleanStarts hTwinBound,
    factoryFlowFamily_admissible G hTwinBound⟩

/--
Package form: clean-start supply + twin bound + factory give the compact source
input used by the generated-flow closing theorem.
-/
def generatedFlowSourceInput_of_factory {A M0 : ℕ}
    (G : GeneratedFlowFactory A M0)
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    GeneratedFlowSourceInput A M0 :=
  { cleanStarts := hCleanStarts
    twinBound := hTwinBound
    family := factoryFlowFamily G hTwinBound
    infiniteFamily :=
      ⟨factoryFlowFamily_infinite G hCleanStarts hTwinBound,
        factoryFlowFamily_admissible G hTwinBound⟩ }

/-#############################################################################
  §2. The remaining local arithmetic object
#############################################################################-/

/--
This is now the real local Step00 source obligation.

For every fresh clean start above the old twin bound, assuming it is not a twin
centre, construct a concrete nonempty Step00 flow ending in a ledger-relevant
terminal.  Proving this must use the real 6m±1 peel/descent arithmetic.
-/
abbrev CleanStartGeneratesFlow (A M0 : ℕ) : Type :=
  GeneratedFlowFactory A M0

/--
After this patch, the old source obligation is equivalent to the existence of a
local factory, plus the already independent clean-start supply and twin bound.
This theorem is intentionally one-way: it identifies the honest next target
without pretending to construct it.
-/
theorem cleanStartGeneratesFlow_closes_source {A M0 : ℕ}
    (hFactory : CleanStartGeneratesFlow A M0) :
    TwinBoundForcesInfiniteGeneratedFlows A M0 :=
  twinBoundForcesInfiniteGeneratedFlows_of_factory hFactory


/-! #### patch: proper_generated_flow_factory -/


/-#############################################################################
  §1. Proper arithmetic peel certificates
#############################################################################-/

/--
A real centre-peel certificate.

This is the arithmetic content that the broad audited `ActiveEdge` did not
store: one side of `m` factors through a divisor and a smaller side of `n`.
The divisor is required to be beyond the clean scale `A`; this is the intended
"active" part of the 6m±1 descent.
-/
structure ProperCenterPeel (A m n : ℕ) where
  inSide : Side
  outSide : Side
  bigDivisor : ℕ
  bigPrime : bigDivisor.Prime
  bigBeyondScale : A < bigDivisor
  factor : sideValue inSide m = bigDivisor * sideValue outSide n
  smaller : n < m
  /-- AUDIT-PATCH (degenerate peel): target `n ≥ 1`. Without this the prime side `p = p·1`
      (`1 = 6·0+1`) gave a peel into center 0 WITHOUT the twin hypothesis — a vacuity exploit of the audit. -/
  targetPos : 1 ≤ n

/--
A proper boundary peel.

The source centre `m` peels arithmetically to a smaller centre `n`, and `n`
has a small-prime defect `q ≤ A` on one of its sides.  This is the real version
of "clean branch exits the A-clean core".
-/
structure ProperBoundaryPeel (A m n q : ℕ) (s : Side) where
  peel : ProperCenterPeel A m n
  smallPrime : q.Prime
  smallWithinScale : q ≤ A
  smallDivides : q ∣ sideValue s n

/-- A proper boundary target is not clean. -/
theorem not_clean_of_properBoundaryPeel {A m n q : ℕ} {s : Side}
    (h : ProperBoundaryPeel A m n q s) : ¬ Clean A n := by
  intro hClean
  have hbad : q ∣ (6 * n - 1) ∨ q ∣ (6 * n + 1) := by
    cases s with
    | minus => exact Or.inl h.smallDivides
    | plus  => exact Or.inr h.smallDivides
  exact hClean q h.smallPrime h.smallWithinScale hbad

/-- A proper centre peel gives the old broad `ActiveEdge`, but not conversely. -/
theorem activeEdge_of_properCenterPeel {A m n : ℕ}
    (h : ProperCenterPeel A m n) : ActiveEdge A m n :=
  ⟨True.intro, h.smaller⟩

/-#############################################################################
  §2. Proper real steps: a strict subgraph of the concrete graph
#############################################################################-/

/--
The proper Step00 relation.

It is a strict arithmetic subrelation of `ConcreteStep00Graph.RealStep`.  The
constructors intentionally mirror the existing concrete graph, but the
centre-originating edges carry `ProperCenterPeel` / `ProperBoundaryPeel` rather
than the broad placeholder `ActiveEdge` alone.
-/
inductive ProperRealStep (A M0 : ℕ) : State → State → Prop
  | clean {m n : ℕ}
      (hmClean : Clean A m)
      (hnClean : Clean A n)
      (hPeel : ProperCenterPeel A m n) :
      ProperRealStep A M0 (State.center m) (State.center n)
  | boundary {m n q : ℕ} {s : Side}
      (hmClean : Clean A m)
      (hBoundary : ProperBoundaryPeel A m n q s) :
      ProperRealStep A M0 (State.center m) (State.defect n q s)
  | peel {n q t : ℕ} {inSide outSide : Side}
      (h : PeelCert n q t inSide outSide) :
      ProperRealStep A M0 (State.defect n q inSide) (State.center t)
  | absorb {n q : ℕ} {s : Side}
      (hOld : n ≤ M0) :
      ProperRealStep A M0 (State.defect n q s) (State.absorber n)

/-- Every proper step is a concrete real step. -/
theorem properRealStep_to_realStep {A M0 : ℕ} {U V : State}
    (h : ProperRealStep A M0 U V) : RealStep A M0 U V := by
  cases h with
  | clean hmClean hnClean hPeel =>
      exact RealStep.clean ⟨hmClean, hnClean, activeEdge_of_properCenterPeel hPeel⟩
  | boundary hmClean hBoundary =>
      exact RealStep.boundary hmClean
        (activeEdge_of_properCenterPeel hBoundary.peel)
        hBoundary.smallPrime hBoundary.smallWithinScale hBoundary.smallDivides
  | peel hcert =>
      exact RealStep.peel hcert
  | absorb hOld =>
      exact RealStep.absorb hOld

/-- Monotonicity of finite paths under relation inclusion. -/
theorem pathN_mono {α : Type*} {R S : α → α → Prop}
    (hRS : ∀ {U V : α}, R U V → S U V) :
    ∀ {n : ℕ} {U V : α}, PathN R n U V → PathN S n U V
  | 0, U, V, h => h
  | Nat.succ n, U, V, h => by
      rcases h with ⟨Z, hStep, hPath⟩
      exact ⟨Z, hRS hStep, pathN_mono hRS hPath⟩

/-- Proper paths lift to concrete Step00 paths. -/
theorem properPath_to_realPath {A M0 n : ℕ} {U V : State}
    (h : PathN (ProperRealStep A M0) n U V) :
    PathN (RealStep A M0) n U V :=
  pathN_mono (R := ProperRealStep A M0) (S := RealStep A M0)
    (fun hStep => properRealStep_to_realStep hStep) h

/-#############################################################################
  §3. Proper generated flows
#############################################################################-/

/--
A generated flow whose stored path uses only proper arithmetic Step00 edges.
-/
structure ProperGeneratedFlow (A M0 : ℕ) where
  start : ℕ
  terminal : State
  steps : ℕ
  nonempty : 0 < steps
  properPath : PathN (ProperRealStep A M0) steps (State.center start) terminal
  startClean : Clean A start
  startFresh : M0 < start
  terminalLegal : Legal A M0 terminal
  ledgerTerminal :
    (Fresh M0 terminal ∧ Defective A terminal ∧ Legal A M0 terminal) ∨
    (OldAbsorber M0 terminal ∧ Legal A M0 terminal)

/-- Convert a proper generated flow into the ordinary generated-flow object. -/
def ProperGeneratedFlow.toGeneratedFlow {A M0 : ℕ}
    (F : ProperGeneratedFlow A M0) : GeneratedFlow A M0 :=
  { start := F.start
    terminal := F.terminal
    steps := F.steps
    nonempty := F.nonempty
    path := properPath_to_realPath F.properPath
    startClean := F.startClean
    startFresh := F.startFresh
    terminalLegal := F.terminalLegal }

/-- The converted flow has the same start. -/
theorem proper_toGeneratedFlow_start {A M0 : ℕ}
    (F : ProperGeneratedFlow A M0) :
    F.toGeneratedFlow.start = F.start := rfl

/-- The converted flow has the same terminal. -/
theorem proper_toGeneratedFlow_terminal {A M0 : ℕ}
    (F : ProperGeneratedFlow A M0) :
    F.toGeneratedFlow.terminal = F.terminal := rfl

/-- Proper generated flows are admissible after conversion. -/
theorem proper_toGeneratedFlow_admissible {A M0 : ℕ}
    (F : ProperGeneratedFlow A M0) :
    FlowAdmissible F.toGeneratedFlow := by
  refine ⟨?_, ?_, ?_⟩
  · exact F.startFresh
  · exact F.terminalLegal
  · rcases F.ledgerTerminal with hFreshDefect | hOld
    · exact Or.inl hFreshDefect
    · exact Or.inr hOld

/-#############################################################################
  §4. Proper factory closes the old factory obligation
#############################################################################-/

/--
The honest local source factory.

This is now the real arithmetic target: every fresh clean non-twin start must
produce a flow whose path consists entirely of proper 6m±1 peel/defect/absorb
steps.
-/
structure ProperGeneratedFlowFactory (A M0 : ℕ) where
  properFlowOf :
    ∀ m : ℕ, M0 < m → Clean A m → ¬ TwinCenterZ m → ProperGeneratedFlow A M0
  start_eq : ∀ m hFresh hClean hNoTwin,
    (properFlowOf m hFresh hClean hNoTwin).start = m

/-- A proper factory induces the earlier generated-flow factory. -/
def generatedFlowFactory_of_proper {A M0 : ℕ}
    (G : ProperGeneratedFlowFactory A M0) : GeneratedFlowFactory A M0 :=
  { flowOf := fun m hFresh hClean hNoTwin =>
      (G.properFlowOf m hFresh hClean hNoTwin).toGeneratedFlow
    admissible := by
      intro m hFresh hClean hNoTwin
      exact proper_toGeneratedFlow_admissible
        (G.properFlowOf m hFresh hClean hNoTwin)
    start_eq := by
      intro m hFresh hClean hNoTwin
      change (G.properFlowOf m hFresh hClean hNoTwin).start = m
      exact G.start_eq m hFresh hClean hNoTwin }

/-- A proper factory closes the generated-flow source obligation. -/
theorem twinBoundForcesInfiniteGeneratedFlows_of_properFactory {A M0 : ℕ}
    (G : ProperGeneratedFlowFactory A M0) :
    TwinBoundForcesInfiniteGeneratedFlows A M0 :=
  twinBoundForcesInfiniteGeneratedFlows_of_factory
    (generatedFlowFactory_of_proper G)

/-- Package form: clean-start supply + twin bound + proper factory give source input. -/
def generatedFlowSourceInput_of_properFactory {A M0 : ℕ}
    (G : ProperGeneratedFlowFactory A M0)
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    GeneratedFlowSourceInput A M0 :=
  generatedFlowSourceInput_of_factory
    (generatedFlowFactory_of_proper G) hCleanStarts hTwinBound

/-#############################################################################
  §5. The sharpened remaining local obligation
#############################################################################-/

/--
The old local factory obligation, sharpened to forbid fake `ActiveEdge` flows.
-/
abbrev ProperCleanStartGeneratesFlow (A M0 : ℕ) : Type :=
  ProperGeneratedFlowFactory A M0

/--
After this patch, the honest source target is a proper factory.  The remaining
work is arithmetic: build `ProperGeneratedFlowFactory A M0` using the real
6m±1 factorisation/peel mechanism.
-/
theorem properCleanStartGeneratesFlow_closes_source {A M0 : ℕ}
    (hFactory : ProperCleanStartGeneratesFlow A M0) :
    TwinBoundForcesInfiniteGeneratedFlows A M0 :=
  twinBoundForcesInfiniteGeneratedFlows_of_properFactory hFactory

/--
A compact marker for the remaining non-glue source obligation.

Unlike `GeneratedFlowFactory`, this cannot be satisfied merely by exploiting the
old placeholder `ActiveEdge := True ∧ n < m`; each source-originating edge must
carry an explicit 6m±1 factorisation certificate.
-/
abbrev TheProperFlowFactoryObligation (A M0 : ℕ) : Type :=
  ProperCleanStartGeneratesFlow A M0


/-! #### patch: proper_flow_wellfounded_builder -/


/-#############################################################################
  §1. Proper flows from a specified start
#############################################################################-/

/--
A proper generated flow whose start is definitionally the external parameter
`m`.  This version is convenient for well-founded recursion: the path starts at
`State.center m`, so no casts through a stored `start_eq` are needed.
-/
structure ProperFlowFrom (A M0 m : ℕ) where
  terminal : State
  steps : ℕ
  nonempty : 0 < steps
  properPath : PathN (ProperRealStep A M0) steps (State.center m) terminal
  startClean : Clean A m
  startFresh : M0 < m
  terminalLegal : Legal A M0 terminal
  ledgerTerminal :
    (Fresh M0 terminal ∧ Defective A terminal ∧ Legal A M0 terminal) ∨
    (OldAbsorber M0 terminal ∧ Legal A M0 terminal)

/-- Convert a `ProperFlowFrom` into the existing `ProperGeneratedFlow`. -/
def ProperFlowFrom.toProperGeneratedFlow {A M0 m : ℕ}
    (F : ProperFlowFrom A M0 m) : ProperGeneratedFlow A M0 :=
  { start := m
    terminal := F.terminal
    steps := F.steps
    nonempty := F.nonempty
    properPath := F.properPath
    startClean := F.startClean
    startFresh := F.startFresh
    terminalLegal := F.terminalLegal
    ledgerTerminal := F.ledgerTerminal }

@[simp] theorem properFlowFrom_toProperGeneratedFlow_start {A M0 m : ℕ}
    (F : ProperFlowFrom A M0 m) :
    F.toProperGeneratedFlow.start = m := rfl

/-#############################################################################
  §2. Immediate proper terminals
#############################################################################-/

/--
A strictly local terminal produced from a clean centre.

`freshDefect` is one proper boundary step:

  center m → defect n q side,

with `n > M0`.

`oldAbsorb` is the boundary step followed by the terminal absorb step:

  center m → defect n q side → absorber n,

with `n ≤ M0`.
-/
inductive ProperImmediateTerminal (A M0 m : ℕ) : Type
  | freshDefect {n q : ℕ} {s : Side}
      (hmFresh : M0 < m)
      (hmClean : Clean A m)
      (hBoundary : ProperBoundaryPeel A m n q s)
      (hFreshTarget : M0 < n) : ProperImmediateTerminal A M0 m
  | oldAbsorb {n q : ℕ} {s : Side}
      (hmFresh : M0 < m)
      (hmClean : Clean A m)
      (hBoundary : ProperBoundaryPeel A m n q s)
      (hOld : n ≤ M0) : ProperImmediateTerminal A M0 m

/-- A local terminal becomes a `ProperFlowFrom`. -/
def ProperImmediateTerminal.toProperFlowFrom {A M0 m : ℕ}
    (T : ProperImmediateTerminal A M0 m) : ProperFlowFrom A M0 m := by
  cases T with
  | @freshDefect n q s hmFresh hmClean hBoundary hFreshTarget =>
      refine
        { terminal := State.defect n q s
          steps := 1
          nonempty := by omega
          properPath := ?_
          startClean := hmClean
          startFresh := hmFresh
          terminalLegal := ?_
          ledgerTerminal := ?_ }
      · exact ⟨State.defect n q s, ProperRealStep.boundary hmClean hBoundary, rfl⟩
      · exact ⟨hBoundary.smallPrime, hBoundary.smallWithinScale, hBoundary.smallDivides⟩
      · exact Or.inl
          ⟨hFreshTarget,
            ⟨hBoundary.smallPrime, hBoundary.smallWithinScale,
              hBoundary.smallDivides⟩,
            ⟨hBoundary.smallPrime, hBoundary.smallWithinScale,
              hBoundary.smallDivides⟩⟩
  | @oldAbsorb n q s hmFresh hmClean hBoundary hOld =>
      refine
        { terminal := State.absorber n
          steps := 2
          nonempty := by omega
          properPath := ?_
          startClean := hmClean
          startFresh := hmFresh
          terminalLegal := hOld
          ledgerTerminal := ?_ }
      · refine ⟨State.defect n q s, ProperRealStep.boundary hmClean hBoundary, ?_⟩
        exact ⟨State.absorber n, ProperRealStep.absorb hOld, rfl⟩
      · exact Or.inr ⟨hOld, hOld⟩

/-#############################################################################
  §3. The exact local one-step resolver
#############################################################################-/

/--
A clean proper descent to a smaller fresh clean centre.
-/
structure ProperCleanDescend (A M0 m : ℕ) where
  next : ℕ
  nextFresh : M0 < next
  nextClean : Clean A next
  peel : ProperCenterPeel A m next

/-- The recursive branch really decreases the centre. -/
theorem ProperCleanDescend.smaller {A M0 m : ℕ}
    (D : ProperCleanDescend A M0 m) : D.next < m :=
  D.peel.smaller

/--
The precise local arithmetic resolver needed for the source construction.

For a fresh clean non-twin centre, it either produces an immediate proper
ledger terminal, or a proper clean descent to a smaller fresh clean centre.
-/
inductive ProperOneStepOutcome (A M0 m : ℕ) : Type
  | terminal (T : ProperImmediateTerminal A M0 m) : ProperOneStepOutcome A M0 m
  | descend  (D : ProperCleanDescend A M0 m) : ProperOneStepOutcome A M0 m

/--
The sharpened local arithmetic obligation.

This is the next true 6m±1 input: prove it from actual factorisation/cofactor
arithmetic.  The rest of this file proves that this local resolver is enough to
build all generated flows under a twin bound.
-/
structure ProperOneStepResolver (A M0 : ℕ) where
  resolve : ∀ m : ℕ,
    M0 < m → Clean A m → ¬ TwinCenterZ m → ProperOneStepOutcome A M0 m

/-#############################################################################
  §4. Prepending one proper clean step
#############################################################################-/

/-- Prepend a proper clean peel to a recursively produced proper flow. -/
def prependProperCleanDescend {A M0 m : ℕ}
    (hmClean : Clean A m)
    (D : ProperCleanDescend A M0 m)
    (F : ProperFlowFrom A M0 D.next) : ProperFlowFrom A M0 m :=
  { terminal := F.terminal
    steps := F.steps + 1
    nonempty := by omega
    properPath := by
      refine ⟨State.center D.next, ?_, F.properPath⟩
      exact ProperRealStep.clean hmClean D.nextClean D.peel
    startClean := hmClean
    startFresh := by
      have hnm : D.next < m := D.smaller
      have hnf : M0 < D.next := D.nextFresh
      omega
    terminalLegal := F.terminalLegal
    ledgerTerminal := F.ledgerTerminal }

/-#############################################################################
  §5. Strong-induction builder under a fixed twin bound
#############################################################################-/

/--
Build a proper flow from a fresh clean start, using a local resolver and the
*global* old twin bound for recursive descendants.
-/
noncomputable def properFlowFrom_of_oneStepResolver {A M0 : ℕ}
    (R : ProperOneStepResolver A M0)
    (hTwinBound : TwinBoundAbove M0)
    (m : ℕ) (hFresh : M0 < m) (hClean : Clean A m) :
    ProperFlowFrom A M0 m := by
  classical
  induction m using Nat.strongRecOn with
  | ind m IH =>
      have hNoTwin : ¬ TwinCenterZ m := hTwinBound m hFresh
      cases R.resolve m hFresh hClean hNoTwin with
      | terminal T =>
          exact T.toProperFlowFrom
      | descend D =>
          exact prependProperCleanDescend hClean D
            (IH D.next D.smaller D.nextFresh D.nextClean)

/--
Under a fixed twin bound, a local resolver induces the earlier proper factory.
The local `¬ TwinCenterZ m` argument is now redundant; the recursive construction
uses the global `TwinBoundAbove M0`, which is what the descent actually needs.
-/
noncomputable def properGeneratedFlowFactory_of_oneStepResolver {A M0 : ℕ}
    (R : ProperOneStepResolver A M0)
    (hTwinBound : TwinBoundAbove M0) : ProperGeneratedFlowFactory A M0 :=
  { properFlowOf := fun m hFresh hClean _hNoTwin =>
      (properFlowFrom_of_oneStepResolver R hTwinBound m hFresh hClean).toProperGeneratedFlow
    start_eq := by
      intro m hFresh hClean hNoTwin
      rfl }

/--
A local one-step resolver closes the source branch under clean-start supply and
a twin bound.
-/
theorem twinBoundForcesInfiniteGeneratedFlows_of_oneStepResolver {A M0 : ℕ}
    (R : ProperOneStepResolver A M0) :
    TwinBoundForcesInfiniteGeneratedFlows A M0 := by
  intro hCleanStarts hTwinBound
  exact twinBoundForcesInfiniteGeneratedFlows_of_properFactory
    (properGeneratedFlowFactory_of_oneStepResolver R hTwinBound)
    hCleanStarts hTwinBound

/-- Package form used by the final Step00 closing layer. -/
noncomputable def generatedFlowSourceInput_of_oneStepResolver {A M0 : ℕ}
    (R : ProperOneStepResolver A M0)
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    GeneratedFlowSourceInput A M0 :=
  generatedFlowSourceInput_of_properFactory
    (properGeneratedFlowFactory_of_oneStepResolver R hTwinBound)
    hCleanStarts hTwinBound

/-#############################################################################
  §6. The remaining source obligation after well-founded assembly
#############################################################################-/

/--
After this patch, `ProperGeneratedFlowFactory` has been reduced to the following
strictly local 6m±1 resolver.
-/
abbrev TheOneStepArithmeticSourceObligation (A M0 : ℕ) : Type :=
  ProperOneStepResolver A M0

/--
The exact status marker: the only source-side arithmetic still missing is the
one-step resolver.  No infinitude, pigeonhole, height, or payment argument is
hidden here.
-/
theorem oneStepResolver_closes_source {A M0 : ℕ}
    (R : TheOneStepArithmeticSourceObligation A M0) :
    TwinBoundForcesInfiniteGeneratedFlows A M0 :=
  twinBoundForcesInfiniteGeneratedFlows_of_oneStepResolver R


/-! #### patch: extended_generated_flow_old_center -/


/-#############################################################################
  §1. Extended ledger terminals
#############################################################################-/

/-- The terminal is an old clean centre inside the old zone. -/
def EndsInOldCleanCenter (A M0 : ℕ) (U : State) : Prop :=
  ∃ n : ℕ, U = State.center n ∧ n ≤ M0 ∧ Clean A n

/--
Extended ledger-relevant terminal.

Compared with `HasLedgerTerminal`, this adds the missing terminal type:
old clean centre.  This prevents the source construction from being blocked by a
perfectly valid peel landing in the old finite zone.
-/
def ExtendedLedgerTerminal (A M0 : ℕ) (U : State) : Prop :=
  (Fresh M0 U ∧ Defective A U ∧ Legal A M0 U) ∨
  (OldAbsorber M0 U ∧ Legal A M0 U) ∨
  EndsInOldCleanCenter A M0 U

/-- Every old clean centre is legal as a centre state. -/
theorem legal_of_oldCleanCenter {A M0 n : ℕ}
    (hClean : Clean A n) : Legal A M0 (State.center n) :=
  hClean

/-- Old clean centres are extended ledger terminals. -/
theorem extendedLedgerTerminal_oldCleanCenter {A M0 n : ℕ}
    (hOld : n ≤ M0) (hClean : Clean A n) :
    ExtendedLedgerTerminal A M0 (State.center n) := by
  exact Or.inr (Or.inr ⟨n, rfl, hOld, hClean⟩)

/-- Ordinary fresh defects are still extended ledger terminals. -/
theorem extendedLedgerTerminal_freshDefect {A M0 : ℕ} {U : State}
    (h : Fresh M0 U ∧ Defective A U ∧ Legal A M0 U) :
    ExtendedLedgerTerminal A M0 U :=
  Or.inl h

/-- Ordinary old absorbers are still extended ledger terminals. -/
theorem extendedLedgerTerminal_oldAbsorber {A M0 : ℕ} {U : State}
    (h : OldAbsorber M0 U ∧ Legal A M0 U) :
    ExtendedLedgerTerminal A M0 U :=
  Or.inr (Or.inl h)

/-#############################################################################
  §2. Extended proper generated flows
#############################################################################-/

/--
A proper generated flow with the corrected ledger terminal predicate.

The path still uses only `ProperRealStep`; no fake edge is added.  The new case
is simply that a path may terminate at `State.center n` with `n ≤ M0` and
`Clean A n`.
-/
structure ExtendedProperGeneratedFlow (A M0 : ℕ) where
  start : ℕ
  terminal : State
  steps : ℕ
  nonempty : 0 < steps
  properPath : PathN (ProperRealStep A M0) steps (State.center start) terminal
  startClean : Clean A start
  startFresh : M0 < start
  terminalLegal : Legal A M0 terminal
  ledgerTerminal : ExtendedLedgerTerminal A M0 terminal

/-- Admissibility for the extended flow carrier. -/
def ExtendedFlowAdmissible {A M0 : ℕ}
    (F : ExtendedProperGeneratedFlow A M0) : Prop :=
  M0 < F.start ∧ Legal A M0 F.terminal ∧
    ExtendedLedgerTerminal A M0 F.terminal

/-- Every stored extended flow is admissible. -/
theorem extendedFlow_admissible {A M0 : ℕ}
    (F : ExtendedProperGeneratedFlow A M0) : ExtendedFlowAdmissible F :=
  ⟨F.startFresh, F.terminalLegal, F.ledgerTerminal⟩

/-- Infinite family of extended generated flows. -/
def InfiniteExtendedGeneratedFlowFamily (A M0 : ℕ)
    (𝓕 : Set (ExtendedProperGeneratedFlow A M0)) : Prop :=
  𝓕.Infinite ∧ ∀ F ∈ 𝓕, ExtendedFlowAdmissible F

/-#############################################################################
  §3. One genuine peel target and its classification
#############################################################################-/

/--
A single proper peel target produced from a clean non-twin centre.

This is deliberately weaker than a full one-step outcome: it only supplies the
proper arithmetic peel.  The target is classified by this file.
-/
structure ProperPeelTarget (A m : ℕ) where
  target : ℕ
  peel : ProperCenterPeel A m target

/--
The remaining local 6m±1 normalizer.

For every fresh clean non-twin centre, produce a genuine proper peel target.
This is the next arithmetic object to prove from factorisation/cofactor
normalisation.  Everything after this point is structural.
-/
structure ProperOneStepNormalizer (A M0 : ℕ) where
  peelOf : ∀ m : ℕ,
    M0 < m → Clean A m → ¬ TwinCenterZ m → ProperPeelTarget A m

/-- A corrected one-step outcome allowing an old clean centre terminal. -/
inductive ExtendedOneStepOutcome (A M0 m : ℕ) : Type
  | freshDefect {n q : ℕ} {s : Side}
      (hmFresh : M0 < m)
      (hmClean : Clean A m)
      (hBoundary : ProperBoundaryPeel A m n q s)
      (hFreshTarget : M0 < n) : ExtendedOneStepOutcome A M0 m
  | oldDefectAbsorb {n q : ℕ} {s : Side}
      (hmFresh : M0 < m)
      (hmClean : Clean A m)
      (hBoundary : ProperBoundaryPeel A m n q s)
      (hOld : n ≤ M0) : ExtendedOneStepOutcome A M0 m
  | oldCleanCenter {n : ℕ}
      (hmFresh : M0 < m)
      (hmClean : Clean A m)
      (hnClean : Clean A n)
      (hPeel : ProperCenterPeel A m n)
      (hOld : n ≤ M0) : ExtendedOneStepOutcome A M0 m
  | descend {n : ℕ}
      (hmFresh : M0 < m)
      (hmClean : Clean A m)
      (hnClean : Clean A n)
      (hPeel : ProperCenterPeel A m n)
      (hFreshTarget : M0 < n) : ExtendedOneStepOutcome A M0 m

/-- Build a proper boundary peel from a proper peel and a proof that the target is not clean. -/
noncomputable def properBoundaryPeel_of_not_clean_target {A m n : ℕ}
    (hPeel : ProperCenterPeel A m n)
    (hNotClean : ¬ Clean A n) :
    Σ' (q : ℕ) (s : Side), ProperBoundaryPeel A m n q s := by
  classical
  unfold Clean at hNotClean
  push_neg at hNotClean
  -- extract the witness (q, divisibility) from Prop-∃ into Type via .choose
  let q : ℕ := hNotClean.choose
  have hq : q.Prime ∧ q ≤ A ∧ (q ∣ (6 * n - 1) ∨ q ∣ (6 * n + 1)) := hNotClean.choose_spec
  obtain ⟨hqPrime, hqA, hbad⟩ := hq
  by_cases hminus : q ∣ (6 * n - 1)
  · exact ⟨q, Side.minus,
      { peel := hPeel, smallPrime := hqPrime, smallWithinScale := hqA, smallDivides := hminus }⟩
  · have hplus : q ∣ (6 * n + 1) := hbad.resolve_left hminus
    exact ⟨q, Side.plus,
      { peel := hPeel, smallPrime := hqPrime, smallWithinScale := hqA, smallDivides := hplus }⟩

/--
Classify a single proper peel target.

This is the point at which the previous graph was too narrow.  If the peel lands
in an old clean centre, we now return `oldCleanCenter` instead of demanding a
fake boundary defect.
-/
noncomputable def ExtendedOneStepOutcome.ofPeelTarget {A M0 m : ℕ}
    (hmFresh : M0 < m)
    (hmClean : Clean A m)
    (P : ProperPeelTarget A m) : ExtendedOneStepOutcome A M0 m := by
  classical
  by_cases hFreshTarget : M0 < P.target
  · by_cases hTargetClean : Clean A P.target
    · exact ExtendedOneStepOutcome.descend hmFresh hmClean hTargetClean P.peel hFreshTarget
    · obtain ⟨q, s, hBoundary⟩ := properBoundaryPeel_of_not_clean_target P.peel hTargetClean
      exact ExtendedOneStepOutcome.freshDefect hmFresh hmClean hBoundary hFreshTarget
  · have hOld : P.target ≤ M0 := by omega
    by_cases hTargetClean : Clean A P.target
    · exact ExtendedOneStepOutcome.oldCleanCenter hmFresh hmClean hTargetClean P.peel hOld
    · obtain ⟨q, s, hBoundary⟩ := properBoundaryPeel_of_not_clean_target P.peel hTargetClean
      exact ExtendedOneStepOutcome.oldDefectAbsorb hmFresh hmClean hBoundary hOld

/-#############################################################################
  §4. Extended flows from one-step outcomes
#############################################################################-/

/-- Extended proper flow whose start is fixed externally. -/
structure ExtendedProperFlowFrom (A M0 m : ℕ) where
  terminal : State
  steps : ℕ
  nonempty : 0 < steps
  properPath : PathN (ProperRealStep A M0) steps (State.center m) terminal
  startClean : Clean A m
  startFresh : M0 < m
  terminalLegal : Legal A M0 terminal
  ledgerTerminal : ExtendedLedgerTerminal A M0 terminal

/-- Convert a fixed-start extended flow to the general extended flow object. -/
def ExtendedProperFlowFrom.toFlow {A M0 m : ℕ}
    (F : ExtendedProperFlowFrom A M0 m) : ExtendedProperGeneratedFlow A M0 :=
  { start := m
    terminal := F.terminal
    steps := F.steps
    nonempty := F.nonempty
    properPath := F.properPath
    startClean := F.startClean
    startFresh := F.startFresh
    terminalLegal := F.terminalLegal
    ledgerTerminal := F.ledgerTerminal }

@[simp] theorem extendedProperFlowFrom_toFlow_start {A M0 m : ℕ}
    (F : ExtendedProperFlowFrom A M0 m) : F.toFlow.start = m := rfl


/-- One proper boundary step to a fresh defect gives an extended flow from `m`. -/
def flowFrom_freshDefect {A M0 m n q : ℕ} {s : Side}
    (hmFresh : M0 < m)
    (hmClean : Clean A m)
    (hBoundary : ProperBoundaryPeel A m n q s)
    (hFreshTarget : M0 < n) : ExtendedProperFlowFrom A M0 m :=
  { terminal := State.defect n q s
    steps := 1
    nonempty := by omega
    properPath := by
      exact ⟨State.defect n q s, ProperRealStep.boundary hmClean hBoundary, rfl⟩
    startClean := hmClean
    startFresh := hmFresh
    terminalLegal := ⟨hBoundary.smallPrime, hBoundary.smallWithinScale, hBoundary.smallDivides⟩
    ledgerTerminal := by
      exact extendedLedgerTerminal_freshDefect
        ⟨hFreshTarget,
          ⟨hBoundary.smallPrime, hBoundary.smallWithinScale, hBoundary.smallDivides⟩,
          ⟨hBoundary.smallPrime, hBoundary.smallWithinScale, hBoundary.smallDivides⟩⟩ }

/-- Boundary step followed by old absorb gives an extended flow from `m`. -/
def flowFrom_oldDefectAbsorb {A M0 m n q : ℕ} {s : Side}
    (hmFresh : M0 < m)
    (hmClean : Clean A m)
    (hBoundary : ProperBoundaryPeel A m n q s)
    (hOld : n ≤ M0) : ExtendedProperFlowFrom A M0 m :=
  { terminal := State.absorber n
    steps := 2
    nonempty := by omega
    properPath := by
      refine ⟨State.defect n q s, ProperRealStep.boundary hmClean hBoundary, ?_⟩
      exact ⟨State.absorber n, ProperRealStep.absorb hOld, rfl⟩
    startClean := hmClean
    startFresh := hmFresh
    terminalLegal := hOld
    ledgerTerminal := by
      exact extendedLedgerTerminal_oldAbsorber ⟨hOld, hOld⟩ }

/-- A proper peel landing directly in an old clean centre gives an extended flow. -/
def flowFrom_oldCleanCenter {A M0 m n : ℕ}
    (hmFresh : M0 < m)
    (hmClean : Clean A m)
    (hnClean : Clean A n)
    (hPeel : ProperCenterPeel A m n)
    (hOld : n ≤ M0) : ExtendedProperFlowFrom A M0 m :=
  { terminal := State.center n
    steps := 1
    nonempty := by omega
    properPath := by
      exact ⟨State.center n, ProperRealStep.clean hmClean hnClean hPeel, rfl⟩
    startClean := hmClean
    startFresh := hmFresh
    terminalLegal := hnClean
    ledgerTerminal := extendedLedgerTerminal_oldCleanCenter hOld hnClean }

/-- Prepend a proper clean descent to a recursively produced extended flow. -/
def prependExtendedDescend {A M0 m n : ℕ}
    (hmClean : Clean A m)
    (hnClean : Clean A n)
    (hPeel : ProperCenterPeel A m n)
    (F : ExtendedProperFlowFrom A M0 n) : ExtendedProperFlowFrom A M0 m :=
  { terminal := F.terminal
    steps := F.steps + 1
    nonempty := by omega
    properPath := by
      refine ⟨State.center n, ?_, F.properPath⟩
      exact ProperRealStep.clean hmClean hnClean hPeel
    startClean := hmClean
    startFresh := by
      have hnm : n < m := hPeel.smaller
      have hnf : M0 < n := F.startFresh
      omega
    terminalLegal := F.terminalLegal
    ledgerTerminal := F.ledgerTerminal }

/-#############################################################################
  §5. Well-founded construction from the normalizer
#############################################################################-/

/--
Build an extended proper flow from a fresh clean start, using only the local
proper peel normalizer and the global twin bound for recursive descendants.
-/
noncomputable def extendedFlowFrom_of_normalizer {A M0 : ℕ}
    (N : ProperOneStepNormalizer A M0)
    (hTwinBound : TwinBoundAbove M0)
    (m : ℕ) (hFresh : M0 < m) (hClean : Clean A m) :
    ExtendedProperFlowFrom A M0 m := by
  classical
  induction m using Nat.strongRecOn with
  | ind m IH =>
      have hNoTwin : ¬ TwinCenterZ m := hTwinBound m hFresh
      let P := N.peelOf m hFresh hClean hNoTwin
      let O := ExtendedOneStepOutcome.ofPeelTarget (A := A) (M0 := M0) hFresh hClean P
      cases O with
      | freshDefect hmFresh hmClean hBoundary hFreshTarget =>
          exact flowFrom_freshDefect hmFresh hmClean hBoundary hFreshTarget
      | oldDefectAbsorb hmFresh hmClean hBoundary hOld =>
          exact flowFrom_oldDefectAbsorb hmFresh hmClean hBoundary hOld
      | oldCleanCenter hmFresh hmClean hnClean hPeel hOld =>
          exact flowFrom_oldCleanCenter hmFresh hmClean hnClean hPeel hOld
      | descend hmFresh hmClean hnClean hPeel hFreshTarget =>
          exact prependExtendedDescend hmClean hnClean hPeel
            (IH _ hPeel.smaller hFreshTarget hnClean)

/-- Local factory for extended flows. -/
structure ExtendedGeneratedFlowFactory (A M0 : ℕ) where
  flowOf : ∀ m : ℕ, M0 < m → Clean A m → ¬ TwinCenterZ m →
    ExtendedProperGeneratedFlow A M0
  admissible : ∀ m hFresh hClean hNoTwin,
    ExtendedFlowAdmissible (flowOf m hFresh hClean hNoTwin)
  start_eq : ∀ m hFresh hClean hNoTwin,
    (flowOf m hFresh hClean hNoTwin).start = m

/-- A normalizer plus a twin bound gives an extended flow factory. -/
noncomputable def extendedGeneratedFlowFactory_of_normalizer {A M0 : ℕ}
    (N : ProperOneStepNormalizer A M0)
    (hTwinBound : TwinBoundAbove M0) : ExtendedGeneratedFlowFactory A M0 :=
  { flowOf := fun m hFresh hClean _hNoTwin =>
      (extendedFlowFrom_of_normalizer N hTwinBound m hFresh hClean).toFlow
    admissible := by
      intro m hFresh hClean hNoTwin
      exact extendedFlow_admissible _
    start_eq := by
      intro m hFresh hClean hNoTwin
      rfl }

/-#############################################################################
  §6. Infinitude is preserved for extended flows
#############################################################################-/

/-- The canonical extended flow family generated from clean starts. -/
def extendedFactoryFlowFamily {A M0 : ℕ}
    (G : ExtendedGeneratedFlowFactory A M0)
    (hTwinBound : TwinBoundAbove M0) : Set (ExtendedProperGeneratedFlow A M0) :=
  {F | ∃ (m : ℕ) (hFresh : M0 < m) (hClean : Clean A m),
    F = G.flowOf m hFresh hClean (hTwinBound m hFresh)}

/-- Every member of the extended factory family is admissible. -/
theorem extendedFactoryFlowFamily_admissible {A M0 : ℕ}
    (G : ExtendedGeneratedFlowFactory A M0)
    (hTwinBound : TwinBoundAbove M0) :
    ∀ F ∈ extendedFactoryFlowFamily G hTwinBound, ExtendedFlowAdmissible F := by
  intro F hF
  rcases hF with ⟨m, hFresh, hClean, rfl⟩
  exact G.admissible m hFresh hClean (hTwinBound m hFresh)

/-- The extended factory preserves infinitude of clean starts. -/
theorem extendedFactoryFlowFamily_infinite {A M0 : ℕ}
    (G : ExtendedGeneratedFlowFactory A M0)
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    (extendedFactoryFlowFamily G hTwinBound).Infinite := by
  classical
  let 𝓕 : Set (ExtendedProperGeneratedFlow A M0) :=
    extendedFactoryFlowFamily G hTwinBound
  intro hFin𝓕
  have hImageFinite : (ExtendedProperGeneratedFlow.start '' 𝓕).Finite :=
    hFin𝓕.image ExtendedProperGeneratedFlow.start
  have hCleanSubset : {m : ℕ | M0 < m ∧ Clean A m} ⊆
      ExtendedProperGeneratedFlow.start '' 𝓕 := by
    intro m hm
    let F : ExtendedProperGeneratedFlow A M0 :=
      G.flowOf m hm.1 hm.2 (hTwinBound m hm.1)
    refine ⟨F, ?_, ?_⟩
    · exact ⟨m, hm.1, hm.2, rfl⟩
    · dsimp [F]
      exact G.start_eq m hm.1 hm.2 (hTwinBound m hm.1)
  exact hCleanStarts (hImageFinite.subset hCleanSubset)

/-- A normalizer closes the corrected extended source branch. -/
theorem twinBoundForcesInfiniteExtendedGeneratedFlows_of_normalizer {A M0 : ℕ}
    (N : ProperOneStepNormalizer A M0)
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
      InfiniteExtendedGeneratedFlowFamily A M0 𝓕 := by
  let G := extendedGeneratedFlowFactory_of_normalizer N hTwinBound
  refine ⟨extendedFactoryFlowFamily G hTwinBound, ?_⟩
  exact ⟨extendedFactoryFlowFamily_infinite G hCleanStarts hTwinBound,
    extendedFactoryFlowFamily_admissible G hTwinBound⟩

/-#############################################################################
  §7. Finite-key pigeonhole on corrected extended flows
#############################################################################-/

/-- Finite semantic ledger projection on corrected extended flows. -/
structure SemanticExtendedFlowLedgerProjection (A M0 : ℕ) where
  Key : Type
  finiteKey : Finite Key
  keyFlow : ExtendedProperGeneratedFlow A M0 → Key

/-- Same-key collision between two corrected generated flows. -/
structure ExtendedFlowSameKeyCollision {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (𝓕 : Set (ExtendedProperGeneratedFlow A M0))
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop where
  distinct : F₁ ≠ F₂
  left_mem : F₁ ∈ 𝓕
  right_mem : F₂ ∈ 𝓕
  left_admissible : ExtendedFlowAdmissible F₁
  right_admissible : ExtendedFlowAdmissible F₂
  same_key : proj.keyFlow F₁ = proj.keyFlow F₂

/-- Pigeonhole on corrected extended flow genealogies. -/
theorem infinite_extended_flows_force_key_collision
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0)
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕) :
    ∃ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
      ExtendedFlowSameKeyCollision proj 𝓕 F₁ F₂ := by
  classical
  letI : Finite proj.Key := proj.finiteKey
  rcases h𝓕 with ⟨hInf, hMem⟩
  obtain ⟨F₁, F₂, hF₁, hF₂, hne, hkey⟩ :=
    BoundaryLedgerCollision.infinite_set_key_collision
      (σ := ExtendedProperGeneratedFlow A M0) (Key := proj.Key)
      (S := 𝓕) hInf proj.keyFlow
  exact ⟨F₁, F₂,
    ⟨hne, hF₁, hF₂, hMem F₁ hF₁, hMem F₂ hF₂, hkey⟩⟩

/-#############################################################################
  §8. The new exact source-side obligation
#############################################################################-/

/--
After this patch the corrected source side is reduced to one arithmetic object:
proper one-step normalisation of a clean non-twin side into a smaller 6n±1
centre.
-/
abbrev TheProperOneStepNormalizerObligation (A M0 : ℕ) : Type :=
  ProperOneStepNormalizer A M0


/-! #### patch: clean_nonTwin_to_cofactor_normalizer -/


/-#############################################################################
  §1. Raw big side divisors from a clean non-twin centre
#############################################################################-/

/--
A raw large-prime divisor of one side of the centre `m`.

This is weaker than `ProperCenterPeel`: it has the big divisor of `6m±1`, but it
has not yet normalized the cofactor into a smaller centre `6n±1`.
-/
structure RawBigSideDivisor (A m : ℕ) where
  inSide : Side
  bigDivisor : ℕ
  bigPrime : bigDivisor.Prime
  bigBeyondScale : A < bigDivisor
  bigDivides : bigDivisor ∣ sideValue inSide m
  /-- AUDIT-PATCH (degenerate peel): the divisor is PROPER — otherwise the prime side divides
      itself and the cofactor 1 = 6·0+1 gives a peel into center 0 WITHOUT the twin hypothesis (vacuity exploit). -/
  properDiv : bigDivisor < sideValue inSide m

/-- Cleanliness of a centre forbids every small prime on the minus side. -/
theorem clean_forbids_minus {A m q : ℕ}
    (hClean : Clean A m) (hq : q.Prime) (hqA : q ≤ A) :
    ¬ q ∣ (6 * m - 1) := by
  intro hdiv
  exact hClean q hq hqA (Or.inl hdiv)

/-- Cleanliness of a centre forbids every small prime on the plus side. -/
theorem clean_forbids_plus {A m q : ℕ}
    (hClean : Clean A m) (hq : q.Prime) (hqA : q ≤ A) :
    ¬ q ∣ (6 * m + 1) := by
  intro hdiv
  exact hClean q hq hqA (Or.inr hdiv)

/--
A clean non-twin centre has a composite side, hence a large prime divisor on
one side.

This is a real proved arithmetic step: no graph edge or projection is used.
(Prop-form of existence; the data is extracted with `.some` below.)
-/
theorem exists_rawBigSideDivisor_of_clean_nonTwin {A m : ℕ}
    (hm : 1 ≤ m)
    (hClean : Clean A m)
    (hNoTwin : ¬ TwinCenterZ m) :
    Nonempty (RawBigSideDivisor A m) := by
  classical
  have hlo : 1 < 6 * m - 1 := by omega
  have hhi : 1 < 6 * m + 1 := by omega
  have hNoTwin' : ¬ ((6 * m - 1).Prime ∧ (6 * m + 1).Prime) := by
    simpa [TwinCenterZ] using hNoTwin
  rcases EuclidsPath.MkNode.composite_side_of_not_twin hlo hhi hNoTwin' with hminus | hplus
  · rcases hminus with ⟨hside, hcomp⟩
    -- b := minFac of the side; COMPOSITENESS is now LOAD-BEARING: it gives b < side (properness).
    set S := 6 * m - 1 with hS
    have hSne1 : S ≠ 1 := by omega
    have hbPrime : S.minFac.Prime := Nat.minFac_prime hSne1
    have hbDiv : S.minFac ∣ S := Nat.minFac_dvd S
    have hbBig : A < S.minFac := by
      by_contra hle
      exact clean_forbids_minus hClean hbPrime (by omega) hbDiv
    have hbLt : S.minFac < S := by
      rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hbDiv) with h | h
      · exact h
      · exact absurd (h ▸ hbPrime) hcomp
    exact ⟨{ inSide := Side.minus
             bigDivisor := S.minFac
             bigPrime := hbPrime
             bigBeyondScale := hbBig
             bigDivides := by simpa [sideValue, hS] using hbDiv
             properDiv := by simpa [sideValue, hS] using hbLt }⟩
  · rcases hplus with ⟨hside, hcomp⟩
    set S := 6 * m + 1 with hS
    have hSne1 : S ≠ 1 := by omega
    have hbPrime : S.minFac.Prime := Nat.minFac_prime hSne1
    have hbDiv : S.minFac ∣ S := Nat.minFac_dvd S
    have hbBig : A < S.minFac := by
      by_contra hle
      exact clean_forbids_plus hClean hbPrime (by omega) hbDiv
    have hbLt : S.minFac < S := by
      rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hbDiv) with h | h
      · exact h
      · exact absurd (h ▸ hbPrime) hcomp
    exact ⟨{ inSide := Side.plus
             bigDivisor := S.minFac
             bigPrime := hbPrime
             bigBeyondScale := hbBig
             bigDivides := by simpa [sideValue, hS] using hbDiv
             properDiv := by simpa [sideValue, hS] using hbLt }⟩

/-- The raw big divisor as data (via `Classical.choice` from existence). -/
noncomputable def rawBigSideDivisor_of_clean_nonTwin {A m : ℕ}
    (hm : 1 ≤ m)
    (hClean : Clean A m)
    (hNoTwin : ¬ TwinCenterZ m) :
    RawBigSideDivisor A m :=
  (exists_rawBigSideDivisor_of_clean_nonTwin hm hClean hNoTwin).some

/-#############################################################################
  §2. The exact remaining cofactor-normalisation input
#############################################################################-/

/--
A normalized cofactor target for a raw big divisor.

It says precisely that the cofactor of the chosen side is again a `6n±1` side,
and that the new centre is strictly smaller.
-/
structure ProperCofactorTarget {A m : ℕ} (R : RawBigSideDivisor A m) where
  target : ℕ
  outSide : Side
  factor : sideValue R.inSide m = R.bigDivisor * sideValue outSide target
  smaller : target < m
  /-- AUDIT-PATCH: the target is a genuine center (`≥ 1`), NOT the degenerate 0. -/
  targetPos : 1 ≤ target

/--
The remaining source-side arithmetic obligation.

This is intentionally much narrower than `ProperOneStepNormalizer`: the only
thing it still has to do is convert a raw large divisor of `6m±1` into a smaller
6n±1 cofactor target.
-/
structure ProperCofactorNormalizer (A : ℕ) where
  normalize : ∀ {m : ℕ}, 1 ≤ m →
    (R : RawBigSideDivisor A m) → ProperCofactorTarget R

/-- A normalized cofactor target yields the `ProperCenterPeel` certificate. -/
def properCenterPeel_of_cofactorTarget {A m : ℕ}
    (R : RawBigSideDivisor A m)
    (T : ProperCofactorTarget R) : ProperCenterPeel A m T.target :=
  { inSide := R.inSide
    outSide := T.outSide
    bigDivisor := R.bigDivisor
    bigPrime := R.bigPrime
    bigBeyondScale := R.bigBeyondScale
    factor := T.factor
    smaller := T.smaller
    targetPos := T.targetPos }

/--
A cofactor normalizer closes the previously isolated one-step normalizer.
-/
noncomputable def properOneStepNormalizer_of_cofactorNormalizer {A M0 : ℕ}
    (C : ProperCofactorNormalizer A) : ProperOneStepNormalizer A M0 :=
  { peelOf := by
      intro m hFresh hClean hNoTwin
      have hm : 1 ≤ m := by omega
      let R : RawBigSideDivisor A m :=
        rawBigSideDivisor_of_clean_nonTwin hm hClean hNoTwin
      let T : ProperCofactorTarget R := C.normalize hm R
      exact
        { target := T.target
          peel := properCenterPeel_of_cofactorTarget R T } }

/-#############################################################################
  §3. Source side closed from the cofactor normalizer
#############################################################################-/

/--
The generated-flow source side follows from the narrow cofactor normalizer.
-/
theorem twinBoundForcesInfiniteExtendedGeneratedFlows_of_cofactorNormalizer
    {A M0 : ℕ}
    (C : ProperCofactorNormalizer A)
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
      InfiniteExtendedGeneratedFlowFamily A M0 𝓕 := by
  exact twinBoundForcesInfiniteExtendedGeneratedFlows_of_normalizer
    (properOneStepNormalizer_of_cofactorNormalizer (A := A) (M0 := M0) C)
    hCleanStarts hTwinBound

/--
After this reduction, the source-side red line is exactly cofactor
normalisation, not graph plumbing and not pigeonhole.
-/
abbrev TheProperCofactorNormalizerObligation (A : ℕ) : Type :=
  ProperCofactorNormalizer A


/-! #### patch: cofactor_normalizer_close -/


/-#############################################################################
  §1. Side signs and Nat/Int bridge
#############################################################################-/

/-- Integer sign attached to a side. -/
def sideEta : Side → ℤ
  | Side.minus => -1
  | Side.plus  => 1

/-- The natural side value, cast to `ℤ`, is `6*m + η`. -/
theorem int_sideValue_eq {m : ℕ} (hm : 1 ≤ m) :
    ∀ s : Side, ((sideValue s m : ℕ) : ℤ) = 6 * (m : ℤ) + sideEta s := by
  intro s
  cases s with
  | minus =>
      have h1 : 1 ≤ 6 * m := by omega
      simp only [sideValue, sideEta]
      omega
  | plus =>
      simp only [sideValue, sideEta]
      push_cast
      ring

/-- The side sign is always one of `±1`. -/
theorem sideEta_pm (s : Side) : sideEta s = 1 ∨ sideEta s = -1 := by
  cases s <;> simp [sideEta]

/-- A positive integer centre recovered from the integer centre equation. -/
theorem int_center_to_nat_side {t η : ℤ}
    (hη : η = 1 ∨ η = -1) (ht0 : 0 ≤ t) (hpos : 0 < 6 * t + η) :
    ∃ n : ℕ, ∃ s : Side,
      ((sideValue s n : ℕ) : ℤ) = 6 * t + η ∧ (n : ℤ) = t := by
  rcases hη with rfl | rfl
  · refine ⟨t.toNat, Side.plus, ?_, ?_⟩
    · have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0
      simp [sideValue, htcast]
    · exact Int.toNat_of_nonneg ht0
  · refine ⟨t.toNat, Side.minus, ?_, ?_⟩
    · have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0
      have htNat : 1 ≤ t.toNat := by
        have htpos : 0 < t := by omega
        omega
      simp [sideValue, htcast]
      omega
    · exact Int.toNat_of_nonneg ht0

/-#############################################################################
  §2. Prime divisors of sides are `≥ 5` and `±1 mod 6`
#############################################################################-/

/-- No side `6m±1` with `m ≥ 1` is divisible by 2. -/
theorem two_not_dvd_sideValue {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    ¬ 2 ∣ sideValue s m := by
  intro h
  have hmod := Nat.mod_eq_zero_of_dvd h
  cases s with
  | minus =>
      simp [sideValue] at hmod
      omega
  | plus =>
      simp [sideValue] at hmod
      omega

/-- No side `6m±1` with `m ≥ 1` is divisible by 3. -/
theorem three_not_dvd_sideValue {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    ¬ 3 ∣ sideValue s m := by
  intro h
  have hmod := Nat.mod_eq_zero_of_dvd h
  cases s with
  | minus =>
      simp [sideValue] at hmod
      omega
  | plus =>
      simp [sideValue] at hmod
      omega

/-- A prime divisor of a side `6m±1` is at least 5. -/
theorem prime_dvd_sideValue_ge_five {b m : ℕ} {s : Side}
    (hm : 1 ≤ m) (hb : b.Prime) (hdiv : b ∣ sideValue s m) : 5 ≤ b := by
  by_contra hnot
  have hlt : b < 5 := Nat.lt_of_not_ge hnot
  have hb2 : 2 ≤ b := hb.two_le
  interval_cases b <;> try norm_num at hb
  · exact two_not_dvd_sideValue hm s hdiv
  · exact three_not_dvd_sideValue hm s hdiv

/-- A prime `b ≥ 5` is congruent to `1` or `5` modulo 6. -/
theorem prime_ge_five_mod_six_nat {b : ℕ} (hb : b.Prime) (h5 : 5 ≤ b) :
    b % 6 = 1 ∨ b % 6 = 5 := by
  have h2not : ¬ 2 ∣ b := by
    intro h2
    rcases hb.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · omega
  have h3not : ¬ 3 ∣ b := by
    intro h3
    rcases hb.eq_one_or_self_of_dvd 3 h3 with h | h
    · norm_num at h
    · omega
  have hcases :
      b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨
      b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5mod
  · have : 2 ∣ b := by omega
    exact False.elim (h2not this)
  · exact Or.inl h1
  · have : 2 ∣ b := by omega
    exact False.elim (h2not this)
  · have : 3 ∣ b := by omega
    exact False.elim (h3not this)
  · have : 2 ∣ b := by omega
    exact False.elim (h2not this)
  · exact Or.inr h5mod

/-- Integer version needed by `RigidClose.cofactor_is_center`. -/
theorem prime_ge_five_mod_six_int {b : ℕ} (hb : b.Prime) (h5 : 5 ≤ b) :
    ((b : ℤ) % 6 = 1 ∨ (b : ℤ) % 6 = 5) := by
  have hnat := prime_ge_five_mod_six_nat hb h5
  rcases hnat with h | h
  · left
    omega
  · right
    omega

/-#############################################################################
  §3. Close the cofactor normalizer
#############################################################################-/

/-- Turn a natural divisibility statement into the integer divisibility expected
by `cofactor_is_center`. -/
theorem int_dvd_side_of_nat_dvd {b m : ℕ} {s : Side}
    (hm : 1 ≤ m) (hdiv : b ∣ sideValue s m) :
    ((b : ℤ) ∣ 6 * (m : ℤ) + sideEta s) := by
  rcases hdiv with ⟨c, hc⟩
  refine ⟨(c : ℤ), ?_⟩
  have hside := int_sideValue_eq (m := m) hm s
  have hcInt : ((sideValue s m : ℕ) : ℤ) = (b : ℤ) * (c : ℤ) := by
    exact_mod_cast hc
  rw [← hside]
  exact hcInt

/-- The raw big divisor has a normalized smaller `6n±1` cofactor target (Prop-form). -/
theorem exists_properCofactorTarget_of_raw {A m : ℕ}
    (hm : 1 ≤ m) (R : RawBigSideDivisor A m) : Nonempty (ProperCofactorTarget R) := by
  classical
  let η : ℤ := sideEta R.inSide
  have hη : η = 1 ∨ η = -1 := sideEta_pm R.inSide
  have hsideInt : ((sideValue R.inSide m : ℕ) : ℤ) = 6 * (m : ℤ) + η :=
    int_sideValue_eq (m := m) hm R.inSide
  have hb5Nat : 5 ≤ R.bigDivisor :=
    prime_dvd_sideValue_ge_five (m := m) (s := R.inSide) hm R.bigPrime R.bigDivides
  have hb5Int : (5 : ℤ) ≤ (R.bigDivisor : ℤ) := by exact_mod_cast hb5Nat
  have hb6Int : ((R.bigDivisor : ℤ) % 6 = 1 ∨ (R.bigDivisor : ℤ) % 6 = 5) :=
    prime_ge_five_mod_six_int R.bigPrime hb5Nat
  have hdvdInt : ((R.bigDivisor : ℤ) ∣ 6 * (m : ℤ) + η) :=
    int_dvd_side_of_nat_dvd (m := m) (s := R.inSide) hm R.bigDivides
  rcases cofactor_is_center
      (t := (m : ℤ)) (q := (R.bigDivisor : ℤ)) (η := η)
      (by exact_mod_cast hm) hη hb5Int hb6Int hdvdInt with
    ⟨t', η', hη', hcenter, ht0, hlt⟩
  rcases R.bigDivides with ⟨c, hcNat⟩
  have hcInt : ((sideValue R.inSide m : ℕ) : ℤ) =
      (R.bigDivisor : ℤ) * (c : ℤ) := by
    exact_mod_cast hcNat
  have hquot_c : (6 * (m : ℤ) + η) / (R.bigDivisor : ℤ) = (c : ℤ) := by
    rw [← hsideInt, hcInt]
    exact Int.mul_ediv_cancel_left (c : ℤ) (by omega)
  have hcPos : 0 < (c : ℤ) := by
    have hsidePos : 0 < ((sideValue R.inSide m : ℕ) : ℤ) := by
      rw [hsideInt]
      rcases hη with h | h <;> rw [h] <;> omega
    nlinarith [hcInt, hb5Int]
  have hcofacPos : 0 < 6 * t' + η' := by
    rw [hcenter, hquot_c]
    exact hcPos
  rcases int_center_to_nat_side hη' ht0 hcofacPos with ⟨target, outSide, hout, htargetCast⟩
  -- AUDIT-PATCH: cofactor c ≥ 2 (from properDiv), hence target ≥ 1 (otherwise sideValue ∈ {0,1}).
  have hside5 : 5 ≤ sideValue R.inSide m := by
    cases hIn : R.inSide <;> simp [sideValue] <;> omega
  have hc2 : 2 ≤ c := by
    by_contra hlt2
    interval_cases c
    · simp at hcNat; omega
    · have : sideValue R.inSide m = R.bigDivisor := by omega
      have := R.properDiv
      omega
  have hc_eq : (c : ℤ) = 6 * t' + η' := by
    rw [← hquot_c, hcenter]
  have hc_center : (c : ℤ) = ((sideValue outSide target : ℕ) : ℤ) := by
    rw [hc_eq, ← hout]
  have htargetPos : 1 ≤ target := by
    by_contra h0
    have ht0' : target = 0 := by omega
    have hcle : (c : ℤ) ≤ 1 := by
      rw [hc_center, ht0']
      cases outSide <;> simp [sideValue]
    have : (2 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc2
    omega
  refine ⟨
    { target := target
      outSide := outSide
      factor := ?_
      smaller := ?_
      targetPos := htargetPos }⟩
  · -- Factor equality back in `ℕ`.
    have hfactorInt : ((sideValue R.inSide m : ℕ) : ℤ) =
        (R.bigDivisor : ℤ) * ((sideValue outSide target : ℕ) : ℤ) := by
      rw [hcInt, hc_center]
    exact_mod_cast hfactorInt
  · -- Strict descent of the centre.
    have htargetLtInt : (target : ℤ) < (m : ℤ) := by
      rw [htargetCast]
      exact hlt
    exact_mod_cast htargetLtInt

/-- The raw big divisor has a normalized smaller `6n±1` cofactor target (data via choice). -/
noncomputable def properCofactorTarget_of_raw {A m : ℕ}
    (hm : 1 ≤ m) (R : RawBigSideDivisor A m) : ProperCofactorTarget R :=
  (exists_properCofactorTarget_of_raw hm R).some

/-- The previously isolated cofactor normalizer is now supplied by the
`RigidClose.cofactor_is_center` bridge. -/
noncomputable def closedProperCofactorNormalizer (A : ℕ) :
    ProperCofactorNormalizer A :=
  { normalize := by
      intro m hm R
      exact properCofactorTarget_of_raw hm R }

/-- Source side now closes from the already-proved clean-start supply and the
proper cofactor normalizer. -/
theorem twinBoundForcesInfiniteExtendedGeneratedFlows_closed_cofactor
    {A M0 : ℕ}
    (hCleanStarts : InfiniteCleanStarts A M0)
    (hTwinBound : TwinBoundAbove M0) :
    ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
      InfiniteExtendedGeneratedFlowFamily A M0 𝓕 := by
  exact twinBoundForcesInfiniteExtendedGeneratedFlows_of_cofactorNormalizer
    (C := closedProperCofactorNormalizer A) hCleanStarts hTwinBound

/-- After this patch, the source side no longer depends on a cofactor oracle. -/
abbrev TheSourceSideAfterCofactorClose (A M0 : ℕ) : Prop :=
  TwinBoundAbove M0 → InfiniteCleanStarts A M0 →
    ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
      InfiniteExtendedGeneratedFlowFamily A M0 𝓕


/-! #### patch: maximal_extended_flow_close -/


/-#############################################################################
  §1. Close infinite clean starts from the existing primorial supply
#############################################################################-/

/-- Convert the integer clean predicate supplied by `Residuals` into the natural
clean predicate used by the concrete graph.  The hypothesis `1 ≤ m` is essential:
for `m = 0`, the natural expression `6*m - 1` truncates to `0`, whereas the
integer expression is `-1`. -/
theorem clean_of_cleanZ_nat {A m : ℕ}
    (hm : 1 ≤ m) (hZ : CleanZ A ((m : ℕ) : ℤ)) : Clean A m := by
  intro q hq hqA hbad
  apply hZ q hq hqA
  rcases hbad with hminus | hplus
  · left
    have hInt : ((q : ℤ) ∣ ((6 * m - 1 : ℕ) : ℤ)) :=
      Int.natCast_dvd_natCast.mpr hminus
    have hEq : ((6 * m - 1 : ℕ) : ℤ) = 6 * (m : ℤ) - 1 := by
      omega
    simpa [hEq] using hInt
  · right
    have hInt : ((q : ℤ) ∣ ((6 * m + 1 : ℕ) : ℤ)) :=
      Int.natCast_dvd_natCast.mpr hplus
    have hEq : ((6 * m + 1 : ℕ) : ℤ) = 6 * (m : ℤ) + 1 := by
      omega
    simpa [hEq] using hInt

/-- A subset of `ℕ` is infinite if it is unbounded above. -/
theorem natSet_infinite_of_unbounded {S : Set ℕ}
    (h : ∀ N : ℕ, ∃ m : ℕ, N < m ∧ m ∈ S) : S.Infinite := by
  classical
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨m, hmN, hmS⟩ := h N
  exact ⟨m, hmS, hmN⟩

/-- The clean-start source is closed using `Residuals.carrier_nonempty_above`.
For every threshold, that theorem supplies a clean primorial multiple above it;
unboundedness gives infinitude. -/
theorem infiniteCleanStarts_closed (A M0 : ℕ) :
    InfiniteCleanStarts A M0 := by
  classical
  refine natSet_infinite_of_unbounded ?_
  intro N
  obtain ⟨m, hmAbove, hCleanZ⟩ :=
    carrier_nonempty_above A (max N M0)
  have hmN : N < m := lt_of_le_of_lt (Nat.le_max_left N M0) hmAbove
  have hmM0 : M0 < m := lt_of_le_of_lt (Nat.le_max_right N M0) hmAbove
  have hm1 : 1 ≤ m := by omega
  refine ⟨m, hmN, ?_⟩
  exact ⟨hmM0, clean_of_cleanZ_nat hm1 hCleanZ⟩

/-#############################################################################
  §2. Resolution and contradiction for corrected extended generated flows
#############################################################################-/

/-- The same two alternatives as before, now for corrected extended flows. -/
abbrev ExtendedFlowResolutionAlternative (A M0 : ℕ) : Prop :=
  LegalCycle (RealStep A M0) (Legal A M0) ∨
    BoundaryDefectPayment.ImpossiblePayment

/-- Neither resolution branch is available for free in the concrete Step00 graph:
`lexRank` forbids cycles, and the payment patch forbids impossible payment. -/
theorem no_extendedFlowResolutionAlternative (A M0 : ℕ) :
    ¬ ExtendedFlowResolutionAlternative A M0 := by
  intro h
  rcases h with hCycle | hPayment
  · exact no_concrete_legalCycle_by_lexRank (A := A) (M0 := M0) hCycle
  · exact BoundaryDefectPayment.impossiblePayment_false hPayment

/-- Semantic resolution of a same-key collision between corrected generated
flows.  This is now the only remaining Euclidean-engine obligation. -/
def SemanticExtendedFlowLedgerCollisionResolves
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    F₁ ≠ F₂ →
    ExtendedFlowAdmissible F₁ →
    ExtendedFlowAdmissible F₂ →
    proj.keyFlow F₁ = proj.keyFlow F₂ →
      ExtendedFlowResolutionAlternative A M0

/-- An infinite corrected generated-flow family plus finite key and semantic
resolution produces one of the two forbidden alternatives. -/
theorem infinite_extended_flows_force_cycle_or_payment
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0)
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕)
    (hResolve : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ExtendedFlowResolutionAlternative A M0 := by
  rcases infinite_extended_flows_force_key_collision
      (A := A) (M0 := M0) proj h𝓕 with ⟨F₁, F₂, hCol⟩
  exact hResolve F₁ F₂
    hCol.distinct hCol.left_admissible hCol.right_admissible hCol.same_key

/-- Corrected extended-flow source plus semantic resolution is contradictory. -/
theorem infinite_extended_flows_impossible_with_resolution
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0)
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕)
    (hResolve : SemanticExtendedFlowLedgerCollisionResolves proj) :
    False := by
  have hAlt : ExtendedFlowResolutionAlternative A M0 :=
    infinite_extended_flows_force_cycle_or_payment
      (A := A) (M0 := M0) proj h𝓕 hResolve
  exact no_extendedFlowResolutionAlternative A M0 hAlt

/-#############################################################################
  §3. Source side is now closed from a twin bound
#############################################################################-/

/-- With the cofactor normalizer closed and clean starts supplied, a twin bound
forces an infinite family of corrected generated flows. -/
theorem twinBoundForcesInfiniteExtendedGeneratedFlows_closed
    {A M0 : ℕ} (hTwinBound : TwinBoundAbove M0) :
    ∃ 𝓕 : Set (ExtendedProperGeneratedFlow A M0),
      InfiniteExtendedGeneratedFlowFamily A M0 𝓕 := by
  exact twinBoundForcesInfiniteExtendedGeneratedFlows_closed_cofactor
    (A := A) (M0 := M0)
    (hCleanStarts := infiniteCleanStarts_closed A M0)
    (hTwinBound := hTwinBound)

/-- Maximal local close: for fixed `A,M0`, the only remaining input is semantic
collision-resolution for the corrected flow ledger projection. -/
theorem twinBound_impossible_with_semanticExtendedResolution
    {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hResolve : SemanticExtendedFlowLedgerCollisionResolves proj) :
    False := by
  obtain ⟨𝓕, h𝓕⟩ :=
    twinBoundForcesInfiniteExtendedGeneratedFlows_closed
      (A := A) (M0 := M0) hTwinBound
  exact infinite_extended_flows_impossible_with_resolution
    (A := A) (M0 := M0) proj h𝓕 hResolve

/-#############################################################################
  §4. From `¬ TwinLowers.Infinite` to a concrete twin bound
#############################################################################-/

/-- If lower twin primes are not infinite, then twin centres are bounded. -/
theorem exists_twinBoundAbove_of_not_twinLowersInfinite
    (hfin : ¬ TwinLowers.Infinite) :
    ∃ M0 : ℕ, TwinBoundAbove M0 := by
  classical
  by_contra hNoBound
  simp only [TwinBoundAbove, not_exists, not_forall, not_not] at hNoBound
  have hUnbounded : ∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m := by
    intro N
    obtain ⟨m, hmN, hTwinZ⟩ := hNoBound N
    refine ⟨m, hmN, ?_⟩
    simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ
  exact hfin (EuclidsPath.infinite_of_unbounded_centers hUnbounded)

/-#############################################################################
  §5. Final near-close statement
#############################################################################-/

/--
Final near-close.

If for a fixed scale `A` one can assign, for every possible finite twin-bound
`M0`, a finite semantic ledger projection on corrected generated flows whose
same-key collisions resolve to cycle-or-payment, then the twin-prime lower set is
infinite.

All other branches are already closed in this file chain:
clean starts, source flows, cofactor normalisation, payment impossibility, and
lexRank acyclicity.
-/
theorem twinLowersInfinite_of_global_semanticExtendedResolution
    (A : ℕ)
    (projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0)
    (hResolve : ∀ M0 : ℕ,
      SemanticExtendedFlowLedgerCollisionResolves (projOf M0)) :
    TwinLowers.Infinite := by
  classical
  by_contra hfin
  obtain ⟨M0, hTwinBound⟩ :=
    exists_twinBoundAbove_of_not_twinLowersInfinite hfin
  exact twinBound_impossible_with_semanticExtendedResolution
    (A := A) (M0 := M0) hTwinBound (projOf M0) (hResolve M0)

/-- The exact remaining obligation after maximal closure. -/
abbrev TheLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0)

/-- If the last semantic obligation is supplied, the twin lower-prime set is
infinite. -/
theorem twinLowersInfinite_of_lastStep00Obligation
    (H : TheLastStep00Obligation) : TwinLowers.Infinite := by
  rcases H with ⟨A, projOf, hResolve⟩
  exact twinLowersInfinite_of_global_semanticExtendedResolution A projOf hResolve




/-! ### Sharpening the final reduction: the certificate = twin-detector; cofinal weakening

`no_extendedFlowResolutionAlternative` (cycle and payment both impossible) turns `Resolves proj` into
"there are NO same-key collisions" = injectivity of the key on admissible flows. And since under a twin-bound the ∞-family
is PROVEN, a finite injective key is impossible ⟹ `Resolves` under a twin-bound is always false. Reversal:
`Resolves` on M0 ⟹ a twin above M0. The input is a twin-detector, NOT a neutral condition. -/

/-- **`resolves_iff_key_injective` — PROVEN (characterization).** `Resolves proj` ⟺ the key is injective
    on admissible extended flows (both resolution alternatives are impossible). -/
theorem resolves_iff_key_injective {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    SemanticExtendedFlowLedgerCollisionResolves proj ↔
    (∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0, F₁ ≠ F₂ →
      ExtendedFlowAdmissible F₁ → ExtendedFlowAdmissible F₂ →
      proj.keyFlow F₁ ≠ proj.keyFlow F₂) := by
  constructor
  · intro hRes F₁ F₂ hne h1 h2 hkey
    exact no_extendedFlowResolutionAlternative A M0 (hRes F₁ F₂ hne h1 h2 hkey)
  · intro hInj F₁ F₂ hne h1 h2 hkey
    exact absurd hkey (hInj F₁ F₂ hne h1 h2)

/-- **`twin_above_of_resolves` — PROVEN (certificate = twin-detector).** `Resolves` at scale `M0`
    PRESENTS a twin above `M0`: otherwise twin-bound + Resolves are contradictory
    (`twinBound_impossible_with_semanticExtendedResolution`). Hence the input is not weaker than the goal at M0. -/
theorem twin_above_of_resolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hRes : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m := by
  by_contra hno
  push_neg at hno
  have hBound : TwinBoundAbove M0 := fun m hm => hno m hm
  exact twinBound_impossible_with_semanticExtendedResolution hBound proj hRes

/-- **`twinLowersInfinite_of_cofinal_resolves` — PROVEN (weakening of TheLastStep00Obligation).**
    `Resolves` on COFINALLY many `M0` (not on all) suffices: each such `M0` gives a twin above,
    twin-centers are unbounded ⟹ `TwinLowers.Infinite`. -/
theorem twinLowersInfinite_of_cofinal_resolves {A : ℕ}
    (hCof : ∀ N : ℕ, ∃ M0, N ≤ M0 ∧
      ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj) :
    EuclidsPath.TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨M0, hNM0, proj, hRes⟩ := hCof N
  obtain ⟨m, hM0m, hTwin⟩ := twin_above_of_resolves proj hRes
  refine ⟨m, by omega, ?_⟩
  simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwin


/-! ### STRICT layer: return-path certificate + final strict reduction audit.
The missing intermediate layer (semantic_extended_collision_expanded) is BUILT: pathN_trans,
return-certificate ⟹ cycle (concatenation of forward+return), both branches refuted, strict⟹old,
TheStrictLastStep00Obligation. Then — the body of the final_strict_reduction_audit brick. -/

open EuclidsPath.LabelledFanIn EuclidsPath.BoundaryLedgerCollision EuclidsPath.BoundaryDefectPayment

-- PATH CONCATENATION (the missing mechanics)
theorem pathN_trans {α : Type*} {R : α → α → Prop} :
    ∀ {n m : ℕ} {X Y Z : α}, PathN R n X Y → PathN R m Y Z → PathN R (n + m) X Z
  | 0, m, X, Y, Z, h1, h2 => by
      have : X = Y := h1
      subst this
      simpa using h2
  | Nat.succ n, m, X, Y, Z, h1, h2 => by
      rcases h1 with ⟨W, hXW, hWY⟩
      have hrec : PathN R (n + m) W Z := pathN_trans hWY h2
      rw [Nat.succ_add]
      exact ⟨W, hXW, hrec⟩

-- RETURN-CERTIFICATE: one of the genealogies returns from the terminal to ITS OWN start
def ExtendedFlowReturnCertificate {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  NonemptyPath (RealStep A M0) F₁.terminal (State.center F₁.start) ∨
  NonemptyPath (RealStep A M0) F₂.terminal (State.center F₂.start)

-- return-certificate ⟹ legal cycle (concatenation of the forward genealogy with the return path)
theorem extendedFlowReturnCertificate_forces_legalCycle {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (h : ExtendedFlowReturnCertificate F₁ F₂) :
    LegalCycle (RealStep A M0) (Legal A M0) := by
  rcases h with hret | hret
  all_goals {
    rcases hret with ⟨k, hk, hpath⟩
    first
    | (refine ⟨State.center F₁.start, F₁.startClean, F₁.steps + k, by have := F₁.nonempty; omega, ?_⟩
       exact pathN_trans (properPath_to_realPath F₁.properPath) hpath)
    | (refine ⟨State.center F₂.start, F₂.startClean, F₂.steps + k, by have := F₂.nonempty; omega, ?_⟩
       exact pathN_trans (properPath_to_realPath F₂.properPath) hpath) }

-- EXPANDED ALTERNATIVE (lower level than LegalCycle ∨ Payment)
def ExpandedExtendedFlowResolutionAlternative {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂ ∨ BoundaryDefectPayment.ImpossiblePayment

-- both branches are ALREADY refuted (cycle — lexRank; payment — primorial)
theorem no_expandedExtendedFlowResolutionAlternative {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    ¬ ExpandedExtendedFlowResolutionAlternative F₁ F₂ := by
  rintro (hret | hpay)
  · exact no_concrete_legalCycle_by_lexRank (A := A) (M0 := M0)
      (extendedFlowReturnCertificate_forces_legalCycle hret)
  · exact BoundaryDefectPayment.impossiblePayment_false hpay

-- STRICT-RESOLVER (the final strict form of the input)
def StrictSemanticExtendedFlowLedgerCollisionResolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    F₁ ≠ F₂ → ExtendedFlowAdmissible F₁ → ExtendedFlowAdmissible F₂ →
    proj.keyFlow F₁ = proj.keyFlow F₂ →
    ExpandedExtendedFlowResolutionAlternative F₁ F₂

-- strict ⟹ the old resolver
theorem strictSemanticExtended_resolves_old {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (h : StrictSemanticExtendedFlowLedgerCollisionResolves proj) :
    SemanticExtendedFlowLedgerCollisionResolves proj := by
  intro F₁ F₂ hne h1 h2 hkey
  rcases h F₁ F₂ hne h1 h2 hkey with hret | hpay
  · exact Or.inl (extendedFlowReturnCertificate_forces_legalCycle hret)
  · exact Or.inr hpay

theorem twinBound_impossible_with_strictSemanticExtendedResolution {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hTwinBound : TwinBoundAbove M0)
    (h : StrictSemanticExtendedFlowLedgerCollisionResolves proj) : False :=
  twinBound_impossible_with_semanticExtendedResolution hTwinBound proj
    (strictSemanticExtended_resolves_old h)

abbrev TheStrictLastStep00Obligation : Prop :=
  ∃ (A : ℕ) (projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0),
    ∀ M0 : ℕ, StrictSemanticExtendedFlowLedgerCollisionResolves (projOf M0)

theorem twinLowersInfinite_of_strictLastStep00Obligation
    (H : TheStrictLastStep00Obligation) : EuclidsPath.TwinLowers.Infinite := by
  obtain ⟨A, projOf, hAll⟩ := H
  exact twinLowersInfinite_of_lastStep00Obligation
    ⟨A, projOf, fun M0 => strictSemanticExtended_resolves_old (hAll M0)⟩



/-! ### final strict reduction audit (brick) -/


/-#############################################################################
  §1. Final names
#############################################################################-/

/--
The final Step00 obligation after all no-cheat and generated-flow refinements.

This is just the strict obligation from the previous patch, renamed here as the
canonical final target of the audit.
-/
abbrev FinalStep00Obligation : Prop :=
  TheStrictLastStep00Obligation

/--
The local final resolver for a chosen scale `A`, twin bound `M0`, and finite
semantic flow-ledger projection `proj`.

This is where the real Euclidean engine must be exhibited.
-/
abbrev FinalLocalCollisionResolver {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  StrictSemanticExtendedFlowLedgerCollisionResolves proj

/--
The explicit local Euclidean-engine certificate for two colliding extended
flows: one of the two terminal states returns to its own start centre.
-/
abbrev FinalReturnCertificate {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂

/--
The strict expanded alternative demanded from a same-key collision.

This is intentionally lower-level than `LegalCycle ∨ ImpossiblePayment`: the
cycle must be produced from a concrete return-path certificate.
-/
abbrev FinalExpandedCollisionAlternative {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExpandedExtendedFlowResolutionAlternative F₁ F₂

/-#############################################################################
  §2. Mechanical bridges already closed
#############################################################################-/

/--
A return certificate mechanically gives a legal cycle.

This is not an arithmetic input: it is path concatenation of the stored forward
flow with the explicit return path.
-/
theorem finalReturnCertificate_forces_legalCycle {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (h : FinalReturnCertificate F₁ F₂) :
    LegalCycle (RealStep A M0) (Legal A M0) :=
  extendedFlowReturnCertificate_forces_legalCycle h

/--
The strict local resolver implies the older near-close resolver.

This records that the final strict target is stronger and more honest than the
previous `cycle ∨ payment` resolver.
-/
theorem finalLocalResolver_implies_oldResolver {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (h : FinalLocalCollisionResolver proj) :
    SemanticExtendedFlowLedgerCollisionResolves proj :=
  strictSemanticExtended_resolves_old h

/--
A twin bound is impossible once the final local resolver is supplied for the
chosen finite semantic projection.
-/
theorem twinBound_impossible_with_finalLocalResolver {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hTwinBound : TwinBoundAbove M0)
    (hResolver : FinalLocalCollisionResolver proj) :
    False :=
  twinBound_impossible_with_strictSemanticExtendedResolution proj hTwinBound hResolver

/-#############################################################################
  §3. Final theorem of the reduction
#############################################################################-/

/--
Final strict reduction theorem.

If the final Step00 obligation is provided, then the lower twin-prime infinitude
statement follows.  All previous construction, pigeonhole, no-cheat, payment,
and acyclicity layers are already consumed by
`twinLowersInfinite_of_strictLastStep00Obligation`.
-/
theorem twinLowersInfinite_of_finalStep00Obligation
    (H : FinalStep00Obligation) : TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation H

/-#############################################################################
  §4. Audit marker: what is *not* proved here
#############################################################################-/

/--
This predicate marks the exact place where an alleged finite semantic projection
would still have to provide real arithmetic content.

It is deliberately not proved here.  A candidate `proj.keyFlow` must be chosen, and
for every same-key collision of distinct admissible generated genealogies one
must extract either:

  * a concrete return path from the terminal of one genealogy back to its own
    start centre; or
  * the already-refuted impossible-payment certificate.

Pigeonhole alone only gives same-key collision.  Projection coarseness alone is
classified as cheating by the no-cheat audit.  The return path/payment extraction
is the remaining Euclidean-engine certificate.
-/
def RemainingEuclideanEngineCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  FinalLocalCollisionResolver proj

/--
A same-key collision still needs the engine certificate.

This is the local audit form: the data below is only an unresolved collision
unless `RemainingEuclideanEngineCertificate proj` can resolve it.
-/
def UnresolvedFinalCollision {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  F₁ ≠ F₂ ∧
  ExtendedFlowAdmissible F₁ ∧
  ExtendedFlowAdmissible F₂ ∧
  proj.keyFlow F₁ = proj.keyFlow F₂ ∧
  ¬ FinalExpandedCollisionAlternative F₁ F₂

/--
Any concrete same-key collision is unresolved unless the final engine certificate
is supplied.  The negation of the expanded alternative follows from the already
closed payment and acyclicity branches.
-/
theorem unresolvedFinalCollision_of_sameKey {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hne : F₁ ≠ F₂)
    (hAdm₁ : ExtendedFlowAdmissible F₁)
    (hAdm₂ : ExtendedFlowAdmissible F₂)
    (hkey : proj.keyFlow F₁ = proj.keyFlow F₂) :
    UnresolvedFinalCollision proj F₁ F₂ := by
  exact ⟨hne, hAdm₁, hAdm₂, hkey, no_expandedExtendedFlowResolutionAlternative⟩




/-- **`twin_above_of_strictResolves` — PROVEN (honesty of the strict form).** The strict resolver at scale
    `M0` ALSO presents a twin above `M0` (via `strict ⟹ old` and `twin_above_of_resolves`). The final
    input in strict form is still a twin-detector, not a neutral condition. -/
theorem twin_above_of_strictResolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (h : StrictSemanticExtendedFlowLedgerCollisionResolves proj) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves proj (strictSemanticExtended_resolves_old h)


/-- **`search_incompressible_under_twinBound` — PROVEN ("local P≠NP" as a theorem).** Under a
    twin-bound NO finite certificate (projection) is injective on admissible genealogies:
    the reverse search PROVABLY does not compress. In the P/NP vocabulary of §12: the asymmetry "verification is easy
    (`pathN_len_le_lexRank`) / search does not compress" — under the hypothesis of finiteness of twins this is a THEOREM,
    and compressibility at any scale presents a twin (`twin_above_of_resolves`). Does NOT prove P≠NP. -/
theorem search_incompressible_under_twinBound {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    ¬ (∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0, F₁ ≠ F₂ →
        ExtendedFlowAdmissible F₁ → ExtendedFlowAdmissible F₂ →
        proj.keyFlow F₁ ≠ proj.keyFlow F₂) := by
  intro hInj
  have hRes : SemanticExtendedFlowLedgerCollisionResolves proj := by
    intro F₁ F₂ hne h1 h2 hkey
    exact absurd hkey (hInj F₁ F₂ hne h1 h2)
  exact twinBound_impossible_with_semanticExtendedResolution hTwinBound proj hRes

/-#############################################################################
  ENERGY LEDGER (brick: energy_ledger_exhaustion).
  A finite energy-token on top of the semantic projection: "did not return — pay
  with fresh energy"; finiteness of `(key, token)` ⟹ double spend ⟹ an already burnt
  alternative (cycle/payment). Below — the brick + machine honesty (detector and
  factorization through the old node).
#############################################################################-/

/--
A finite energy ledger attached to a finite semantic flow-ledger projection.

`token F` is the finite resource consumed by the genealogy `F` if it is absorbed
by the old system without producing an explicit return path.  The central
soundness field is `no_double_spend_resolves`: two distinct admissible flows that
have the same semantic ledger key and the same energy token cannot remain two
independent absorptions.  Their double spend must resolve to the strict expanded
alternative: explicit return path or impossible payment.
-/
structure ExtendedFlowEnergyLedger {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) where
  Energy : Type
  finiteEnergy : Finite Energy
  token : ExtendedProperGeneratedFlow A M0 → Energy
  no_double_spend_resolves :
    ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
      F₁ ≠ F₂ →
      ExtendedFlowAdmissible F₁ →
      ExtendedFlowAdmissible F₂ →
      proj.keyFlow F₁ = proj.keyFlow F₂ →
      token F₁ = token F₂ →
        ExpandedExtendedFlowResolutionAlternative F₁ F₂

/-- The finite combined key: semantic ledger slot plus consumed energy token. -/
def energyCollisionKey {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (E : ExtendedFlowEnergyLedger proj)
    (F : ExtendedProperGeneratedFlow A M0) : proj.Key × E.Energy :=
  (proj.keyFlow F, E.token F)

/--
If two distinct admissible flows have the same ledger key, then avoiding the
strict expanded alternative forces them to use different energy tokens.

This is the local formal meaning of "to avoid the Euclidean engine, the system
must pay fresh energy."  The proof is not arithmetic: it is exactly the
no-double-spend rule of the energy ledger, contraposed.
-/
theorem same_key_without_expandedAlternative_requires_distinct_energy
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0}
    (E : ExtendedFlowEnergyLedger proj)
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hne : F₁ ≠ F₂)
    (hAdm₁ : ExtendedFlowAdmissible F₁)
    (hAdm₂ : ExtendedFlowAdmissible F₂)
    (hkey : proj.keyFlow F₁ = proj.keyFlow F₂)
    (hNoAlt : ¬ ExpandedExtendedFlowResolutionAlternative F₁ F₂) :
    E.token F₁ ≠ E.token F₂ := by
  intro htok
  exact hNoAlt (E.no_double_spend_resolves F₁ F₂ hne hAdm₁ hAdm₂ hkey htok)

/--
In the concrete Step00 graph the strict expanded alternative is already
impossible, so every same-key collision must spend different energy tokens.

This is the precise "pay new energy or return" dichotomy after the return and
payment branches have been burned.
-/
theorem same_key_collision_requires_fresh_energy
    {A M0 : ℕ} {proj : SemanticExtendedFlowLedgerProjection A M0}
    (E : ExtendedFlowEnergyLedger proj)
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hne : F₁ ≠ F₂)
    (hAdm₁ : ExtendedFlowAdmissible F₁)
    (hAdm₂ : ExtendedFlowAdmissible F₂)
    (hkey : proj.keyFlow F₁ = proj.keyFlow F₂) :
    E.token F₁ ≠ E.token F₂ := by
  exact same_key_without_expandedAlternative_requires_distinct_energy
    E hne hAdm₁ hAdm₂ hkey no_expandedExtendedFlowResolutionAlternative

/--
An infinite admissible extended-flow family is impossible once the finite energy
ledger is supplied.

The proof uses real non-vacuous pigeonhole:

  * the family lives in the unbounded genealogy type;
  * the codomain is finite only after quotienting to `(semantic key, energy)`;
  * two distinct genealogies with the same combined key force the strict
    expanded alternative by `no_double_spend_resolves`;
  * that alternative is already impossible by lexRank/payment closure.
-/
theorem infinite_extended_flows_impossible_with_energyLedger
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0)
    (E : ExtendedFlowEnergyLedger proj)
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕) :
    False := by
  classical
  letI : Finite proj.Key := proj.finiteKey
  letI : Finite E.Energy := E.finiteEnergy
  haveI : Finite (proj.Key × E.Energy) := inferInstance
  rcases h𝓕 with ⟨hInf, hAdm⟩
  obtain ⟨F₁, F₂, hF₁, hF₂, hne, hCombined⟩ :=
    BoundaryLedgerCollision.infinite_set_key_collision
      (σ := ExtendedProperGeneratedFlow A M0)
      (Key := proj.Key × E.Energy)
      (S := 𝓕)
      hInf
      (energyCollisionKey E)
  have hkey : proj.keyFlow F₁ = proj.keyFlow F₂ := by
    simpa [energyCollisionKey] using congrArg Prod.fst hCombined
  have htok : E.token F₁ = E.token F₂ := by
    simpa [energyCollisionKey] using congrArg Prod.snd hCombined
  have hAlt : ExpandedExtendedFlowResolutionAlternative F₁ F₂ :=
    E.no_double_spend_resolves F₁ F₂ hne (hAdm F₁ hF₁) (hAdm F₂ hF₂) hkey htok
  exact no_expandedExtendedFlowResolutionAlternative hAlt

/--
A twin bound is impossible once, for the chosen projection, a finite energy
ledger is supplied.

All source-side work is reused from the maximal extended-flow close: a twin
bound gives infinitely many generated genealogies.  The present theorem only
adds the finite-energy exhaustion argument.
-/
theorem twinBound_impossible_with_energyLedger
    {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (E : ExtendedFlowEnergyLedger proj) :
    False := by
  obtain ⟨𝓕, h𝓕⟩ :=
    twinBoundForcesInfiniteExtendedGeneratedFlows_closed
      (A := A) (M0 := M0) hTwinBound
  exact infinite_extended_flows_impossible_with_energyLedger
    (A := A) (M0 := M0) proj E h𝓕

/--
The energy form of the last Step00 obligation.

For one fixed scale `A`, every possible last-twin bound `M0` receives a finite
semantic flow projection and a finite energy ledger over that projection.  This
is stronger in shape than the old final resolver, but more informative: it says
exactly why a legal non-returning engine would have to spend unbounded energy.
-/
abbrev EnergyLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∃ EOf : ∀ M0 : ℕ, ExtendedFlowEnergyLedger (projOf M0),
        True

/--
Energy obligation implies lower twin infinitude.

Assume finitely many lower twin centres.  Choose a bound `M0`.  The source-side
machinery creates infinitely many extended generated genealogies above `M0`.
The finite product `(ledger key, energy token)` then produces a double spend,
which is forbidden by the energy ledger and the already closed return/payment
branches.
-/
theorem twinLowersInfinite_of_energyLastStep00Obligation
    (H : EnergyLastStep00Obligation) : TwinLowers.Infinite := by
  classical
  by_contra hfin
  obtain ⟨M0, hTwinBound⟩ := exists_twinBoundAbove_of_not_twinLowersInfinite hfin
  rcases H with ⟨A, projOf, EOf, _⟩
  exact twinBound_impossible_with_energyLedger
    (A := A) (M0 := M0)
    hTwinBound (projOf M0) (EOf M0)

/--
The exact remaining energy certificate for a candidate projection.

A candidate `proj.keyFlow` is not enough.  To avoid the no-cheat failure, one must
also provide a finite `Energy` type and prove that a same-key/same-energy double
spend extracts a strict expanded alternative.  Since the expanded alternative is
already impossible in the concrete graph, an infinite family cannot pay forever.
-/
def RemainingFiniteEnergyCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  Nonempty (ExtendedFlowEnergyLedger proj)

/-! #### Machine honesty of the energy form (post-audit, mandatory) -/

/-- **`twin_above_of_energyLedger` — PROVEN (honesty of the energy form).** The energy-ledger at
    scale `M0` ALSO presents a twin above `M0`: it is not weaker than the goal scale-wise. Like
    the previous resolvers, the energy certificate is a twin-DETECTOR, not a neutral condition. -/
theorem twin_above_of_energyLedger {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (E : ExtendedFlowEnergyLedger proj) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m := by
  by_contra hno
  push_neg at hno
  exact twinBound_impossible_with_energyLedger (fun m hm => hno m hm) proj E

/-- Combined projection: the energy-ledger is exactly a REFINEMENT OF THE KEY of the old
    semantic projection to `Key × Energy` (finiteness is preserved). -/
def combinedEnergyProjection {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (E : ExtendedFlowEnergyLedger proj) :
    SemanticExtendedFlowLedgerProjection A M0 where
  Key := proj.Key × E.Energy
  finiteKey := by
    letI : Finite proj.Key := proj.finiteKey
    letI : Finite E.Energy := E.finiteEnergy
    exact inferInstance
  keyFlow := energyCollisionKey E

/-- **`combinedEnergyProjection_resolves` — PROVEN (factorization).** The combined
    projection resolves collisions in the old sense: the energy form is NOT a new node, but the old node
    with a refined key. Substantively `no_double_spend_resolves` (under an already burnt
    alternative) = injectivity of the combined key on admissible genealogies. -/
theorem combinedEnergyProjection_resolves {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (E : ExtendedFlowEnergyLedger proj) :
    SemanticExtendedFlowLedgerCollisionResolves (combinedEnergyProjection E) := by
  intro F₁ F₂ hne h1 h2 hkey
  exact absurd
    (E.no_double_spend_resolves F₁ F₂ hne h1 h2
      (congrArg Prod.fst hkey) (congrArg Prod.snd hkey))
    no_expandedExtendedFlowResolutionAlternative

/-- **`lastStep00Obligation_of_energy` — PROVEN (energy form ⟹ old node).**
    The energy obligation machine-factorizes through `TheLastStep00Obligation`:
    it is a reformulation of the final node, not a bypass. The openness of the node has NOT decreased —
    all arithmetic now lives in the construction of the energy-ledger. -/
theorem lastStep00Obligation_of_energy
    (H : EnergyLastStep00Obligation) : TheLastStep00Obligation := by
  rcases H with ⟨A, projOf, EOf, _⟩
  exact ⟨A, fun M0 => combinedEnergyProjection (EOf M0),
    fun M0 => combinedEnergyProjection_resolves (EOf M0)⟩

/-#############################################################################
  NESTED UNIVERSES (brick: nested_universes_engine).
  A diagnostic unfolding of the node: one-sided nesting (the terminal of the outer
  genealogy enters the start of the inner one) — a STRICT DESCENT of lexRank, not a cycle;
  mutual nesting — a legal cycle (burnt by lexRank); an infinite chain
  of nestings is impossible (rank-descent in ℕ). Below — the brick + machine honesty:
  nested-resolver ⟺ old resolver (both alternatives burnt), nested-node
  ⟺ old node, and the nested-resolver is also a twin-detector.
#############################################################################-/

/-- Return of a genealogy from the terminal to ITS OWN start (reference for self-nesting). -/
def ExtendedFlowReturnsToStart {A M0 : ℕ}
    (F : ExtendedProperGeneratedFlow A M0) : Prop :=
  NonemptyPath (RealStep A M0) F.terminal (State.center F.start)

/-#############################################################################
  §1. One-way nested universes
#############################################################################-/

/--
`F_outer` contains `F_inner` as an internal generated universe if, after the
stored forward genealogy of `F_outer` reaches its terminal, the concrete Step00
graph has a nonempty path to the start centre of `F_inner`.

This is not yet a cycle.  It is the formal version of:

  outer terminal enters the inner universe.
-/
def NestedUniverseEmbedding {A M0 : ℕ}
    (F_outer F_inner : ExtendedProperGeneratedFlow A M0) : Prop :=
  NonemptyPath (RealStep A M0) F_outer.terminal (State.center F_inner.start)

/-- Self-nesting is exactly the previous return-to-start certificate. -/
theorem selfNested_iff_returnsToStart {A M0 : ℕ}
    (F : ExtendedProperGeneratedFlow A M0) :
    NestedUniverseEmbedding F F ↔ ExtendedFlowReturnsToStart F := by
  rfl

/--
A one-way nesting strictly decreases the start-rank.

Forward path of `F_outer` already strictly decreases `lexRank`, and the nesting
path decreases it further.  Hence the inner start is a strictly smaller copy of
the outer start.
-/
theorem nestedUniverseEmbedding_drops_startRank {A M0 : ℕ}
    {F_outer F_inner : ExtendedProperGeneratedFlow A M0}
    (hNest : NestedUniverseEmbedding F_outer F_inner) :
    lexRank (State.center F_inner.start) <
      lexRank (State.center F_outer.start) := by
  rcases hNest with ⟨r, hrPos, hRetarget⟩
  have hWhole :
      PathN (RealStep A M0) (F_outer.steps + r)
        (State.center F_outer.start) (State.center F_inner.start) :=
    pathN_trans (properPath_to_realPath F_outer.properPath) hRetarget
  have hPos : 0 < F_outer.steps + r := by
    omega
  exact
    pathN_rank_strict_of_pos_of_step_decrease
      (R := RealStep A M0) (rank := lexRank)
      (by
        intro U V hStep
        exact lexRank_strict_decrease_on_RealStep hStep)
      hPos hWhole

/-#############################################################################
  §2. Mutual nesting is a legal Euclidean engine
#############################################################################-/

/-- Two generated universes are mutually nested when each terminal enters the
start of the other. -/
def MutuallyNestedUniverses {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  NestedUniverseEmbedding F₁ F₂ ∧ NestedUniverseEmbedding F₂ F₁

/--
Mutual nesting mechanically builds a legal cycle.

The cycle is:

  center(start F₁)
    →⁺ terminal F₁
    →⁺ center(start F₂)
    →⁺ terminal F₂
    →⁺ center(start F₁)
-/
theorem mutuallyNestedUniverses_forces_legalCycle {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hMutual : MutuallyNestedUniverses F₁ F₂) :
    LegalCycle (RealStep A M0) (Legal A M0) := by
  rcases hMutual with ⟨h₁₂, h₂₁⟩
  rcases h₁₂ with ⟨r₁₂, hr₁₂, hPath₁₂⟩
  rcases h₂₁ with ⟨r₂₁, hr₂₁, hPath₂₁⟩
  refine ⟨State.center F₁.start, ?_, ?_⟩
  · exact F₁.startClean
  · refine ⟨F₁.steps + r₁₂ + F₂.steps + r₂₁, ?_, ?_⟩
    · omega
    · have hForward₁ :
          PathN (RealStep A M0) F₁.steps
            (State.center F₁.start) F₁.terminal :=
        properPath_to_realPath F₁.properPath
      have hForward₂ :
          PathN (RealStep A M0) F₂.steps
            (State.center F₂.start) F₂.terminal :=
        properPath_to_realPath F₂.properPath
      have hToStart₂ :
          PathN (RealStep A M0) (F₁.steps + r₁₂)
            (State.center F₁.start) (State.center F₂.start) :=
        pathN_trans hForward₁ hPath₁₂
      have hToTerminal₂ :
          PathN (RealStep A M0) ((F₁.steps + r₁₂) + F₂.steps)
            (State.center F₁.start) F₂.terminal :=
        pathN_trans hToStart₂ hForward₂
      have hCyclePath :
          PathN (RealStep A M0)
            (((F₁.steps + r₁₂) + F₂.steps) + r₂₁)
            (State.center F₁.start) (State.center F₁.start) :=
        pathN_trans hToTerminal₂ hPath₂₁
      simpa [Nat.add_assoc] using hCyclePath

/-- Mutual nesting is impossible in the concrete Step00 graph because it creates
an explicit legal cycle, and `lexRank` forbids all such cycles. -/
theorem no_mutuallyNestedUniverses {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    ¬ MutuallyNestedUniverses F₁ F₂ := by
  intro h
  exact no_concrete_legalCycle_by_lexRank
    (A := A) (M0 := M0)
    (mutuallyNestedUniverses_forces_legalCycle h)

/-- Equivalently, mutual nesting creates a rank contradiction. -/
theorem mutuallyNestedUniverses_rank_contradiction {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hMutual : MutuallyNestedUniverses F₁ F₂) : False := by
  rcases hMutual with ⟨h₁₂, h₂₁⟩
  have hdrop₁₂ := nestedUniverseEmbedding_drops_startRank h₁₂
  have hdrop₂₁ := nestedUniverseEmbedding_drops_startRank h₂₁
  omega

/-#############################################################################
  §3. Infinite nested chains are forbidden
#############################################################################-/

/-- A one-way nested-universe chain. -/
def NestedUniverseChain {A M0 : ℕ}
    (C : ℕ → ExtendedProperGeneratedFlow A M0) : Prop :=
  ∀ i : ℕ, NestedUniverseEmbedding (C i) (C (i + 1))

/-- Along a nested chain, the start-rank drops by at least one at each step. -/
theorem nestedUniverseChain_rank_bound {A M0 : ℕ}
    {C : ℕ → ExtendedProperGeneratedFlow A M0}
    (hC : NestedUniverseChain C) :
    ∀ n : ℕ,
      lexRank (State.center (C n).start) + n ≤
        lexRank (State.center (C 0).start) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hdrop :
          lexRank (State.center (C (n + 1)).start) <
            lexRank (State.center (C n).start) :=
        nestedUniverseEmbedding_drops_startRank (hC n)
      omega

/-- No infinite legal nested-universe chain exists in the concrete Step00 graph. -/
theorem no_nestedUniverseChain {A M0 : ℕ}
    (C : ℕ → ExtendedProperGeneratedFlow A M0) :
    ¬ NestedUniverseChain C := by
  intro hC
  have hBound :=
    nestedUniverseChain_rank_bound (A := A) (M0 := M0)
      (C := C) hC (lexRank (State.center (C 0).start) + 1)
  omega

/-- A same-key perpetual nested engine for a semantic flow-ledger projection. -/
structure SameKeyNestedUniverseEngine {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) where
  chain : ℕ → ExtendedProperGeneratedFlow A M0
  admissible : ∀ i : ℕ, ExtendedFlowAdmissible (chain i)
  same_key : ∀ i : ℕ, proj.keyFlow (chain i) = proj.keyFlow (chain (i + 1))
  nested : NestedUniverseChain chain

/-- Such a same-key perpetual nested engine cannot exist. -/
theorem no_sameKeyNestedUniverseEngine {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (E : SameKeyNestedUniverseEngine proj) : False :=
  no_nestedUniverseChain E.chain E.nested

/-#############################################################################
  §4. Nested-universe resolution alternatives
#############################################################################-/

/--
A local same-key collision may resolve by:

  * direct return-path certificate;
  * mutual nesting, which is already a cycle;
  * impossible payment.

A merely one-way nesting is deliberately not included here as a final resolution:
it is only a smaller internal universe.  If it can be repeated forever, §3
forbids it; if it closes back, §2 turns it into a cycle.
-/
def NestedUniverseResolutionAlternative {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂ ∨
    MutuallyNestedUniverses F₁ F₂ ∨
    ImpossiblePayment

/-- The nested-universe alternative implies the older cycle-or-payment
resolution alternative. -/
theorem nestedUniverseAlternative_forces_resolutionAlternative {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (h : NestedUniverseResolutionAlternative F₁ F₂) :
    ExtendedFlowResolutionAlternative A M0 := by
  rcases h with hReturn | hRest
  · exact Or.inl (extendedFlowReturnCertificate_forces_legalCycle hReturn)
  · rcases hRest with hMutual | hPay
    · exact Or.inl (mutuallyNestedUniverses_forces_legalCycle hMutual)
    · exact Or.inr hPay

/-- Therefore the nested-universe alternative is also impossible once produced,
because it implies either a forbidden cycle or an impossible payment. -/
theorem no_nestedUniverseResolutionAlternative {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    ¬ NestedUniverseResolutionAlternative F₁ F₂ := by
  intro h
  exact no_extendedFlowResolutionAlternative A M0
    (nestedUniverseAlternative_forces_resolutionAlternative h)

/--
A semantic resolver in nested-universe form.

This is another strict expansion of the last Step00 obligation.  It says that a
same-key genealogy collision must produce a genuine local object: direct return,
mutual nesting, or impossible payment.  It still does not allow the projection
itself to manufacture the engine.
-/
def NestedSemanticExtendedFlowLedgerCollisionResolves
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    F₁ ≠ F₂ →
    ExtendedFlowAdmissible F₁ →
    ExtendedFlowAdmissible F₂ →
    proj.keyFlow F₁ = proj.keyFlow F₂ →
      NestedUniverseResolutionAlternative F₁ F₂

/-- The nested-universe resolver implies the previous near-close resolver. -/
theorem nestedSemanticExtended_resolves_old {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNested : NestedSemanticExtendedFlowLedgerCollisionResolves proj) :
    SemanticExtendedFlowLedgerCollisionResolves proj := by
  intro F₁ F₂ hne hAdm₁ hAdm₂ hkey
  exact nestedUniverseAlternative_forces_resolutionAlternative
    (hNested F₁ F₂ hne hAdm₁ hAdm₂ hkey)

/-- The nested-universe last obligation. -/
abbrev TheNestedUniverseLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∀ M0 : ℕ, NestedSemanticExtendedFlowLedgerCollisionResolves (projOf M0)

/-- The nested-universe last obligation is sufficient for infinitude of twins. -/
theorem twinLowersInfinite_of_nestedUniverseLastStep00Obligation
    (H : TheNestedUniverseLastStep00Obligation) : TwinLowers.Infinite := by
  rcases H with ⟨A, projOf, hNested⟩
  exact twinLowersInfinite_of_lastStep00Obligation
    ⟨A, projOf, fun M0 => nestedSemanticExtended_resolves_old (hNested M0)⟩

/-#############################################################################
  §5. Audit reading
#############################################################################-/

/--
A one-way nested universe is not a final engine.  It is a strict descent.
This proposition is the exact remaining shape of the arithmetic task: prove
that same-key collisions cannot keep producing merely one-way strict nestings
forever without eventually returning or paying.
-/
def OneWayNestingIsOnlyDescent {A M0 : ℕ}
    (F_outer F_inner : ExtendedProperGeneratedFlow A M0) : Prop :=
  NestedUniverseEmbedding F_outer F_inner ∧
    lexRank (State.center F_inner.start) <
      lexRank (State.center F_outer.start)

/-- A one-way nesting certifies only strict descent, not a cycle. -/
theorem oneWayNesting_is_only_descent {A M0 : ℕ}
    {F_outer F_inner : ExtendedProperGeneratedFlow A M0}
    (hNest : NestedUniverseEmbedding F_outer F_inner) :
    OneWayNestingIsOnlyDescent F_outer F_inner :=
  ⟨hNest, nestedUniverseEmbedding_drops_startRank hNest⟩

/--
Final audit name: the Euclidean engine is now either direct return, mutual
nesting, or the impossibility of an infinite same-key nested chain.
-/
abbrev RemainingNestedUniverseEngineCertificate
    {A M0 : ℕ} (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NestedSemanticExtendedFlowLedgerCollisionResolves proj


/-! Machine honesty of the nested form -/

theorem returnCertificate_iff_either_returns {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) :
    ExtendedFlowReturnCertificate F₁ F₂ ↔
      ExtendedFlowReturnsToStart F₁ ∨ ExtendedFlowReturnsToStart F₂ := Iff.rfl

theorem nestedResolves_iff_resolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj ↔
      SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · exact nestedSemanticExtended_resolves_old
  · intro hOld F₁ F₂ hne h1 h2 hkey
    exact ((no_extendedFlowResolutionAlternative A M0)
      (hOld F₁ F₂ hne h1 h2 hkey)).elim

theorem nestedUniverseLastStep00Obligation_iff_lastStep00Obligation :
    TheNestedUniverseLastStep00Obligation ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 => nestedSemanticExtended_resolves_old (h M0)⟩
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 =>
      (nestedResolves_iff_resolves (projOf M0)).mpr (h M0)⟩

theorem twin_above_of_nestedResolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (h : NestedSemanticExtendedFlowLedgerCollisionResolves proj) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves proj (nestedSemanticExtended_resolves_old h)

/-#############################################################################
  SINGULARITIES ON THE LEDGER SEAM (brick: ledger_seam_singularity).
  Classification of a same-key collision: return / nesting (into one of the sides) /
  payment / SINGULARITY (the seam glued histories that the graph cannot glue).
  A dangling nesting — a descent instead of an engine. Audit-reduction of the brick:
  NoSingularity + NoDangling ⟹ nested-resolver. Below — the brick + machine
  honesty: both halves of the audit mutually annihilate into "there are no collisions at all"
  (= injectivity), the seam-node ⟺ old node, and this is again a twin-detector.
#############################################################################-/

/-#############################################################################
  §1. Same-key seam collisions and singularities
#############################################################################-/

/--
A same-key ledger seam collision of two admissible extended genealogies.
This is only the common precondition; it is not yet an engine.
-/
def LedgerSeamCollision {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  F₁ ≠ F₂ ∧
  ExtendedFlowAdmissible F₁ ∧
  ExtendedFlowAdmissible F₂ ∧
  proj.keyFlow F₁ = proj.keyFlow F₂

/--
A singularity on the ledger seam.

The projection identifies two different admissible genealogies by one finite
semantic key, but the concrete graph gives none of the legitimate realizations:
no direct return, no nesting in either direction, and no payment contradiction.
-/
def LedgerSeamSingularity {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamCollision proj F₁ F₂ ∧
  ¬ ExtendedFlowReturnCertificate F₁ F₂ ∧
  ¬ NestedUniverseEmbedding F₁ F₂ ∧
  ¬ NestedUniverseEmbedding F₂ F₁ ∧
  ¬ ImpossiblePayment

/-- A projection has no seam singularities if no same-key collision is a broken
ledger seam. -/
def NoLedgerSeamSingularity {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    ¬ LedgerSeamSingularity proj F₁ F₂

/-- A singularity is by definition an unresolved same-key collision. -/
theorem ledgerSeamSingularity_is_unresolved {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (h : LedgerSeamSingularity proj F₁ F₂) :
    LedgerSeamCollision proj F₁ F₂ ∧
    ¬ ExtendedFlowReturnCertificate F₁ F₂ ∧
    ¬ NestedUniverseEmbedding F₁ F₂ ∧
    ¬ NestedUniverseEmbedding F₂ F₁ ∧
    ¬ ImpossiblePayment := by
  exact h

/-#############################################################################
  §2. Classical seam classification
#############################################################################-/

/--
The broad classification of a same-key collision.

This is a tautological classifier, not a proof of Step00: a collision either
already has one of the concrete witnesses, or it is exactly a seam singularity.
-/
def SeamCollisionClassificationAlternative {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂ ∨
  NestedUniverseEmbedding F₁ F₂ ∨
  NestedUniverseEmbedding F₂ F₁ ∨
  ImpossiblePayment ∨
  LedgerSeamSingularity proj F₁ F₂

/--
Every same-key collision classically falls into the broad seam classification.
The last case is precisely the singularity case.
-/
theorem seamCollision_classical_classification {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hColl : LedgerSeamCollision proj F₁ F₂) :
    SeamCollisionClassificationAlternative proj F₁ F₂ := by
  classical
  by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
  · exact Or.inl hReturn
  · by_cases hNest₁₂ : NestedUniverseEmbedding F₁ F₂
    · exact Or.inr (Or.inl hNest₁₂)
    · by_cases hNest₂₁ : NestedUniverseEmbedding F₂ F₁
      · exact Or.inr (Or.inr (Or.inl hNest₂₁))
      · by_cases hPay : ImpossiblePayment
        · exact Or.inr (Or.inr (Or.inr (Or.inl hPay)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hColl, hReturn, hNest₁₂, hNest₂₁, hPay⟩)))

/-#############################################################################
  §3. Dangling one-way nesting
#############################################################################-/

/--
A dangling one-way nesting is another non-closing seam phenomenon.

There is a same-key collision and at least one one-way nesting, but it is not a
mutual nesting, not a return-path resolution, and not a payment contradiction.
Such a case is not a cycle; it is only a smaller internal universe.  If it is
allowed as a final resolution, the proof has smuggled a descent in place of an
engine.
-/
def DanglingOneWayNesting {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamCollision proj F₁ F₂ ∧
  ¬ ExtendedFlowReturnCertificate F₁ F₂ ∧
  ¬ MutuallyNestedUniverses F₁ F₂ ∧
  ¬ ImpossiblePayment ∧
  (NestedUniverseEmbedding F₁ F₂ ∨ NestedUniverseEmbedding F₂ F₁)

/-- No dangling one-way nesting means a same-key one-way nesting cannot remain
as a terminal explanation: it must close into mutual nesting, return, or payment.
-/
def NoDanglingOneWayNesting {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    ¬ DanglingOneWayNesting proj F₁ F₂

/-- Under `NoDanglingOneWayNesting`, any one-way nesting in an unresolved
collision must actually be mutual. -/
theorem oneWayNesting_forces_mutual_of_noDangling {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hNoDangling : NoDanglingOneWayNesting proj)
    (hColl : LedgerSeamCollision proj F₁ F₂)
    (hNoReturn : ¬ ExtendedFlowReturnCertificate F₁ F₂)
    (hNoPayment : ¬ ImpossiblePayment)
    (hOneWay : NestedUniverseEmbedding F₁ F₂ ∨ NestedUniverseEmbedding F₂ F₁) :
    MutuallyNestedUniverses F₁ F₂ := by
  classical
  by_contra hNoMutual
  exact hNoDangling F₁ F₂
    ⟨hColl, hNoReturn, hNoMutual, hNoPayment, hOneWay⟩

/-#############################################################################
  §4. From no singularity/no dangling to the old nested resolver
#############################################################################-/

/--
Closing alternatives are the ones that already imply the old cycle-or-payment
resolver: direct return, mutual nesting, payment, or a singularity marker.
The singularity marker is included only so that `NoLedgerSeamSingularity` can
explicitly discharge it.
-/
def SeamClosingAlternative {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂ ∨
  MutuallyNestedUniverses F₁ F₂ ∨
  ImpossiblePayment ∨
  LedgerSeamSingularity proj F₁ F₂

/--
The broad seam classification, plus the no-dangling audit, yields a closing
alternative.  This is where a bare one-way nesting is rejected as a final engine.
-/
theorem seamClassification_to_closingAlternative {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hNoDangling : NoDanglingOneWayNesting proj)
    (hColl : LedgerSeamCollision proj F₁ F₂)
    (hClass : SeamCollisionClassificationAlternative proj F₁ F₂) :
    SeamClosingAlternative proj F₁ F₂ := by
  classical
  rcases hClass with hReturn | hRest
  · exact Or.inl hReturn
  · rcases hRest with hNest₁₂ | hRest
    · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
      · exact Or.inl hReturn
      · by_cases hPay : ImpossiblePayment
        · exact Or.inr (Or.inr (Or.inl hPay))
        · have hMut : MutuallyNestedUniverses F₁ F₂ :=
            oneWayNesting_forces_mutual_of_noDangling
              (proj := proj) hNoDangling hColl hReturn hPay (Or.inl hNest₁₂)
          exact Or.inr (Or.inl hMut)
    · rcases hRest with hNest₂₁ | hRest
      · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
        · exact Or.inl hReturn
        · by_cases hPay : ImpossiblePayment
          · exact Or.inr (Or.inr (Or.inl hPay))
          · have hMut : MutuallyNestedUniverses F₁ F₂ :=
              oneWayNesting_forces_mutual_of_noDangling
                (proj := proj) hNoDangling hColl hReturn hPay (Or.inr hNest₂₁)
            exact Or.inr (Or.inl hMut)
      · rcases hRest with hPay | hSing
        · exact Or.inr (Or.inr (Or.inl hPay))
        · exact Or.inr (Or.inr (Or.inr hSing))

/-- A closing alternative becomes the old nested-universe resolution once seam
singularities are forbidden. -/
theorem closingAlternative_forces_nestedResolution {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hClose : SeamClosingAlternative proj F₁ F₂) :
    NestedUniverseResolutionAlternative F₁ F₂ := by
  rcases hClose with hReturn | hRest
  · exact Or.inl hReturn
  · rcases hRest with hMutual | hRest
    · exact Or.inr (Or.inl hMutual)
    · rcases hRest with hPay | hSing
      · exact Or.inr (Or.inr hPay)
      · exact False.elim ((hNoSing F₁ F₂) hSing)

/--
The exact seam audit reduction:
if the projection has neither seam singularities nor dangling one-way nestings,
then it supplies the nested-universe semantic resolver required by the existing
near-close machinery.
-/
theorem noSingularity_noDangling_resolves_nested {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj := by
  intro F₁ F₂ hne hAdm₁ hAdm₂ hkey
  have hColl : LedgerSeamCollision proj F₁ F₂ :=
    ⟨hne, hAdm₁, hAdm₂, hkey⟩
  have hClass : SeamCollisionClassificationAlternative proj F₁ F₂ :=
    seamCollision_classical_classification hColl
  have hClose : SeamClosingAlternative proj F₁ F₂ :=
    seamClassification_to_closingAlternative
      (proj := proj) hNoDangling hColl hClass
  exact closingAlternative_forces_nestedResolution hNoSing hClose

/-- The same audit reduction phrased all the way down to the old resolver. -/
theorem noSingularity_noDangling_resolves_old {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    SemanticExtendedFlowLedgerCollisionResolves proj :=
  nestedSemanticExtended_resolves_old
    (noSingularity_noDangling_resolves_nested
      (proj := proj) hNoSing hNoDangling)

/-#############################################################################
  §5. Last obligation in seam-audit form
#############################################################################-/

/--
The final Step00 obligation in seam-audit form.

For one fixed scale `A`, every hypothetical last-twin bound `M0` must admit a
semantic ledger projection whose same-key collisions have no broken seam and no
dangling one-way nesting.  Then the already-proved machinery forces infinitely
many twins.
-/
abbrev TheSeamAuditLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∀ M0 : ℕ,
        NoLedgerSeamSingularity (projOf M0) ∧
        NoDanglingOneWayNesting (projOf M0)

/-- Seam-audit last obligation implies the nested-universe last obligation. -/
theorem seamAuditLastStep00Obligation_implies_nestedUniverseLast
    (H : TheSeamAuditLastStep00Obligation) :
    TheNestedUniverseLastStep00Obligation := by
  rcases H with ⟨A, projOf, hAudit⟩
  refine ⟨A, projOf, ?_⟩
  intro M0
  exact noSingularity_noDangling_resolves_nested
    (proj := projOf M0) (hAudit M0).1 (hAudit M0).2

/-- Therefore the seam-audit last obligation is sufficient for infinitude of
lower twin centres. -/
theorem twinLowersInfinite_of_seamAuditLastStep00Obligation
    (H : TheSeamAuditLastStep00Obligation) : TwinLowers.Infinite :=
  twinLowersInfinite_of_nestedUniverseLastStep00Obligation
    (seamAuditLastStep00Obligation_implies_nestedUniverseLast H)

/-#############################################################################
  §6. Audit names
#############################################################################-/

/-- The singularity certificate which an auditor should try to rule out for a
candidate projection. -/
abbrev RemainingSeamSingularityCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoLedgerSeamSingularity proj

/-- The dangling one-way nesting certificate which an auditor should try to rule
out for a candidate projection. -/
abbrev RemainingNoDanglingNestedUniverseCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoDanglingOneWayNesting proj

/-- A same-key collision whose only explanation is a singularity marks a cheating
or incomplete ledger projection: the finite key glues histories that the real
Step00 graph cannot legally glue. -/
def ProjectionCreatesBrokenSeam {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∃ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    LedgerSeamSingularity proj F₁ F₂

/-- A same-key collision whose only explanation is one-way nesting marks a
projection that has produced descent but not an engine. -/
def ProjectionCreatesDanglingNesting {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∃ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    DanglingOneWayNesting proj F₁ F₂

/-! Machine honesty of the seam form -/

/-- The return certificate is refuted unconditionally (it builds a legal cycle). -/
theorem no_extendedFlowReturnCertificate {A M0 : ℕ}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    ¬ ExtendedFlowReturnCertificate F₁ F₂ := fun h =>
  no_concrete_legalCycle_by_lexRank (A := A) (M0 := M0)
    (extendedFlowReturnCertificate_forces_legalCycle h)

/-- Singularity = a collision without nestings (the remaining bans are satisfied for free). -/
theorem ledgerSeamSingularity_iff {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    LedgerSeamSingularity proj F₁ F₂ ↔
      (LedgerSeamCollision proj F₁ F₂ ∧
        ¬ NestedUniverseEmbedding F₁ F₂ ∧ ¬ NestedUniverseEmbedding F₂ F₁) := by
  constructor
  · rintro ⟨hColl, _, hN12, hN21, _⟩
    exact ⟨hColl, hN12, hN21⟩
  · rintro ⟨hColl, hN12, hN21⟩
    exact ⟨hColl, no_extendedFlowReturnCertificate, hN12, hN21,
      BoundaryDefectPayment.impossiblePayment_false⟩

/-- Dangling = a collision with at least one nesting (the remaining bans — for free). -/
theorem danglingOneWayNesting_iff {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    DanglingOneWayNesting proj F₁ F₂ ↔
      (LedgerSeamCollision proj F₁ F₂ ∧
        (NestedUniverseEmbedding F₁ F₂ ∨ NestedUniverseEmbedding F₂ F₁)) := by
  constructor
  · rintro ⟨hColl, _, _, _, hOne⟩
    exact ⟨hColl, hOne⟩
  · rintro ⟨hColl, hOne⟩
    exact ⟨hColl, no_extendedFlowReturnCertificate,
      no_mutuallyNestedUniverses, BoundaryDefectPayment.impossiblePayment_false, hOne⟩

/-- NoSingularity ⟺ "every same-key collision carries a nesting". -/
theorem noLedgerSeamSingularity_iff {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    NoLedgerSeamSingularity proj ↔
      ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
        LedgerSeamCollision proj F₁ F₂ →
          (NestedUniverseEmbedding F₁ F₂ ∨ NestedUniverseEmbedding F₂ F₁) := by
  constructor
  · intro hNo F₁ F₂ hColl
    by_contra hNone
    push_neg at hNone
    exact hNo F₁ F₂ (ledgerSeamSingularity_iff.mpr ⟨hColl, hNone.1, hNone.2⟩)
  · intro hAll F₁ F₂ hSing
    rcases ledgerSeamSingularity_iff.mp hSing with ⟨hColl, hN12, hN21⟩
    rcases hAll F₁ F₂ hColl with h | h
    · exact hN12 h
    · exact hN21 h

/-- NoDangling ⟺ "no same-key collision carries a nesting". -/
theorem noDanglingOneWayNesting_iff {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    NoDanglingOneWayNesting proj ↔
      ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
        LedgerSeamCollision proj F₁ F₂ →
          ¬ (NestedUniverseEmbedding F₁ F₂ ∨ NestedUniverseEmbedding F₂ F₁) := by
  constructor
  · intro hNo F₁ F₂ hColl hOne
    exact hNo F₁ F₂ (danglingOneWayNesting_iff.mpr ⟨hColl, hOne⟩)
  · intro hAll F₁ F₂ hD
    rcases danglingOneWayNesting_iff.mp hD with ⟨hColl, hOne⟩
    exact hAll F₁ F₂ hColl hOne

/-- MUTUAL ANNIHILATION: the two audit conditions together ⟹ there are NO same-key collisions AT ALL. -/
theorem seamAudit_forces_no_collision {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
      ¬ LedgerSeamCollision proj F₁ F₂ := by
  intro F₁ F₂ hColl
  have hOne := (noLedgerSeamSingularity_iff (proj := proj)).mp hNoSing F₁ F₂ hColl
  exact (noDanglingOneWayNesting_iff (proj := proj)).mp hNoDangling F₁ F₂ hColl hOne

/-- Seam-audit ⟺ old resolver: the pair of conditions is again injectivity of the key. -/
theorem seamAudit_iff_resolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    (NoLedgerSeamSingularity proj ∧ NoDanglingOneWayNesting proj) ↔
      SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · rintro ⟨hNoSing, hNoDangling⟩
    exact noSingularity_noDangling_resolves_old hNoSing hNoDangling
  · intro hRes
    have hNoColl : ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
        ¬ LedgerSeamCollision proj F₁ F₂ := by
      rintro F₁ F₂ ⟨hne, h1, h2, hkey⟩
      exact no_extendedFlowResolutionAlternative A M0 (hRes F₁ F₂ hne h1 h2 hkey)
    constructor
    · intro F₁ F₂ hSing
      exact hNoColl F₁ F₂ hSing.1
    · intro F₁ F₂ hD
      exact hNoColl F₁ F₂ hD.1

/-- Seam-obligation ⟺ old node (a reformulation, not a bypass). -/
theorem seamAuditLastStep00Obligation_iff_lastStep00Obligation :
    TheSeamAuditLastStep00Obligation ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 => (seamAudit_iff_resolves (projOf M0)).mp (h M0)⟩
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 => (seamAudit_iff_resolves (projOf M0)).mpr (h M0)⟩

/-- Seam-audit at scale M0 — also a twin-detector. -/
theorem twin_above_of_seamAudit {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves proj
    (noSingularity_noDangling_resolves_old hNoSing hNoDangling)

/-#############################################################################
  FAITHFUL PROJECTION / NO LOSS OF CAUSAL INFORMATION (brick:
  faithful_projection_no_information_loss).
  "The key may forget only gauge-information": the gluing of two distinct
  admissible genealogies must have a causal explanation (return /
  nesting / payment). Loss of information ⟺ a seam singularity (proven
  by the brick). Below — the brick + machine honesty: the pair (gauge-faithfulness,
  no-dangling) ⟺ old resolver, obligation ⟺ old node, twin-detector.
#############################################################################-/

/-#############################################################################
  §1. Causal alternatives and information loss
#############################################################################-/

/--
The broad causal explanations allowed for a same-key collision before we decide
whether a one-way nesting is a final explanation or only a dangling descent.
-/
def CausalCollisionAlternative {A M0 : ℕ}
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂ ∨
  NestedUniverseEmbedding F₁ F₂ ∨
  NestedUniverseEmbedding F₂ F₁ ∨
  ImpossiblePayment

/--
A projection has lost causal information at a pair of flows if it identifies two
distinct admissible genealogies by one key, but no causal explanation exists for
that identification.
-/
def CausalInformationLoss {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamCollision proj F₁ F₂ ∧
  ¬ CausalCollisionAlternative F₁ F₂

/--
A same-key collision without causal explanation is exactly a ledger seam
singularity.  This theorem is pure propositional bookkeeping: it certifies that
"forgotten causal information" and "broken seam" are the same audit failure.
-/
theorem causalInformationLoss_iff_ledgerSeamSingularity {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    CausalInformationLoss proj F₁ F₂ ↔ LedgerSeamSingularity proj F₁ F₂ := by
  constructor
  · intro h
    rcases h with ⟨hColl, hNoAlt⟩
    refine ⟨hColl, ?_, ?_, ?_, ?_⟩
    · intro hReturn
      exact hNoAlt (Or.inl hReturn)
    · intro hNest₁₂
      exact hNoAlt (Or.inr (Or.inl hNest₁₂))
    · intro hNest₂₁
      exact hNoAlt (Or.inr (Or.inr (Or.inl hNest₂₁)))
    · intro hPay
      exact hNoAlt (Or.inr (Or.inr (Or.inr hPay)))
  · intro h
    rcases h with ⟨hColl, hNoReturn, hNoNest₁₂, hNoNest₂₁, hNoPay⟩
    refine ⟨hColl, ?_⟩
    intro hAlt
    rcases hAlt with hReturn | hRest
    · exact hNoReturn hReturn
    · rcases hRest with hNest₁₂ | hRest
      · exact hNoNest₁₂ hNest₁₂
      · rcases hRest with hNest₂₁ | hPay
        · exact hNoNest₂₁ hNest₂₁
        · exact hNoPay hPay

/-- A projection has no causal information loss if no same-key collision is an
unexplained identification. -/
def NoCausalInformationLoss {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    ¬ CausalInformationLoss proj F₁ F₂

/-- No causal-information loss is equivalent to the previous no-singularity
audit condition. -/
theorem noCausalInformationLoss_iff_noLedgerSeamSingularity {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    NoCausalInformationLoss proj ↔ NoLedgerSeamSingularity proj := by
  constructor
  · intro hNoLoss F₁ F₂ hSing
    exact hNoLoss F₁ F₂
      ((causalInformationLoss_iff_ledgerSeamSingularity
        (proj := proj) (F₁ := F₁) (F₂ := F₂)).2 hSing)
  · intro hNoSing F₁ F₂ hLoss
    exact hNoSing F₁ F₂
      ((causalInformationLoss_iff_ledgerSeamSingularity
        (proj := proj) (F₁ := F₁) (F₂ := F₂)).1 hLoss)

/-- Existence of lost causal information is exactly creation of a broken seam. -/
def ProjectionForgetsCausalInformation {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∃ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    CausalInformationLoss proj F₁ F₂

/-- The existential diagnostic is the same as the previous broken-seam marker. -/
theorem projectionForgetsCausalInformation_iff_brokenSeam {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    ProjectionForgetsCausalInformation proj ↔ ProjectionCreatesBrokenSeam proj := by
  constructor
  · intro h
    rcases h with ⟨F₁, F₂, hLoss⟩
    exact ⟨F₁, F₂,
      (causalInformationLoss_iff_ledgerSeamSingularity
        (proj := proj) (F₁ := F₁) (F₂ := F₂)).1 hLoss⟩
  · intro h
    rcases h with ⟨F₁, F₂, hSing⟩
    exact ⟨F₁, F₂,
      (causalInformationLoss_iff_ledgerSeamSingularity
        (proj := proj) (F₁ := F₁) (F₂ := F₂)).2 hSing⟩

/-#############################################################################
  §2. Faithfulness: same key means same genealogy or causal relation
#############################################################################-/

/--
A causally faithful projection is one where every same-key seam collision of
distinct admissible flows has a causal explanation.
-/
def CausallyFaithfulProjection {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    LedgerSeamCollision proj F₁ F₂ →
      CausalCollisionAlternative F₁ F₂

/-- Causal faithfulness is exactly absence of causal information loss. -/
theorem causallyFaithful_iff_noCausalInformationLoss {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    CausallyFaithfulProjection proj ↔ NoCausalInformationLoss proj := by
  classical
  constructor
  · intro hFaith F₁ F₂ hLoss
    exact hLoss.2 (hFaith F₁ F₂ hLoss.1)
  · intro hNoLoss F₁ F₂ hColl
    by_contra hNoAlt
    exact hNoLoss F₁ F₂ ⟨hColl, hNoAlt⟩

/-- Therefore causal faithfulness is equivalent to forbidding seam
singularities. -/
theorem causallyFaithful_iff_noLedgerSeamSingularity {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    CausallyFaithfulProjection proj ↔ NoLedgerSeamSingularity proj := by
  exact (causallyFaithful_iff_noCausalInformationLoss
      (proj := proj)).trans
    (noCausalInformationLoss_iff_noLedgerSeamSingularity
      (proj := proj))

/--
This is the strict "information may only be gauge" condition in direct form.
If two admissible flows have the same key, then either they are literally the
same genealogy or the key equality has a causal explanation.
-/
def KeyEqualityForgetsOnlyGaugeInformation {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    ExtendedFlowAdmissible F₁ →
    ExtendedFlowAdmissible F₂ →
    proj.keyFlow F₁ = proj.keyFlow F₂ →
      F₁ = F₂ ∨ CausalCollisionAlternative F₁ F₂

/-- The direct gauge condition implies causal faithfulness on distinct
same-key collisions. -/
theorem keyEqualityGauge_implies_causallyFaithful {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hGauge : KeyEqualityForgetsOnlyGaugeInformation proj) :
    CausallyFaithfulProjection proj := by
  intro F₁ F₂ hColl
  rcases hColl with ⟨hne, hAdm₁, hAdm₂, hkey⟩
  rcases hGauge F₁ F₂ hAdm₁ hAdm₂ hkey with hEq | hAlt
  · exact False.elim (hne hEq)
  · exact hAlt

/-- Conversely, causal faithfulness gives the direct gauge condition by splitting
on literal equality of genealogies. -/
theorem causallyFaithful_implies_keyEqualityGauge {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hFaith : CausallyFaithfulProjection proj) :
    KeyEqualityForgetsOnlyGaugeInformation proj := by
  classical
  intro F₁ F₂ hAdm₁ hAdm₂ hkey
  by_cases hEq : F₁ = F₂
  · exact Or.inl hEq
  · exact Or.inr (hFaith F₁ F₂ ⟨hEq, hAdm₁, hAdm₂, hkey⟩)

/-- The direct gauge formulation and the collision formulation are equivalent. -/
theorem keyEqualityGauge_iff_causallyFaithful {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    KeyEqualityForgetsOnlyGaugeInformation proj ↔ CausallyFaithfulProjection proj := by
  constructor
  · exact keyEqualityGauge_implies_causallyFaithful
  · exact causallyFaithful_implies_keyEqualityGauge

/-- The direct gauge formulation is also equivalent to the no-singularity audit. -/
theorem keyEqualityGauge_iff_noLedgerSeamSingularity {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    KeyEqualityForgetsOnlyGaugeInformation proj ↔ NoLedgerSeamSingularity proj := by
  exact (keyEqualityGauge_iff_causallyFaithful (proj := proj)).trans
    (causallyFaithful_iff_noLedgerSeamSingularity (proj := proj))

/-#############################################################################
  §3. From faithful projection to the nested resolver
#############################################################################-/

/--
Causal faithfulness plus the no-dangling audit yields the nested-universe
resolver.  This is the strict form of "the projection forgets only gauge data".
-/
theorem causallyFaithful_noDangling_resolves_nested {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hFaith : CausallyFaithfulProjection proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj := by
  intro F₁ F₂ hne hAdm₁ hAdm₂ hkey
  have hColl : LedgerSeamCollision proj F₁ F₂ :=
    ⟨hne, hAdm₁, hAdm₂, hkey⟩
  have hAlt : CausalCollisionAlternative F₁ F₂ :=
    hFaith F₁ F₂ hColl
  rcases hAlt with hReturn | hRest
  · exact Or.inl hReturn
  · rcases hRest with hNest₁₂ | hRest
    · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
      · exact Or.inl hReturn
      · by_cases hPay : ImpossiblePayment
        · exact Or.inr (Or.inr hPay)
        · have hMut : MutuallyNestedUniverses F₁ F₂ :=
            oneWayNesting_forces_mutual_of_noDangling
              (proj := proj) hNoDangling hColl hReturn hPay (Or.inl hNest₁₂)
          exact Or.inr (Or.inl hMut)
    · rcases hRest with hNest₂₁ | hPay
      · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
        · exact Or.inl hReturn
        · by_cases hPay' : ImpossiblePayment
          · exact Or.inr (Or.inr hPay')
          · have hMut : MutuallyNestedUniverses F₁ F₂ :=
              oneWayNesting_forces_mutual_of_noDangling
                (proj := proj) hNoDangling hColl hReturn hPay' (Or.inr hNest₂₁)
            exact Or.inr (Or.inl hMut)
      · exact Or.inr (Or.inr hPay)

/-- Direct key-equality gauge faithfulness plus no-dangling also gives the nested
resolver. -/
theorem keyEqualityGauge_noDangling_resolves_nested {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hGauge : KeyEqualityForgetsOnlyGaugeInformation proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj :=
  causallyFaithful_noDangling_resolves_nested
    (proj := proj)
    (keyEqualityGauge_implies_causallyFaithful hGauge)
    hNoDangling

/-- Direct key-equality gauge faithfulness plus no-dangling gives the old
cycle-or-payment resolver through the nested-universe bridge. -/
theorem keyEqualityGauge_noDangling_resolves_old {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hGauge : KeyEqualityForgetsOnlyGaugeInformation proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    SemanticExtendedFlowLedgerCollisionResolves proj :=
  nestedSemanticExtended_resolves_old
    (keyEqualityGauge_noDangling_resolves_nested
      (proj := proj) hGauge hNoDangling)

/-#############################################################################
  §4. Faithful projection packages and final obligation
#############################################################################-/

/-- A candidate projection together with the exact two audit certificates needed
for the existing Step00 machine. -/
structure FaithfulGaugeProjectionPackage (A M0 : ℕ) where
  proj : SemanticExtendedFlowLedgerProjection A M0
  forgetsOnlyGauge : KeyEqualityForgetsOnlyGaugeInformation proj
  noDangling : NoDanglingOneWayNesting proj

/-- A faithful gauge package supplies the nested resolver. -/
theorem faithfulGaugePackage_resolves_nested {A M0 : ℕ}
    (P : FaithfulGaugeProjectionPackage A M0) :
    NestedSemanticExtendedFlowLedgerCollisionResolves P.proj :=
  keyEqualityGauge_noDangling_resolves_nested
    (proj := P.proj) P.forgetsOnlyGauge P.noDangling

/-- A faithful gauge package supplies the old resolver. -/
theorem faithfulGaugePackage_resolves_old {A M0 : ℕ}
    (P : FaithfulGaugeProjectionPackage A M0) :
    SemanticExtendedFlowLedgerCollisionResolves P.proj :=
  nestedSemanticExtended_resolves_old
    (faithfulGaugePackage_resolves_nested P)

/--
Final obligation in the faithful-projection form.

For one fixed scale `A`, every hypothetical last-twin bound `M0` must admit a
finite semantic flow-ledger projection which forgets only gauge information and
has no dangling one-way nesting.
-/
abbrev TheFaithfulGaugeLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ POf : ∀ M0 : ℕ, FaithfulGaugeProjectionPackage A M0,
      True

/-- Faithful-gauge last obligation implies the nested-universe last obligation. -/
theorem faithfulGaugeLastStep00Obligation_implies_nestedUniverseLast
    (H : TheFaithfulGaugeLastStep00Obligation) :
    TheNestedUniverseLastStep00Obligation := by
  rcases H with ⟨A, POf, _⟩
  refine ⟨A, (fun M0 => (POf M0).proj), ?_⟩
  intro M0
  exact faithfulGaugePackage_resolves_nested (POf M0)

/-- Therefore the faithful-projection last obligation is sufficient for infinitude
of lower twin centres. -/
theorem twinLowersInfinite_of_faithfulGaugeLastStep00Obligation
    (H : TheFaithfulGaugeLastStep00Obligation) : TwinLowers.Infinite :=
  twinLowersInfinite_of_nestedUniverseLastStep00Obligation
    (faithfulGaugeLastStep00Obligation_implies_nestedUniverseLast H)

/-#############################################################################
  §5. Audit markers
#############################################################################-/

/-- The exact local certificate still required from a proposed `proj.keyFlow`: key
equality must identify only literal sameness or causally related histories. -/
abbrev RemainingNoInformationLossCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  KeyEqualityForgetsOnlyGaugeInformation proj

/-- A bad projection is one which creates a same-key collision that has no causal
explanation. -/
def ProjectionLosesCausalData {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ProjectionForgetsCausalInformation proj

/-- Losing causal data is the same audit failure as creating a broken seam. -/
theorem projectionLosesCausalData_iff_brokenSeam {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    ProjectionLosesCausalData proj ↔ ProjectionCreatesBrokenSeam proj :=
  projectionForgetsCausalInformation_iff_brokenSeam (proj := proj)

/-- The finite key may be non-injective.  What it may not do is identify two
distinct admissible flows without a return/nesting/payment explanation. -/
def ProjectionIsAllowedToForget {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  KeyEqualityForgetsOnlyGaugeInformation proj ∧
  NoDanglingOneWayNesting proj

/-- Allowed forgetting is exactly the pair of certificates consumed by the
faithful-gauge package. -/
theorem allowedForgetting_resolves_nested {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (h : ProjectionIsAllowedToForget proj) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj :=
  keyEqualityGauge_noDangling_resolves_nested
    (proj := proj) h.1 h.2

/-! Machine honesty of the faithful-gauge form -/

/-- The pair (gauge-faithfulness, no-dangling) ⟺ old resolver (via seam-audit). -/
theorem gaugePair_iff_resolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    (KeyEqualityForgetsOnlyGaugeInformation proj ∧ NoDanglingOneWayNesting proj) ↔
      SemanticExtendedFlowLedgerCollisionResolves proj := by
  rw [keyEqualityGauge_iff_noLedgerSeamSingularity]
  exact seamAudit_iff_resolves proj

/-- Faithful-gauge-obligation ⟺ old node (a reformulation, not a bypass). -/
theorem faithfulGaugeLastStep00Obligation_iff_lastStep00Obligation :
    TheFaithfulGaugeLastStep00Obligation ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, POf, _⟩
    exact ⟨A, fun M0 => (POf M0).proj,
      fun M0 => faithfulGaugePackage_resolves_old (POf M0)⟩
  · rintro ⟨A, projOf, h⟩
    refine ⟨A, fun M0 =>
      { proj := projOf M0
        forgetsOnlyGauge := ((gaugePair_iff_resolves (projOf M0)).mpr (h M0)).1
        noDangling := ((gaugePair_iff_resolves (projOf M0)).mpr (h M0)).2 },
      trivial⟩

/-- Faithful-gauge-package at scale M0 — also a twin-detector. -/
theorem twin_above_of_faithfulGaugePackage {A M0 : ℕ}
    (P : FaithfulGaugeProjectionPackage A M0) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves P.proj (faithfulGaugePackage_resolves_old P)

/-#############################################################################
  UNIVERSE WITHOUT ENERGY (brick: no_energy_stable_universe).
  "No payment channel" = a same-key collision can rely only on
  geometry (return/nesting) or a singularity marker. The brick honestly
  avoids the vacuous Energy := Empty. Below — the brick + machine honesty:
  under the two seam-bans the support-condition is vacuous, the triple ⟺ the audit pair
  ⟺ old resolver; obligation ⟺ old node; twin-detector.
#############################################################################-/

/-#############################################################################
  §1. No-energy alternatives
#############################################################################-/

/--
The local alternatives available to a same-key collision when the system has no
payment/energy channel.

The last case, `LedgerSeamSingularity`, is not a valid support mechanism; it is
included only as a diagnostic marker for a broken ledger seam.
-/
def NoEnergySupportAlternative {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂ ∨
  NestedUniverseEmbedding F₁ F₂ ∨
  NestedUniverseEmbedding F₂ F₁ ∨
  LedgerSeamSingularity proj F₁ F₂

/--
A no-energy support law for a candidate finite ledger projection.

If two distinct admissible genealogies have the same semantic key, the collision
must be supported geometrically by return/nesting, or else explicitly marked as
a seam singularity.  No payment alternative is allowed here.
-/
def NoEnergyCollisionSupport {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    F₁ ≠ F₂ →
    ExtendedFlowAdmissible F₁ →
    ExtendedFlowAdmissible F₂ →
    proj.keyFlow F₁ = proj.keyFlow F₂ →
      NoEnergySupportAlternative proj F₁ F₂

/--
A no-energy stable universe is one whose same-key collisions have only geometric
support, with seam singularities and dangling one-way nestings ruled out by
separate audit conditions.
-/
def NoEnergyStableUniverse {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoEnergyCollisionSupport proj ∧
  NoLedgerSeamSingularity proj ∧
  NoDanglingOneWayNesting proj

/-#############################################################################
  §2. No-energy support reduces to the nested resolver
#############################################################################-/

/--
A no-energy support alternative, together with no seam singularity and no
dangling one-way nesting, yields the old nested-universe resolution alternative.

This is the formal version of:

  no energy + stable ledger seam
    ⟹ same-key collision must be supported by a return path or mutual nesting.
-/
theorem noEnergyAlternative_to_nestedResolution {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoDangling : NoDanglingOneWayNesting proj)
    (hColl : LedgerSeamCollision proj F₁ F₂)
    (hAlt : NoEnergySupportAlternative proj F₁ F₂) :
    NestedUniverseResolutionAlternative F₁ F₂ := by
  classical
  rcases hAlt with hReturn | hRest
  · exact Or.inl hReturn
  · rcases hRest with hNest₁₂ | hRest
    · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
      · exact Or.inl hReturn
      · by_cases hPay : ImpossiblePayment
        · exact Or.inr (Or.inr hPay)
        · have hMut : MutuallyNestedUniverses F₁ F₂ :=
            oneWayNesting_forces_mutual_of_noDangling
              (proj := proj) hNoDangling hColl hReturn hPay (Or.inl hNest₁₂)
          exact Or.inr (Or.inl hMut)
    · rcases hRest with hNest₂₁ | hSing
      · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
        · exact Or.inl hReturn
        · by_cases hPay : ImpossiblePayment
          · exact Or.inr (Or.inr hPay)
          · have hMut : MutuallyNestedUniverses F₁ F₂ :=
              oneWayNesting_forces_mutual_of_noDangling
                (proj := proj) hNoDangling hColl hReturn hPay (Or.inr hNest₂₁)
            exact Or.inr (Or.inl hMut)
      · exact False.elim ((hNoSing F₁ F₂) hSing)

/--
No-energy support plus the two seam-audit prohibitions gives the nested resolver
required by the existing near-close machinery.
-/
theorem noEnergySupport_resolves_nested {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoEnergy : NoEnergyCollisionSupport proj)
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoDangling : NoDanglingOneWayNesting proj) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj := by
  intro F₁ F₂ hne hAdm₁ hAdm₂ hkey
  have hColl : LedgerSeamCollision proj F₁ F₂ :=
    ⟨hne, hAdm₁, hAdm₂, hkey⟩
  have hAlt : NoEnergySupportAlternative proj F₁ F₂ :=
    hNoEnergy F₁ F₂ hne hAdm₁ hAdm₂ hkey
  exact noEnergyAlternative_to_nestedResolution
    (proj := proj) hNoSing hNoDangling hColl hAlt

/-- Same reduction packaged as a stable-universe theorem. -/
theorem noEnergyStableUniverse_resolves_nested {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoEnergyStableUniverse proj) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj :=
  noEnergySupport_resolves_nested
    (proj := proj) H.1 H.2.1 H.2.2

/-- Consequently a no-energy stable universe also supplies the older
cycle-or-payment resolver.  The payment branch may still syntactically appear in
that old resolver, but the construction of the resolver did not use an energy
or payment channel. -/
theorem noEnergyStableUniverse_resolves_old {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoEnergyStableUniverse proj) :
    SemanticExtendedFlowLedgerCollisionResolves proj :=
  nestedSemanticExtended_resolves_old
    (noEnergyStableUniverse_resolves_nested (proj := proj) H)

/-#############################################################################
  §3. Collapse for an infinite generated-flow family
#############################################################################-/

/--
An infinite family of generated genealogies cannot be supported by a finite
no-energy stable ledger.  The contradiction goes through the usual finite-key
pigeonhole, then through the no-energy nested resolver, and finally through
lexRank/payment impossibility already proved elsewhere.
-/
theorem infinite_extended_flows_impossible_noEnergyStableUniverse
    {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕)
    (H : NoEnergyStableUniverse proj) :
    False := by
  exact infinite_extended_flows_impossible_with_resolution
    (A := A) (M0 := M0) proj h𝓕
    (noEnergyStableUniverse_resolves_old (proj := proj) H)

/--
Under a hypothetical last-twin bound, a no-energy stable ledger is impossible.
This is the formal version of:

  after the last twin, infinitely many fresh flows must be absorbed;
  if there is no energy channel, the old finite universe can only support them
  by return/nesting;
  but return/nesting is forbidden by lexRank once it closes.
-/
theorem twinBound_impossible_with_noEnergyStableUniverse
    {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (H : NoEnergyStableUniverse proj) :
    False := by
  obtain ⟨𝓕, h𝓕⟩ :=
    twinBoundForcesInfiniteExtendedGeneratedFlows_closed
      (A := A) (M0 := M0) hTwinBound
  exact infinite_extended_flows_impossible_noEnergyStableUniverse
    (A := A) (M0 := M0) (proj := proj) h𝓕 H

/-#############################################################################
  §4. Final no-energy last obligation
#############################################################################-/

/--
The no-energy version of the final Step00 obligation.

For one fixed scale `A`, every hypothetical last-twin bound `M0` admits a finite
semantic projection whose same-key collisions are geometrically supported
without payment, and whose seam audit forbids singularity and dangling nesting.
-/
abbrev TheNoEnergyStableUniverseLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∀ M0 : ℕ, NoEnergyStableUniverse (projOf M0)

/-- The no-energy stable-universe last obligation implies the nested-universe
last obligation. -/
theorem noEnergyStableUniverseLast_implies_nestedUniverseLast
    (H : TheNoEnergyStableUniverseLastStep00Obligation) :
    TheNestedUniverseLastStep00Obligation := by
  rcases H with ⟨A, projOf, hStable⟩
  refine ⟨A, projOf, ?_⟩
  intro M0
  exact noEnergyStableUniverse_resolves_nested
    (proj := projOf M0) (hStable M0)

/-- Therefore a no-energy stable Step00 universe is sufficient for infinitude of
lower twin centres. -/
theorem twinLowersInfinite_of_noEnergyStableUniverseLastStep00Obligation
    (H : TheNoEnergyStableUniverseLastStep00Obligation) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_nestedUniverseLastStep00Obligation
    (noEnergyStableUniverseLast_implies_nestedUniverseLast H)

/-#############################################################################
  §5. Audit names
#############################################################################-/

/-- The remaining certificate for the no-energy interpretation: same-key
collisions must be supported geometrically, not by payment. -/
abbrev RemainingNoEnergySupportCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoEnergyCollisionSupport proj

/-- A candidate projection with no payment channel fails precisely by creating a
same-key collision that is not geometrically supported except by a broken seam. -/
def ProjectionNeedsEnergyOrSingularity {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∃ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    LedgerSeamCollision proj F₁ F₂ ∧
    ¬ ExtendedFlowReturnCertificate F₁ F₂ ∧
    ¬ NestedUniverseEmbedding F₁ F₂ ∧
    ¬ NestedUniverseEmbedding F₂ F₁

/--
Reading guide:
if `ProjectionNeedsEnergyOrSingularity proj` holds, then a no-energy interpretation
of `proj` can succeed only by allowing a broken seam.  If broken seams are forbidden,
then the projection must add a genuine energy/payment channel or produce a
return/nesting engine.
-/
abbrev NoEnergyReadingGuide {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoEnergyCollisionSupport proj ∧
  NoLedgerSeamSingularity proj ∧
  NoDanglingOneWayNesting proj

/-! Machine honesty of the no-energy form -/

/-- Under the two seam-bans the support-condition is VACUOUS: the triple ⟺ the audit pair. -/
theorem noEnergyStableUniverse_iff_seamAudit {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    NoEnergyStableUniverse proj ↔
      (NoLedgerSeamSingularity proj ∧ NoDanglingOneWayNesting proj) := by
  constructor
  · rintro ⟨_, hNoSing, hNoDangling⟩
    exact ⟨hNoSing, hNoDangling⟩
  · rintro ⟨hNoSing, hNoDangling⟩
    refine ⟨?_, hNoSing, hNoDangling⟩
    intro F₁ F₂ hne h1 h2 hkey
    exact (seamAudit_forces_no_collision hNoSing hNoDangling F₁ F₂
      ⟨hne, h1, h2, hkey⟩).elim

/-- No-energy stable universe ⟺ old resolver. -/
theorem noEnergyStableUniverse_iff_resolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    NoEnergyStableUniverse proj ↔
      SemanticExtendedFlowLedgerCollisionResolves proj :=
  noEnergyStableUniverse_iff_seamAudit.trans (seamAudit_iff_resolves proj)

/-- No-energy-obligation ⟺ old node (a reformulation, not a bypass). -/
theorem noEnergyStableUniverseLastStep00Obligation_iff_lastStep00Obligation :
    TheNoEnergyStableUniverseLastStep00Obligation ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 =>
      (noEnergyStableUniverse_iff_resolves (projOf M0)).mp (h M0)⟩
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 =>
      (noEnergyStableUniverse_iff_resolves (projOf M0)).mpr (h M0)⟩

/-- No-energy stable universe at scale M0 — also a twin-detector. -/
theorem twin_above_of_noEnergyStableUniverse {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (H : NoEnergyStableUniverse proj) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves proj (noEnergyStableUniverse_resolves_old H)

/-#############################################################################
  NO INFINITE COMPRESSION OF INFORMATION (brick:
  no_infinite_information_compression).
  "Gauge may be forgotten, causality may not be compressed forever": strict
  compression = collision + one-sided nesting (lexRank descent, not a final);
  an ∞-chain of compressions is impossible (via nested-chains). Fix of the brick: in
  the reverse cases ¬Return is flipped via Or.symm. Below — the brick +
  machine honesty: NoCompression ⟺ NoDangling, the audit pair ⟺ old
  resolver, obligation ⟺ old node, twin-detector.
#############################################################################-/

/-#############################################################################
  §1. Strict causal information compression
#############################################################################-/

/--
A strict information-compression step from `F_outer` to `F_inner`.

The finite semantic key has identified two admissible genealogies.  There is no
return certificate, no mutual nesting/engine, and no payment contradiction; the
only available realization is that `F_inner` is a smaller internal universe of
`F_outer`.

This is a legal descent event, not a final resolution of the Step00 collision.
-/
def StrictInformationCompression {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F_outer F_inner : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamCollision proj F_outer F_inner ∧
  NestedUniverseEmbedding F_outer F_inner ∧
  ¬ ExtendedFlowReturnCertificate F_outer F_inner ∧
  ¬ MutuallyNestedUniverses F_outer F_inner ∧
  ¬ ImpossiblePayment

/-- A projection has no unresolved one-way compression steps.  This is stronger
than merely saying that infinite compression chains are impossible; it forbids
using a single dangling compression as a terminal explanation of a collision. -/
def NoStrictInformationCompression {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    ¬ StrictInformationCompression proj F₁ F₂

/-- A strict information-compression step strictly decreases the start-rank of
the internal universe. -/
theorem strictInformationCompression_drops_rank {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F_outer F_inner : ExtendedProperGeneratedFlow A M0}
    (h : StrictInformationCompression proj F_outer F_inner) :
    lexRank (State.center F_inner.start) <
      lexRank (State.center F_outer.start) := by
  exact nestedUniverseEmbedding_drops_startRank h.2.1

/-#############################################################################
  §2. Infinite compression chains are impossible
#############################################################################-/

/-- An infinite chain of strict information-compression steps. -/
def InformationCompressionChain {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (C : ℕ → ExtendedProperGeneratedFlow A M0) : Prop :=
  ∀ i : ℕ, StrictInformationCompression proj (C i) (C (i + 1))

/-- Every information-compression chain is in particular a nested-universe
chain. -/
theorem informationCompressionChain_to_nestedUniverseChain {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {C : ℕ → ExtendedProperGeneratedFlow A M0}
    (hC : InformationCompressionChain proj C) :
    NestedUniverseChain C := by
  intro i
  exact (hC i).2.1

/-- There is no infinite chain of strict causal information compression in the
concrete Step00 graph.  This is the precise formal version of: information may
be compressed into a smaller internal universe, but not forever. -/
theorem no_informationCompressionChain {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (C : ℕ → ExtendedProperGeneratedFlow A M0) :
    ¬ InformationCompressionChain proj C := by
  intro hC
  exact no_nestedUniverseChain C
    (informationCompressionChain_to_nestedUniverseChain (proj := proj) hC)

/-- Equivalently, the rank of a finite prefix of a compression chain has already
dropped by at least the prefix length.  This is useful for audit/debugging: the
compression cannot be hidden in a finite semantic key without consuming concrete
`lexRank`. -/
theorem informationCompressionChain_rank_bound {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {C : ℕ → ExtendedProperGeneratedFlow A M0}
    (hC : InformationCompressionChain proj C) :
    ∀ n : ℕ,
      lexRank (State.center (C n).start) + n ≤
        lexRank (State.center (C 0).start) := by
  exact nestedUniverseChain_rank_bound
    (C := C) (informationCompressionChain_to_nestedUniverseChain (proj := proj) hC)

/-#############################################################################
  §3. Same-key collisions classified with compression as an explicit case
#############################################################################-/

/--
The full information-theoretic classification of a same-key seam collision.

The compression alternatives are the two possible one-way embeddings.  They are
kept separate from mutual nesting: mutual nesting is already an engine, whereas
strict compression is only a smaller internal universe and cannot be accepted as
an infinite support mechanism.
-/
def InformationCompressionAlternative {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  ExtendedFlowReturnCertificate F₁ F₂ ∨
  MutuallyNestedUniverses F₁ F₂ ∨
  ImpossiblePayment ∨
  LedgerSeamSingularity proj F₁ F₂ ∨
  StrictInformationCompression proj F₁ F₂ ∨
  StrictInformationCompression proj F₂ F₁

/-- Same-key seam collisions classically fall into the explicit information
classification: return, mutual nesting, payment, singularity, or strict
one-way compression in one of the two directions.

This theorem is only a classifier; it does not prove Step00.  It names the
remaining non-closing case as compression rather than silently accepting it as an
engine. -/
theorem seamCollision_informationCompression_classification {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hColl : LedgerSeamCollision proj F₁ F₂) :
    InformationCompressionAlternative proj F₁ F₂ := by
  classical
  have hClass := seamCollision_classical_classification (proj := proj) hColl
  rcases hClass with hReturn | hRest
  · exact Or.inl hReturn
  · rcases hRest with hNest₁₂ | hRest
    · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
      · exact Or.inl hReturn
      · by_cases hMut : MutuallyNestedUniverses F₁ F₂
        · exact Or.inr (Or.inl hMut)
        · by_cases hPay : ImpossiblePayment
          · exact Or.inr (Or.inr (Or.inl hPay))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hColl, hNest₁₂, hReturn, hMut, hPay⟩))))
    · rcases hRest with hNest₂₁ | hRest
      · by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
        · exact Or.inl hReturn
        · by_cases hMut : MutuallyNestedUniverses F₁ F₂
          · exact Or.inr (Or.inl hMut)
          · by_cases hPay : ImpossiblePayment
            · exact Or.inr (Or.inr (Or.inl hPay))
            · have hCollRev : LedgerSeamCollision proj F₂ F₁ := by
                rcases hColl with ⟨hne, hAdm₁, hAdm₂, hkey⟩
                exact ⟨Ne.symm hne, hAdm₂, hAdm₁, hkey.symm⟩
              have hNoMutRev : ¬ MutuallyNestedUniverses F₂ F₁ := by
                intro hRev
                exact hMut hRev.symm
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨hCollRev, hNest₂₁, fun h => hReturn h.symm, hNoMutRev, hPay⟩))))
      · rcases hRest with hPay | hSing
        · exact Or.inr (Or.inr (Or.inl hPay))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hSing)))

/-#############################################################################
  §4. Compression audit versus dangling nesting audit
#############################################################################-/

/-- If a projection has no strict information-compression steps, then it has no
dangling one-way nesting. -/
theorem noStrictCompression_implies_noDangling {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoStrictInformationCompression proj) :
    NoDanglingOneWayNesting proj := by
  intro F₁ F₂ hDangling
  rcases hDangling with ⟨hColl, hNoReturn, hNoMutual, hNoPayment, hOneWay⟩
  rcases hOneWay with hNest₁₂ | hNest₂₁
  · exact H F₁ F₂
      ⟨hColl, hNest₁₂, hNoReturn, hNoMutual, hNoPayment⟩
  · have hCollRev : LedgerSeamCollision proj F₂ F₁ := by
      rcases hColl with ⟨hne, hAdm₁, hAdm₂, hkey⟩
      exact ⟨Ne.symm hne, hAdm₂, hAdm₁, hkey.symm⟩
    have hNoMutualRev : ¬ MutuallyNestedUniverses F₂ F₁ := by
      intro hMutRev
      exact hNoMutual hMutRev.symm
    exact H F₂ F₁
      ⟨hCollRev, hNest₂₁, fun h => hNoReturn h.symm, hNoMutualRev, hNoPayment⟩

/-- No seam singularities plus no strict compression gives the existing nested
resolver.  This is the clean audit form of:

  a finite projection may forget only gauge information;
  it may not forget causal information into a singular seam;
  and it may not use one-way compression as a final support mechanism.
-/
theorem noSingularity_noStrictCompression_resolves_nested {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj) :
    NestedSemanticExtendedFlowLedgerCollisionResolves proj := by
  exact noSingularity_noDangling_resolves_nested
    (proj := proj)
    hNoSing
    (noStrictCompression_implies_noDangling (proj := proj) hNoCompression)

/-- And therefore it also gives the old cycle-or-payment resolver. -/
theorem noSingularity_noStrictCompression_resolves_old {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj) :
    SemanticExtendedFlowLedgerCollisionResolves proj :=
  nestedSemanticExtended_resolves_old
    (noSingularity_noStrictCompression_resolves_nested
      (proj := proj) hNoSing hNoCompression)

/-#############################################################################
  §5. Final obligation phrased as no singularity + no infinite compression
#############################################################################-/

/--
The information-compression version of the last Step00 obligation.

For one fixed scale `A`, every last-twin bound `M0` must have a finite semantic
flow-ledger projection whose same-key collisions have neither seam singularities
nor unresolved strict compression.  Under those two audit conditions, the
existing generated-flow machinery closes the twin-prime contradiction.
-/
abbrev InformationCompressionLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
      ∀ M0 : ℕ,
        NoLedgerSeamSingularity (projOf M0) ∧
        NoStrictInformationCompression (projOf M0)

/-- The information-compression last obligation implies the old strict final
obligation and hence infinitely many lower twin centers. -/
theorem twinLowersInfinite_of_informationCompressionLastStep00Obligation
    (H : InformationCompressionLastStep00Obligation) :
    TwinLowers.Infinite := by
  rcases H with ⟨A, projOf, hAudit⟩
  exact twinLowersInfinite_of_global_semanticExtendedResolution
    (A := A)
    (projOf := projOf)
    (by
      intro M0
      exact noSingularity_noStrictCompression_resolves_old
        (proj := projOf M0)
        (hAudit M0).1
        (hAudit M0).2)

/-#############################################################################
  §6. Human-readable residue of the patch
#############################################################################-/

/--
The remaining concrete certificate after this patch.

The finite projection must be conservative on causal information:
if it identifies two admissible genealogies, then the identification is either
an engine/payment event or a single smaller compression step.  But such steps
cannot continue forever by `lexRank`, and they cannot be accepted as terminal
ledger explanations under `NoStrictInformationCompression`.
-/
abbrev RemainingNoInfiniteCompressionCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoLedgerSeamSingularity proj ∧
  NoStrictInformationCompression proj

/-! Machine honesty of the compression form -/

/-- Compression = collision + nesting (the remaining bans are satisfied for free). -/
theorem strictInformationCompression_iff {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    StrictInformationCompression proj F₁ F₂ ↔
      (LedgerSeamCollision proj F₁ F₂ ∧ NestedUniverseEmbedding F₁ F₂) := by
  constructor
  · rintro ⟨hColl, hNest, _, _, _⟩
    exact ⟨hColl, hNest⟩
  · rintro ⟨hColl, hNest⟩
    exact ⟨hColl, hNest, no_extendedFlowReturnCertificate,
      no_mutuallyNestedUniverses, BoundaryDefectPayment.impossiblePayment_false⟩

/-- The ban on compression ⟺ the ban on dangling nestings (both directions). -/
theorem noStrictCompression_iff_noDangling {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0} :
    NoStrictInformationCompression proj ↔ NoDanglingOneWayNesting proj := by
  constructor
  · exact noStrictCompression_implies_noDangling
  · intro hNoDangling F₁ F₂ hComp
    rcases strictInformationCompression_iff.mp hComp with ⟨hColl, hNest⟩
    exact (noDanglingOneWayNesting_iff.mp hNoDangling) F₁ F₂ hColl (Or.inl hNest)

/-- Compression-audit ⟺ old resolver. -/
theorem compressionAudit_iff_resolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    (NoLedgerSeamSingularity proj ∧ NoStrictInformationCompression proj) ↔
      SemanticExtendedFlowLedgerCollisionResolves proj := by
  rw [noStrictCompression_iff_noDangling]
  exact seamAudit_iff_resolves proj

/-- Compression-obligation ⟺ old node (a reformulation, not a bypass). -/
theorem informationCompressionLastStep00Obligation_iff_lastStep00Obligation :
    InformationCompressionLastStep00Obligation ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 =>
      (compressionAudit_iff_resolves (projOf M0)).mp (h M0)⟩
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 =>
      (compressionAudit_iff_resolves (projOf M0)).mpr (h M0)⟩

/-- Compression-audit at scale M0 — also a twin-detector. -/
theorem twin_above_of_compressionAudit {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves proj
    (noSingularity_noStrictCompression_resolves_old hNoSing hNoCompression)

/-#############################################################################
  INFORMATION ATOMS / EXTRACTION AND MIXING WITHOUT AN ENGINE (bricks:
  information_atom_extraction + no_free_information_mixing).
  An atom = a genealogy without strict compression; an atomless universe generates
  an ∞-chain of compressions (Classical.choose-orbit) — impossible, so in every
  inhabited universe there IS an atom (an unconditional result). Extraction/
  mixing of information without return/engine/payment — a singularity or a
  compression; impossible under the audit pair. Below — the bricks + machine
  honesty: extraction/mixing-without-an-engine ⟺ just a collision (the bans
  satisfied for free), atomic-obligation ⟺ old node, twin-detectors.
#############################################################################-/

/-#############################################################################
  §1. Information atoms
#############################################################################-/

/--
`F` is an information atom for the projection `proj` if no admissible generated
flow can be obtained from it by a strict causal information-compression step.

This is the formal version of: the start of `F` is an indivisible unit of causal
information for the current ledger view.
-/
def InformationAtom {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F : ExtendedProperGeneratedFlow A M0) : Prop :=
  ∀ G : ExtendedProperGeneratedFlow A M0,
    ¬ StrictInformationCompression proj F G

/-- `F` is non-atomic if it admits a strict compression into a smaller internal
universe. -/
def InformationSplits {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F : ExtendedProperGeneratedFlow A M0) : Prop :=
  ∃ G : ExtendedProperGeneratedFlow A M0,
    StrictInformationCompression proj F G

/-- Atom/split are exact complements, classically. -/
theorem not_informationAtom_iff_splits {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F : ExtendedProperGeneratedFlow A M0} :
    ¬ InformationAtom proj F ↔ InformationSplits proj F := by
  classical
  constructor
  · intro hAtom
    unfold InformationAtom at hAtom
    push_neg at hAtom
    exact hAtom
  · rintro ⟨G, hComp⟩ hAtom
    exact hAtom G hComp

/-- A whole projection is atomless if every generated genealogy can still be
strictly compressed. -/
def NoInformationAtoms {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F : ExtendedProperGeneratedFlow A M0,
    InformationSplits proj F

/-- The classical successor chosen by an atomless projection.  This definition
is deliberately local to the audit layer: it is not an algorithmic construction,
only a witness extractor from `NoInformationAtoms`. -/
noncomputable def compressionSuccessor {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoInformationAtoms proj)
    (F : ExtendedProperGeneratedFlow A M0) :
    ExtendedProperGeneratedFlow A M0 :=
  Classical.choose (H F)

/-- The chosen successor is really a strict compression target. -/
theorem compressionSuccessor_spec {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoInformationAtoms proj)
    (F : ExtendedProperGeneratedFlow A M0) :
    StrictInformationCompression proj F (compressionSuccessor H F) := by
  exact Classical.choose_spec (H F)

/-- The orbit obtained by repeatedly compressing a non-atomic genealogy. -/
noncomputable def compressionOrbit {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoInformationAtoms proj)
    (F₀ : ExtendedProperGeneratedFlow A M0) :
    ℕ → ExtendedProperGeneratedFlow A M0 :=
  fun n => Nat.rec F₀ (fun _ F => compressionSuccessor H F) n

/-- An atomless universe generates an infinite strict information-compression
chain from any starting flow. -/
theorem atomless_generates_informationCompressionChain {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoInformationAtoms proj)
    (F₀ : ExtendedProperGeneratedFlow A M0) :
    InformationCompressionChain proj (compressionOrbit H F₀) := by
  intro i
  unfold compressionOrbit
  -- `Nat.rec` at `i + 1` unfolds to the chosen successor of the value at `i`.
  exact compressionSuccessor_spec (proj := proj) H
    (Nat.rec F₀ (fun _ F => compressionSuccessor H F) i)

/-- Hence, if at least one generated flow exists, a globally atomless
information universe is impossible.  Otherwise it would produce an infinite
strict-compression chain, contradicting `lexRank` well-foundedness. -/
theorem no_global_atomless_information_universe {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (F₀ : ExtendedProperGeneratedFlow A M0) :
    ¬ NoInformationAtoms proj := by
  intro H
  exact no_informationCompressionChain
    (proj := proj)
    (compressionOrbit H F₀)
    (atomless_generates_informationCompressionChain (proj := proj) H F₀)

/-- Equivalently: every inhabited stable generated-flow universe has at least
one information atom. -/
theorem exists_informationAtom_of_inhabited {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (F₀ : ExtendedProperGeneratedFlow A M0) :
    ∃ F : ExtendedProperGeneratedFlow A M0,
      InformationAtom proj F := by
  classical
  by_contra hNoAtom
  push_neg at hNoAtom
  have H : NoInformationAtoms proj := by
    intro F
    exact (not_informationAtom_iff_splits (proj := proj) (F := F)).mp (hNoAtom F)
  exact no_global_atomless_information_universe (proj := proj) F₀ H

/-#############################################################################
  §2. Taking information without starting the engine
#############################################################################-/

/--
A same-key collision tries to remove the information distinguishing two
admissible genealogies when it identifies them by the finite key but refuses all
engine/payment explanations.

This object is intentionally *not* a valid resolver.  It is the formal version
of:

  the ledger has taken causal information away, but no return engine, mutual
  nesting engine, or payment has been supplied.
-/
def InformationExtractionWithoutEngine {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamCollision proj F₁ F₂ ∧
  ¬ ExtendedFlowReturnCertificate F₁ F₂ ∧
  ¬ MutuallyNestedUniverses F₁ F₂ ∧
  ¬ ImpossiblePayment

/--
The extraction is explained if it is either a forbidden seam singularity or a
strict information-compression step in one of the two directions.
-/
def ExtractionFailureAlternative {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamSingularity proj F₁ F₂ ∨
  StrictInformationCompression proj F₁ F₂ ∨
  StrictInformationCompression proj F₂ F₁

/--
Trying to take causal information without a return engine, mutual nesting, or
payment can only be a seam singularity or a strict one-way compression.

This is pure classification over the already formalized seam alternatives.  It
is the precise audit statement:

  information cannot be removed for free; if no engine/payment witness appears,
  the attempt is either a broken seam or a descending compression event.
-/
theorem informationExtractionWithoutEngine_classifies {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (h : InformationExtractionWithoutEngine proj F₁ F₂) :
    ExtractionFailureAlternative proj F₁ F₂ := by
  classical
  rcases h with ⟨hColl, hNoReturn, hNoMutual, hNoPayment⟩
  have hAlt := seamCollision_informationCompression_classification
    (proj := proj) hColl
  rcases hAlt with hReturn | hAlt
  · exact False.elim (hNoReturn hReturn)
  · rcases hAlt with hMutual | hAlt
    · exact False.elim (hNoMutual hMutual)
    · rcases hAlt with hPayment | hAlt
      · exact False.elim (hNoPayment hPayment)
      · rcases hAlt with hSing | hAlt
        · exact Or.inl hSing
        · rcases hAlt with hComp₁₂ | hComp₂₁
          · exact Or.inr (Or.inl hComp₁₂)
          · exact Or.inr (Or.inr hComp₂₁)

/-- If seam singularities and strict compressions are both forbidden, then one
cannot extract information without starting an engine or paying. -/
theorem no_free_information_extraction {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj) :
    ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
      ¬ InformationExtractionWithoutEngine proj F₁ F₂ := by
  intro F₁ F₂ hExtract
  have hClass := informationExtractionWithoutEngine_classifies
    (proj := proj) hExtract
  rcases hClass with hSing | hRest
  · exact hNoSing F₁ F₂ hSing
  · rcases hRest with hComp₁₂ | hComp₂₁
    · exact hNoCompression F₁ F₂ hComp₁₂
    · exact hNoCompression F₂ F₁ hComp₂₁

/-- A positive form: under the no-singularity/no-compression audit, every
same-key seam collision must trigger the engine/payment alternatives. -/
theorem information_cannot_be_taken_without_engine_or_payment {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj)
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hColl : LedgerSeamCollision proj F₁ F₂) :
    ExtendedFlowReturnCertificate F₁ F₂ ∨
    MutuallyNestedUniverses F₁ F₂ ∨
    ImpossiblePayment := by
  classical
  by_cases hReturn : ExtendedFlowReturnCertificate F₁ F₂
  · exact Or.inl hReturn
  · by_cases hMutual : MutuallyNestedUniverses F₁ F₂
    · exact Or.inr (Or.inl hMutual)
    · by_cases hPayment : ImpossiblePayment
      · exact Or.inr (Or.inr hPayment)
      · have hExtract : InformationExtractionWithoutEngine proj F₁ F₂ :=
          ⟨hColl, hReturn, hMutual, hPayment⟩
        exact False.elim
          ((no_free_information_extraction
              (proj := proj) hNoSing hNoCompression) F₁ F₂ hExtract)

/-#############################################################################
  §3. Final audit package
#############################################################################-/

/--
The atom/extraction version of the remaining local certificate.

It consists of the two exact non-cheating principles:

  * no broken seam: the projection may not identify two genealogies that the
    real graph cannot glue;
  * no unresolved strict compression: information may be compressed only as a
    genuine descent, not as a terminal explanation of a ledger collision.

Under these two conditions, causal information cannot be taken without producing
an engine/payment alternative, and an inhabited generated-flow universe must have
an information atom.
-/
structure AtomicInformationAuditPackage (A M0 : ℕ) where
  proj : SemanticExtendedFlowLedgerProjection A M0
  noSeamSingularity : NoLedgerSeamSingularity proj
  noStrictCompression : NoStrictInformationCompression proj

/-- The package gives the old nested resolver. -/
theorem atomicInformationAudit_resolves_nested {A M0 : ℕ}
    (P : AtomicInformationAuditPackage A M0) :
    NestedSemanticExtendedFlowLedgerCollisionResolves P.proj :=
  noSingularity_noStrictCompression_resolves_nested
    (proj := P.proj) P.noSeamSingularity P.noStrictCompression

/-- The package gives the old cycle-or-payment resolver. -/
theorem atomicInformationAudit_resolves_old {A M0 : ℕ}
    (P : AtomicInformationAuditPackage A M0) :
    SemanticExtendedFlowLedgerCollisionResolves P.proj :=
  noSingularity_noStrictCompression_resolves_old
    (proj := P.proj) P.noSeamSingularity P.noStrictCompression

/-- The final Step00 obligation stated as atomic information conservation:
for one fixed scale, every last-twin bound has a finite semantic projection
whose same-key collisions neither tear a seam nor use unresolved strict
compression as a terminal support mechanism. -/
abbrev AtomicInformationLastStep00Obligation : Prop :=
  ∃ A : ℕ,
    ∃ POf : ∀ M0 : ℕ, AtomicInformationAuditPackage A M0,
      True

/-- Atomic information conservation is sufficient for the already constructed
Step00 machine to conclude infinitely many lower twin centers. -/
theorem twinLowersInfinite_of_atomicInformationLastStep00Obligation
    (H : AtomicInformationLastStep00Obligation) :
    TwinLowers.Infinite := by
  rcases H with ⟨A, POf, _⟩
  exact twinLowersInfinite_of_global_semanticExtendedResolution
    (A := A)
    (projOf := fun M0 => (POf M0).proj)
    (by
      intro M0
      exact atomicInformationAudit_resolves_old (POf M0))

/-- Human-readable residue: this is the exact remaining certificate behind the
slogan “a start is an indivisible information unit; information cannot be taken
without starting the engine.” -/
abbrev RemainingAtomicInformationCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoLedgerSeamSingularity proj ∧
  NoStrictInformationCompression proj

/-#############################################################################
  §1. Causal mixing collisions
#############################################################################-/

/--
A same-key collision genuinely mixes causal information when the two generated
flows have different start atoms and different terminal ledger states.

This rules out two weaker phenomena:

* merely two certificates for the same start;
* merely two histories ending at the same terminal.

A mixing collision is the case where the finite key has identified two distinct
source/terminal pairings.
-/
def InformationMixingCollision {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamCollision proj F₁ F₂ ∧
  F₁.start ≠ F₂.start ∧
  F₁.terminal ≠ F₂.terminal

/--
Free information mixing is a mixing collision that refuses all engine/payment
explanations already accepted by the audit:

* no direct return certificate;
* no mutual nesting engine;
* no impossible-payment certificate.

It is deliberately not a valid final resolver.
-/
def InformationMixingWithoutEngine {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  InformationMixingCollision proj F₁ F₂ ∧
  ¬ ExtendedFlowReturnCertificate F₁ F₂ ∧
  ¬ MutuallyNestedUniverses F₁ F₂ ∧
  ¬ ImpossiblePayment

/-- Every free mixing event is, in particular, a free extraction event. -/
theorem informationMixingWithoutEngine_to_extraction {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (h : InformationMixingWithoutEngine proj F₁ F₂) :
    InformationExtractionWithoutEngine proj F₁ F₂ := by
  rcases h with ⟨hMix, hNoReturn, hNoMutual, hNoPayment⟩
  exact ⟨hMix.1, hNoReturn, hNoMutual, hNoPayment⟩

/-#############################################################################
  §2. Classification of free mixing
#############################################################################-/

/--
The possible explanations of a free mixing attempt are inherited from the
extraction layer: either the ledger seam is singular, or the event is actually a
strict one-way information-compression descent in one of the two directions.
-/
def MixingFailureAlternative {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁ F₂ : ExtendedProperGeneratedFlow A M0) : Prop :=
  LedgerSeamSingularity proj F₁ F₂ ∨
  StrictInformationCompression proj F₁ F₂ ∨
  StrictInformationCompression proj F₂ F₁

/--
A free mixing attempt classifies as a seam singularity or strict compression.
This is the precise formal version of:

  information cannot be mixed for free; if no engine/payment witness appears,
  the attempt is either a broken seam or a descending compression event.
-/
theorem informationMixingWithoutEngine_classifies {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (h : InformationMixingWithoutEngine proj F₁ F₂) :
    MixingFailureAlternative proj F₁ F₂ := by
  exact informationExtractionWithoutEngine_classifies
    (proj := proj) (informationMixingWithoutEngine_to_extraction (proj := proj) h)

/--
If seam singularities and unresolved strict compression are forbidden, then no
free information mixing is possible.
-/
theorem no_free_information_mixing {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj) :
    ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
      ¬ InformationMixingWithoutEngine proj F₁ F₂ := by
  intro F₁ F₂ hMix
  have hExtract : InformationExtractionWithoutEngine proj F₁ F₂ :=
    informationMixingWithoutEngine_to_extraction (proj := proj) hMix
  exact (no_free_information_extraction
    (proj := proj) hNoSing hNoCompression) F₁ F₂ hExtract

/--
Positive form: every genuine same-key mixing collision must trigger an
engine/payment alternative, unless the projection violates the no-singularity or
no-compression audit.
-/
theorem information_cannot_be_mixed_without_engine_or_payment {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj)
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hMix : InformationMixingCollision proj F₁ F₂) :
    ExtendedFlowReturnCertificate F₁ F₂ ∨
    MutuallyNestedUniverses F₁ F₂ ∨
    ImpossiblePayment := by
  exact information_cannot_be_taken_without_engine_or_payment
    (proj := proj) hNoSing hNoCompression hMix.1

/-#############################################################################
  §3. Optional square version: explicit cross-wiring
#############################################################################-/

/--
A concrete square witnessing that source atoms and terminal ledger states have
been cross-wired.

`F₁₁` and `F₂₂` are the two original flows.  `F₁₂` has the first start and the
second terminal; `F₂₁` has the second start and the first terminal.  This square
is not itself an engine.  It only records the exact place where causal
information has been permuted.
-/
structure InformationMixingSquare {A M0 : ℕ}
    (F₁₁ F₂₂ F₁₂ F₂₁ : ExtendedProperGeneratedFlow A M0) : Prop where
  distinctStarts : F₁₁.start ≠ F₂₂.start
  distinctTerminals : F₁₁.terminal ≠ F₂₂.terminal
  crossStart₁₂ : F₁₂.start = F₁₁.start
  crossTerminal₁₂ : F₁₂.terminal = F₂₂.terminal
  crossStart₂₁ : F₂₁.start = F₂₂.start
  crossTerminal₂₁ : F₂₁.terminal = F₁₁.terminal

/--
A same-key mixing square: the two crossed flows occupy the same finite ledger
class as the original pair.  This is a stronger diagnostic object than a single
mixing collision, but it is still only an audit object, not a resolver.
-/
structure SameKeyInformationMixingSquare {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (F₁₁ F₂₂ F₁₂ F₂₁ : ExtendedProperGeneratedFlow A M0) : Prop
    extends InformationMixingSquare F₁₁ F₂₂ F₁₂ F₂₁ where
  originalSameKey : proj.keyFlow F₁₁ = proj.keyFlow F₂₂
  crossSameKey₁₂ : proj.keyFlow F₁₂ = proj.keyFlow F₁₁
  crossSameKey₂₁ : proj.keyFlow F₂₁ = proj.keyFlow F₂₂
  crossedDistinct₁₂ : F₁₂ ≠ F₁₁ ∨ F₁₂ ≠ F₂₂
  crossedDistinct₂₁ : F₂₁ ≠ F₁₁ ∨ F₂₁ ≠ F₂₂

/--
A same-key mixing square always contains a same-key mixing collision between the
original opposite corners, provided the original flows are admissible and
distinct as flows.
-/
theorem sameKeyMixingSquare_to_mixingCollision {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁₁ F₂₂ F₁₂ F₂₁ : ExtendedProperGeneratedFlow A M0}
    (hAdm₁ : ExtendedFlowAdmissible F₁₁)
    (hAdm₂ : ExtendedFlowAdmissible F₂₂)
    (hNe : F₁₁ ≠ F₂₂)
    (hSq : SameKeyInformationMixingSquare proj F₁₁ F₂₂ F₁₂ F₂₁) :
    InformationMixingCollision proj F₁₁ F₂₂ := by
  refine ⟨?_, hSq.distinctStarts, hSq.distinctTerminals⟩
  exact ⟨hNe, hAdm₁, hAdm₂, hSq.originalSameKey⟩

/--
Therefore, under the same no-cheat audit assumptions, an explicit same-key
mixing square cannot be used to mix information without triggering the
engine/payment alternatives for the original two corners.
-/
theorem sameKeyMixingSquare_forces_engine_or_payment {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (hNoSing : NoLedgerSeamSingularity proj)
    (hNoCompression : NoStrictInformationCompression proj)
    {F₁₁ F₂₂ F₁₂ F₂₁ : ExtendedProperGeneratedFlow A M0}
    (hAdm₁ : ExtendedFlowAdmissible F₁₁)
    (hAdm₂ : ExtendedFlowAdmissible F₂₂)
    (hNe : F₁₁ ≠ F₂₂)
    (hSq : SameKeyInformationMixingSquare proj F₁₁ F₂₂ F₁₂ F₂₁) :
    ExtendedFlowReturnCertificate F₁₁ F₂₂ ∨
    MutuallyNestedUniverses F₁₁ F₂₂ ∨
    ImpossiblePayment := by
  have hMix : InformationMixingCollision proj F₁₁ F₂₂ :=
    sameKeyMixingSquare_to_mixingCollision
      (proj := proj) hAdm₁ hAdm₂ hNe hSq
  exact information_cannot_be_mixed_without_engine_or_payment
    (proj := proj) hNoSing hNoCompression hMix

/-#############################################################################
  §4. Audit package
#############################################################################-/

/--
The no-free-mixing version of the already isolated final audit assumptions.
It is intentionally the same mathematical burden as the atom/extraction layer:
no broken seams and no unresolved strict compression.
-/
structure NoFreeInformationMixingAuditPackage (A M0 : ℕ) where
  proj : SemanticExtendedFlowLedgerProjection A M0
  noSeamSingularity : NoLedgerSeamSingularity proj
  noStrictCompression : NoStrictInformationCompression proj

/-- The package forbids free mixing. -/
theorem noFreeInformationMixingAudit_forbids_mixing {A M0 : ℕ}
    (P : NoFreeInformationMixingAuditPackage A M0) :
    ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
      ¬ InformationMixingWithoutEngine P.proj F₁ F₂ := by
  exact no_free_information_mixing
    (proj := P.proj) P.noSeamSingularity P.noStrictCompression

/-- The package still gives the old nested resolver, hence plugs into the
already built final Step00 machine. -/
theorem noFreeInformationMixingAudit_resolves_nested {A M0 : ℕ}
    (P : NoFreeInformationMixingAuditPackage A M0) :
    NestedSemanticExtendedFlowLedgerCollisionResolves P.proj :=
  noSingularity_noStrictCompression_resolves_nested
    (proj := P.proj) P.noSeamSingularity P.noStrictCompression

/-- Human-readable residue: information may be projected only modulo gauge data;
it may not be mixed across different start/terminal pairings without producing
an engine/payment witness. -/
abbrev RemainingNoFreeMixingCertificate {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  NoLedgerSeamSingularity proj ∧
  NoStrictInformationCompression proj

/-! Machine honesty of the atom/extraction/mixing forms -/

/-- Extraction-without-an-engine = just a collision (the three bans satisfied for free). -/
theorem informationExtractionWithoutEngine_iff_collision {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    InformationExtractionWithoutEngine proj F₁ F₂ ↔
      LedgerSeamCollision proj F₁ F₂ := by
  constructor
  · exact fun h => h.1
  · intro hColl
    exact ⟨hColl, no_extendedFlowReturnCertificate,
      no_mutuallyNestedUniverses, BoundaryDefectPayment.impossiblePayment_false⟩

/-- Mixing-without-an-engine = just a mixing-collision. -/
theorem informationMixingWithoutEngine_iff_mixingCollision {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0} :
    InformationMixingWithoutEngine proj F₁ F₂ ↔
      InformationMixingCollision proj F₁ F₂ := by
  constructor
  · exact fun h => h.1
  · intro hMix
    exact ⟨hMix, no_extendedFlowReturnCertificate,
      no_mutuallyNestedUniverses, BoundaryDefectPayment.impossiblePayment_false⟩

/-- Atomic-obligation ⟺ old node (a reformulation, not a bypass). -/
theorem atomicInformationLastStep00Obligation_iff_lastStep00Obligation :
    AtomicInformationLastStep00Obligation ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, POf, _⟩
    exact ⟨A, fun M0 => (POf M0).proj, fun M0 =>
      (compressionAudit_iff_resolves ((POf M0).proj)).mp
        ⟨(POf M0).noSeamSingularity, (POf M0).noStrictCompression⟩⟩
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, fun M0 =>
      { proj := projOf M0
        noSeamSingularity :=
          ((compressionAudit_iff_resolves (projOf M0)).mpr (h M0)).1
        noStrictCompression :=
          ((compressionAudit_iff_resolves (projOf M0)).mpr (h M0)).2 },
      trivial⟩

/-- Atomic-package at scale M0 — also a twin-detector. -/
theorem twin_above_of_atomicInformationAudit {A M0 : ℕ}
    (P : AtomicInformationAuditPackage A M0) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves P.proj (atomicInformationAudit_resolves_old P)

/-- No-free-mixing-package at scale M0 — also a twin-detector. -/
theorem twin_above_of_noFreeMixingAudit {A M0 : ℕ}
    (P : NoFreeInformationMixingAuditPackage A M0) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_resolves P.proj
    (nestedSemanticExtended_resolves_old
      (noFreeInformationMixingAudit_resolves_nested P))

/-#############################################################################
  STABLE NO-ENGINE THEORY (brick: stable_no_engine_theory).
  Object-level meta-audit: a finite-twin universe, stable and without
  energy/seams/compression/mixing, is impossible — an attempt to close it
  BUILDS an explicit engine (legal cycle), which is forbidden by lexRank. Fixes:
  ConcreteEuclideanEngineWitness : Prop; the existential of the theory via Nonempty.
  Below — the brick + machine honesty: existence of the theory ⟺ old node
  (the diagnostic fields are recoverable from the resolver); a per-scale detector.
#############################################################################-/

/-#############################################################################
  §1. A stable no-engine Step00 theory
#############################################################################-/

/--
`NoFreeInformationMixing` is the proposition-level form of the theorem
`no_free_information_mixing`: no pair of generated genealogies may be cross-wired
by the ledger projection without engine/payment/singularity/compression support.
-/
def NoFreeInformationMixing {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) : Prop :=
  ∀ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
    ¬ InformationMixingWithoutEngine proj F₁ F₂

/--
A stable no-engine Step00 theory at one scale `A`.

The fields are deliberately separated:

* `stableNoEnergy` is the operative closing assumption used by the already
  proved no-energy universe theorem: same-key collisions must be geometrically
  supported and no broken seam / dangling nesting is permitted.
* `noStrictCompression` and `noMixing` are diagnostic strengthening fields. They
  record that the projection is not allowed to stabilise itself by unresolved
  one-way information compression or by cross-wiring different source/terminal
  information. They are not needed for the shortest close, but they make explicit
  the intended interpretation: the ledger may forget only gauge information.
-/
structure StableNoEngineStep00Theory (A : ℕ) where
  projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0
  stableNoEnergy : ∀ M0 : ℕ, NoEnergyStableUniverse (projOf M0)
  noStrictCompression : ∀ M0 : ℕ, NoStrictInformationCompression (projOf M0)
  noMixing : ∀ M0 : ℕ, NoFreeInformationMixing (projOf M0)

/--
The short operational content of a stable no-engine theory: it gives exactly the
last obligation of the no-energy stable-universe layer.
-/
theorem stableNoEngineTheory_to_noEnergyLast {A : ℕ}
    (T : StableNoEngineStep00Theory A) :
    TheNoEnergyStableUniverseLastStep00Obligation := by
  exact ⟨A, T.projOf, T.stableNoEnergy⟩

/--
Therefore a stable no-engine Step00 theory is already sufficient to derive
infinitely many lower twin centres.
-/
theorem twinLowersInfinite_of_stableNoEngineTheory {A : ℕ}
    (T : StableNoEngineStep00Theory A) : TwinLowers.Infinite :=
  twinLowersInfinite_of_noEnergyStableUniverseLastStep00Obligation
    (stableNoEngineTheory_to_noEnergyLast T)

/--
Internal no-go form: a stable no-engine Step00 theory is incompatible with the
finite-twin assumption.
-/
theorem finiteTwins_impossible_of_stableNoEngineTheory {A : ℕ}
    (T : StableNoEngineStep00Theory A)
    (hFiniteTwins : ¬ TwinLowers.Infinite) : False :=
  hFiniteTwins (twinLowersInfinite_of_stableNoEngineTheory T)

/-#############################################################################
  §2. What it means to "prove the stable finite theory": it builds an engine
#############################################################################-/

/--
A concrete Euclidean engine witness in the present Step00 graph.  It is just a
legal nonempty cycle, packaged as data so that later audit lemmas can say:
"this attempted explanation has constructed a perpetual engine".
-/
structure ConcreteEuclideanEngineWitness (A M0 : ℕ) : Prop where
  cycle : LegalCycle (RealStep A M0) (Legal A M0)

/--
No concrete Euclidean engine witness exists in the corrected Step00 graph,
because `lexRank` strictly decreases along every real edge.
-/
theorem no_concreteEuclideanEngineWitness {A M0 : ℕ} :
    ¬ ConcreteEuclideanEngineWitness A M0 := by
  intro W
  exact no_concrete_legalCycle_by_lexRank
    (A := A) (M0 := M0) W.cycle

/--
A single same-key collision inside a no-energy stable universe already builds a
concrete Euclidean engine witness.

This is the precise formal version of:

  without energy and without seam breaks, holding two identified genealogies in
  one ledger slot forces geometric support; geometric support is return or
  mutual nesting; either one is a legal cycle.

The `ImpossiblePayment` branch appears only because the older nested resolver
has that historical alternative; it is immediately eliminated by
`impossiblePayment_false`.
-/
theorem stableNoEnergy_collision_builds_engine {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoEnergyStableUniverse proj)
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hne : F₁ ≠ F₂)
    (hAdm₁ : ExtendedFlowAdmissible F₁)
    (hAdm₂ : ExtendedFlowAdmissible F₂)
    (hKey : proj.keyFlow F₁ = proj.keyFlow F₂) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hNested : NestedUniverseResolutionAlternative F₁ F₂ :=
    noEnergyStableUniverse_resolves_nested (proj := proj) H
      F₁ F₂ hne hAdm₁ hAdm₂ hKey
  rcases hNested with hReturn | hRest
  · exact ⟨extendedFlowReturnCertificate_forces_legalCycle hReturn⟩
  · rcases hRest with hMutual | hPay
    · exact ⟨mutuallyNestedUniverses_forces_legalCycle hMutual⟩
    · exact False.elim (impossiblePayment_false hPay)

/--
Since such an engine witness is impossible, a same-key collision cannot exist in
a no-energy stable universe.
-/
theorem no_stableNoEnergy_sameKey_collision {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoEnergyStableUniverse proj)
    {F₁ F₂ : ExtendedProperGeneratedFlow A M0}
    (hne : F₁ ≠ F₂)
    (hAdm₁ : ExtendedFlowAdmissible F₁)
    (hAdm₂ : ExtendedFlowAdmissible F₂)
    (hKey : proj.keyFlow F₁ = proj.keyFlow F₂) : False := by
  exact no_concreteEuclideanEngineWitness
    (stableNoEnergy_collision_builds_engine
      (proj := proj) H hne hAdm₁ hAdm₂ hKey)

/-#############################################################################
  §3. Infinite generated-flow load forces the forbidden engine
#############################################################################-/

/--
An infinite generated-flow family, together with a finite stable ledger key,
forces a same-key collision; in a no-energy stable universe that collision is a
concrete Euclidean engine.
-/
theorem infiniteFlows_in_stableNoEnergy_build_engine {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoEnergyStableUniverse proj)
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕) :
    ∃ F₁ F₂ : ExtendedProperGeneratedFlow A M0,
      ExtendedFlowSameKeyCollision proj 𝓕 F₁ F₂ ∧
      ConcreteEuclideanEngineWitness A M0 := by
  rcases infinite_extended_flows_force_key_collision
      (A := A) (M0 := M0) proj h𝓕 with ⟨F₁, F₂, hCol⟩
  have hEngine : ConcreteEuclideanEngineWitness A M0 :=
    stableNoEnergy_collision_builds_engine
      (proj := proj) H
      hCol.distinct hCol.left_admissible hCol.right_admissible hCol.same_key
  exact ⟨F₁, F₂, hCol, hEngine⟩

/--
The same statement as contradiction: a no-energy stable finite ledger cannot
absorb an infinite generated-flow load.
-/
theorem infiniteFlows_impossible_in_stableNoEnergy {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoEnergyStableUniverse proj)
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕) : False := by
  rcases infiniteFlows_in_stableNoEnergy_build_engine
      (proj := proj) H h𝓕 with ⟨_F₁, _F₂, _hCol, hEngine⟩
  exact no_concreteEuclideanEngineWitness hEngine

/--
Readable corollary: to close a finite-twin universe under stable no-energy
rules, one must construct a forbidden engine.

The theorem is intentionally local: it starts from an already generated infinite
family.  The earlier source-side patches prove that such a family is generated
from a last-twin bound.  This local theorem isolates the engine extraction.
-/
theorem finiteLoadStableTheory_requires_engine {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (H : NoEnergyStableUniverse proj)
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)}
    (h𝓕 : InfiniteExtendedGeneratedFlowFamily A M0 𝓕) :
    ∃ W : ConcreteEuclideanEngineWitness A M0, True := by
  rcases infiniteFlows_in_stableNoEnergy_build_engine
      (proj := proj) H h𝓕 with ⟨_F₁, _F₂, _hCol, hEngine⟩
  exact ⟨hEngine, trivial⟩

/-#############################################################################
  §4. Stable no-engine theory as an impossible finite-twin theory
#############################################################################-/

/--
A named proposition for the phrase "there is a stable no-engine Step00 theory".
-/
abbrev StableNoEngineStep00TheoryExists : Prop :=
  ∃ A : ℕ, Nonempty (StableNoEngineStep00Theory A)

/--
If such a stable no-engine theory exists, then lower twin centres are infinite.
-/
theorem twinLowersInfinite_of_stableNoEngineTheoryExists
    (H : StableNoEngineStep00TheoryExists) : TwinLowers.Infinite := by
  rcases H with ⟨A, ⟨T⟩⟩
  exact twinLowersInfinite_of_stableNoEngineTheory (A := A) T

/--
Thus a stable no-engine Step00 theory cannot coexist with the finite-twin
hypothesis.
-/
theorem no_finiteTwin_stableNoEngineTheory
    (H : StableNoEngineStep00TheoryExists)
    (hFiniteTwins : ¬ TwinLowers.Infinite) : False :=
  hFiniteTwins (twinLowersInfinite_of_stableNoEngineTheoryExists H)

/-#############################################################################
  §5. Audit residue
#############################################################################-/

/--
Audit phrase, as a proposition: proving a stable finite-twin universe without
energy/seam/compression/mixing support forces construction of a concrete
Euclidean engine.  Since such engines are impossible by `lexRank`, the stable
finite-twin theory is internally inconsistent.
-/
abbrev ProvingStableFiniteTwinTheoryBuildsPerpetualEngine : Prop :=
  ∀ {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)},
    NoEnergyStableUniverse proj →
    InfiniteExtendedGeneratedFlowFamily A M0 𝓕 →
      ∃ W : ConcreteEuclideanEngineWitness A M0, True

/-- The audit phrase is realised by the finite-load engine extraction theorem. -/
theorem provingStableFiniteTwinTheoryBuildsPerpetualEngine :
    ProvingStableFiniteTwinTheoryBuildsPerpetualEngine := by
  intro A M0 proj 𝓕 hStable hFlows
  exact finiteLoadStableTheory_requires_engine
    (proj := proj) hStable hFlows

/--
The stronger, fully forbidden form: the same attempted stable explanation is
impossible because the engine it builds is disallowed.
-/
abbrev StableFiniteTwinTheoryIsImpossible : Prop :=
  ∀ {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    {𝓕 : Set (ExtendedProperGeneratedFlow A M0)},
    NoEnergyStableUniverse proj →
    InfiniteExtendedGeneratedFlowFamily A M0 𝓕 → False

/-- The impossible form follows immediately from `lexRank`. -/
theorem stableFiniteTwinTheoryIsImpossible :
    StableFiniteTwinTheoryIsImpossible := by
  intro A M0 proj 𝓕 hStable hFlows
  exact infiniteFlows_impossible_in_stableNoEnergy
    (proj := proj) hStable hFlows

/-! Machine honesty of the stable-no-engine form -/

/-- "A stable no-engine theory exists" ⟺ old node (full equivalence:
    the diagnostic fields noStrictCompression/noMixing are recoverable from the resolver). -/
theorem stableNoEngineTheoryExists_iff_lastStep00Obligation :
    StableNoEngineStep00TheoryExists ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, ⟨T⟩⟩
    exact (noEnergyStableUniverseLastStep00Obligation_iff_lastStep00Obligation).mp
      ⟨A, T.projOf, T.stableNoEnergy⟩
  · rintro ⟨A, projOf, h⟩
    refine ⟨A, ⟨⟨projOf,
      fun M0 => (noEnergyStableUniverse_iff_resolves (projOf M0)).mpr (h M0),
      fun M0 => ((compressionAudit_iff_resolves (projOf M0)).mpr (h M0)).2,
      fun M0 F₁ F₂ hMix => ?_⟩⟩⟩
    obtain ⟨⟨hne, hAdm₁, hAdm₂, hkey⟩, -, -⟩ :=
      informationMixingWithoutEngine_iff_mixingCollision.mp hMix
    exact no_extendedFlowResolutionAlternative A M0
      (h M0 F₁ F₂ hne hAdm₁ hAdm₂ hkey)

/-- The stable theory at each scale M0 presents a twin above M0 (detector). -/
theorem twin_above_of_stableNoEngineTheory {A : ℕ}
    (T : StableNoEngineStep00Theory A) (M0 : ℕ) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_noEnergyStableUniverse (T.projOf M0) (T.stableNoEnergy M0)

/-#############################################################################
  DUAL AUDIT: NO REFUTATION WITHOUT AN ENGINE (brick:
  dual_no_refutation_without_engine).
  The dual slogan: a local attempt to REFUTE a stable no-engine
  theory by a same-key collision itself builds a forbidden engine. NOT metamathematics
  (not independence) — an object-level fact of the architecture. Fixes: data-structures
  attempt → impossibility in the form `→ False`. Below — the brick + machine
  honesty: attempt is empty DIRECTLY via seam-honesty (stable packs
  "there are no collisions" together with a collision) — the duality = surfaced ex-falso.
#############################################################################-/

/-#############################################################################
  §1. A local same-key refutation attempt
#############################################################################-/

/--
A local attempt to refute a stable no-engine ledger theory.

It consists of exactly the data one would naturally use to attack the theory:
two different admissible generated genealogies which the finite ledger projection
identifies by the same key.

The field `stable` is important: without the no-energy/no-seam stability
principle, a same-key collision can merely be a fake collision produced by a
bad projection.  Under stability, the already proved resolver says that the
collision must be geometrically supported, hence it builds an engine.
-/
structure LocalStableRefutationAttempt {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) where
  stable : NoEnergyStableUniverse proj
  F₁ : ExtendedProperGeneratedFlow A M0
  F₂ : ExtendedProperGeneratedFlow A M0
  distinct : F₁ ≠ F₂
  left_admissible : ExtendedFlowAdmissible F₁
  right_admissible : ExtendedFlowAdmissible F₂
  same_key : proj.keyFlow F₁ = proj.keyFlow F₂

/--
A local stable refutation attempt is already a concrete Euclidean engine.

This is the formal version of:

  to refute the stable no-energy ledger by a real same-key collision, one must
  produce the forbidden return/cycle mechanism.
-/
theorem localStableRefutationAttempt_builds_engine {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (R : LocalStableRefutationAttempt proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  exact stableNoEnergy_collision_builds_engine
    (proj := proj) R.stable
    R.distinct R.left_admissible R.right_admissible R.same_key

/--
Therefore no such local stable refutation attempt can exist in the corrected
Step00 graph, since the constructed engine is forbidden by `lexRank`.
-/
theorem no_localStableRefutationAttempt {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (R : LocalStableRefutationAttempt proj) : False :=
  no_concreteEuclideanEngineWitness
    (localStableRefutationAttempt_builds_engine (proj := proj) R)

/-#############################################################################
  §2. Refuting by infinite load is also engine construction
#############################################################################-/

/--
An infinite-load refutation attempt: a stable finite ledger is asked to absorb
an infinite generated-flow family.

The previous source-side patches are what produce such an infinite family from
a last-twin bound.  Here we isolate the local contradiction: finite key +
infinite family gives a same-key collision; stability turns that collision into
an engine.
-/
structure InfiniteLoadStableRefutationAttempt {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) where
  stable : NoEnergyStableUniverse proj
  𝓕 : Set (ExtendedProperGeneratedFlow A M0)
  infiniteFlows : InfiniteExtendedGeneratedFlowFamily A M0 𝓕

/--
An infinite-load refutation attempt contains a local same-key refutation attempt,
by pigeonhole over the finite semantic key.
-/
theorem infiniteLoadStableRefutationAttempt_to_local {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (R : InfiniteLoadStableRefutationAttempt proj) :
    ∃ L : LocalStableRefutationAttempt proj, True := by
  rcases infinite_extended_flows_force_key_collision
      (A := A) (M0 := M0) proj R.infiniteFlows with ⟨F₁, F₂, hCol⟩
  refine ⟨{ stable := R.stable
            F₁ := F₁
            F₂ := F₂
            distinct := hCol.distinct
            left_admissible := hCol.left_admissible
            right_admissible := hCol.right_admissible
            same_key := hCol.same_key }, trivial⟩

/--
Thus an infinite-load refutation attempt is also an engine construction.
-/
theorem infiniteLoadStableRefutationAttempt_builds_engine {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (R : InfiniteLoadStableRefutationAttempt proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  rcases infiniteLoadStableRefutationAttempt_to_local
      (proj := proj) R with ⟨L, _⟩
  exact localStableRefutationAttempt_builds_engine (proj := proj) L

/--
And therefore the infinite-load refutation attempt is impossible.
-/
theorem no_infiniteLoadStableRefutationAttempt {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (R : InfiniteLoadStableRefutationAttempt proj) : False :=
  no_concreteEuclideanEngineWitness
    (infiniteLoadStableRefutationAttempt_builds_engine (proj := proj) R)

/-#############################################################################
  §3. The exact dual slogan
#############################################################################-/

/--
Predicate-level slogan: every local refutation of a stable no-engine ledger by a
same-key collision is a perpetual-engine construction.
-/
abbrev RefutingStableTheoryBuildsPerpetualEngine : Prop :=
  ∀ {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0},
    LocalStableRefutationAttempt proj →
      ConcreteEuclideanEngineWitness A M0

/-- The slogan is realised by `localStableRefutationAttempt_builds_engine`. -/
theorem refutingStableTheoryBuildsPerpetualEngine :
    RefutingStableTheoryBuildsPerpetualEngine := by
  intro A M0 proj R
  exact localStableRefutationAttempt_builds_engine (proj := proj) R

/--
Forbidden dual form: since concrete Euclidean engines are impossible, no local
same-key refutation of a stable no-engine ledger is available.
-/
abbrev RefutingStableTheoryWithoutEngineIsImpossible : Prop :=
  ∀ {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0},
    LocalStableRefutationAttempt proj → False

/-- The forbidden dual form follows immediately from `lexRank`. -/
theorem refutingStableTheoryWithoutEngineIsImpossible :
    RefutingStableTheoryWithoutEngineIsImpossible := by
  intro A M0 proj
  exact no_localStableRefutationAttempt (proj := proj)

/--
Infinite-load version of the same dual audit: attempting to refute the stable
ledger by forcing it to absorb infinitely many generated genealogies also builds
the forbidden engine.
-/
abbrev InfiniteLoadRefutationBuildsPerpetualEngine : Prop :=
  ∀ {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0},
    InfiniteLoadStableRefutationAttempt proj →
      ConcreteEuclideanEngineWitness A M0

/-- Realisation of the infinite-load dual slogan. -/
theorem infiniteLoadRefutationBuildsPerpetualEngine :
    InfiniteLoadRefutationBuildsPerpetualEngine := by
  intro A M0 proj R
  exact infiniteLoadStableRefutationAttempt_builds_engine (proj := proj) R

/--
Therefore an infinite-load refutation without engine is also impossible.
-/
abbrev InfiniteLoadRefutationWithoutEngineIsImpossible : Prop :=
  ∀ {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0},
    InfiniteLoadStableRefutationAttempt proj → False

/-- Realisation of the infinite-load impossible form. -/
theorem infiniteLoadRefutationWithoutEngineIsImpossible :
    InfiniteLoadRefutationWithoutEngineIsImpossible := by
  intro A M0 proj
  exact no_infiniteLoadStableRefutationAttempt (proj := proj)

/-#############################################################################
  §4. Audit residue
#############################################################################-/

/--
Audit phrase as a proposition:

  In this Step00 architecture, proving the stable finite theory builds a
  perpetual engine; refuting it internally by a real same-key collision also
  builds the same forbidden object.  The obstruction is not a Lean/metalogical
  incompleteness claim.  It is the object-level fact that any genuine local
  attack on the stable ledger must pass through a return/cycle certificate.
-/
abbrev ProvingOrRefutingStableTheoryRequiresEngine : Prop :=
  ProvingStableFiniteTwinTheoryBuildsPerpetualEngine ∧
  RefutingStableTheoryBuildsPerpetualEngine ∧
  InfiniteLoadRefutationBuildsPerpetualEngine

/-- The combined audit slogan is realised by the previous theorems. -/
theorem provingOrRefutingStableTheoryRequiresEngine :
    ProvingOrRefutingStableTheoryRequiresEngine := by
  exact ⟨provingStableFiniteTwinTheoryBuildsPerpetualEngine,
         refutingStableTheoryBuildsPerpetualEngine,
         infiniteLoadRefutationBuildsPerpetualEngine⟩

/--
The fully forbidden form: all those engine-mediated routes are impossible in the
corrected concrete Step00 graph, because `lexRank` rules out legal cycles.
-/
abbrev NoProofOrRefutationWithoutForbiddenEngine : Prop :=
  StableFiniteTwinTheoryIsImpossible ∧
  RefutingStableTheoryWithoutEngineIsImpossible ∧
  InfiniteLoadRefutationWithoutEngineIsImpossible

/-- The forbidden combined form. -/
theorem noProofOrRefutationWithoutForbiddenEngine :
    NoProofOrRefutationWithoutForbiddenEngine := by
  exact ⟨stableFiniteTwinTheoryIsImpossible,
         refutingStableTheoryWithoutEngineIsImpossible,
         infiniteLoadRefutationWithoutEngineIsImpossible⟩

/-! Machine honesty of the dual form -/

/-- DIRECT emptiness of the attempt: attempt packs "there are no collisions" (stable ⟹ resolver)
    together with a collision — a contradiction without a bypass through an engine. The dual
    slogan = an explicitly surfaced ex-falso; both routes are the same fact. -/
theorem localStableRefutationAttempt_empty {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (R : LocalStableRefutationAttempt proj) : False :=
  seamAudit_forces_no_collision R.stable.2.1 R.stable.2.2 R.F₁ R.F₂
    ⟨R.distinct, R.left_admissible, R.right_admissible, R.same_key⟩

/-- Direct emptiness of the infinite-load attempt (via the resolver, without an engine). -/
theorem infiniteLoadStableRefutationAttempt_empty {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (R : InfiniteLoadStableRefutationAttempt proj) : False :=
  infinite_extended_flows_impossible_with_resolution
    (A := A) (M0 := M0) proj R.infiniteFlows
    ((noEnergyStableUniverse_iff_resolves proj).mp R.stable)

/-#############################################################################
  NO INTERNAL DECISION WITHOUT AN ENGINE (brick:
  no_internal_decision_without_engine_theorem).
  The audit conclusion package: inside the architecture a stable finite-twin branch
  can be neither proven nor refuted by the permitted local mechanisms
  without building an engine (all engines are burnt by lexRank). The brick itself honestly
  marks: this is NOT metamathematical independence (§4). Fixes:
  SomeConcreteEuclideanEngine → ∃-Prop (data A,M0 under ¬); proof-attempt
  impossibility → `→ False`. Below — the brick + machine honesty: "prove"
  and "refute" carry the SAME fields; all branches are empty directly.
#############################################################################-/

/-#############################################################################
  §1. Stable proof attempts and the common engine target
#############################################################################-/

/--
A proof attempt for the stable finite-twin branch, in the precise object-level
sense used by the audit.

It consists of a no-energy stable ledger together with an infinite generated-flow
load.  The earlier patches prove that such data build a concrete Euclidean
engine witness.
-/
structure InternalStableProofAttempt {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) where
  stable : NoEnergyStableUniverse proj
  𝓕 : Set (ExtendedProperGeneratedFlow A M0)
  infiniteFlows : InfiniteExtendedGeneratedFlowFamily A M0 𝓕

/--
A scale-indexed concrete Euclidean engine witness, hiding only the parameters
`A` and `M0`.
-/
def SomeConcreteEuclideanEngine : Prop :=
  ∃ A M0 : ℕ, ConcreteEuclideanEngineWitness A M0

/--
There is no concrete Euclidean engine at any scale in the corrected Step00 graph.
-/
theorem no_someConcreteEuclideanEngine :
    ¬ SomeConcreteEuclideanEngine := by
  rintro ⟨A, M0, W⟩
  exact no_concreteEuclideanEngineWitness W

/--
Every internal stable proof attempt builds a concrete Euclidean engine.
-/
theorem internalStableProofAttempt_builds_engine {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (P : InternalStableProofAttempt proj) :
    SomeConcreteEuclideanEngine := by
  rcases finiteLoadStableTheory_requires_engine
      (proj := proj) P.stable P.infiniteFlows with ⟨W, _⟩
  exact ⟨A, M0, W⟩

/--
Therefore no internal stable proof attempt exists without constructing the
forbidden engine.
-/
theorem no_internalStableProofAttempt {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (P : InternalStableProofAttempt proj) : False :=
  no_someConcreteEuclideanEngine
    (internalStableProofAttempt_builds_engine (proj := proj) P)

/-#############################################################################
  §2. Unified internal decision attempts
#############################################################################-/

/--
The three object-level ways the audited architecture can try to decide the
stable finite-twin branch:

* `prove`: present a stable ledger plus an infinite generated-flow load;
* `refuteLocal`: present a real local same-key collision against the stable
  ledger;
* `refuteInfinite`: present an infinite-load refutation against the stable
  ledger.

The previous patches showed that each of these constructs the same forbidden
object: a concrete Euclidean engine witness.
-/
inductive InternalStableDecisionAttempt : Prop where
  | prove {A M0 : ℕ}
      {proj : SemanticExtendedFlowLedgerProjection A M0}
      (P : InternalStableProofAttempt proj) :
      InternalStableDecisionAttempt
  | refuteLocal {A M0 : ℕ}
      {proj : SemanticExtendedFlowLedgerProjection A M0}
      (R : LocalStableRefutationAttempt proj) :
      InternalStableDecisionAttempt
  | refuteInfinite {A M0 : ℕ}
      {proj : SemanticExtendedFlowLedgerProjection A M0}
      (R : InfiniteLoadStableRefutationAttempt proj) :
      InternalStableDecisionAttempt

/--
Any internal decision attempt builds a concrete Euclidean engine.
-/
theorem internalStableDecisionAttempt_builds_engine
    (D : InternalStableDecisionAttempt) :
    SomeConcreteEuclideanEngine := by
  cases D with
  | prove P =>
      exact internalStableProofAttempt_builds_engine P
  | refuteLocal R =>
      exact ⟨_, _, localStableRefutationAttempt_builds_engine R⟩
  | refuteInfinite R =>
      exact ⟨_, _, infiniteLoadStableRefutationAttempt_builds_engine R⟩

/--
Consequently, no internal decision attempt is available in the corrected
no-engine Step00 architecture.
-/
theorem no_internalStableDecisionAttempt :
    ¬ InternalStableDecisionAttempt := by
  intro D
  exact no_someConcreteEuclideanEngine
    (internalStableDecisionAttempt_builds_engine D)

/-#############################################################################
  §3. The exact theorem: neither prove nor refute inside this architecture
#############################################################################-/

/--
Object-level slogan as a proposition:

  Inside this Step00 architecture, the stable finite-twin branch cannot be
  proved or refuted by the audited local mechanisms without constructing a
  forbidden Euclidean engine.
-/
abbrev NoInternalDecisionWithoutForbiddenEngine : Prop :=
  ¬ InternalStableDecisionAttempt

/--
The formal theorem requested by the audit discussion.

This says “neither prove nor refute” only in the internal architectural sense:
every allowed proof/refutation route first builds a concrete engine, and every
such engine is ruled out by the already proved `lexRank` acyclicity theorem.
-/
theorem noInternalDecisionWithoutForbiddenEngine :
    NoInternalDecisionWithoutForbiddenEngine := by
  exact no_internalStableDecisionAttempt

/--
Equivalent named version using the earlier dual audit package.
-/
abbrev EarlierDualAuditNoDecision : Prop :=
  NoProofOrRefutationWithoutForbiddenEngine

/--
The earlier dual audit package also realises the same “no internal decision”
claim: proof, local refutation, and infinite-load refutation are all forbidden
unless a concrete engine is constructed.
-/
theorem earlierDualAuditNoDecision : EarlierDualAuditNoDecision := by
  exact noProofOrRefutationWithoutForbiddenEngine

/-#############################################################################
  §4. Explicit boundary: not a global independence theorem
#############################################################################-/

/--
A marker proposition recording the scope of the result.

It is intentionally just `True`: the mathematical content is in
`noInternalDecisionWithoutForbiddenEngine`.  This marker prevents the audit text
from being read as a Gödel-style independence claim for the ordinary twin-prime
statement.  Such a claim would require a separate formal proof system and
metatheory, which are not part of the Step00 graph.
-/
abbrev ThisIsObjectLevelNotMetamathematicalIndependence : Prop := True

theorem thisIsObjectLevelNotMetamathematicalIndependence :
    ThisIsObjectLevelNotMetamathematicalIndependence := by
  trivial

/-! Machine honesty of the no-decision form -/

/-- "Proof attempt" carries LITERALLY the same fields as the infinite-load "refutation
    attempt" (stable + 𝓕 + infiniteFlows): the dichotomy "prove/refute"
    is nominal here — both are empty directly via seam-honesty. -/
theorem internalStableProofAttempt_empty {A M0 : ℕ}
    {proj : SemanticExtendedFlowLedgerProjection A M0}
    (P : InternalStableProofAttempt proj) : False :=
  infiniteLoadStableRefutationAttempt_empty
    ⟨P.stable, P.𝓕, P.infiniteFlows⟩

/-- Direct emptiness of the decision attempt (without a bypass through an engine): all three
    branches are empty via seam-honesty — no-decision = surfaced ex-falso. -/
theorem internalStableDecisionAttempt_empty_directly :
    InternalStableDecisionAttempt → False := by
  intro D
  cases D with
  | prove P => exact internalStableProofAttempt_empty P
  | refuteLocal R => exact localStableRefutationAttempt_empty R
  | refuteInfinite R => exact infiniteLoadStableRefutationAttempt_empty R

/-#############################################################################
  ARCHITECTURE-RELATIVE INDEPENDENCE (brick:
  architecture_relative_independence).
  The strongest honest form: if the proof/refutation certificates of an external
  system factorize through audited Step00-attempts, then the system has
  neither (both build a forbidden engine). The brick itself honestly
  limits the scope (§3-§4: NOT Gödel independence for ZFC/PA/Lean).
  Below — the brick + machine honesty: a translator into the empty type of attempts
  exists ⟺ the domain is empty — the strength of the claim is entirely in the premise of the bridge.
#############################################################################-/

/-#############################################################################
  §1. Abstract proof/refutation interfaces that factor through Step00
#############################################################################-/

/--
A formal decision interface for the finite-twin branch, relative to this Step00
architecture.

`Proof` and `Refutation` are *not* arbitrary mathematical proofs.  They are the
proof/refutation certificates of whatever external system one wants to study,
under the explicit assumption that each such certificate can be translated into
an audited `InternalStableDecisionAttempt`.

Thus the fields `proofToInternal` and `refutationToInternal` are the whole
bridge from the external proof system to the Step00 graph.  Without such a
bridge, no independence conclusion about the external system is claimed.
-/
structure Step00DecisionInterface where
  Proof : Type
  Refutation : Type
  proofToInternal : Proof → InternalStableDecisionAttempt
  refutationToInternal : Refutation → InternalStableDecisionAttempt

/--
Every relative proof certificate constructs the forbidden concrete engine.
-/
theorem step00Proof_builds_engine
    (S : Step00DecisionInterface) (p : S.Proof) :
    SomeConcreteEuclideanEngine := by
  exact internalStableDecisionAttempt_builds_engine (S.proofToInternal p)

/--
Every relative refutation certificate constructs the forbidden concrete engine.
-/
theorem step00Refutation_builds_engine
    (S : Step00DecisionInterface) (r : S.Refutation) :
    SomeConcreteEuclideanEngine := by
  exact internalStableDecisionAttempt_builds_engine (S.refutationToInternal r)

/--
Therefore the relative proof type is empty.
-/
theorem no_step00RelativeProof
    (S : Step00DecisionInterface) :
    IsEmpty S.Proof := by
  refine ⟨?_⟩
  intro p
  exact no_someConcreteEuclideanEngine (step00Proof_builds_engine S p)

/--
Therefore the relative refutation type is empty.
-/
theorem no_step00RelativeRefutation
    (S : Step00DecisionInterface) :
    IsEmpty S.Refutation := by
  refine ⟨?_⟩
  intro r
  exact no_someConcreteEuclideanEngine (step00Refutation_builds_engine S r)

/-#############################################################################
  §2. Relative independence statement
#############################################################################-/

/--
Architecture-relative independence of the finite-twin branch for an interface
`S`: there is neither an `S.Proof` nor an `S.Refutation`.
-/
abbrev ArchitectureRelativeIndependence
    (S : Step00DecisionInterface) : Prop :=
  IsEmpty S.Proof ∧ IsEmpty S.Refutation

/--
The formal relative-independence theorem.

If proof and refutation certificates of an external system factor through the
audited Step00 internal decision attempts, then the system has neither kind of
certificate.
-/
theorem architectureRelativeIndependence
    (S : Step00DecisionInterface) :
    ArchitectureRelativeIndependence S := by
  exact ⟨no_step00RelativeProof S, no_step00RelativeRefutation S⟩

/--
Equivalent proposition phrased as “no internal proof or refutation”.
-/
abbrev NoRelativeDecision
    (S : Step00DecisionInterface) : Prop :=
  (¬ Nonempty S.Proof) ∧ (¬ Nonempty S.Refutation)

/--
The same result with `Nonempty` rather than `IsEmpty`.
-/
theorem noRelativeDecision
    (S : Step00DecisionInterface) :
    NoRelativeDecision S := by
  constructor
  · intro hp
    rcases hp with ⟨p⟩
    exact no_someConcreteEuclideanEngine (step00Proof_builds_engine S p)
  · intro hr
    rcases hr with ⟨r⟩
    exact no_someConcreteEuclideanEngine (step00Refutation_builds_engine S r)

/-#############################################################################
  §3. What a genuine metamathematical independence theorem would require
#############################################################################-/

/--
A marker for an external proof theory.  This is intentionally only a structure of
interfaces, not a theorem about ZFC/PA/Lean/etc.

To turn the architecture-relative theorem into a true metamathematical
independence theorem for a concrete theory `T`, one would have to instantiate
this structure with actual proof codes and prove the two translation fields.
-/
structure ExternalProofTheory where
  Sentence : Type
  proves : Sentence → Type
  refutes : Sentence → Type

/--
A concrete statement inside an external proof theory is Step00-mediated if both
proofs and refutations of that statement translate into internal Step00 decision
attempts.
-/
structure Step00MediatedStatement
    (T : ExternalProofTheory) (φ : T.Sentence) where
  proofToInternal : T.proves φ → InternalStableDecisionAttempt
  refutationToInternal : T.refutes φ → InternalStableDecisionAttempt

/--
The induced Step00 decision interface for a mediated external statement.
-/
def Step00MediatedStatement.toInterface
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    Step00DecisionInterface where
  Proof := T.proves φ
  Refutation := T.refutes φ
  proofToInternal := M.proofToInternal
  refutationToInternal := M.refutationToInternal

/--
A mediated external statement is independent relative to the Step00 architecture.
-/
theorem mediatedStatement_relativeIndependence
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    ArchitectureRelativeIndependence M.toInterface := by
  exact architectureRelativeIndependence M.toInterface

/--
Same result, explicitly: no proof and no refutation codes exist for a statement
whose proof/refutation mechanisms are Step00-mediated.
-/
theorem mediatedStatement_noProof_noRefutation
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    (IsEmpty (T.proves φ)) ∧ (IsEmpty (T.refutes φ)) := by
  exact mediatedStatement_relativeIndependence M

/-#############################################################################
  §4. Scope guard
#############################################################################-/

/--
Scope marker: this file proves only architecture-relative independence.

It does not assert absolute independence of the twin-prime conjecture from any
standard foundational theory.  The only claim is conditional: once proofs and
refutations are forced to pass through the audited Step00 no-engine decision
interface, both sides are impossible because both construct a forbidden engine.
-/
abbrev ThisIsOnlyArchitectureRelativeIndependence : Prop := True

theorem thisIsOnlyArchitectureRelativeIndependence :
    ThisIsOnlyArchitectureRelativeIndependence := by
  trivial

/-! Machine honesty of the relative-independence form -/

/-- HONESTY: mediatability = emptiness. A translator into the (empty) type of
    deciding attempts exists ⟺ the domain is empty. The hypothesis "certificates
    factor through Step00" already CONTAINS the conclusion "there are no
    certificates": the bridge is precisely emptiness. Relative independence is
    correct, but its strength lies entirely in the premise. -/
theorem translation_to_decisionAttempt_iff_empty (P : Type) :
    Nonempty (P → InternalStableDecisionAttempt) ↔ IsEmpty P := by
  constructor
  · rintro ⟨f⟩
    exact ⟨fun p => (internalStableDecisionAttempt_empty_directly (f p)).elim⟩
  · intro hEmpty
    exact ⟨fun p => (hEmpty.false p).elim⟩

/-#############################################################################
  EXTERNAL UNIVERSE PRINCIPLE / SELF-CERTIFYING ENGINE (brick:
  external_universe_self_engine_contradiction).
  Three "external principles" (strict / no-energy / finite-energy obligations)
  as inputs yield twins; their internalization as Step00 attempts builds a
  forbidden engine — "the engine proves itself" = contradiction.
  Fixes: both self-proof structures declared : Prop. Below — the brick +
  machine honesty: BoundaryCrossingSelfProof P ⟺ P ∧ ¬P (tautological
  prohibition for ANY P); external-only ⟺ P itself; plus the missing link —
  strict obligation ⟺ the old node.
#############################################################################-/

/-#############################################################################
  §1. External universe-generating principles
#############################################################################-/

/--
The strict external Step00 principle.

This is exactly the return-path version of the last Step00 obligation.  It is
called “external” here because the previous no-internal-decision patches show
that it cannot be manufactured by the stable no-engine decision interface
without constructing the forbidden engine.
-/
abbrev ExternalUniverseGeneratingPrinciple : Prop :=
  TheStrictLastStep00Obligation

/--
As an external input, the strict universe-generating principle produces the
Step00 conclusion: infinitude of lower twin centres.
-/
theorem externalUniverseGeneratingPrinciple_generates_twins
    (H : ExternalUniverseGeneratingPrinciple) : TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation H

/--
The no-energy version of the external universe principle.  This is the form in
which the system is asked to hold the universe together without a payment
channel: same-key collisions must be geometrically supported, not paid for.
-/
abbrev NoEnergyUniverseGeneratingPrinciple : Prop :=
  TheNoEnergyStableUniverseLastStep00Obligation

/--
As an external input, the no-energy stable universe principle also generates
infinitely many lower twin centres.
-/
theorem noEnergyUniverseGeneratingPrinciple_generates_twins
    (H : NoEnergyUniverseGeneratingPrinciple) : TwinLowers.Infinite :=
  twinLowersInfinite_of_noEnergyStableUniverseLastStep00Obligation H

/--
The finite-energy version of the external universe principle.  This is the
version where every non-returning absorption must consume a token from a finite
energy ledger.
-/
abbrev FiniteEnergyUniverseGeneratingPrinciple : Prop :=
  EnergyLastStep00Obligation

/--
As an external input, the finite-energy principle also generates infinitely many
lower twin centres.
-/
theorem finiteEnergyUniverseGeneratingPrinciple_generates_twins
    (H : FiniteEnergyUniverseGeneratingPrinciple) : TwinLowers.Infinite :=
  twinLowersInfinite_of_energyLastStep00Obligation H

/-#############################################################################
  §2. Self-proof across the boundary of the system
#############################################################################-/

/--
A boundary-crossing self-proof attempt for an external principle.

The field `external` is a principle treated as an outside input.  The field
`internalize` says that this same principle can be converted into an internal
Step00 decision attempt.  The latter is exactly what the previous audit forbids:
any internal decision attempt builds a concrete Euclidean engine.
-/
structure BoundaryCrossingSelfProof
    (P : Prop) : Prop where
  external : P
  internalize : P → InternalStableDecisionAttempt

/--
Any boundary-crossing self-proof attempt builds the forbidden concrete engine.
-/
theorem boundaryCrossingSelfProof_builds_engine
    {P : Prop} (B : BoundaryCrossingSelfProof P) :
    SomeConcreteEuclideanEngine :=
  internalStableDecisionAttempt_builds_engine (B.internalize B.external)

/--
Therefore no boundary-crossing self-proof attempt exists.

This is the formal version of:

  if the external universe-generating principle tries to prove itself from
  inside the no-engine Step00 system, it creates the forbidden engine.
-/
theorem no_boundaryCrossingSelfProof
    {P : Prop} : ¬ BoundaryCrossingSelfProof P := by
  intro B
  exact no_someConcreteEuclideanEngine
    (boundaryCrossingSelfProof_builds_engine B)

/-- The strict external Step00 principle cannot be internally self-certified. -/
theorem no_strictExternalUniverse_selfProof :
    ¬ BoundaryCrossingSelfProof ExternalUniverseGeneratingPrinciple :=
  no_boundaryCrossingSelfProof

/-- The no-energy external universe principle cannot be internally self-certified. -/
theorem no_noEnergyUniverse_selfProof :
    ¬ BoundaryCrossingSelfProof NoEnergyUniverseGeneratingPrinciple :=
  no_boundaryCrossingSelfProof

/-- The finite-energy external universe principle cannot be internally self-certified. -/
theorem no_finiteEnergyUniverse_selfProof :
    ¬ BoundaryCrossingSelfProof FiniteEnergyUniverseGeneratingPrinciple :=
  no_boundaryCrossingSelfProof

/-#############################################################################
  §3. The self-certifying perpetual engine contradiction
#############################################################################-/

/--
A self-certifying perpetual engine is, in this architecture, an internal decision
attempt that certifies its own engine.  It is deliberately not given any extra
power: the engine is extracted by the already proved theorem
`internalStableDecisionAttempt_builds_engine`.
-/
structure SelfCertifyingPerpetualEngine : Prop where
  attempt : InternalStableDecisionAttempt

/-- A self-certifying perpetual engine builds the concrete forbidden engine. -/
theorem selfCertifyingPerpetualEngine_builds_engine
    (E : SelfCertifyingPerpetualEngine) : SomeConcreteEuclideanEngine :=
  internalStableDecisionAttempt_builds_engine E.attempt

/--
No self-certifying perpetual engine exists.

This is the precise formal reading of:

  “the perpetual engine proves itself” collapses into contradiction,
  because the proof itself is the forbidden engine witness.
-/
theorem no_selfCertifyingPerpetualEngine :
    ¬ SelfCertifyingPerpetualEngine := by
  intro E
  exact no_someConcreteEuclideanEngine
    (selfCertifyingPerpetualEngine_builds_engine E)

/-- If one nevertheless assumes such a self-proof, contradiction follows. -/
theorem selfCertifyingPerpetualEngine_contradiction
    (E : SelfCertifyingPerpetualEngine) : False :=
  no_selfCertifyingPerpetualEngine E

/-#############################################################################
  §4. “The engine can prove itself only outside the system, but lacks energy”
#############################################################################-/

/--
An outside Step00 principle closes the universe only as an external input.  The
moment a map back into the internal decision interface is supplied, it becomes a
forbidden engine construction.
-/
abbrev ExternalOnlyUniversePrinciple
    (P : Prop) : Prop :=
  P ∧ ¬ BoundaryCrossingSelfProof P

/-- The strict last principle is external-only relative to this architecture. -/
theorem strictUniversePrinciple_is_externalOnly
    (H : ExternalUniverseGeneratingPrinciple) :
    ExternalOnlyUniversePrinciple ExternalUniverseGeneratingPrinciple := by
  exact ⟨H, no_strictExternalUniverse_selfProof⟩

/-- The no-energy universe principle is external-only relative to this architecture. -/
theorem noEnergyUniversePrinciple_is_externalOnly
    (H : NoEnergyUniverseGeneratingPrinciple) :
    ExternalOnlyUniversePrinciple NoEnergyUniverseGeneratingPrinciple := by
  exact ⟨H, no_noEnergyUniverse_selfProof⟩

/-- The finite-energy universe principle is external-only relative to this architecture. -/
theorem finiteEnergyUniversePrinciple_is_externalOnly
    (H : FiniteEnergyUniverseGeneratingPrinciple) :
    ExternalOnlyUniversePrinciple FiniteEnergyUniverseGeneratingPrinciple := by
  exact ⟨H, no_finiteEnergyUniverse_selfProof⟩

/--
A no-energy self-support attempt: the system tries to use a no-energy universe
principle and also internalise it as its own proof.  This is exactly the case
where the universe is supposed to be held together without an energy/payment
channel.
-/
abbrev NoEnergySelfSupportAttempt : Prop :=
  BoundaryCrossingSelfProof NoEnergyUniverseGeneratingPrinciple

/-- No no-energy self-support attempt exists. -/
theorem no_noEnergySelfSupportAttempt :
    ¬ NoEnergySelfSupportAttempt :=
  no_noEnergyUniverse_selfProof

/--
If a no-energy self-support attempt is assumed, it builds the forbidden engine.
-/
theorem noEnergySelfSupportAttempt_builds_engine
    (B : NoEnergySelfSupportAttempt) : SomeConcreteEuclideanEngine :=
  boundaryCrossingSelfProof_builds_engine B

/--
And therefore a no-energy self-support attempt is contradictory.
-/
theorem noEnergySelfSupportAttempt_contradiction
    (B : NoEnergySelfSupportAttempt) : False :=
  no_noEnergySelfSupportAttempt B

/-#############################################################################
  §5. Final audit slogans as propositions
#############################################################################-/

/--
Slogan 1: an external universe-generating principle may generate the Step00
conclusion, but it is not internally self-certifying without a forbidden engine.
-/
abbrev ExternalPrincipleGeneratesButDoesNotSelfCertify : Prop :=
  (ExternalUniverseGeneratingPrinciple → TwinLowers.Infinite) ∧
  ¬ BoundaryCrossingSelfProof ExternalUniverseGeneratingPrinciple

/-- Realisation of slogan 1. -/
theorem externalPrincipleGeneratesButDoesNotSelfCertify :
    ExternalPrincipleGeneratesButDoesNotSelfCertify := by
  exact ⟨externalUniverseGeneratingPrinciple_generates_twins,
         no_strictExternalUniverse_selfProof⟩

/--
Slogan 2: the no-energy universe cannot prove its own stability from inside the
system.  If it tries, the proof is the forbidden engine.
-/
abbrev NoEnergyUniverseCannotSelfSupport : Prop :=
  ¬ NoEnergySelfSupportAttempt

/-- Realisation of slogan 2. -/
theorem noEnergyUniverseCannotSelfSupport :
    NoEnergyUniverseCannotSelfSupport :=
  no_noEnergySelfSupportAttempt

/--
Slogan 3: “the perpetual engine proves itself” is not a proof; in the audited
Step00 graph it is a contradiction.
-/
abbrev PerpetualEngineSelfProofIsContradiction : Prop :=
  ¬ SelfCertifyingPerpetualEngine

/-- Realisation of slogan 3. -/
theorem perpetualEngineSelfProofIsContradiction :
    PerpetualEngineSelfProofIsContradiction :=
  no_selfCertifyingPerpetualEngine

/-#############################################################################
  §6. Scope guard
#############################################################################-/

/--
Scope marker.  This is an object-level Step00 theorem, not a global statement
about all possible mathematical proof systems.  To turn it into a metatheorem
about a concrete theory, one still needs an explicit translation from that
external theory into `InternalStableDecisionAttempt`, as in
`Step00DecisionInterface`.
-/
abbrev ThisIsExternalPrincipleNotAbsoluteIndependence : Prop := True

theorem thisIsExternalPrincipleNotAbsoluteIndependence :
    ThisIsExternalPrincipleNotAbsoluteIndependence := by
  trivial

/-! Machine honesty of the external-universe form -/

/-- HONESTY: self-proof ⟺ `P ∧ ¬P`. Internalization into the empty type of
    attempts is exactly negation, hence "internal self-certification is
    forbidden" for ANY statement — including true ones. The load-bearing part of
    the slogans is only the generates_twins implications (already known). -/
theorem boundaryCrossingSelfProof_iff_and_not {P : Prop} :
    BoundaryCrossingSelfProof P ↔ (P ∧ ¬ P) := by
  constructor
  · intro B
    exact ⟨B.external,
      fun hp => internalStableDecisionAttempt_empty_directly (B.internalize hp)⟩
  · intro h
    exact (h.2 h.1).elim

/-- "External-only" adds nothing to P: the second conjunct is free. -/
theorem externalOnlyUniversePrinciple_iff {P : Prop} :
    ExternalOnlyUniversePrinciple P ↔ P := by
  constructor
  · exact fun h => h.1
  · intro hp
    exact ⟨hp, no_boundaryCrossingSelfProof⟩

/-- The missing link of the family of forms: strict resolver ⟺ old resolver. -/
theorem strictResolves_iff_resolves {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    StrictSemanticExtendedFlowLedgerCollisionResolves proj ↔
      SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · exact strictSemanticExtended_resolves_old
  · intro hOld F₁ F₂ hne h1 h2 hkey
    exact ((no_extendedFlowResolutionAlternative A M0)
      (hOld F₁ F₂ hne h1 h2 hkey)).elim

/-- Strict obligation ⟺ the old node (closes the family of equivalences). -/
theorem strictLastStep00Obligation_iff_lastStep00Obligation :
    TheStrictLastStep00Obligation ↔ TheLastStep00Obligation := by
  constructor
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 => (strictResolves_iff_resolves (projOf M0)).mp (h M0)⟩
  · rintro ⟨A, projOf, h⟩
    exact ⟨A, projOf, fun M0 => (strictResolves_iff_resolves (projOf M0)).mpr (h M0)⟩

/-#############################################################################
  MACHINE NARROWING OF THE NODE: THE A ≤ 4 BRANCH IS REFUTED (adversarial audit,
  probe agent; checked and integrated).
  The 5-adic chain c(k+1) = 5·c(k) + 1 (identity 6·(5x+1)−1 = 5·(6x+1),
  bigDivisor 5 > A) yields an INFINITE admissible family WITHOUT twin hypotheses
  for A ≤ 4, M0 = 1: purity is free (2 and 3 do not divide 6m±1), all
  post-audit patches are done honestly. Pigeonhole ⟹ no finite-key projection
  resolves ⟹ the A ≤ 4 branch of the node is dead; ∃A lives only in A ≥ 5. For
  A ≥ 5 the same trick requires clean starts with control of the peel targets —
  Dirichlet-class arithmetic, absent from the repo (and probably behind the red
  line): satisfiability of the node for A ≥ 5 remains genuinely open.
#############################################################################-/

/-- For `A ≤ 4` every center `m ≥ 1` is clean: the candidates are only 2 and 3,
    neither of which divides `6m ± 1`. -/
theorem clean_of_scale_le_four {A : ℕ} (hA : A ≤ 4) {m : ℕ} (hm : 1 ≤ m) :
    Clean A m := by
  intro q hq hqA hbad
  have h2 : 2 ≤ q := hq.two_le
  have h4 : q ≤ 4 := le_trans hqA hA
  interval_cases q
  · rcases hbad with h | h <;> omega
  · rcases hbad with h | h <;> omega
  · exact absurd hq (by norm_num)

/-- The 5-adic descent chain 1, 6, 31, 156, …: `c(k+1) = 5·c(k) + 1`. -/
def fiveAdicChain : ℕ → ℕ
  | 0 => 1
  | k + 1 => 5 * fiveAdicChain k + 1

theorem fiveAdicChain_pos : ∀ k, 1 ≤ fiveAdicChain k
  | 0 => le_refl 1
  | k + 1 => by show 1 ≤ 5 * fiveAdicChain k + 1; omega

theorem fiveAdicChain_strictMono : StrictMono fiveAdicChain :=
  strictMono_nat_of_lt_succ (fun k => by
    have := fiveAdicChain_pos k
    show fiveAdicChain k < 5 * fiveAdicChain k + 1
    omega)

/-- Proper peel `center c(k+1) → center c(k)`: identity
    `6·(5x+1) − 1 = 5·(6x+1)`, bigDivisor 5 (prime, > A when A ≤ 4);
    ALL post-audit patches (smaller, targetPos) are done honestly. -/
def fiveAdicChainPeel {A : ℕ} (hA : A ≤ 4) (k : ℕ) :
    ProperCenterPeel A (fiveAdicChain (k + 1)) (fiveAdicChain k) :=
  { inSide := Side.minus
    outSide := Side.plus
    bigDivisor := 5
    bigPrime := by norm_num
    bigBeyondScale := by omega
    factor := by
      show 6 * (5 * fiveAdicChain k + 1) - 1 = 5 * (6 * fiveAdicChain k + 1)
      omega
    smaller := by
      have := fiveAdicChain_pos k
      show fiveAdicChain k < 5 * fiveAdicChain k + 1
      omega
    targetPos := fiveAdicChain_pos k }

/-- The full proper path from `center c(k)` down to `center 1`. -/
theorem fiveAdicChainPath {A : ℕ} (hA : A ≤ 4) :
    ∀ k, PathN (ProperRealStep A 1) k
      (State.center (fiveAdicChain k)) (State.center 1) := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
      exact ⟨State.center (fiveAdicChain n),
        ProperRealStep.clean (clean_of_scale_le_four hA (fiveAdicChain_pos (n + 1)))
          (clean_of_scale_le_four hA (fiveAdicChain_pos n)) (fiveAdicChainPeel hA n),
        ih⟩

/-- Admissible genealogy for each k — WITHOUT ANY twin hypothesis. -/
def fiveAdicChainFlow {A : ℕ} (hA : A ≤ 4) (k : ℕ) :
    ExtendedProperGeneratedFlow A 1 :=
  { start := fiveAdicChain (k + 1)
    terminal := State.center 1
    steps := k + 1
    nonempty := Nat.succ_pos k
    properPath := fiveAdicChainPath hA (k + 1)
    startClean := clean_of_scale_le_four hA (fiveAdicChain_pos (k + 1))
    startFresh := by
      have := fiveAdicChain_pos k
      show 1 < 5 * fiveAdicChain k + 1
      omega
    terminalLegal := clean_of_scale_le_four hA le_rfl
    ledgerTerminal := extendedLedgerTerminal_oldCleanCenter le_rfl
      (clean_of_scale_le_four hA le_rfl) }

theorem fiveAdicChainFlow_injective {A : ℕ} (hA : A ≤ 4) :
    Function.Injective (fiveAdicChainFlow hA) := by
  intro k₁ k₂ h
  have hstart : fiveAdicChain (k₁ + 1) = fiveAdicChain (k₂ + 1) :=
    congrArg ExtendedProperGeneratedFlow.start h
  have := fiveAdicChain_strictMono.injective hstart
  omega

/-- **TWO distinct admissible genealogies UNCONDITIONALLY** (A ≤ 4, M0 = 1):
    neither TwinBoundAbove nor ¬TwinCenterZ is used anywhere. -/
theorem two_admissible_flows_unconditional {A : ℕ} (hA : A ≤ 4) :
    ∃ F₁ F₂ : ExtendedProperGeneratedFlow A 1,
      F₁ ≠ F₂ ∧ ExtendedFlowAdmissible F₁ ∧ ExtendedFlowAdmissible F₂ := by
  refine ⟨fiveAdicChainFlow hA 0, fiveAdicChainFlow hA 1, ?_,
    extendedFlow_admissible _, extendedFlow_admissible _⟩
  intro h
  exact absurd (fiveAdicChainFlow_injective hA h) (by omega)

/-- The family is infinite ⟹ NO finite-key projection resolves on
    (A ≤ 4, M0 = 1): pigeonhole yields a same-key pair, the alternative is burnt. -/
theorem no_projection_resolves_at_smallScale {A : ℕ} (hA : A ≤ 4)
    (proj : SemanticExtendedFlowLedgerProjection A 1) :
    ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  intro hRes
  letI : Finite proj.Key := proj.finiteKey
  obtain ⟨k₁, k₂, hne, hkey⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun k => proj.keyFlow (fiveAdicChainFlow hA k))
  have hFne : fiveAdicChainFlow hA k₁ ≠ fiveAdicChainFlow hA k₂ :=
    fun h => hne (fiveAdicChainFlow_injective hA h)
  exact no_extendedFlowResolutionAlternative A 1
    (hRes _ _ hFne (extendedFlow_admissible _) (extendedFlow_admissible _) hkey)

/-- **THE A ≤ 4 BRANCH OF THE NODE IS MACHINE-REFUTED**: no family of projections
    over such an A resolves on all M0 (it already fails at M0 = 1). -/
theorem smallScale_branch_of_lastStep00Obligation_refuted {A : ℕ} (hA : A ≤ 4) :
    ¬ ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
        ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0) := by
  rintro ⟨projOf, hRes⟩
  exact no_projection_resolves_at_smallScale hA (projOf 1) (hRes 1)

/-- **NARROWING OF THE NODE**: `∃A` in TheLastStep00Obligation lives only in `A ≥ 5`. -/
theorem lastStep00Obligation_forces_scale_ge_five
    (H : TheLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧
      ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
        ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0) := by
  rcases H with ⟨A, projOf, h⟩
  by_cases hA : 5 ≤ A
  · exact ⟨A, hA, projOf, h⟩
  · exact absurd ⟨projOf, h⟩
      (smallScale_branch_of_lastStep00Obligation_refuted (by omega))

/-#############################################################################
  INTERNAL CAUSE OF A NEW UNIVERSE (brick: internal_cause_of_new_universe;
  the dependent layer RealisedNegationOfCausalClosure is RECONSTRUCTED — the
  brick causal_closure_negation_self_destruct is absent from the supply).
  An external cause (input/axiom) generates a universe; a full internal cause
  = boundary-crossing self-proof = forbidden engine; the realised negation of
  the cause self-destructs. Below — the layer + brick + machine honesty:
  internal cause ⟺ P ∧ ¬P (tautological for any P); the trichotomy of modes
  COLLAPSES into "mode ⟺ external input P".
#############################################################################-/

/-- Realised negation of causal-closure: a concrete INTERNAL obstruction —
    a stable ledger + a real same-key collision against it (not a bare external
    logical ¬P). The layer is RECONSTRUCTED per the specification of the
    missing brick causal_closure_negation_self_destruct. -/
def RealisedNegationOfCausalClosure : Prop :=
  ∃ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    Nonempty (LocalStableRefutationAttempt proj)

/-- The realised negation self-destructs: the attempt is empty (lexRank/seam). -/
theorem no_realisedNegationOfCausalClosure :
    ¬ RealisedNegationOfCausalClosure := by
  rintro ⟨A, M0, proj, ⟨R⟩⟩
  exact no_localStableRefutationAttempt R

/-#############################################################################
  §1. External cause versus internal cause
#############################################################################-/

/--
An external cause for a universe-generating principle is just the principle
accepted as an outside input.

This is intentionally weak: it says nothing about derivability inside the
Step00 ledger-flow universe.
-/
abbrev ExternalUniverseCause (P : Prop) : Prop := P

/--
An internal cause for a universe-generating principle is a boundary-crossing
self-proof: from the principle itself one can manufacture an internal stable
Step00 decision attempt.

This is exactly the dangerous case.  Previous patches show that any such
internalisation builds the forbidden Euclidean engine.
-/
abbrev InternalUniverseCause (P : Prop) : Prop :=
  BoundaryCrossingSelfProof P

/--
An external cause may be used as an external input; an internal cause is not
thereby obtained.
-/
abbrev ExternalButNotInternalCause (P : Prop) : Prop :=
  ExternalUniverseCause P ∧ ¬ InternalUniverseCause P

/--
Any internal cause constructs the forbidden concrete Euclidean engine.
-/
theorem internalUniverseCause_builds_engine {P : Prop}
    (h : InternalUniverseCause P) : SomeConcreteEuclideanEngine :=
  boundaryCrossingSelfProof_builds_engine h

/--
No internal cause for a complete universe-generating principle exists in the
stable no-engine Step00 architecture.
-/
theorem no_internalUniverseCause {P : Prop} :
    ¬ InternalUniverseCause P :=
  no_boundaryCrossingSelfProof

/--
If an internal cause is nevertheless assumed, contradiction follows.
-/
theorem internalUniverseCause_contradiction {P : Prop}
    (h : InternalUniverseCause P) : False :=
  no_internalUniverseCause h

/-#############################################################################
  §2. The Step00 causal-closure principle as an external cause
#############################################################################-/

/--
The strict Step00 causal-closure universe has an external cause exactly when the
strict external universe-generating principle is supplied as an outside input.
-/
abbrev StrictStep00UniverseHasExternalCause : Prop :=
  ExternalUniverseCause ExternalUniverseGeneratingPrinciple

/--
The strict Step00 causal-closure universe has no internal cause.
-/
abbrev StrictStep00UniverseHasNoInternalCause : Prop :=
  ¬ InternalUniverseCause ExternalUniverseGeneratingPrinciple

/--
External cause of the strict Step00 universe produces the already audited twin
infinitude conclusion.
-/
theorem strictStep00ExternalCause_generates_twins
    (h : StrictStep00UniverseHasExternalCause) : TwinLowers.Infinite :=
  externalUniverseGeneratingPrinciple_generates_twins h

/--
The strict Step00 universe cannot have a complete internal cause.
-/
theorem strictStep00Universe_has_no_internalCause :
    StrictStep00UniverseHasNoInternalCause :=
  no_strictExternalUniverse_selfProof

/--
If someone claims an internal cause for the strict Step00 universe, that claim
is a forbidden-engine contradiction.
-/
theorem strictStep00InternalCause_contradiction
    (h : InternalUniverseCause ExternalUniverseGeneratingPrinciple) : False :=
  strictStep00Universe_has_no_internalCause h

/--
With an external cause supplied, the strict Step00 universe is external-only:
it generates the Step00 conclusion, but it cannot be self-caused internally.
-/
theorem strictStep00Universe_externalOnly
    (h : StrictStep00UniverseHasExternalCause) :
    ExternalButNotInternalCause ExternalUniverseGeneratingPrinciple := by
  exact ⟨h, strictStep00Universe_has_no_internalCause⟩

/-#############################################################################
  §3. No-energy universe: an internal cause would be self-support
#############################################################################-/

/--
The no-energy Step00 universe has an external cause when the no-energy stable
universe principle is supplied as an outside input.
-/
abbrev NoEnergyStep00UniverseHasExternalCause : Prop :=
  ExternalUniverseCause NoEnergyUniverseGeneratingPrinciple

/--
An internal cause for the no-energy universe is exactly the no-energy
self-support attempt isolated in the previous patch.
-/
theorem noEnergyInternalCause_iff_selfSupport :
    InternalUniverseCause NoEnergyUniverseGeneratingPrinciple ↔
      NoEnergySelfSupportAttempt := by
  rfl

/--
The no-energy universe cannot cause/support itself internally.
-/
theorem noEnergyStep00Universe_has_no_internalCause :
    ¬ InternalUniverseCause NoEnergyUniverseGeneratingPrinciple :=
  no_noEnergyUniverse_selfProof

/--
If a no-energy universe tries to be internally self-caused, contradiction
follows.  This is the formal version of: without an external cause or energy,
self-support is the forbidden engine.
-/
theorem noEnergyInternalCause_contradiction
    (h : InternalUniverseCause NoEnergyUniverseGeneratingPrinciple) : False :=
  noEnergyStep00Universe_has_no_internalCause h

/--
With an external no-energy cause supplied, the no-energy universe is still
external-only relative to the audited architecture.
-/
theorem noEnergyStep00Universe_externalOnly
    (h : NoEnergyStep00UniverseHasExternalCause) :
    ExternalButNotInternalCause NoEnergyUniverseGeneratingPrinciple := by
  exact ⟨h, noEnergyStep00Universe_has_no_internalCause⟩

/-#############################################################################
  §4. Arguing by contradiction about the cause
#############################################################################-/

/--
A bare external denial that there is an internal cause is a harmless logical
hypothesis.  It has no local Step00 content until realised as a concrete seam
or stable-counterexample object.
-/
abbrev ExternalDenialOfInternalCause (P : Prop) : Prop :=
  ¬ InternalUniverseCause P

/--
For the strict Step00 universe, the external denial of an internal cause is in
fact already true in the audited architecture.
-/
theorem strictStep00_externalDenialOfInternalCause :
    ExternalDenialOfInternalCause ExternalUniverseGeneratingPrinciple :=
  strictStep00Universe_has_no_internalCause

/--
For the no-energy Step00 universe, the external denial of an internal cause is
also true.
-/
theorem noEnergy_externalDenialOfInternalCause :
    ExternalDenialOfInternalCause NoEnergyUniverseGeneratingPrinciple :=
  noEnergyStep00Universe_has_no_internalCause

/--
A realised denial of causal cause inside Step00 is exactly a realised negation
of causal closure: it must present a concrete local obstruction rather than a
bare external logical negation.
-/
abbrev RealisedDenialOfCausalCause : Prop :=
  RealisedNegationOfCausalClosure

/--
No realised denial of causal cause exists in the stable Step00 architecture.
-/
theorem no_realisedDenialOfCausalCause :
    ¬ RealisedDenialOfCausalCause :=
  no_realisedNegationOfCausalClosure

/--
Thus a proof by contradiction against the existence of a cause has no internal
realisation unless it leaves the audited stable/no-engine universe.
-/
theorem byContra_noInternalCause_has_no_internal_realisation
    {P : Prop} (h : ExternalDenialOfInternalCause P) :
    ¬ RealisedDenialOfCausalCause := by
  exact no_realisedDenialOfCausalCause

/-#############################################################################
  §5. Final trichotomy: external cause, internal engine, or singular failure
#############################################################################-/

/--
A cause mode for a Step00 universe-generating principle.

The three possibilities correspond to the prose analysis:

  * `external`: the universe is generated by an outside input/axiom;
  * `internal`: the universe attempts to cause itself internally;
  * `negated`: the system tries to realise the denial of a causal explanation.

Theorems below show that only the external mode survives in the audited
no-engine architecture.
-/
inductive UniverseCauseMode (P : Prop) : Prop where
  | external (h : ExternalUniverseCause P) : UniverseCauseMode P
  | internal (h : InternalUniverseCause P) : UniverseCauseMode P
  | negated (h : RealisedDenialOfCausalCause) : UniverseCauseMode P

/--
The internal cause mode is impossible.
-/
theorem universeCauseMode_internal_impossible {P : Prop}
    (h : InternalUniverseCause P) : False :=
  internalUniverseCause_contradiction h

/--
The realised-negation mode is impossible.
-/
theorem universeCauseMode_negated_impossible
    (h : RealisedDenialOfCausalCause) : False :=
  no_realisedDenialOfCausalCause h

/--
If a universe cause mode does not use an external input, contradiction follows.
-/
theorem nonExternalUniverseCauseMode_impossible {P : Prop}
    (M : UniverseCauseMode P)
    (hNotExternal : ¬ ExternalUniverseCause P) : False := by
  cases M with
  | external h => exact hNotExternal h
  | internal h => exact universeCauseMode_internal_impossible h
  | negated h => exact universeCauseMode_negated_impossible h

/--
For the strict Step00 causal-closure universe: any surviving cause mode must be
external.  Internal self-cause builds the forbidden engine; realised denial
self-destructs.
-/
theorem strictStep00_cause_must_be_external
    (M : UniverseCauseMode ExternalUniverseGeneratingPrinciple)
    (hNoExternal : ¬ ExternalUniverseCause ExternalUniverseGeneratingPrinciple) :
    False :=
  nonExternalUniverseCauseMode_impossible M hNoExternal

/--
For the no-energy Step00 universe: any surviving cause mode must also be
external.  An internal cause is precisely no-energy self-support, i.e. the
forbidden engine.
-/
theorem noEnergyStep00_cause_must_be_external
    (M : UniverseCauseMode NoEnergyUniverseGeneratingPrinciple)
    (hNoExternal : ¬ ExternalUniverseCause NoEnergyUniverseGeneratingPrinciple) :
    False :=
  nonExternalUniverseCauseMode_impossible M hNoExternal

/-#############################################################################
  §6. Final slogans as checked propositions
#############################################################################-/

/--
Slogan 1: a new Step00 universe may have an external cause, but not a complete
internal cause, in the audited no-engine architecture.
-/
abbrev NewUniverseCanBeExternallyButNotInternallyCaused : Prop :=
  StrictStep00UniverseHasExternalCause →
    ExternalButNotInternalCause ExternalUniverseGeneratingPrinciple

/-- Realisation of slogan 1. -/
theorem newUniverseCanBeExternallyButNotInternallyCaused :
    NewUniverseCanBeExternallyButNotInternallyCaused :=
  strictStep00Universe_externalOnly

/--
Slogan 2: if the no-energy universe tries to cause/support itself internally,
that self-cause is the forbidden engine contradiction.
-/
abbrev NoEnergySelfCauseIsForbiddenEngineContradiction : Prop :=
  ¬ InternalUniverseCause NoEnergyUniverseGeneratingPrinciple

/-- Realisation of slogan 2. -/
theorem noEnergySelfCauseIsForbiddenEngineContradiction :
    NoEnergySelfCauseIsForbiddenEngineContradiction :=
  noEnergyStep00Universe_has_no_internalCause

/--
Slogan 3: arguing by contradiction against the causal cause is legal externally,
but any internal realisation of that denial self-destructs.
-/
abbrev ByContraAgainstCauseHasNoInternalRealisation : Prop :=
  ∀ P : Prop,
    ExternalDenialOfInternalCause P → ¬ RealisedDenialOfCausalCause

/-- Realisation of slogan 3. -/
theorem byContraAgainstCauseHasNoInternalRealisation :
    ByContraAgainstCauseHasNoInternalRealisation := by
  intro P h
  exact byContra_noInternalCause_has_no_internal_realisation h

/--
Scope marker: this is an object-level theorem about Step00 causal closure, not a
claim that ordinary external classical reasoning is forbidden.
-/
abbrev ThisDoesNotForbidExternalCausesOrExternalByContra : Prop := True

theorem thisDoesNotForbidExternalCausesOrExternalByContra :
    ThisDoesNotForbidExternalCausesOrExternalByContra := by
  trivial

/-! Machine honesty of the cause form -/

/-- Internal cause ⟺ `P ∧ ¬P` (the same tautological fact as for
    self-proof): "there is no full internal cause" holds for ANY P. -/
theorem internalUniverseCause_iff_and_not {P : Prop} :
    InternalUniverseCause P ↔ (P ∧ ¬ P) :=
  boundaryCrossingSelfProof_iff_and_not

/-- THE TRICHOTOMY COLLAPSES: since the internal and negated branches are empty,
    the cause mode ⟺ just the external input P. "Only the external cause
    survives" — literally: there are no other inhabited branches. -/
theorem universeCauseMode_iff {P : Prop} :
    UniverseCauseMode P ↔ P := by
  constructor
  · intro M
    cases M with
    | external h => exact h
    | internal h => exact (internalUniverseCause_contradiction h).elim
    | negated h => exact (no_realisedNegationOfCausalClosure h).elim
  · exact UniverseCauseMode.external

/-#############################################################################
  FINITE CAUSAL TOWERS BY INDUCTION (brick: finite_causal_tower_induction).
  The finite tower "someone created the universe" is classified by induction into
  4 outcomes: external boundary / seam / payment / engine; without all four
  the tower is impossible; an ∞-tower with strict ℕ-descent of rank is impossible.
  Fixes: InfiniteRankedCausalTower carries data → impossibility `→ False`;
  CausalTowerAuditSummary declared : Prop (theorem-compatibility).
  Below — the brick + machine honesty: outcome ⟺ P and tower ⟺ P (only the
  boundary branch is inhabited — "adding creators does not remove the boundary"
  literally).
#############################################################################-/

/-#############################################################################
  §1. Boundary/failure alternatives for a causal tower
#############################################################################-/

/--
The four allowed ways for a causal tower to avoid being a closed internal
self-cause.

`external` is the legitimate outside boundary/axiom.
`seam` is the forbidden realised denial of causal closure.
`payment` is the energy/payment branch.
`engine` is the forbidden Euclidean return/cycle witness.
-/
inductive CausalTowerOutcome (P : Prop) : Prop where
  | external : ExternalUniverseCause P → CausalTowerOutcome P
  | seam : RealisedDenialOfCausalCause → CausalTowerOutcome P
  | payment : ImpossiblePayment → CausalTowerOutcome P
  | engine : SomeConcreteEuclideanEngine → CausalTowerOutcome P

/--
A causal tower of finite depth `n` for a principle `P`.

This is deliberately an audit datatype: it records all ways a finite tower can
terminate or fail.  The only genuinely internal constructor is `internal`, and
previous patches show that an internal cause immediately builds the forbidden
engine.

The `extend` constructor represents adding one more “someone else caused it”
level above the current tower.  Induction on this constructor is the formal
version of: adding finitely many extra causal universes never removes the need
for an external boundary, seam, payment, or engine.
-/
inductive FiniteCausalTowerAttempt (P : Prop) : ℕ → Prop where
  | boundary {n : ℕ} : ExternalUniverseCause P → FiniteCausalTowerAttempt P n
  | seam {n : ℕ} : RealisedDenialOfCausalCause → FiniteCausalTowerAttempt P n
  | payment {n : ℕ} : ImpossiblePayment → FiniteCausalTowerAttempt P n
  | internal {n : ℕ} : InternalUniverseCause P → FiniteCausalTowerAttempt P n
  | extend {n : ℕ} : FiniteCausalTowerAttempt P n →
      FiniteCausalTowerAttempt P (n + 1)

/--
Every finite causal tower attempt classifies into one of the four outcomes.
The proof is ordinary induction on the tower.
-/
theorem finiteCausalTowerAttempt_classifies
    {P : Prop} {n : ℕ}
    (T : FiniteCausalTowerAttempt P n) : CausalTowerOutcome P := by
  induction T with
  | boundary h => exact CausalTowerOutcome.external h
  | seam h => exact CausalTowerOutcome.seam h
  | payment h => exact CausalTowerOutcome.payment h
  | internal h =>
      exact CausalTowerOutcome.engine (internalUniverseCause_builds_engine h)
  | extend T ih => exact ih

/--
A closed finite tower without external boundary, seam, payment, or engine cannot
exist.
-/
theorem no_finiteCausalTowerAttempt_without_boundary_or_failure
    {P : Prop} {n : ℕ}
    (hNoExternal : ¬ ExternalUniverseCause P)
    (hNoSeam : ¬ RealisedDenialOfCausalCause)
    (hNoPayment : ¬ ImpossiblePayment)
    (hNoEngine : ¬ SomeConcreteEuclideanEngine) :
    ¬ FiniteCausalTowerAttempt P n := by
  intro T
  cases finiteCausalTowerAttempt_classifies T with
  | external h => exact hNoExternal h
  | seam h => exact hNoSeam h
  | payment h => exact hNoPayment h
  | engine h => exact hNoEngine h

/--
Specialisation: if the external Step00 causal-closure principle is not supplied
as an outside axiom, no finite internal causal tower can manufacture it without
hitting seam/payment/engine.
-/
theorem no_finiteTower_for_strictStep00_without_external_or_failure
    {n : ℕ}
    (hNoExternal : ¬ ExternalUniverseCause ExternalUniverseGeneratingPrinciple)
    (hNoSeam : ¬ RealisedDenialOfCausalCause)
    (hNoPayment : ¬ ImpossiblePayment) :
    ¬ FiniteCausalTowerAttempt ExternalUniverseGeneratingPrinciple n := by
  exact no_finiteCausalTowerAttempt_without_boundary_or_failure
    hNoExternal hNoSeam hNoPayment no_someConcreteEuclideanEngine

/--
Specialisation: the no-energy universe also cannot be manufactured by a finite
internal tower without external boundary, seam, payment, or engine.
-/
theorem no_finiteTower_for_noEnergyStep00_without_external_or_failure
    {n : ℕ}
    (hNoExternal : ¬ ExternalUniverseCause NoEnergyUniverseGeneratingPrinciple)
    (hNoSeam : ¬ RealisedDenialOfCausalCause)
    (hNoPayment : ¬ ImpossiblePayment) :
    ¬ FiniteCausalTowerAttempt NoEnergyUniverseGeneratingPrinciple n := by
  exact no_finiteCausalTowerAttempt_without_boundary_or_failure
    hNoExternal hNoSeam hNoPayment no_someConcreteEuclideanEngine

/-#############################################################################
  §2. “Someone else” finite creation chains
#############################################################################-/

/--
A finite chain of “someone else caused this universe” is just a finite causal
tower attempt.  The name is added to make the intended reading explicit.
-/
abbrev FiniteSomeoneElseCreationChain (P : Prop) (n : ℕ) : Prop :=
  FiniteCausalTowerAttempt P n

/--
A finite “someone else” chain still needs one of the same four outcomes.  Adding
finitely many creators above the universe never removes the boundary problem.
-/
theorem finiteSomeoneElseCreationChain_classifies
    {P : Prop} {n : ℕ}
    (T : FiniteSomeoneElseCreationChain P n) : CausalTowerOutcome P :=
  finiteCausalTowerAttempt_classifies T

/--
No finite “someone else” chain can be completely internal and stable.
-/
theorem no_finiteSomeoneElseCreationChain_without_boundary_or_failure
    {P : Prop} {n : ℕ}
    (hNoExternal : ¬ ExternalUniverseCause P)
    (hNoSeam : ¬ RealisedDenialOfCausalCause)
    (hNoPayment : ¬ ImpossiblePayment)
    (hNoEngine : ¬ SomeConcreteEuclideanEngine) :
    ¬ FiniteSomeoneElseCreationChain P n :=
  no_finiteCausalTowerAttempt_without_boundary_or_failure
    hNoExternal hNoSeam hNoPayment hNoEngine

/-#############################################################################
  §3. Infinite towers require non-well-founded rank descent
#############################################################################-/

/--
A bare infinite causal tower with a natural rank strictly decreasing at every
level.  This abstracts the concrete Step00 situation, where nested universes or
information-compression steps strictly decrease `lexRank`.
-/
structure InfiniteRankedCausalTower where
  rank : ℕ → ℕ
  drops : ∀ i : ℕ, rank (i + 1) < rank i

/--
There is no infinite strictly descending chain in natural numbers.
-/
theorem no_infinite_nat_strict_descent
    (rank : ℕ → ℕ)
    (hdrop : ∀ i : ℕ, rank (i + 1) < rank i) : False := by
  have hle : ∀ n : ℕ, rank n + n ≤ rank 0 := by
    intro n
    induction n with
    | zero =>
        omega
    | succ n ih =>
        have hs : rank (n + 1) + 1 ≤ rank n := Nat.succ_le_of_lt (hdrop n)
        omega
  have hbad := hle (rank 0 + 1)
  omega

/--
Therefore no infinite ranked causal tower exists.
-/
theorem no_infiniteRankedCausalTower
    (T : InfiniteRankedCausalTower) : False :=
  no_infinite_nat_strict_descent T.rank T.drops

/--
A convenient alias for the concrete Step00 reading: an infinite tower of nested
universes is impossible whenever each nesting/compression step strictly lowers a
natural rank.
-/
abbrev NoWellFoundedInfiniteCausalRegress : Prop :=
  InfiniteRankedCausalTower → False

/--
The well-founded no-regress principle is already available from natural-number
rank descent.
-/
theorem noWellFoundedInfiniteCausalRegress :
    NoWellFoundedInfiniteCausalRegress :=
  no_infiniteRankedCausalTower

/-#############################################################################
  §4. Final slogan theorem
#############################################################################-/

/--
Final finite-and-well-founded causal-tower slogan.

A finite tower needs an external boundary, seam, payment, or engine.  An
infinite tower is possible only if the alleged causal levels fail to be
well-founded by a natural rank.
-/
structure CausalTowerAuditSummary (P : Prop) : Prop where
  finite_tower_classifies :
    ∀ {n : ℕ}, FiniteCausalTowerAttempt P n → CausalTowerOutcome P
  no_closed_finite_tower :
    (¬ ExternalUniverseCause P) →
    (¬ RealisedDenialOfCausalCause) →
    (¬ ImpossiblePayment) →
    (¬ SomeConcreteEuclideanEngine) →
      ∀ {n : ℕ}, ¬ FiniteCausalTowerAttempt P n
  no_well_founded_infinite_tower :
    NoWellFoundedInfiniteCausalRegress

/--
The audit summary for any proposed Step00 universe-generating principle.
-/
theorem causalTowerAuditSummary (P : Prop) :
    CausalTowerAuditSummary P where
  finite_tower_classifies := by
    intro n T
    exact finiteCausalTowerAttempt_classifies T
  no_closed_finite_tower := by
    intro hNoExternal hNoSeam hNoPayment hNoEngine n
    exact no_finiteCausalTowerAttempt_without_boundary_or_failure
      hNoExternal hNoSeam hNoPayment hNoEngine
  no_well_founded_infinite_tower := noWellFoundedInfiniteCausalRegress

/--
Concrete slogan for the strict Step00 causal-closure universe.
-/
theorem strictStep00_causalTowerAuditSummary :
    CausalTowerAuditSummary ExternalUniverseGeneratingPrinciple :=
  causalTowerAuditSummary ExternalUniverseGeneratingPrinciple

/--
Concrete slogan for the no-energy Step00 causal-closure universe.
-/
theorem noEnergyStep00_causalTowerAuditSummary :
    CausalTowerAuditSummary NoEnergyUniverseGeneratingPrinciple :=
  causalTowerAuditSummary NoEnergyUniverseGeneratingPrinciple

/-! Machine honesty of the tower form -/

/-- Tower outcome ⟺ P: seam/payment/engine are burnt, only external is inhabited. -/
theorem causalTowerOutcome_iff {P : Prop} : CausalTowerOutcome P ↔ P := by
  constructor
  · intro O
    cases O with
    | external h => exact h
    | seam h => exact (no_realisedNegationOfCausalClosure h).elim
    | payment h => exact (BoundaryDefectPayment.impossiblePayment_false h).elim
    | engine h => exact (no_someConcreteEuclideanEngine h).elim
  · exact CausalTowerOutcome.external

/-- THE TOWER COLLAPSES: a finite tower of any depth ⟺ just P. "Adding
    creators does not remove the boundary problem" — literally: the single
    inhabited chain of constructors runs into the boundary (external input P). -/
theorem finiteCausalTowerAttempt_iff {P : Prop} {n : ℕ} :
    FiniteCausalTowerAttempt P n ↔ P := by
  constructor
  · intro T
    exact causalTowerOutcome_iff.mp (finiteCausalTowerAttempt_classifies T)
  · intro hp
    exact FiniteCausalTowerAttempt.boundary hp

/-#############################################################################
  INTERNAL FIRST CAUSE = ENGINE (brick: internal_first_cause_is_engine).
  The final distinction: an external first cause is a boundary/axiom; an internal
  one (belonging to the same closed system) is a self-cause = forbidden
  engine; "a creator inside the same system" is impossible. The brick itself
  honestly limits its scope (§5: external axioms are NOT declared engines).
  Below — the brick + machine honesty: internal first cause ⟺ P ∧ ¬P;
  the first-cause mode collapses (FirstCauseMode P ⟺ P).
#############################################################################-/

/-#############################################################################
  §1. First causes: external boundary versus internal self-cause
#############################################################################-/

/--
An external first cause for a proposition/universe principle is simply an
outside input.  It is not required to be represented by a Step00 path, ledger
edge, generated flow, or internal decision attempt.
-/
abbrev ExternalFirstCause (P : Prop) : Prop :=
  ExternalUniverseCause P

/--
An internal first cause for a proposition/universe principle is an internal
cause in the already audited sense: a boundary-crossing self-proof of the same
principle inside the Step00 causal universe.

This is the dangerous case.  It attempts to put the cause of the whole closed
system inside that same closed system.
-/
abbrev InternalFirstCause (P : Prop) : Prop :=
  InternalUniverseCause P

/--
A first cause is external-only when it is supplied as a boundary condition but
cannot be internalised as a self-cause.
-/
abbrev ExternalOnlyFirstCause (P : Prop) : Prop :=
  ExternalFirstCause P ∧ ¬ InternalFirstCause P

/--
A same-system creator is just an internal first cause: the alleged creator is
not outside the closed causal universe but belongs to the same Step00 causal
system.
-/
abbrev SameClosedSystemCreator (P : Prop) : Prop :=
  InternalFirstCause P

/-#############################################################################
  §2. Internal first cause builds the forbidden engine
#############################################################################-/

/--
Any internal first cause constructs the forbidden concrete Euclidean engine.
This is the formal version of:

  if the first cause belongs to the universe it causes, then it is self-causal;
  self-causality in Step00 is a return/cycle engine.
-/
theorem internalFirstCause_builds_engine {P : Prop}
    (h : InternalFirstCause P) : SomeConcreteEuclideanEngine :=
  internalUniverseCause_builds_engine h

/--
No internal first cause exists in the stable no-engine Step00 architecture.
-/
theorem no_internalFirstCause {P : Prop} :
    ¬ InternalFirstCause P :=
  no_internalUniverseCause

/--
Assuming an internal first cause immediately gives contradiction.
-/
theorem internalFirstCause_contradiction {P : Prop}
    (h : InternalFirstCause P) : False :=
  no_internalFirstCause h

/--
A creator inside the same closed causal system is impossible for the same
reason: it is an internal first cause and hence a forbidden engine.
-/
theorem sameClosedSystemCreator_contradiction {P : Prop}
    (h : SameClosedSystemCreator P) : False :=
  internalFirstCause_contradiction h

/--
Readable theorem: an internal first cause is a perpetual-engine witness.
-/
abbrev InternalFirstCauseIsPerpetualEngine : Prop :=
  ∀ P : Prop, InternalFirstCause P → SomeConcreteEuclideanEngine

/-- Realisation of the slogan above. -/
theorem internalFirstCauseIsPerpetualEngine :
    InternalFirstCauseIsPerpetualEngine := by
  intro P h
  exact internalFirstCause_builds_engine h

/--
Readable theorem: an internal first cause is impossible because the resulting
perpetual engine is already forbidden.
-/
abbrev NoInternalFirstCauseWithoutForbiddenEngine : Prop :=
  ∀ P : Prop, ¬ InternalFirstCause P

/-- Realisation of the no-go theorem. -/
theorem noInternalFirstCauseWithoutForbiddenEngine :
    NoInternalFirstCauseWithoutForbiddenEngine := by
  intro P
  exact no_internalFirstCause

/-#############################################################################
  §3. External first cause is not an internal engine
#############################################################################-/

/--
The strict external universe-generating principle, when supplied from outside,
is an external first cause.
-/
abbrev StrictStep00ExternalFirstCause : Prop :=
  ExternalFirstCause ExternalUniverseGeneratingPrinciple

/--
The strict Step00 principle cannot also be internally first-caused.
-/
abbrev StrictStep00NoInternalFirstCause : Prop :=
  ¬ InternalFirstCause ExternalUniverseGeneratingPrinciple

/--
Supplying the strict Step00 principle externally gives an external-only first
cause: it is a boundary condition, not a self-supporting engine.
-/
theorem strictStep00_externalOnlyFirstCause
    (h : StrictStep00ExternalFirstCause) :
    ExternalOnlyFirstCause ExternalUniverseGeneratingPrinciple := by
  exact ⟨h, strictStep00Universe_has_no_internalCause⟩

/--
The no-energy universe principle, if supplied from outside, is also only an
external first cause; internalising it is the no-energy self-support attempt and
is impossible.
-/
theorem noEnergyStep00_externalOnlyFirstCause
    (h : ExternalFirstCause NoEnergyUniverseGeneratingPrinciple) :
    ExternalOnlyFirstCause NoEnergyUniverseGeneratingPrinciple := by
  exact ⟨h, noEnergyStep00Universe_has_no_internalCause⟩

/-#############################################################################
  §4. First-cause modes
#############################################################################-/

/--
A first-cause mode for a universe-generating principle.

The `internal` branch is the forbidden-engine branch.  The `negated` branch is
an internally realised denial of causal explanation, already shown to be a
seam/engine self-destruction.  Only the external branch survives.
-/
inductive FirstCauseMode (P : Prop) : Prop where
  | external (h : ExternalFirstCause P) : FirstCauseMode P
  | internal (h : InternalFirstCause P) : FirstCauseMode P
  | negated (h : RealisedDenialOfCausalCause) : FirstCauseMode P

/--
The internal first-cause mode is impossible.
-/
theorem firstCauseMode_internal_impossible {P : Prop}
    (h : InternalFirstCause P) : False :=
  internalFirstCause_contradiction h

/--
The realised-denial mode is impossible.
-/
theorem firstCauseMode_negated_impossible
    (h : RealisedDenialOfCausalCause) : False :=
  no_realisedDenialOfCausalCause h

/--
If no external first cause is supplied, any claimed first-cause mode collapses.
-/
theorem nonExternalFirstCauseMode_impossible {P : Prop}
    (M : FirstCauseMode P)
    (hNoExternal : ¬ ExternalFirstCause P) : False := by
  cases M with
  | external h => exact hNoExternal h
  | internal h => exact firstCauseMode_internal_impossible h
  | negated h => exact firstCauseMode_negated_impossible h

/--
For the strict Step00 universe, any surviving first cause must be external.
-/
theorem strictStep00_firstCause_must_be_external
    (M : FirstCauseMode ExternalUniverseGeneratingPrinciple)
    (hNoExternal : ¬ ExternalFirstCause ExternalUniverseGeneratingPrinciple) :
    False :=
  nonExternalFirstCauseMode_impossible M hNoExternal

/--
For the no-energy Step00 universe, any surviving first cause must also be
external.  A same-system first cause is the forbidden no-energy self-support
engine.
-/
theorem noEnergyStep00_firstCause_must_be_external
    (M : FirstCauseMode NoEnergyUniverseGeneratingPrinciple)
    (hNoExternal : ¬ ExternalFirstCause NoEnergyUniverseGeneratingPrinciple) :
    False :=
  nonExternalFirstCauseMode_impossible M hNoExternal

/-#############################################################################
  §5. Final checked slogans
#############################################################################-/

/--
Slogan 1: an external first cause is an axiom/boundary; it is not an internal
engine unless it is internalised as a self-cause.
-/
abbrev ExternalFirstCauseIsBoundaryNotEngine : Prop :=
  StrictStep00ExternalFirstCause →
    ExternalOnlyFirstCause ExternalUniverseGeneratingPrinciple

/-- Realisation of slogan 1. -/
theorem externalFirstCauseIsBoundaryNotEngine :
    ExternalFirstCauseIsBoundaryNotEngine :=
  strictStep00_externalOnlyFirstCause

/--
Slogan 2: an internal first cause is the forbidden perpetual engine.
-/
abbrev InternalFirstCauseIsForbiddenEngine : Prop :=
  InternalFirstCauseIsPerpetualEngine

/-- Realisation of slogan 2. -/
theorem internalFirstCauseIsForbiddenEngine :
    InternalFirstCauseIsForbiddenEngine :=
  internalFirstCauseIsPerpetualEngine

/--
Slogan 3: nobody inside the same closed causal Step00 system can create the
whole system without becoming the forbidden engine.
-/
abbrev NoSameSystemCreatorWithoutEngine : Prop :=
  ∀ P : Prop, SameClosedSystemCreator P → False

/-- Realisation of slogan 3. -/
theorem noSameSystemCreatorWithoutEngine :
    NoSameSystemCreatorWithoutEngine := by
  intro P h
  exact sameClosedSystemCreator_contradiction h

/--
Final scope marker: the theorem is object-level for Step00 causal closure.  It
separates internal first cause from external axiom; it does not identify every
external axiom in all mathematics with an internal engine.
-/
abbrev ThisDoesNotTurnExternalAxiomsIntoEngines : Prop := True

theorem thisDoesNotTurnExternalAxiomsIntoEngines :
    ThisDoesNotTurnExternalAxiomsIntoEngines := by
  trivial

/-! Machine honesty of the first-cause form -/

/-- Internal first cause ⟺ `P ∧ ¬P` (inherited tautology). -/
theorem internalFirstCause_iff_and_not {P : Prop} :
    InternalFirstCause P ↔ (P ∧ ¬ P) :=
  internalUniverseCause_iff_and_not

/-- The first-cause mode COLLAPSES: `FirstCauseMode P ⟺ P` — only the external
    branch is inhabited; "a first cause must be external" — literally. -/
theorem firstCauseMode_iff {P : Prop} : FirstCauseMode P ↔ P := by
  constructor
  · intro M
    cases M with
    | external h => exact h
    | internal h => exact (internalFirstCause_contradiction h).elim
    | negated h => exact (no_realisedDenialOfCausalCause h).elim
  · exact FirstCauseMode.external

end GeneratedFlowFormulation


/-! ### §12. Structural analogy P/NP (NOT a proof of P≠NP and NOT of twins).
FORWARD (P): path length ≤ lexRank of the start (proven). REVERSE (NP): a finite key does not recover
the genealogy (proven). NODE PolyCertificateSuffices = SemanticFlowLedgerCollisionResolves — input. -/

namespace PvsNPAnalogy
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph.StrictLedgerAudit
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation


open EuclidsPath.LabelledFanIn
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph.StrictLedgerAudit
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-! ### §1. FORWARD = P: path length is bounded by lexRank of the start (polynomial verification) -/

/--
**`pathN_len_le_lexRank` — PROVEN.** Any forward path of length `n` from `X` has `n ≤ lexRank X`.
I.e. the forward run of the engine is "cheap": the number of steps is bounded by the start coordinate
(linearly in `lexRank`), and checking path legality is step-by-step. This is the P-side of the analogy.
A consequence of `lexRank` descent. -/
theorem pathN_len_le_lexRank {A M0 : ℕ} :
    ∀ n X Y, PathN (RealStep A M0) n X Y → n ≤ lexRank X := by
  intro n
  induction n with
  | zero => intro X Y h; omega
  | succ k ih =>
      intro X Y h
      obtain ⟨Z, hXZ, hZY⟩ := h
      have h1 : lexRank Z < lexRank X := lexRank_strict_decrease_on_RealStep hXZ
      have h2 : k ≤ lexRank Z := ih Z Y hZY
      omega

/-- The genealogy has polynomially-bounded length: `steps ≤ lexRank (center start)`. -/
theorem generatedFlow_steps_le_lexRank {A M0 : ℕ} (F : GeneratedFlow A M0) :
    F.steps ≤ lexRank (State.center F.start) :=
  pathN_len_le_lexRank F.steps (State.center F.start) F.terminal F.path

/-- **`VerificationEasy` — the P form.** "Checking genealogy `F` is cheap": the length is bounded by
    `lexRank` of the start (the witness is checked in a number of steps ≤ the coordinate). This is a
    PROVABLE property of the graph. -/
def VerificationEasy {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  F.steps ≤ lexRank (State.center F.start)

theorem verificationEasy_always {A M0 : ℕ} (F : GeneratedFlow A M0) : VerificationEasy F :=
  generatedFlow_steps_le_lexRank F

/-! ### §2. REVERSE = NP: a finite certificate does NOT recover the genealogy (search is not compressible) -/

/--
**`SearchNotCompressible` — the NP form.** On an infinite family of states a finite projection key does
NOT determine the state (⟹ all the more it does not recover the full genealogy). I.e. "compressing the
reverse search into a polynomial certificate" is impossible at the level of states. A direct consequence
of the §10 audit. -/
def SearchNotCompressible {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) (S : Set State) : Prop :=
  ¬ KeyDeterminesStateOn proj S

/-- **`search_not_compressible_of_infinite` — PROVEN.** For any finite projection on an infinite
    family the search is not compressible: the key loses information. This is the NP-side: the
    certificate is not equivalent to the full reverse path. -/
theorem search_not_compressible_of_infinite {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State} (hInf : S.Infinite) :
    SearchNotCompressible proj S :=
  finite_key_cannot_determine_state_on_infinite proj hInf

/-! ### §3. THE ANALOGY AS A THEOREM: verify and search are structurally distinct (not a slogan)

FORWARD is bounded by lexRank (proven), REVERSE does not compress into a finite key (proven). Hence
"verification" and "search" are here separated MACHINE-WISE: verify is always easy, while compressing
the search is impossible. -/

/--
**`verify_easy_but_search_not_compressible` — PROVEN (the analogy as a fact).** Simultaneously:
(1) EVERY genealogy is checked cheaply (`VerificationEasy`, the `lexRank` bound); and
(2) on an infinite family the search does NOT compress into a finite key (`SearchNotCompressible`).
This is the machine form of the asymmetry "verification is easy / search is not compressible" — a
structural shadow of P vs NP, WITHOUT asserting P≠NP. -/
theorem verify_easy_but_search_not_compressible {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State} (hInf : S.Infinite) :
    (∀ F : GeneratedFlow A M0, VerificationEasy F) ∧ SearchNotCompressible proj S :=
  ⟨verificationEasy_always, search_not_compressible_of_infinite proj hInf⟩

/-! ### §4. THE NODE: "a polynomial certificate suffices" = SemanticFlowLedgerCollisionResolves

The remaining input dressed in P/NP clothing: "a finite (polynomial) certificate of the reverse path
DECIDES that a collision of two genealogies = a real cycle". This is EXACTLY
SemanticFlowLedgerCollisionResolves. NOT proven — and §2 shows why: the certificate loses information,
so "the certificate suffices" is extra arithmetic. -/

/-- **`PolyCertificateSuffices` (input).** An alias for `SemanticFlowLedgerCollisionResolves` in
    P/NP terms: a finite certificate of a genealogy collision suffices to derive the resolution
    (cycle ∨ impossible payment). NOT proven. -/
def PolyCertificateSuffices {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0) : Prop :=
  SemanticFlowLedgerCollisionResolves proj

/--
**`branch_closes_if_polyCertificateSuffices` — PROVEN (conditional on the node).** IF a polynomial
certificate suffices (`PolyCertificateSuffices`) AND there is an infinite family of genealogies, THEN
the branch collapses (`False`) — a mirror of `generatedFlowStep00Package_false`. The node is NOT
presented: it is the same irreducible twins input, merely named in P/NP terms. -/
theorem branch_closes_if_polyCertificateSuffices {A M0 : ℕ}
    (proj : SemanticFlowLedgerProjection A M0)
    {𝓕 : Set (GeneratedFlow A M0)}
    (h𝓕 : InfiniteGeneratedFlowFamily A M0 𝓕)
    (hCert : PolyCertificateSuffices proj) :
    False :=
  infinite_generated_flows_impossible_with_resolution proj h𝓕 hCert

/-! ### §12bis. The final twins reduction = the P/NP node (machine link)

A chain of 7 factory bricks reduced the ENTIRE twins branch to `TheLastStep00Obligation`
(`∃ A projOf, ∀ M0, SemanticExtendedFlowLedgerCollisionResolves (projOf M0)`). This is exactly
"a polynomial certificate of the reverse path suffices" — the form of the P/NP node. We fix machine-wise
that the single remaining twins input HAS the form "the certificate suffices ⟹ infinitude of twins". -/

/-- **`twin_reduction_is_pnp_node` — PROVEN (machine link).** `TheLastStep00Obligation` (a certificate
    for resolving genealogy collisions suffices) ⟹ `TwinLowers.Infinite`. This is a reformulation of the
    already-proven `twinLowersInfinite_of_lastStep00Obligation`: the single twins input is the P/NP node
    "does a polynomial certificate of the reverse path suffice". Does NOT prove twins. -/
theorem twin_reduction_is_pnp_node
    (H : TheLastStep00Obligation) : EuclidsPath.TwinLowers.Infinite :=
  twinLowersInfinite_of_lastStep00Obligation H

end PvsNPAnalogy

/-#############################################################################
  INTEGER SIGNED FIREWALL (brick: integer_signed_firewall).
  ℤ-centers yield no new engine: the sign is a gauge (mirror of sides under z↦−z),
  every signed step is a pullback of an unsigned one, the gauge-flip +k→−k is not
  a step (lexRank), the zero center is not a carrier (6·0±1 = ∓1... ±1). Below —
  the brick + machine honesty: the firewall is DEFINITIONAL (SignedRealStep ⟺
  projection is a design choice, not a theorem about independent signed dynamics),
  the projection is surjective (full gauge fibration), the concrete killing of +k→−k.
#############################################################################-/

open EuclidsPath.LabelledFanIn
open EuclidsPath.BoundaryLedgerCollision

/-#############################################################################
  §1. Signed sides and the arithmetic mirror
#############################################################################-/

/-- The side mirror induced by `z ↦ -z`: `6(-k)-1 = -(6k+1)` and conversely. -/
def mirrorSide : Side → Side
  | Side.minus => Side.plus
  | Side.plus  => Side.minus

/-- Integer-valued signed side expression. -/
def signedSideValue : Side → ℤ → ℤ
  | Side.minus, z => 6 * z - 1
  | Side.plus,  z => 6 * z + 1

/-- The negative integer centre is the signed mirror of the positive one. -/
theorem signedSideValue_neg_mirror (z : ℤ) (s : Side) :
    signedSideValue s (-z) = - signedSideValue (mirrorSide s) z := by
  cases s <;> simp [signedSideValue, mirrorSide] <;> ring

/-#############################################################################
  §2. Signed Step00 states and unsigned projection
#############################################################################-/

/--
Signed version of the concrete Step00 state space.

The centre coordinate is now an integer.  Defect primes remain natural numbers:
the sign lives only on the carrier coordinate, not on the small-prime witness.
-/
inductive SignedState where
  | center   : ℤ → SignedState
  | defect   : ℤ → ℕ → Side → SignedState
  | absorber : ℤ → SignedState
deriving DecidableEq

/--
Projection from the signed integer graph to the audited natural graph.

The side is mirrored on negative centres, so that the side label records the
same absolute `6|z|±1` carrier after projection.
-/
def projectSignedState : SignedState → State
  | SignedState.center z       => State.center (Int.natAbs z)
  | SignedState.defect z q s   =>
      if z < 0 then
        State.defect (Int.natAbs z) q (mirrorSide s)
      else
        State.defect (Int.natAbs z) q s
  | SignedState.absorber z     => State.absorber (Int.natAbs z)

/-- Centre coordinate after forgetting signed gauge. -/
def signedCenterAbs (U : SignedState) : ℕ :=
  centerOf (projectSignedState U)

/-- The signed lexicographic rank is just the unsigned rank of the projection. -/
def signedLexRank (U : SignedState) : ℕ :=
  lexRank (projectSignedState U)

/-- Signed legality is inherited from the unsigned projected graph. -/
def SignedLegal (A M0 : ℕ) (U : SignedState) : Prop :=
  Legal A M0 (projectSignedState U)

/-- Signed freshness is inherited from the unsigned projected graph. -/
def SignedFresh (M0 : ℕ) (U : SignedState) : Prop :=
  Fresh M0 (projectSignedState U)

/-- Signed defects are exactly signed states whose unsigned projection is defective. -/
def SignedDefective (A : ℕ) (U : SignedState) : Prop :=
  Defective A (projectSignedState U)

/-#############################################################################
  §3. Signed real steps are only projected real steps
#############################################################################-/

/--
The signed real-step relation is the pullback of the unsigned real-step relation.

This is intentionally restrictive.  A sign flip by itself is not a new real
transition; it is gauge only.  A signed transition is genuine only when its
unsigned projection is already a genuine concrete Step00 transition.
-/
inductive SignedRealStep (A M0 : ℕ) : SignedState → SignedState → Prop
  | ofProjected {U V : SignedState}
      (h : RealStep A M0 (projectSignedState U) (projectSignedState V)) :
      SignedRealStep A M0 U V

/-- Every signed real step projects to an unsigned real step. -/
theorem signedStep_projects_to_unsignedStep
    {A M0 : ℕ} {U V : SignedState}
    (h : SignedRealStep A M0 U V) :
    RealStep A M0 (projectSignedState U) (projectSignedState V) := by
  cases h with
  | ofProjected hProjected => exact hProjected

/-- The signed lexicographic rank strictly decreases on every genuine signed step. -/
theorem signedLexRank_strict_decrease_on_SignedRealStep
    {A M0 : ℕ} {U V : SignedState}
    (h : SignedRealStep A M0 U V) :
    signedLexRank V < signedLexRank U := by
  exact lexRank_strict_decrease_on_RealStep
    (A := A) (M0 := M0)
    (signedStep_projects_to_unsignedStep h)

/-- Signed gauge equivalence: two signed states have the same unsigned payload. -/
def SignedGaugeEquivalent (U V : SignedState) : Prop :=
  projectSignedState U = projectSignedState V

/--
A pure signed gauge flip cannot be a real Step00 transition.

This kills the fake engine `+k -> -k -> +k`: if the unsigned payload is unchanged,
then any genuine real step would force `lexRank W < lexRank W`.
-/
theorem same_projection_signed_step_impossible
    {A M0 : ℕ} {U V : SignedState}
    (hGauge : SignedGaugeEquivalent U V) :
    ¬ SignedRealStep A M0 U V := by
  intro hStep
  have hlt : lexRank (projectSignedState V) < lexRank (projectSignedState U) :=
    lexRank_strict_decrease_on_RealStep
      (A := A) (M0 := M0)
      (signedStep_projects_to_unsignedStep hStep)
  dsimp [SignedGaugeEquivalent] at hGauge
  rw [hGauge] at hlt
  exact (Nat.lt_irrefl (lexRank (projectSignedState V))) hlt

/-#############################################################################
  §4. Signed paths and signed engines project to unsigned paths and engines
#############################################################################-/

/-- A signed path projects pointwise to an unsigned path of the same length. -/
theorem pathN_project_signed
    {A M0 : ℕ} :
    ∀ {n : ℕ} {U V : SignedState},
      PathN (SignedRealStep A M0) n U V →
      PathN (RealStep A M0) n (projectSignedState U) (projectSignedState V) := by
  intro n
  induction n with
  | zero =>
      intro U V h
      dsimp [PathN] at h ⊢
      cases h
      rfl
  | succ n ih =>
      intro U V h
      dsimp [PathN] at h ⊢
      rcases h with ⟨Z, hUZ, hZV⟩
      refine ⟨projectSignedState Z, ?_, ?_⟩
      · exact signedStep_projects_to_unsignedStep hUZ
      · exact ih hZV

/-- A nonempty signed self-path projects to a nonempty unsigned self-path. -/
theorem nonemptyPath_project_signed
    {A M0 : ℕ} {U : SignedState}
    (h : NonemptyPath (SignedRealStep A M0) U U) :
    NonemptyPath (RealStep A M0) (projectSignedState U) (projectSignedState U) := by
  rcases h with ⟨n, hpos, hPath⟩
  exact ⟨n, hpos, pathN_project_signed (A := A) (M0 := M0) hPath⟩

/-- Signed Euclidean engine: a legal nonempty signed cycle. -/
abbrev SignedEuclideanEngine (A M0 : ℕ) : Prop :=
  LegalCycle (SignedRealStep A M0) (SignedLegal A M0)

/-- Any signed engine projects to an unsigned concrete Step00 engine. -/
theorem signedEngine_projects_to_unsignedEngine
    {A M0 : ℕ}
    (h : SignedEuclideanEngine A M0) :
    LegalCycle (RealStep A M0) (Legal A M0) := by
  rcases h with ⟨U, hLegal, hPath⟩
  exact ⟨projectSignedState U, hLegal, nonemptyPath_project_signed hPath⟩

/-- There are no signed Euclidean engines. -/
theorem no_signedEuclideanEngine
    {A M0 : ℕ} :
    ¬ SignedEuclideanEngine A M0 := by
  intro hSigned
  exact no_concrete_legalCycle_by_lexRank
    (A := A) (M0 := M0)
    (signedEngine_projects_to_unsignedEngine hSigned)

/-#############################################################################
  §5. The zero centre is degenerate, not a carrier
#############################################################################-/

/--
A signed state is a nondegenerate carrier only if its projected centre is
positive.  This excludes the centre `0`, whose sides are `-1` and `1`.
-/
def SignedTwinCarrier : SignedState → Prop
  | SignedState.center z       => 0 < Int.natAbs z
  | SignedState.defect z _ _   => 0 < Int.natAbs z
  | SignedState.absorber z     => 0 < Int.natAbs z

/-- The zero centre does not carry a twin-prime pair. -/
theorem zero_center_not_signedTwinCarrier :
    ¬ SignedTwinCarrier (SignedState.center 0) := by
  simp [SignedTwinCarrier]

/-- The zero defect state is also degenerate as a carrier coordinate. -/
theorem zero_defect_not_signedTwinCarrier {q : ℕ} {s : Side} :
    ¬ SignedTwinCarrier (SignedState.defect 0 q s) := by
  simp [SignedTwinCarrier]

/-- The zero absorber is degenerate as a carrier coordinate. -/
theorem zero_absorber_not_signedTwinCarrier :
    ¬ SignedTwinCarrier (SignedState.absorber 0) := by
  simp [SignedTwinCarrier]

/-#############################################################################
  §6. Firewall package
#############################################################################-/

/--
The signed-integer firewall: adding the negative half of `ℤ` creates no new
Step00 engine and no legal same-projection gauge step.
-/
structure IntegerSignedFirewall (A M0 : ℕ) where
  signedStepProjects :
    ∀ {U V : SignedState},
      SignedRealStep A M0 U V →
      RealStep A M0 (projectSignedState U) (projectSignedState V)
  sameProjectionNoStep :
    ∀ {U V : SignedState},
      SignedGaugeEquivalent U V → ¬ SignedRealStep A M0 U V
  noSignedEngine :
    ¬ SignedEuclideanEngine A M0
  zeroCenterDegenerate :
    ¬ SignedTwinCarrier (SignedState.center 0)

/-- The concrete firewall is supplied by projection plus `lexRank`. -/
def integerSignedFirewall (A M0 : ℕ) : IntegerSignedFirewall A M0 where
  signedStepProjects := by
    intro U V h
    exact signedStep_projects_to_unsignedStep h
  sameProjectionNoStep := by
    intro U V hGauge
    exact same_projection_signed_step_impossible
      (A := A) (M0 := M0) hGauge
  noSignedEngine := by
    exact no_signedEuclideanEngine (A := A) (M0 := M0)
  zeroCenterDegenerate := by
    exact zero_center_not_signedTwinCarrier

/--
Final audit slogan as a proposition:

`ℤ` adds only signed gauge mirrors.  Any genuine signed engine descends to the
already-impossible unsigned engine.
-/
abbrev IntegerSignedFirewallSlogan (A M0 : ℕ) : Prop :=
  (∀ h : SignedEuclideanEngine A M0, False) ∧
  (∀ {U V : SignedState}, SignedGaugeEquivalent U V → ¬ SignedRealStep A M0 U V) ∧
  ¬ SignedTwinCarrier (SignedState.center 0)

/-- The signed firewall slogan follows from the concrete firewall package. -/
theorem integerSignedFirewall_slogan (A M0 : ℕ) :
    IntegerSignedFirewallSlogan A M0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact no_signedEuclideanEngine (A := A) (M0 := M0) h
  · intro U V hGauge
    exact same_projection_signed_step_impossible
      (A := A) (M0 := M0) hGauge
  · exact zero_center_not_signedTwinCarrier

/-! Machine honesty of the signed form -/

/-- HONESTY: the firewall is DEFINITIONAL. SignedRealStep is a pullback by
    construction, hence "signs add no dynamics" is a design choice fixed by an
    exact iff, not a theorem about independently given signed dynamics. -/
theorem signedRealStep_iff_projected {A M0 : ℕ} {U V : SignedState} :
    SignedRealStep A M0 U V ↔
      RealStep A M0 (projectSignedState U) (projectSignedState V) := by
  constructor
  · exact signedStep_projects_to_unsignedStep
  · exact SignedRealStep.ofProjected

/-- The projection is surjective: the signed layer is a full gauge fibration over
    the unsigned graph (fibers = sign choices), nothing is lost. -/
theorem projectSignedState_surjective :
    Function.Surjective projectSignedState := by
  intro W
  cases W with
  | center n => exact ⟨SignedState.center (n : ℤ), by simp [projectSignedState]⟩
  | defect n q s =>
      refine ⟨SignedState.defect (n : ℤ) q s, ?_⟩
      simp [projectSignedState]
  | absorber n => exact ⟨SignedState.absorber (n : ℤ), by simp [projectSignedState]⟩

/-- The concrete killing of a fake engine: the step `+k → −k` is impossible
    (both projections are center |k|). -/
theorem no_center_sign_flip_step {A M0 : ℕ} (z : ℤ) :
    ¬ SignedRealStep A M0 (SignedState.center z) (SignedState.center (-z)) :=
  same_projection_signed_step_impossible
    (by simp [SignedGaugeEquivalent, projectSignedState])

end ConcreteStep00Graph
end EuclidsPath
