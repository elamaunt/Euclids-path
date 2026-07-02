/-
  ConcreteStep00Graph — КОНКРЕТНЫЙ граф Step00 для ветки 6m±1 (не абстрактный σ) + лексикографическая высота.
  Источник: EuclidsPath_concrete_step00_graph_patch + EuclidsPath_step00_lex_height_patch.
  Проза: prose/24_BoundaryDecomp.md (раздел «Конкретный граф 6m±1 и lex-высота»).

  Строит реальный граф: State (center/defect/absorber), индуктивный RealStep (clean/boundary/peel/absorb)
  с арифметикой PeelCert (6n±1 = q·(6t±1)), Legal через Clean/делимость. НЕ вакуумен.
  ГЛАВНОЕ: `lexRank = 3·center + phase` (center=2,defect=1,absorber=0) СТРОГО ПАДАЕТ на КАЖДОМ ребре,
  включая absorb (где центр сохраняется — phase 1→0). Высота μ здесь ДОКАЗАНА, а не вход.
  Остаток bounded-пакета: ledger-проекция + ∞-семья дефектов + collision-resolve. НЕ закрывает Step00.
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

/-! ### §6–8. Безусловная (глобальная) ацикличность из lexRank

Убывающий ℕ-ранг `lexRank` САМ запрещает циклы (well-founded), без границы `B` и без co-height.
Источник: EuclidsPath_step00_lexRank_acyclic_patch. Anti-cycle сторона снята ГЛОБАЛЬНО. -/

/-- Ранг, строго убывающий вдоль ребра, слабо убывает вдоль любого пути. -/
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

/-- Строго убывающий ранг строго убывает вдоль НЕПУСТОГО пути. -/
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

/-- Строгий ℕ-спуск вдоль ребра запрещает непустой self-путь (прямой well-founded, без co-height). -/
theorem no_nonemptyPath_of_step_decrease
    {α : Type*} {R : α → α → Prop} {rank : α → ℕ}
    (hstep : ∀ {U V : α}, R U V → rank V < rank U) (W : α) :
    ¬ NonemptyPath R W W := by
  rintro ⟨n, hpos, hPathN⟩
  exact Nat.lt_irrefl (rank W)
    (pathN_rank_strict_of_pos_of_step_decrease (R := R) (rank := rank) hstep hpos hPathN)

/-- **Конкретный граф Step00 ацикличен ГЛОБАЛЬНО** (безусловно, из `lexRank`). -/
theorem no_concrete_nonemptyPath_by_lexRank {A M0 : ℕ} (W : State) :
    ¬ NonemptyPath (RealStep A M0) W W :=
  no_nonemptyPath_of_step_decrease (R := RealStep A M0) (rank := lexRank)
    (fun hStep => lexRank_strict_decrease_on_RealStep hStep) W

/-- Нет legal-цикла в конкретном графе (форма для ledger-collision). -/
theorem no_concrete_legalCycle_by_lexRank {A M0 : ℕ} :
    ¬ LegalCycle (RealStep A M0) (Legal A M0) := by
  rintro ⟨W, _hLegal, hPath⟩
  exact no_concrete_nonemptyPath_by_lexRank (A := A) (M0 := M0) W hPath

/-- ∞ свежих дефектов + collision-resolve ⟹ `False` НАПРЯМУЮ из `lexRank` (без границы `B`). -/
theorem infinite_fresh_defects_impossible_by_lexRank
    {A M0 : ℕ} {S : Set State}
    (proj : LedgerProjection A M0)
    (hS : InfiniteFreshDefectFamily A M0 S)
    (hResolve : ConcreteLedgerCollisionResolves A M0 proj) : False :=
  no_concrete_legalCycle_by_lexRank (A := A) (M0 := M0)
    (infinite_fresh_defects_force_concrete_cycle (A := A) (M0 := M0) (S := S) proj hS hResolve)

/-- Unbounded-пакет: без поля высоты и без `B` (anti-cycle = `lexRank`). -/
structure UnboundedConcreteStep00CollapsePackage (A M0 : ℕ) where
  proj : LedgerProjection A M0
  S : Set State
  infiniteFreshDefects : InfiniteFreshDefectFamily A M0 S
  collisionResolves : ConcreteLedgerCollisionResolves A M0 proj

/-- Любой unbounded-пакет схлопывается по `lexRank`. -/
theorem unboundedConcreteStep00CollapsePackage_false {A M0 : ℕ}
    (P : UnboundedConcreteStep00CollapsePackage A M0) : False :=
  infinite_fresh_defects_impossible_by_lexRank P.proj P.infiniteFreshDefects P.collisionResolves

/-- Остаток после глобальной ацикличности: ТРИ позитивных входа (proj, ∞-семья, resolve). -/
abbrev TheUnboundedConcreteGraphObligation (A M0 : ℕ) : Prop :=
  ∃ P : UnboundedConcreteStep00CollapsePackage A M0, True


/-! ### §9. ПРАВИЛЬНЫЙ неограниченный ledger-граф (не вакуумный: State ∞, Key конечен).
Источник: EuclidsPath_proper_unbounded_ledger_graph_patch. Заменяет вакуумный finite-strict:
пиджонхол на бесконечном подмножестве НЕОГРАНИЧЕННОГО State → конечный ledger-ключ. -/

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


/-! ### §10. Строгий аудит проекции Π (анти-читинг: запрет identity-ключа и скрытого центра).
Источник: EuclidsPath_semantic_ledger_strict_audit_patch. Не доказывает soundness Π —
машинно запрещает жульнические проекции; вся арифметика изолирована в SemanticLedgerCollisionResolves. -/

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



/-! ### §11. Generated-flow формулировка источника (кратность сохранена).
Источник: EuclidsPath_generated_flow_strict_formulation_patch. Пиджонхол на ГЕНЕАЛОГИЯХ
(поток = старт+непустой путь+ledger-терминал), не на состояниях — fan-in не стирается. -/

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


/-! ### Построение источника: generated-flow factory из чистого не-twin старта (7 кирпичей).
InfiniteCleanStarts закрыт КОНСТРУКТИВНЫМ primorial; well-founded flow-builder; cofactor-нормализатор
через реальную 6m±1 арифметику. Близнецы сведены к ОДНОМУ входу SemanticExtendedFlowLedgerCollisionResolves. -/
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
  -- извлечь свидетеля (q, делимость) из Prop-∃ в Type через .choose
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
(Prop-форма существования; данные извлекаются `.some` ниже.)
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
    have hcleanSide : ∀ q : ℕ, q.Prime → q ≤ A → ¬ q ∣ (6 * m - 1) := by
      intro q hq hqA
      exact clean_forbids_minus hClean hq hqA
    rcases EuclidsPath.Residuals.clean_side_composite_big_divisor
        (by omega) hcomp hcleanSide with ⟨b, hbPrime, hbBig, hbDiv⟩
    have hbDiv' : b ∣ sideValue Side.minus m := by simpa [sideValue] using hbDiv
    exact ⟨{ inSide := Side.minus
             bigDivisor := b
             bigPrime := hbPrime
             bigBeyondScale := hbBig
             bigDivides := hbDiv' }⟩
  · rcases hplus with ⟨hside, hcomp⟩
    have hcleanSide : ∀ q : ℕ, q.Prime → q ≤ A → ¬ q ∣ (6 * m + 1) := by
      intro q hq hqA
      exact clean_forbids_plus hClean hq hqA
    rcases EuclidsPath.Residuals.clean_side_composite_big_divisor
        (by omega) hcomp hcleanSide with ⟨b, hbPrime, hbBig, hbDiv⟩
    have hbDiv' : b ∣ sideValue Side.plus m := by simpa [sideValue] using hbDiv
    exact ⟨{ inSide := Side.plus
             bigDivisor := b
             bigPrime := hbPrime
             bigBeyondScale := hbBig
             bigDivides := hbDiv' }⟩

/-- Сырой большой делитель как данные (через `Classical.choice` из существования). -/
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
    smaller := T.smaller }

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
  refine ⟨
    { target := target
      outSide := outSide
      factor := ?_
      smaller := ?_ }⟩
  · -- Factor equality back in `ℕ`.
    have hc_eq : (c : ℤ) = 6 * t' + η' := by
      rw [← hquot_c, hcenter]
    have hc_center : (c : ℤ) = ((sideValue outSide target : ℕ) : ℤ) := by
      rw [hc_eq, ← hout]
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



end GeneratedFlowFormulation


/-! ### §12. Структурная аналогия P/NP (НЕ доказательство P≠NP и НЕ близнецов).
FORWARD (P): длина пути ≤ lexRank старта (доказано). REVERSE (NP): конечный ключ не восстанавливает
генеалогию (доказано). УЗЕЛ PolyCertificateSuffices = SemanticFlowLedgerCollisionResolves — вход. -/

namespace PvsNPAnalogy
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph.StrictLedgerAudit
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation


open EuclidsPath.LabelledFanIn
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph.StrictLedgerAudit
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-! ### §1. FORWARD = P: длина пути ограничена lexRank старта (полиномиальная проверка) -/

/--
**`pathN_len_le_lexRank` — ДОКАЗАНА.** Любой forward-путь длины `n` из `X` имеет `n ≤ lexRank X`.
Т.е. прямой ход двигателя «дёшев»: число шагов ограничено координатой старта (линейно по `lexRank`),
и проверка легальности пути — пошаговая. Это P-сторона аналогии. Следствие `lexRank`-спуска. -/
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

/-- Генеалогия имеет полиномиально-ограниченную длину: `steps ≤ lexRank (center start)`. -/
theorem generatedFlow_steps_le_lexRank {A M0 : ℕ} (F : GeneratedFlow A M0) :
    F.steps ≤ lexRank (State.center F.start) :=
  pathN_len_le_lexRank F.steps (State.center F.start) F.terminal F.path

/-- **`VerificationEasy` — форма P.** «Проверить генеалогию `F` дёшево»: длина ограничена `lexRank`
    старта (свидетель проверяется за число шагов ≤ координаты). Это ДОКАЗУЕМОЕ свойство графа. -/
def VerificationEasy {A M0 : ℕ} (F : GeneratedFlow A M0) : Prop :=
  F.steps ≤ lexRank (State.center F.start)

theorem verificationEasy_always {A M0 : ℕ} (F : GeneratedFlow A M0) : VerificationEasy F :=
  generatedFlow_steps_le_lexRank F

/-! ### §2. REVERSE = NP: конечный сертификат НЕ восстанавливает генеалогию (поиск не сжимается) -/

/--
**`SearchNotCompressible` — форма NP.** На бесконечной семье состояний конечный ключ проекции НЕ
определяет состояние (⟹ тем более не восстанавливает полную генеалогию). Т.е. «сжать обратный поиск
в полиномиальный сертификат» невозможно на уровне состояний. Прямое следствие §10-аудита. -/
def SearchNotCompressible {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) (S : Set State) : Prop :=
  ¬ KeyDeterminesStateOn proj S

/-- **`search_not_compressible_of_infinite` — ДОКАЗАНА.** Для любой конечной проекции на бесконечной
    семье поиск не сжимается: ключ теряет информацию. Это NP-сторона: сертификат не эквивалентен
    полному обратному пути. -/
theorem search_not_compressible_of_infinite {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State} (hInf : S.Infinite) :
    SearchNotCompressible proj S :=
  finite_key_cannot_determine_state_on_infinite proj hInf

/-! ### §3. АНАЛОГИЯ КАК ТЕОРЕМА: verify и search структурно различны (не лозунг)

FORWARD ограничен lexRank (доказано), REVERSE не сжимается в конечный ключ (доказано). Значит
«проверка» и «поиск» здесь разделены МАШИННО: verify всегда лёгок, а сжатие поиска — невозможно. -/

/--
**`verify_easy_but_search_not_compressible` — ДОКАЗАНА (аналогия как факт).** Одновременно:
(1) КАЖДАЯ генеалогия проверяется дёшево (`VerificationEasy`, ограничение `lexRank`); и
(2) на бесконечной семье поиск НЕ сжимается в конечный ключ (`SearchNotCompressible`).
Это машинная форма асимметрии «проверка легка / поиск не сжимается» — структурная тень P vs NP,
БЕЗ утверждения P≠NP. -/
theorem verify_easy_but_search_not_compressible {A M0 : ℕ}
    (proj : SemanticLedgerProjection A M0) {S : Set State} (hInf : S.Infinite) :
    (∀ F : GeneratedFlow A M0, VerificationEasy F) ∧ SearchNotCompressible proj S :=
  ⟨verificationEasy_always, search_not_compressible_of_infinite proj hInf⟩

/-! ### §4. УЗЕЛ: «полиномиальный сертификат достаточен» = SemanticFlowLedgerCollisionResolves

Оставшийся вход в одежде P/NP: «конечный (полиномиальный) сертификат обратного пути РЕШАЕТ, что
коллизия двух генеалогий = настоящий цикл». Это РОВНО SemanticFlowLedgerCollisionResolves. НЕ доказан —
и §2 показывает почему: сертификат теряет информацию, поэтому «сертификата достаточно» — доп. арифметика. -/

/-- **`PolyCertificateSuffices` (вход).** Псевдоним для `SemanticFlowLedgerCollisionResolves` в
    P/NP-терминах: конечный сертификат коллизии генеалогий достаточен, чтобы вывести резолюцию
    (цикл ∨ невозможная оплата). НЕ доказан. -/
def PolyCertificateSuffices {A M0 : ℕ} (proj : SemanticFlowLedgerProjection A M0) : Prop :=
  SemanticFlowLedgerCollisionResolves proj

/--
**`branch_closes_if_polyCertificateSuffices` — ДОКАЗАНА (условно на узле).** ЕСЛИ полиномиальный
сертификат достаточен (`PolyCertificateSuffices`) И есть бесконечная семья генеалогий, ТО ветка
схлопывается (`False`) — зеркало `generatedFlowStep00Package_false`. Узел НЕ предъявлен: это тот же
несводимый вход близнецов, лишь названный по-P/NP. -/
theorem branch_closes_if_polyCertificateSuffices {A M0 : ℕ}
    (proj : SemanticFlowLedgerProjection A M0)
    {𝓕 : Set (GeneratedFlow A M0)}
    (h𝓕 : InfiniteGeneratedFlowFamily A M0 𝓕)
    (hCert : PolyCertificateSuffices proj) :
    False :=
  infinite_generated_flows_impossible_with_resolution proj h𝓕 hCert


end PvsNPAnalogy

end ConcreteStep00Graph
end EuclidsPath
