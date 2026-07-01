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

end ConcreteStep00Graph
end EuclidsPath
