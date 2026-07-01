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
