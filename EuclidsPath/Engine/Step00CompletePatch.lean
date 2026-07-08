/-
  Step00CompletePatch.lean

  One-file patch containing the new material developed after inspecting
  `euclids-path-code-only.lean`:

  1. Audit: finite-key semantic resolution is injectivity, hence equivalent
     to finiteness of `ExtendedProperGeneratedFlow`.
  2. Adic refutation: a parametrized `p ≡ -1 mod 6*oldPrimorial A` chain
     gives infinitely many extended generated flows at fixed horizon.
  3. Consequence: `¬ TheStrictLastStep00Obligation`; with the existing
     `step00FirstCause` axiom this yields `False`.
  4. Unit pump: “+1 fuel per step” as `RawWork - 1`, converted to
     ordinary `PaidDynamics`.
  5. Time pump: “time cannot stop”; a live state must close or tick.
     If close violations are ruled out, the engine forces a twin above
     the horizon.

  Intended location in the project:
    EuclidsPath/Engine/Step00CompletePatch.lean

  Imports the existing axiom file deliberately, because the final theorem
  `step00FirstCause_inconsistent` is an audit result showing that the old
  first-cause axiom is incompatible with the arithmetic-flow machinery.
-/

import EuclidsPath.Engine.CausalClosureAxiom
import EuclidsPath.Engine.PaidDynamics
import EuclidsPath.Engine.HigherEnergy

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace Step00CompletePatch

open EuclidsPath.Residuals
open EuclidsPath.PaidDynamics
open EuclidsPath.HigherEnergy
open EuclidsPath.CleanGraph
open EuclidsPath.LabelledFanIn
open EuclidsPath.BoundaryLedgerCollision
open EuclidsPath.BoundaryDefectPayment
open EuclidsPath.ConcreteStep00Graph.ProperUnboundedLedgerGraph

/-!
## Part I: audit of the old finite-key Step00 obligation
-/

theorem resolves_iff_keyFlow_injective {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    SemanticExtendedFlowLedgerCollisionResolves proj ↔
      Function.Injective proj.keyFlow := by
  constructor
  · intro hRes F₁ F₂ hkey
    by_contra hne
    have hNoKey :
        proj.keyFlow F₁ ≠ proj.keyFlow F₂ :=
      (resolves_iff_key_injective proj).mp hRes
        F₁ F₂ hne
        (extendedFlow_admissible F₁)
        (extendedFlow_admissible F₂)
    exact hNoKey hkey
  · intro hInj
    exact (resolves_iff_key_injective proj).mpr
      (by
        intro F₁ F₂ hne _ _ hkey
        exact hne (hInj hkey))

theorem strictResolves_iff_keyFlow_injective {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    StrictSemanticExtendedFlowLedgerCollisionResolves proj ↔
      Function.Injective proj.keyFlow := by
  exact (strictResolves_iff_resolves proj).trans
    (resolves_iff_keyFlow_injective proj)

theorem exists_strictResolver_iff_finite_extendedFlows (A M0 : ℕ) :
    (∃ proj : SemanticExtendedFlowLedgerProjection A M0,
      StrictSemanticExtendedFlowLedgerCollisionResolves proj)
    ↔ Finite (ExtendedProperGeneratedFlow A M0) := by
  constructor
  · rintro ⟨proj, hRes⟩
    letI : Finite proj.Key := proj.finiteKey
    letI : Fintype proj.Key := Fintype.ofFinite proj.Key
    have hInj : Function.Injective proj.keyFlow :=
      (strictResolves_iff_keyFlow_injective proj).mp hRes
    letI : Fintype (ExtendedProperGeneratedFlow A M0) :=
      Fintype.ofInjective proj.keyFlow hInj
    exact inferInstance
  · intro hFin
    let proj : SemanticExtendedFlowLedgerProjection A M0 :=
      { Key := ExtendedProperGeneratedFlow A M0
        finiteKey := hFin
        keyFlow := fun F => F }
    refine ⟨proj, ?_⟩
    exact (strictResolves_iff_keyFlow_injective proj).mpr
      (by
        intro F₁ F₂ h
        exact h)

theorem strictLastStep00Obligation_iff_exists_scale_all_extendedFlows_finite :
    TheStrictLastStep00Obligation ↔
      ∃ A : ℕ, ∀ M0 : ℕ, Finite (ExtendedProperGeneratedFlow A M0) := by
  constructor
  · rintro ⟨A, projOf, hAll⟩
    refine ⟨A, ?_⟩
    intro M0
    exact (exists_strictResolver_iff_finite_extendedFlows A M0).mp
      ⟨projOf M0, hAll M0⟩
  · rintro ⟨A, hFin⟩
    refine ⟨A,
      (fun M0 =>
        { Key := ExtendedProperGeneratedFlow A M0
          finiteKey := hFin M0
          keyFlow := fun F => F }),
      ?_⟩
    intro M0
    exact
      (strictResolves_iff_keyFlow_injective
        ({ Key := ExtendedProperGeneratedFlow A M0
           finiteKey := hFin M0
           keyFlow := fun F => F } :
          SemanticExtendedFlowLedgerProjection A M0)).mpr
        (by
          intro F₁ F₂ h
          exact h)

/-!
## Part II: adic chain refutation of the old Step00 obligation

The chain uses a prime `p` with
  p + 1 = 6 * (t * oldPrimorial A),
so each center is a multiple of `oldPrimorial A` and therefore clean.
-/

structure GoodAdicPrimeData (A : ℕ) where
  p : ℕ
  t : ℕ
  pPrime : p.Prime
  t_pos : 0 < t
  pBeyondScale : A < p
  p_plus_one_eq : p + 1 = 6 * (t * oldPrimorial A)

def adicCoeffChain {A : ℕ} (D : GoodAdicPrimeData A) : ℕ → ℕ
  | 0 => 1
  | k + 1 => D.p * adicCoeffChain D k + D.t

def adicCenter {A : ℕ} (D : GoodAdicPrimeData A) (k : ℕ) : ℕ :=
  adicCoeffChain D k * oldPrimorial A

theorem adicCoeffChain_pos {A : ℕ} (D : GoodAdicPrimeData A) :
    ∀ k, 1 ≤ adicCoeffChain D k
  | 0 => by
      simp [adicCoeffChain]
  | k + 1 => by
      have ht : 1 ≤ D.t := Nat.succ_le_of_lt D.t_pos
      simp [adicCoeffChain]
      omega

theorem adicCoeffChain_lt_succ {A : ℕ} (D : GoodAdicPrimeData A) (k : ℕ) :
    adicCoeffChain D k < adicCoeffChain D (k + 1) := by
  have hp : 1 ≤ D.p := Nat.succ_le_of_lt D.pPrime.pos
  have ht : 0 < D.t := D.t_pos
  have hmul :
      adicCoeffChain D k ≤ D.p * adicCoeffChain D k := by
    calc
      adicCoeffChain D k = 1 * adicCoeffChain D k := by ring
      _ ≤ D.p * adicCoeffChain D k :=
        Nat.mul_le_mul_right _ hp
  change adicCoeffChain D k < D.p * adicCoeffChain D k + D.t
  exact lt_of_le_of_lt hmul (Nat.lt_add_of_pos_right ht)

theorem adicCoeffChain_strictMono {A : ℕ} (D : GoodAdicPrimeData A) :
    StrictMono (adicCoeffChain D) :=
  strictMono_nat_of_lt_succ (adicCoeffChain_lt_succ D)

theorem adicCenter_pos {A : ℕ} (D : GoodAdicPrimeData A) (k : ℕ) :
    1 ≤ adicCenter D k := by
  unfold adicCenter
  have hc : 1 ≤ adicCoeffChain D k := adicCoeffChain_pos D k
  have hP : 0 < oldPrimorial A := oldPrimorial_pos A
  exact Nat.succ_le_of_lt
    (Nat.mul_pos (Nat.succ_le_iff.mp hc) hP)

theorem adicCenter_strictMono {A : ℕ} (D : GoodAdicPrimeData A) :
    StrictMono (adicCenter D) := by
  intro i j hij
  unfold adicCenter
  have hcoeff : adicCoeffChain D i < adicCoeffChain D j :=
    adicCoeffChain_strictMono D hij
  have hP : 0 < oldPrimorial A := oldPrimorial_pos A
  exact Nat.mul_lt_mul_of_pos_right hcoeff hP

theorem adicCenter_clean {A : ℕ} (D : GoodAdicPrimeData A) (k : ℕ) :
    Clean A (adicCenter D k) := by
  apply clean_of_cleanZ_nat
  · exact adicCenter_pos D k
  · simpa [adicCenter] using
      primorial_multiple_clean A
        (adicCoeffChain D k)
        (adicCoeffChain_pos D k)

theorem adicCenter_zero {A : ℕ} (D : GoodAdicPrimeData A) :
    adicCenter D 0 = oldPrimorial A := by
  simp [adicCenter, adicCoeffChain]

theorem adicCenter_factor {A : ℕ}
    (D : GoodAdicPrimeData A) (k : ℕ) :
    sideValue Side.minus (adicCenter D (k + 1)) =
      D.p * sideValue Side.plus (adicCenter D k) := by
  simp [sideValue, adicCenter, adicCoeffChain]
  have hmain :
      6 * ((D.p * adicCoeffChain D k + D.t) * oldPrimorial A)
        =
      D.p * (6 * (adicCoeffChain D k * oldPrimorial A) + 1) + 1 := by
    nlinarith [D.p_plus_one_eq]
  omega

def adicChainPeel {A : ℕ} (D : GoodAdicPrimeData A) (k : ℕ) :
    ProperCenterPeel A (adicCenter D (k + 1)) (adicCenter D k) :=
  { inSide := Side.minus
    outSide := Side.plus
    bigDivisor := D.p
    bigPrime := D.pPrime
    bigBeyondScale := D.pBeyondScale
    factor := adicCenter_factor D k
    smaller := by
      exact adicCenter_strictMono D (Nat.lt_succ_self k)
    targetPos := adicCenter_pos D k }

theorem adicChainPath {A : ℕ} (D : GoodAdicPrimeData A) :
    ∀ k, PathN (ProperRealStep A (oldPrimorial A)) k
      (State.center (adicCenter D k))
      (State.center (oldPrimorial A)) := by
  intro k
  induction k with
  | zero =>
      show State.center (adicCenter D 0) = State.center (oldPrimorial A)
      rw [adicCenter_zero]
  | succ n ih =>
      exact ⟨State.center (adicCenter D n),
        ProperRealStep.clean
          (adicCenter_clean D (n + 1))
          (adicCenter_clean D n)
          (adicChainPeel D n),
        ih⟩

def adicChainFlow {A : ℕ} (D : GoodAdicPrimeData A) (k : ℕ) :
    ExtendedProperGeneratedFlow A (oldPrimorial A) :=
  { start := adicCenter D (k + 1)
    terminal := State.center (oldPrimorial A)
    steps := k + 1
    nonempty := Nat.succ_pos k
    properPath := adicChainPath D (k + 1)
    startClean := adicCenter_clean D (k + 1)
    startFresh := by
      have h :
          adicCenter D 0 < adicCenter D (k + 1) :=
        adicCenter_strictMono D (Nat.succ_pos k)
      simpa [adicCenter, adicCoeffChain] using h
    terminalLegal := by
      have h := legal_of_oldCleanCenter (M0 := oldPrimorial A) (adicCenter_clean D 0)
      rwa [adicCenter_zero] at h
    ledgerTerminal := by
      exact extendedLedgerTerminal_oldCleanCenter le_rfl
        (by
          simpa [adicCenter, adicCoeffChain] using adicCenter_clean D 0) }

theorem adicChainFlow_injective {A : ℕ} (D : GoodAdicPrimeData A) :
    Function.Injective (adicChainFlow D) := by
  intro k₁ k₂ h
  have hstart :
      adicCenter D (k₁ + 1) = adicCenter D (k₂ + 1) :=
    congrArg ExtendedProperGeneratedFlow.start h
  have hk :
      k₁ + 1 = k₂ + 1 :=
    (adicCenter_strictMono D).injective hstart
  omega

theorem adicChainFlowFamily_infinite {A : ℕ} (D : GoodAdicPrimeData A) :
    InfiniteExtendedGeneratedFlowFamily A (oldPrimorial A)
      (Set.range (adicChainFlow D)) :=
  ⟨Set.infinite_range_of_injective (adicChainFlow_injective D),
   fun F _ => extendedFlow_admissible F⟩

theorem no_projection_resolves_at_adicPrimorialScale
    {A : ℕ} (D : GoodAdicPrimeData A)
    (proj : SemanticExtendedFlowLedgerProjection A (oldPrimorial A)) :
    ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  intro hRes
  exact infinite_extended_flows_impossible_with_resolution
    (A := A)
    (M0 := oldPrimorial A)
    proj
    (adicChainFlowFamily_infinite D)
    hRes

theorem no_projection_strictResolves_at_adicPrimorialScale
    {A : ℕ} (D : GoodAdicPrimeData A)
    (proj : SemanticExtendedFlowLedgerProjection A (oldPrimorial A)) :
    ¬ StrictSemanticExtendedFlowLedgerCollisionResolves proj := by
  intro hStrict
  exact no_projection_resolves_at_adicPrimorialScale D proj
    (strictSemanticExtended_resolves_old hStrict)

theorem not_theStrictLastStep00Obligation_of_goodAdicData
    (hGood : ∀ A : ℕ, Nonempty (GoodAdicPrimeData A)) :
    ¬ TheStrictLastStep00Obligation := by
  rintro ⟨A, projOf, hAll⟩
  rcases hGood A with ⟨D⟩
  exact no_projection_strictResolves_at_adicPrimorialScale D
    (projOf (oldPrimorial A))
    (hAll (oldPrimorial A))

/-!
### Dirichlet input for `GoodAdicPrimeData`
-/

def adicModulus (A : ℕ) : ℕ :=
  6 * oldPrimorial A

theorem adicModulus_pos (A : ℕ) :
    0 < adicModulus A := by
  unfold adicModulus
  exact Nat.mul_pos (by norm_num) (oldPrimorial_pos A)

theorem adicModulus_pred_coprime (A : ℕ) :
    Nat.Coprime (adicModulus A - 1) (adicModulus A) := by
  have hEq : adicModulus A = (adicModulus A - 1) + 1 := by
    have hQ : 0 < adicModulus A := adicModulus_pos A
    omega
  rw [hEq]
  exact Nat.coprime_self_add_right.mpr
    (Nat.coprime_one_right (adicModulus A - 1))

theorem adicPrime_unbounded (A N : ℕ) :
    ∃ p : ℕ,
      N < p ∧
      p.Prime ∧
      p ≡ adicModulus A - 1 [MOD adicModulus A] := by
  exact Nat.forall_exists_prime_gt_and_modEq
    N
    (q := adicModulus A)
    (a := adicModulus A - 1)
    (adicModulus_pos A).ne'
    (adicModulus_pred_coprime A)

theorem exists_t_of_mod_pred
    {Q p : ℕ}
    (hQ : 0 < Q)
    (hmod : p ≡ Q - 1 [MOD Q]) :
    ∃ t : ℕ, 0 < t ∧ p + 1 = Q * t := by
  have hpmod : p % Q = Q - 1 := by
    have hmod' : p % Q = (Q - 1) % Q := by
      simpa [Nat.ModEq] using hmod
    have hpred : (Q - 1) % Q = Q - 1 := by
      exact Nat.mod_eq_of_lt (by omega)
    simpa [hpred] using hmod'
  refine ⟨p / Q + 1, Nat.succ_pos _, ?_⟩
  have hdivmod : p / Q * Q + p % Q = p :=
    Nat.div_add_mod' p Q
  have hdecomp : p / Q * Q + (Q - 1) = p := by
    simpa [hpmod] using hdivmod
  calc
    p + 1 = (p / Q * Q + (Q - 1)) + 1 := by
      rw [hdecomp]
    _ = p / Q * Q + Q := by
      omega
    _ = Q * (p / Q + 1) := by
      ring

theorem goodAdicPrimeData_exists (A : ℕ) :
    Nonempty (GoodAdicPrimeData A) := by
  let Q := adicModulus A
  obtain ⟨p, hpGt, hpPrime, hpMod⟩ :=
    adicPrime_unbounded A (max A Q)
  have hA_lt_p : A < p :=
    lt_of_le_of_lt (le_max_left A Q) hpGt
  have hQ_pos : 0 < Q := by
    simpa [Q] using adicModulus_pos A
  obtain ⟨t, ht_pos, ht_eq⟩ :=
    exists_t_of_mod_pred hQ_pos hpMod
  refine ⟨
    { p := p
      t := t
      pPrime := hpPrime
      t_pos := ht_pos
      pBeyondScale := hA_lt_p
      p_plus_one_eq := ?_ }⟩
  have hQdef : Q = 6 * oldPrimorial A := by
    simp [Q, adicModulus]
  calc
    p + 1 = Q * t := ht_eq
    _ = (6 * oldPrimorial A) * t := by rw [hQdef]
    _ = 6 * (t * oldPrimorial A) := by ring

theorem not_theStrictLastStep00Obligation :
    ¬ TheStrictLastStep00Obligation := by
  exact not_theStrictLastStep00Obligation_of_goodAdicData
    goodAdicPrimeData_exists

theorem not_theLastStep00Obligation :
    ¬ TheLastStep00Obligation := by
  intro H
  exact not_theStrictLastStep00Obligation
    ((strictLastStep00Obligation_iff_lastStep00Obligation).mpr H)

/-!
### The old first-cause node becomes inconsistent if imported.
-/

theorem step00FirstCause_inconsistent : False := by
  exact quarantine_inconsistent_if_node_refuted
    not_theStrictLastStep00Obligation

theorem step00FirstCause_inconsistent_direct : False := by
  exact not_theStrictLastStep00Obligation step00CausalClosure

/-!
## Part III: unit pump layer — “+1 fuel per step”
-/

structure UnitPumpedDynamics
    (σ : Type)
    (Step : σ → σ → Prop) where
  Total : σ → ℕ
  RawWork : σ → σ → ℕ
  rawWork_ge_two :
    ∀ {x y : σ}, Step x y → 2 ≤ RawWork x y
  paid_with_one :
    ∀ {x y : σ}, Step x y →
      Total y + RawWork x y ≤ Total x + 1

def UnitPumpedDynamics.netWork
    {σ : Type}
    {Step : σ → σ → Prop}
    (D : UnitPumpedDynamics σ Step)
    (x y : σ) : ℕ :=
  D.RawWork x y - 1

def UnitPumpedDynamics.toPaidDynamics
    {σ : Type}
    {Step : σ → σ → Prop}
    (D : UnitPumpedDynamics σ Step) :
    PaidDynamics σ Step where
  Total := D.Total
  Work := D.netWork
  work_pos := by
    intro x y hStep
    unfold UnitPumpedDynamics.netWork
    have hW : 2 ≤ D.RawWork x y :=
      D.rawWork_ge_two hStep
    omega
  paid := by
    intro x y hStep
    unfold UnitPumpedDynamics.netWork
    have hPaid :
        D.Total y + D.RawWork x y ≤ D.Total x + 1 :=
      D.paid_with_one hStep
    have hW : 2 ≤ D.RawWork x y :=
      D.rawWork_ge_two hStep
    omega

theorem unitPumped_strict_drop
    {σ : Type}
    {Step : σ → σ → Prop}
    (D : UnitPumpedDynamics σ Step)
    {x y : σ}
    (hStep : Step x y) :
    D.Total y < D.Total x := by
  exact paidDynamics_strict_drop D.toPaidDynamics hStep

theorem unitPumped_no_infinite_run
    {σ : Type}
    {Step : σ → σ → Prop}
    (D : UnitPumpedDynamics σ Step) :
    ¬ ∃ path : ℕ → σ,
      ∀ k, Step (path k) (path (k + 1)) := by
  exact no_infinite_paid_run D.toPaidDynamics

def rawWorkFromRank
    {σ : Type}
    (rank : σ → ℕ)
    (x y : σ) : ℕ :=
  rank x - rank y + 1

def unitPumped_of_strictRankDrop
    {σ : Type}
    {Step : σ → σ → Prop}
    (rank : σ → ℕ)
    (hdrop : ∀ {x y : σ}, Step x y → rank y < rank x) :
    UnitPumpedDynamics σ Step where
  Total := rank
  RawWork := rawWorkFromRank rank
  rawWork_ge_two := by
    intro x y hStep
    unfold rawWorkFromRank
    have h : rank y < rank x := hdrop hStep
    omega
  paid_with_one := by
    intro x y hStep
    unfold rawWorkFromRank
    have h : rank y < rank x := hdrop hStep
    omega

def properRealStepUnitPump
    (A M0 : ℕ) :
    UnitPumpedDynamics State (ProperRealStep A M0) :=
  unitPumped_of_strictRankDrop
    lexRank
    (by
      intro U V hStep
      exact lexRank_strict_decrease_on_RealStep
        (properRealStep_to_realStep hStep))

theorem properRealStep_unitPumped_strict_drop
    {A M0 : ℕ}
    {U V : State}
    (hStep : ProperRealStep A M0 U V) :
    lexRank V < lexRank U := by
  exact unitPumped_strict_drop
    (properRealStepUnitPump A M0)
    hStep

theorem no_infinite_properRealStep_run
    (A M0 : ℕ) :
    ¬ ∃ path : ℕ → State,
      ∀ k, ProperRealStep A M0 (path k) (path (k + 1)) := by
  exact unitPumped_no_infinite_run
    (properRealStepUnitPump A M0)

theorem properRealStep_path_budget
    (A M0 : ℕ)
    (path : ℕ → State)
    (hStep : ∀ k, ProperRealStep A M0 (path k) (path (k + 1))) :
    ∀ n,
      (∑ k ∈ Finset.range n,
        (properRealStepUnitPump A M0).toPaidDynamics.Work
          (path k)
          (path (k + 1)))
        + (properRealStepUnitPump A M0).toPaidDynamics.Total (path n)
      ≤ (properRealStepUnitPump A M0).toPaidDynamics.Total (path 0) := by
  exact paidDynamics_path_budget
    (properRealStepUnitPump A M0).toPaidDynamics
    path
    hStep

/-!
## Part IV: time pump — “time cannot stop”

A live state must either close or tick.  If close never occurs,
well-founded descent forbids the live state from existing.
-/

structure TimeSerialRankEngine
    (σ : Type)
    (Step : σ → σ → Prop) where
  Live : σ → Prop
  Close : σ → Prop
  Rank : σ → ℕ
  step_or_close :
    ∀ x, Live x → Close x ∨ ∃ y, Live y ∧ Step x y
  rank_drops :
    ∀ {x y : σ}, Live x → Step x y → Rank y < Rank x

theorem timeSerialRankEngine_forces_close
    {σ : Type}
    {Step : σ → σ → Prop}
    (E : TimeSerialRankEngine σ Step)
    (hStart : ∃ x, E.Live x) :
    ∃ x, E.Live x ∧ E.Close x := by
  by_contra hNoCloseExists
  have hNoClose :
      ∀ x, E.Live x → ¬ E.Close x := by
    intro x hx hcx
    exact hNoCloseExists ⟨x, hx, hcx⟩
  have hNoLive :
      ¬ ∃ x, E.Live x := by
    exact no_live_state_if_closes_or_moves_down
      E.Live
      E.Close
      (fun x y => E.Live x ∧ Step x y)
      (fun x => (E.Rank x, 0))
      (by
        intro x hx
        rcases E.step_or_close x hx with hClose | ⟨y, hyLive, hStep⟩
        · exact Or.inl hClose
        · exact Or.inr ⟨y, hyLive, hx, hStep⟩)
      hNoClose
      (by
        intro x y hMove
        exact Or.inl (E.rank_drops hMove.1 hMove.2))
  exact hNoLive hStart

def TwinClose (M0 : ℕ) : State → Prop
  | State.center m => M0 < m ∧ TwinCenterZ m
  | _              => False

structure TimeStopViolation
    (A M0 : ℕ)
    (Live : State → Prop)
    (U : State) : Prop where
  live : Live U
  not_twin : ¬ TwinClose M0 U
  stuck : ¬ ∃ V, Live V ∧ ProperRealStep A M0 U V

def TimeClose
    (A M0 : ℕ)
    (Live : State → Prop)
    (U : State) : Prop :=
  TwinClose M0 U ∨ TimeStopViolation A M0 Live U

structure ProperTimePumpEngine (A M0 : ℕ) where
  Live : State → Prop
  start_live : ∃ U, Live U
  step_or_close :
    ∀ U, Live U →
      TimeClose A M0 Live U ∨
      ∃ V, Live V ∧ ProperRealStep A M0 U V

def ProperTimePumpEngine.toRankEngine
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    TimeSerialRankEngine State (ProperRealStep A M0) where
  Live := E.Live
  Close := TimeClose A M0 E.Live
  Rank := lexRank
  step_or_close := E.step_or_close
  rank_drops := by
    intro U V hLive hStep
    exact lexRank_strict_decrease_on_RealStep
      (properRealStep_to_realStep hStep)

theorem properTimePumpEngine_forces_close
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    ∃ U, E.Live U ∧ TimeClose A M0 E.Live U := by
  exact timeSerialRankEngine_forces_close
    E.toRankEngine
    E.start_live

theorem properTimePumpEngine_forces_twin_or_violation
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0) :
    (∃ m : ℕ, M0 < m ∧ TwinCenterZ m) ∨
    (∃ U : State, E.Live U ∧ TimeStopViolation A M0 E.Live U) := by
  obtain ⟨U, hLive, hClose⟩ :=
    properTimePumpEngine_forces_close E
  rcases hClose with hTwin | hViolation
  · cases U with
    | center m =>
        exact Or.inl ⟨m, hTwin.1, hTwin.2⟩
    | defect n q s =>
        simp [TwinClose] at hTwin
    | absorber n =>
        simp [TwinClose] at hTwin
  · exact Or.inr ⟨U, hLive, hViolation⟩

theorem properTimePumpEngine_forces_twin
    {A M0 : ℕ}
    (E : ProperTimePumpEngine A M0)
    (hNoViolation :
      ∀ U, E.Live U → ¬ TimeStopViolation A M0 E.Live U) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  rcases properTimePumpEngine_forces_twin_or_violation E with hTwin | hBad
  · exact hTwin
  · rcases hBad with ⟨U, hLive, hViolation⟩
    exact False.elim ((hNoViolation U hLive) hViolation)

abbrev TimePumpStep00Obligation : Prop :=
  ∀ M0 : ℕ,
    ∃ A : ℕ,
      ∃ E : ProperTimePumpEngine A M0,
        ∀ U, E.Live U → ¬ TimeStopViolation A M0 E.Live U

theorem twinCenters_unbounded_of_timePumpStep00
    (H : TimePumpStep00Obligation) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  rcases H M0 with ⟨A, E, hNoViolation⟩
  exact properTimePumpEngine_forces_twin E hNoViolation

theorem twinLowersInfinite_of_timePumpStep00
    (H : TimePumpStep00Obligation) :
    TwinLowers.Infinite := by
  apply EuclidsPath.infinite_of_unbounded_centers
  intro N
  obtain ⟨m, hNm, hTwinZ⟩ :=
    twinCenters_unbounded_of_timePumpStep00 H N
  refine ⟨m, hNm, ?_⟩
  simpa [EuclidsPath.Residuals.TwinCenterZ, EuclidsPath.IsTwinCenter] using hTwinZ

/-!
## Summary theorem for the new replacement direction

This theorem is the clean replacement for the old finite-key Step00 route:
`TimePumpStep00Obligation` implies twin infinitude without requiring a
finite global collision resolver.
-/

theorem timePumpStep00_generates_twins :
    TimePumpStep00Obligation → TwinLowers.Infinite :=
  twinLowersInfinite_of_timePumpStep00

end Step00CompletePatch
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
