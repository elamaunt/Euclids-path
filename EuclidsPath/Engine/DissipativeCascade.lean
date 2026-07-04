/-
  DissipativeCascade — dissipative cascade certificate: decomposition of the Liouville-localisation node.
  Source: dissipative cascade blueprint (Step00 / RH / Navier–Stokes analogy).
  Prose: prose/24_BoundaryDecomp.md (section "Dissipative cascade and capacity/overflow").

  IDEA (shared by Step00 / RH / NS): "a defect cannot vanish; if it does not close, it must
  move and pay". This is already embodied in `ClosedUniverse.no_infinite_closed_paid_run`,
  `DichotomyEngine.close_forced`, `RankJumpBridge` (rank/parity). Here — the NEW part: **capacity /
  overflow** decomposition of the node `RankJumpLocalization` (Liouville imbalance ⟹ twin-jump) into two smaller ones:
    (1) irrelevant-cancellation (the irrelevant part does not overflow the bound);
    (2) pairing (the relevant imbalance does not fit into the cancelling pairs ⟹ jump).

  PROVED HERE (pure sums/triangle, std axioms, no sorry):
    * `L_eq_relevant_add_irrelevant` (§10, `Finset.sum_union` — blueprint sorry CLOSED);
    * `relevantViolation_of_globalViolation` (§10 overflow, triangle — blueprint sorry CLOSED);
    * `twinJump_of_relevantViolation` / assembly (§11).

  HONEST BOUNDARY. This is NOT a proof of RH/NS/twins. Analytic inputs remain: `IrrelevantCancellation`
  (bound on the irrelevant part) and `TwinCarrierPairing.unpaired_gives_jump` — they replace the larger
  `RankJumpLocalization`, but are themselves unproved. ℝ-budget caveat (§2): unlike the ℕ-engine, strictly
  positive work over ℝ does NOT give well-foundedness (series 1/2^n) — so the NS analogy is structural only.
-/
import Mathlib
import EuclidsPath.Engine.RankJumpBridge

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.DissipativeCascade

open scoped BigOperators
open ArithmeticFunction
open EuclidsPath.RankJumpBridge

/-! ### §2. ℕ-budget vs ℝ-budget: why the NS analogy is structural only (machine counterexample)

For the ℕ-engine `Total y + Work ≤ Total x` with `0 < Work` gives `Total y < Total x` ⟹ well-founded.
For ℝ strictly positive work does NOT forbid an infinite descending series (`1/2^n`). We fix this machine-verifiably. -/

/-- **`real_positive_work_not_wellfounded` — PROVED (§2 warning).** There exists an ℝ-sequence
    with strictly positive "work step" at each step, but a finite total descent: `a n = 1/2^n`.
    Hence ℝ-dissipation without quantisation/rank does NOT give finiteness — unlike the ℕ-engine. -/
theorem real_positive_work_not_wellfounded :
    ∃ a : ℕ → ℝ, (∀ n, a (n + 1) < a n) ∧ (∀ n, 0 < a n) ∧ (∀ n, 0 < a n - a (n + 1)) := by
  refine ⟨fun n => (1 / 2) ^ n, ?_, ?_, ?_⟩
  · intro n
    simp only
    have h : (0:ℝ) < (1/2) ^ n := by positivity
    calc (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
      _ < (1/2) ^ n * 1 := by nlinarith
      _ = (1/2) ^ n := by ring
  · intro n; simp only; positivity
  · intro n
    simp only
    have h : (0:ℝ) < (1/2) ^ n := by positivity
    have he : (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
    rw [he]; nlinarith

/-! ### §2bis. Quantisation SAVES the ℝ-cascade (completing the §2 warning)

The §2 counterexample showed: positive work over ℝ does not give finiteness. Here is the EXACT remedy (option 3
of the blueprint): a uniform lower bound δ on the dissipation of a bad step. This is the form of a genuine NS certificate:
"every cascade transition to a smaller scale dissipates ≥ δ" ⟹ the cascade is finite. -/

/-- **`real_cascade_bounded_of_uniform_work` — PROVED (quantisation).** Under uniform δ-dissipation
    the accumulated work after n steps is ≤ E(0): `n·δ ≤ Total(path 0)`. -/
theorem real_cascade_bounded_of_uniform_work
    {State : Type} {Step : State → State → Prop}
    (Total : State → ℝ) (Work : State → State → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hpaid : ∀ {x y}, Step x y → Total y + Work x y ≤ Total x)
    (hwork : ∀ {x y}, Step x y → δ ≤ Work x y)
    (hnonneg : ∀ x, 0 ≤ Total x)
    (path : ℕ → State) (hstep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ n : ℕ, (n : ℝ) * δ ≤ Total (path 0) := by
  intro n
  have key : ∀ m : ℕ, Total (path m) + (m : ℝ) * δ ≤ Total (path 0) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        have hp := hpaid (hstep k)
        have hw := hwork (hstep k)
        have : Total (path (k+1)) + δ ≤ Total (path k) := by linarith
        push_cast
        linarith
  have := key n
  have := hnonneg (path n)
  linarith

/-- **`no_infinite_uniform_dissipative_cascade` — PROVED.** An infinite uniformly-dissipative
    ℝ-cascade is impossible: `n·δ` would exceed `E(0)`. This is the honest ℝ-analogue of `no_infinite_closed_paid_run`
    and the EXACT form that an NS regularity certificate must have. -/
theorem no_infinite_uniform_dissipative_cascade
    {State : Type} {Step : State → State → Prop}
    (Total : State → ℝ) (Work : State → State → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hpaid : ∀ {x y}, Step x y → Total y + Work x y ≤ Total x)
    (hwork : ∀ {x y}, Step x y → δ ≤ Work x y)
    (hnonneg : ∀ x, 0 ≤ Total x) :
    ¬ ∃ path : ℕ → State, ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hstep⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (Total (path 0) / δ)
  have hb := real_cascade_bounded_of_uniform_work Total Work δ hδ hpaid hwork hnonneg path hstep n
  have : Total (path 0) / δ * δ < (n : ℝ) * δ :=
    mul_lt_mul_of_pos_right hn hδ
  rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at this
  linarith

/-! ### §10. Partition and capacity / overflow -/

/-- Partition of `[1,X]` into the relevant (twin-carrier) and irrelevant parts. -/
structure LiouvilleTwinPartition where
  relevant : ℕ → Finset ℕ
  irrelevant : ℕ → Finset ℕ
  disjoint : ∀ X, Disjoint (relevant X) (irrelevant X)
  union_eq : ∀ X, relevant X ∪ irrelevant X = Finset.Icc 1 X

/-- Liouville summatory function. -/
noncomputable def L (x : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 x, liouville n

/-- Relevant sum. -/
noncomputable def LRelevant (P : LiouvilleTwinPartition) (X : ℕ) : ℤ :=
  ∑ n ∈ P.relevant X, liouville n

/-- Irrelevant sum. -/
noncomputable def LIrrelevant (P : LiouvilleTwinPartition) (X : ℕ) : ℤ :=
  ∑ n ∈ P.irrelevant X, liouville n

/-- **`L_eq_relevant_add_irrelevant` — PROVED (blueprint sorry closed).** `L = LRelevant + LIrrelevant`
    by the disjoint-union partition (`Finset.sum_union`). -/
theorem L_eq_relevant_add_irrelevant (P : LiouvilleTwinPartition) (X : ℕ) :
    L X = LRelevant P X + LIrrelevant P X := by
  unfold L LRelevant LIrrelevant
  rw [← P.union_eq X, Finset.sum_union (P.disjoint X)]

/-- `LiouvilleViolation` (global imbalance) — from `RankJumpBridge`. -/
def LiouvilleViolation : Prop := EuclidsPath.RankJumpBridge.LiouvilleViolation

/-- The irrelevant part is bounded (analytic INPUT, unproved). -/
def IrrelevantCancellation (P : LiouvilleTwinPartition) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ X : ℕ, |(LIrrelevant P X : ℝ)| ≤ C * (X : ℝ) ^ ((1 / 2 : ℝ) + ε)

/-- Relevant imbalance (the part that overflows after the overflow step). -/
def RelevantLiouvilleViolation (P : LiouvilleTwinPartition) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 < C →
    ∃ X : ℕ, C * (X : ℝ) ^ ((1 / 2 : ℝ) + ε) < |(LRelevant P X : ℝ)|

/--
  **`relevantViolation_of_globalViolation` — PROVED (§10 overflow, blueprint sorry closed).**
  If there is a global imbalance and the irrelevant part is bounded, then the relevant part overflows.
  Triangle: `|L| ≤ |LRelevant| + |LIrrelevant|`; when `|L|` is large and `|LIrrelevant|` is bounded,
  `|LRelevant|` must be large. We take `C' = C + Cirr` (bound of the irrelevant part) as the threshold. -/
theorem relevantViolation_of_globalViolation (P : LiouvilleTwinPartition)
    (hCancel : IrrelevantCancellation P)
    (hV : LiouvilleViolation) : RelevantLiouvilleViolation P := by
  obtain ⟨ε, hε, hbig⟩ := hV
  obtain ⟨Cirr, hCirr, hirr⟩ := hCancel ε hε
  refine ⟨ε, hε, ?_⟩
  intro C hC
  -- threshold for the global imbalance: C + Cirr
  obtain ⟨X, hX⟩ := hbig (C + Cirr) (by positivity)
  refine ⟨X, ?_⟩
  -- |L X| = |LRelevant + LIrrelevant| ≤ |LRelevant| + |LIrrelevant|  (triangle inequality)
  have hLsplit : (L X : ℝ) = (LRelevant P X : ℝ) + (LIrrelevant P X : ℝ) := by
    have := L_eq_relevant_add_irrelevant P X
    exact_mod_cast this
  have htri : |(L X : ℝ)| ≤ |(LRelevant P X : ℝ)| + |(LIrrelevant P X : ℝ)| := by
    rw [hLsplit]; exact abs_add_le _ _
  have hirrX : |(LIrrelevant P X : ℝ)| ≤ Cirr * (X : ℝ) ^ ((1 / 2 : ℝ) + ε) := hirr X
  -- hX : (C+Cirr)*X^... < |L X|
  -- (C+Cirr)·Xᵖ < |L| ≤ |LRel| + |LIrr| ≤ |LRel| + Cirr·Xᵖ  ⟹  C·Xᵖ < |LRel|  (conclude)
  set p := (X : ℝ) ^ ((1 / 2 : ℝ) + ε) with hp
  have h1 : (C + Cirr) * p < |(LRelevant P X : ℝ)| + |(LIrrelevant P X : ℝ)| :=
    lt_of_lt_of_le hX htri
  have h2 : |(LIrrelevant P X : ℝ)| ≤ Cirr * p := hirrX
  nlinarith [h1, h2]

/-! ### §11. Pairing capacity: the relevant imbalance does not fit into the cancelling pairs ⟹ jump -/

/-- `TwinCarrierEnergyJump` — from `RankJumpBridge`. -/
def TwinCarrierEnergyJump (TwinSystem : RankParitySystem) : Prop :=
  EuclidsPath.RankJumpBridge.TwinCarrierEnergyJump TwinSystem

/-- Pairing structure: relevant points are encoded into the twin system; cancelling pairs flip the sign;
    the uncancelled remainder gives a jump (the last field is an analytic INPUT). -/
structure TwinCarrierPairing (P : LiouvilleTwinPartition) (TwinSystem : RankParitySystem) where
  encode : ∀ {X : ℕ}, {n : ℕ // n ∈ P.relevant X} → TwinSystem.State
  paired : TwinSystem.State → TwinSystem.State → Prop
  paired_flips_sign : ∀ a b, paired a b → TwinSystem.sign a = - TwinSystem.sign b
  unpaired_gives_jump : RelevantLiouvilleViolation P → TwinCarrierEnergyJump TwinSystem

/-- **`twinJump_of_relevantViolation` — PROVED (§11).** Relevant imbalance ⟹ twin jump (via
    the input `unpaired_gives_jump`). -/
theorem twinJump_of_relevantViolation (P : LiouvilleTwinPartition)
    (TwinSystem : RankParitySystem) (Pair : TwinCarrierPairing P TwinSystem)
    (hRel : RelevantLiouvilleViolation P) : TwinCarrierEnergyJump TwinSystem :=
  Pair.unpaired_gives_jump hRel

/-- Full localisation package: partition + cancellation + pairing. -/
structure LiouvilleToTwinLocalization (TwinSystem : RankParitySystem) where
  P : LiouvilleTwinPartition
  irrelevant_cancellation : IrrelevantCancellation P
  pairing : TwinCarrierPairing P TwinSystem

/--
  **`liouvilleViolation_localizes — PROVED (assembly §10+§11).** The full package decomposes the node
  `RankJumpLocalizationTarget`: global Liouville imbalance ⟹ (overflow) relevant imbalance ⟹
  (pairing) twin jump. This splits ONE large input `RankJumpLocalization` into TWO smaller ones
  (`irrelevant_cancellation`, `pairing.unpaired_gives_jump`). They themselves are analytic inputs, unproved. -/
theorem liouvilleViolation_localizes (TwinSystem : RankParitySystem)
    (Loc : LiouvilleToTwinLocalization TwinSystem)
    (hV : LiouvilleViolation) : TwinCarrierEnergyJump TwinSystem := by
  have hRel : RelevantLiouvilleViolation Loc.P :=
    relevantViolation_of_globalViolation Loc.P Loc.irrelevant_cancellation hV
  exact twinJump_of_relevantViolation Loc.P TwinSystem Loc.pairing hRel

end EuclidsPath.DissipativeCascade
