/-
  RiemannRankProjectionAudit — ⚠️ VACUITY EPISODE №2 (Riemann branch):
  GOAL OF ROUTE №8 EXPOSED AS UNANCHORED. Prose: prose/24, prose/30.

  FOUND by adversarial probe-agent, verified manually:
    * TwinCarrierEnergyJump = Nonempty (RankEnergyJump ...) — WITHOUT anchoring to
      a violation/carrier: for the natural system LiouvilleRankSystem
      (rank = Ω, sign = λ) it is an UNCONDITIONAL theorem (states 1 and 2);
    * FULL package LiouvilleToTwinLocalization is inhabited with ZERO analytic
      input (fullLocalization_noInput): partition "everything is relevant",
      IrrelevantCancellation is trivial, paired := False;
    * the field paired is INERT (unpaired_gives_jump never mentions it);
      pieces (B)/(C) of the gradual route are dischargeable for free or nearly free
      (crossing_gives_carrier — honest ledger of relevant non-emptiness);
    * (A) window bookkeeping is CLOSED honestly: concrete ledger
      mass = |LRelevant|, capacity = ⌈X^{1/2+ε}⌉; relevantViolation_gives_window.

  HONEST CONCLUSION (wall_relevant / wall_global): the sole load-bearing wall
  of route №8 is exactly ¬LiouvilleViolation, i.e. an RH-strength bound on the
  Liouville sum function. The decomposition "cancellation + pairing" was a FORGED
  decomposition: the pairing side carried no weight. The route requires
  REFORMULATION with a goal anchored to the violation. RH is NOT proved,
  inputs are NOT closed — the vacuity of one of the wrappers has been exposed.
-/
import Mathlib
import EuclidsPath.Engine.RiemannRankProjection

set_option autoImplicit false

namespace WindowBookkeeping

open EuclidsPath.DissipativeCascade
open RiemannGradualRankOverflow
open RiemannGradualRankOverflow.GradualCarrierLedger

/-! ### The concrete ledger -/

/-- Concrete gradual ledger for a partition `P` and exponent parameter `ε`:
    `mass n = |LRelevant P n|`, `capacity n = ⌈n^(1/2+ε)⌉`. -/
noncomputable def concreteLedger (P : LiouvilleTwinPartition) (ε : ℝ) :
    GradualCarrierLedger where
  mass n := |LRelevant P n|
  capacity n := ⌈(n : ℝ) ^ ((1 / 2 : ℝ) + ε)⌉

/-! ### Bookkeeping at 0 -/

/-- The relevant part of the empty range `[1,0]` is empty. -/
theorem relevant_zero (P : LiouvilleTwinPartition) : P.relevant 0 = ∅ := by
  have h := P.union_eq 0
  rw [Finset.Icc_eq_empty (by omega)] at h
  exact (Finset.union_eq_empty.mp h).1

/-- `LRelevant P 0 = 0`. -/
theorem LRelevant_zero (P : LiouvilleTwinPartition) : LRelevant P 0 = 0 := by
  simp [LRelevant, relevant_zero P]

/-- `initial_safe`: the defect at prefix 0 is nonpositive (in fact zero). -/
theorem concreteLedger_defect_zero (P : LiouvilleTwinPartition) {ε : ℝ} (hε : 0 < ε) :
    (concreteLedger P ε).defect 0 ≤ 0 := by
  have hp : ((1 / 2 : ℝ) + ε) ≠ 0 := by positivity
  have hmass : (concreteLedger P ε).mass 0 = 0 := by
    simp [concreteLedger, LRelevant_zero P]
  have hcap : (concreteLedger P ε).capacity 0 = 0 := by
    show ⌈((0 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + ε)⌉ = 0
    rw [Nat.cast_zero, Real.zero_rpow hp, Int.ceil_zero]
  simp [defect, hmass, hcap]

/-! ### The overflow prefix -/

/-- `final_overflow`: from the `∀ C` violation clause (instantiated at `C = 2`)
    we extract a prefix `N` with strictly positive defect. -/
theorem exists_defect_pos (P : LiouvilleTwinPartition) {ε : ℝ} (hε : 0 < ε)
    (hC : ∀ C : ℝ, 0 < C →
      ∃ X : ℕ, C * (X : ℝ) ^ ((1 / 2 : ℝ) + ε) < |(LRelevant P X : ℝ)|) :
    ∃ N : ℕ, 0 < (concreteLedger P ε).defect N := by
  obtain ⟨X, hX⟩ := hC 2 (by norm_num)
  refine ⟨X, ?_⟩
  have hppos : (0 : ℝ) < (1 / 2 : ℝ) + ε := by positivity
  -- X ≥ 1 (otherwise the violation at X = 0 reads 0 < 0)
  have hX1 : 1 ≤ X := by
    rcases Nat.eq_zero_or_pos X with h0 | h1
    · subst h0
      rw [LRelevant_zero P, Nat.cast_zero, Real.zero_rpow (ne_of_gt hppos)] at hX
      norm_num at hX
    · exact h1
  have hxr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  -- 1 ≤ X^p
  have hone_le : (1 : ℝ) ≤ (X : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
    simpa [Real.one_rpow] using
      Real.rpow_le_rpow zero_le_one hxr hppos.le
  -- ceil bound: (⌈X^p⌉ : ℝ) < X^p + 1 ≤ 2·X^p < |LRelevant X|
  have hceil : ((⌈(X : ℝ) ^ ((1 / 2 : ℝ) + ε)⌉ : ℤ) : ℝ) <
      (X : ℝ) ^ ((1 / 2 : ℝ) + ε) + 1 := Int.ceil_lt_add_one _
  have hchain : ((⌈(X : ℝ) ^ ((1 / 2 : ℝ) + ε)⌉ : ℤ) : ℝ) < |(LRelevant P X : ℝ)| := by
    linarith
  -- back to ℤ
  have hint : (⌈(X : ℝ) ^ ((1 / 2 : ℝ) + ε)⌉ : ℤ) < |LRelevant P X| := by
    rw [← Int.cast_abs] at hchain
    exact_mod_cast hchain
  have hgoal : (concreteLedger P ε).defect X =
      |LRelevant P X| - ⌈(X : ℝ) ^ ((1 / 2 : ℝ) + ε)⌉ := rfl
  rw [hgoal]
  omega

/-! ### Window extraction (the clean theorem form) -/

/-- **Piece (A), theorem form.** A relevant Liouville violation yields a concrete
    gradual carrier ledger together with a gradual overflow window. -/
theorem relevantViolation_gives_window (P : LiouvilleTwinPartition)
    (hV : RelevantLiouvilleViolation P) :
    ∃ (L : GradualCarrierLedger) (N : ℕ), GradualOverflowWindow L N := by
  obtain ⟨ε, hε, hC⟩ := hV
  obtain ⟨N, hN⟩ := exists_defect_pos P hε hC
  exact ⟨concreteLedger P ε, N,
    { initial_safe := concreteLedger_defect_zero P hε
      final_overflow := hN }⟩

/-! ### Packaged route form -/

open Classical in
/-- **Piece (A), packaged structure form.** The `GlobalRelevantOverflowToWindow`
    structure fixes `L` and `N` as fields while our witnesses depend on the
    violation; the mismatch is resolved with classical choice (`dite` on the
    violation proposition + `Exists.choose`). -/
noncomputable def windowRoute (P : LiouvilleTwinPartition) :
    GlobalRelevantOverflowToWindow :=
  if h : RelevantLiouvilleViolation P then
    { RelevantOverflow := RelevantLiouvilleViolation P
      L := (relevantViolation_gives_window P h).choose
      N := (relevantViolation_gives_window P h).choose_spec.choose
      window_of_overflow := fun _ =>
        (relevantViolation_gives_window P h).choose_spec.choose_spec }
  else
    { RelevantOverflow := RelevantLiouvilleViolation P
      L := concreteLedger P 1
      N := 0
      window_of_overflow := fun hV => absurd hV h }

/-- The packaged route really has `RelevantOverflow = RelevantLiouvilleViolation P`
    (in both branches of the classical split). -/
theorem windowRoute_RelevantOverflow_eq (P : LiouvilleTwinPartition) :
    (windowRoute P).RelevantOverflow = RelevantLiouvilleViolation P := by
  unfold windowRoute
  split <;> rfl

/-- Downstream sanity check: the packaged route plugs into the gradual chain —
    together with a `GradualRankProjectionCertificate` for its ledger it forces a
    rank jump from the violation. -/
theorem windowRoute_forces_rankJump (P : LiouvilleTwinPartition)
    (C : GradualRankProjectionCertificate (windowRoute P).L)
    (hV : RelevantLiouvilleViolation P) :
    Nonempty RankJumpWitness := by
  have hOv : (windowRoute P).RelevantOverflow := by
    rw [windowRoute_RelevantOverflow_eq]; exact hV
  exact gradualOverflow_forces_rankJump C ((windowRoute P).window_of_overflow hOv)

end WindowBookkeeping

namespace PairingProbeP1

open ArithmeticFunction
open EuclidsPath.RankJumpBridge

/-- **P1.1** The natural system's jump proposition is unconditionally true:
    states `1` (Ω = 0, λ = 1) and `2` (Ω = 1, λ = -1) already jump. -/
theorem liouvilleRankSystem_has_jump :
    EuclidsPath.RankJumpBridge.TwinCarrierEnergyJump LiouvilleRankSystem := by
  refine ⟨{ before := ⟨1, one_ne_zero⟩
            after := ⟨2, by norm_num⟩
            rank_changes := ?_
            sign_changes := ?_ }⟩
  · show cardFactors 1 ≠ cardFactors 2
    rw [cardFactors_one, cardFactors_apply_prime Nat.prime_two]
    omega
  · show liouville 1 ≠ liouville 2
    rw [liouville_apply one_ne_zero,
      liouville_apply (by norm_num : (2 : ℕ) ≠ 0),
      cardFactors_one, cardFactors_apply_prime Nat.prime_two]
    norm_num

#print axioms liouvilleRankSystem_has_jump

/-- **P1.1a** Consequence: the central node
    `RankJumpLocalizationTarget LiouvilleRankSystem` is TRIVIALLY true —
    the conclusion holds without touching the hypothesis. -/
theorem localizationTarget_trivial_for_natural_system :
    RankJumpLocalizationTarget LiouvilleRankSystem :=
  fun _ => liouvilleRankSystem_has_jump

#print axioms localizationTarget_trivial_for_natural_system

/-- **P1.1b** Dual consequence: no `SpectralToTwinRankBridge` can be built with
    the natural system, since `jump_to_factory` forces `¬Jump` but the jump is
    a theorem. So the natural instance is USELESS for the downstream route. -/
theorem no_bridge_for_natural_system {OffCriticalZero : Type} :
    ¬ Nonempty (SpectralToTwinRankBridge OffCriticalZero LiouvilleRankSystem) := by
  rintro ⟨B⟩
  exact no_closedPaidFactory (B.jump_to_factory liouvilleRankSystem_has_jump)

#print axioms no_bridge_for_natural_system

/-- Elements of any relevant set are nonzero (they live in `Icc 1 k`).
    Note: `LiouvilleTwinPartition` is ABSTRACT — `relevant` is an arbitrary
    Finset-valued field, tied to twin centers only by intention, not by type. -/
theorem mem_relevant_ne_zero
    (P : EuclidsPath.DissipativeCascade.LiouvilleTwinPartition)
    {k n : ℕ} (h : n ∈ P.relevant k) : n ≠ 0 := by
  have hmem : n ∈ Finset.Icc 1 k := by
    rw [← P.union_eq k]
    exact Finset.mem_union_left _ h
  have h1 := (Finset.mem_Icc.mp hmem).1
  omega

/-- **P1.2** A NON-VACUOUS rank-visibility map: the carrier is an actual
    relevant integer `n`, before-rank `Ω n`, after-rank `Ω (2n)`, and the
    strict jump is honest arithmetic `Ω (2n) = Ω n + 1`. -/
def honestVisibility
    (P : EuclidsPath.DissipativeCascade.LiouvilleTwinPartition) (k : ℕ) :
    {n : ℕ // n ∈ P.relevant k} → RiemannRankProjection.RankJumpWitness :=
  fun u =>
  { beforeRank := (cardFactors u.1 : ℤ)
    afterRank := (cardFactors (2 * u.1) : ℤ)
    jump := by
      have h0 : u.1 ≠ 0 := mem_relevant_ne_zero P u.2
      have h2 : cardFactors (2 * u.1) = cardFactors 2 + cardFactors u.1 :=
        cardFactors_mul (by norm_num) h0
      rw [h2, cardFactors_apply_prime Nat.prime_two]
      push_cast
      omega }

#print axioms honestVisibility

/-- **P1.3 (HONESTY)** The same field is dischargeable with NO arithmetic at
    all: `RankJumpWitness` is a bare pair of integers, untethered from any
    `RankParitySystem`, so `⟨0, 1⟩` serves every carrier type. -/
def trivialVisibility (Carrier : Type) :
    Carrier → RiemannRankProjection.RankJumpWitness :=
  fun _ => { beforeRank := 0, afterRank := 1, jump := zero_lt_one }

#print axioms trivialVisibility

/-- **P1.4** A FULL `TwinCarrierPairing` for the natural system with
    `paired := fun _ _ => False`: `paired_flips_sign` is vacuous and
    `unpaired_gives_jump` discards its hypothesis (the jump is a theorem).
    Note `unpaired_gives_jump` never mentions `paired` — the relation is inert. -/
def fullPairing (P : EuclidsPath.DissipativeCascade.LiouvilleTwinPartition) :
    EuclidsPath.DissipativeCascade.TwinCarrierPairing P LiouvilleRankSystem where
  encode := fun {_X} n => ⟨n.1, mem_relevant_ne_zero P n.2⟩
  paired := fun _ _ => False
  paired_flips_sign := fun _ _ h => h.elim
  unpaired_gives_jump := fun _ => liouvilleRankSystem_has_jump

#print axioms fullPairing

/-- The all-relevant partition (irrelevant part empty). -/
def trivialPartition : EuclidsPath.DissipativeCascade.LiouvilleTwinPartition where
  relevant := fun X => Finset.Icc 1 X
  irrelevant := fun _ => ∅
  disjoint := fun _ => Finset.disjoint_empty_right _
  union_eq := fun _ => Finset.union_empty _

/-- Irrelevant cancellation holds trivially for the empty irrelevant part. -/
theorem irrelevantCancellation_trivial :
    EuclidsPath.DissipativeCascade.IrrelevantCancellation trivialPartition := by
  intro ε hε
  refine ⟨1, one_pos, fun X => ?_⟩
  have h0 : EuclidsPath.DissipativeCascade.LIrrelevant trivialPartition X = 0 := by
    simp [EuclidsPath.DissipativeCascade.LIrrelevant, trivialPartition]
  rw [h0]
  simp only [Int.cast_zero, abs_zero, one_mul]
  positivity

#print axioms irrelevantCancellation_trivial

/-- **P1.5 (VERDICT for the natural system)** The ENTIRE localization package
    of `DissipativeCascade` — partition + irrelevant cancellation + pairing —
    is inhabited with ZERO analytic input when the TwinSystem is the natural
    `LiouvilleRankSystem`. The route-#8 node is vacuous there, because
    `TwinCarrierEnergyJump LiouvilleRankSystem` is simply a theorem. -/
def fullLocalization_noInput :
    EuclidsPath.DissipativeCascade.LiouvilleToTwinLocalization LiouvilleRankSystem where
  P := trivialPartition
  irrelevant_cancellation := irrelevantCancellation_trivial
  pairing := fullPairing trivialPartition

#print axioms fullLocalization_noInput

end PairingProbeP1

/-
  PairingProbeP2 — probe of piece (C) first-crossing-creates-unpaired for route #8.

  Question P2: can `first_crossing_creates_unpaired` be instantiated for the
  ledger mass = |LRelevant|?  Answer: YES, fully and non-vacuously — a first
  crossing with nonnegative capacity forces `LRelevant k ≠ 0`, hence the
  relevant set at `k` is nonempty (empty sums vanish), giving a concrete
  carrier.  Combined with the honest Ω-visibility (n ↦ 2n), a complete
  `GradualRankProjectionCertificate` compiles, and via the repo's own bridge
  `twinCarrierPairing_of_gradualRoute` a full `TwinCarrierPairing` follows.

  HONESTY, also machine-checked below:
    * In `TwinCarrierPairing`, the `paired` relation is INERT:
      `paired := False` always discharges `paired_flips_sign`, and
      `unpaired_gives_jump` does not mention `paired` at all.  So piece (C)
      collapses to the bare implication `RelevantViolation → Jump`.
    * For any TwinSystem usable downstream (`jump_to_factory` forces the
      system to be jump-free, per `jumpToFactory_iff_no_jump`), a pairing is
      then EXACTLY `¬ RelevantLiouvilleViolation P`, and with irrelevant
      cancellation it is `¬ LiouvilleViolation` — the RH-strength bound.
      That is where the whole weight of route #8 sits.
-/





namespace PairingProbeP2

open ArithmeticFunction
open EuclidsPath.DissipativeCascade
open RiemannGradualRankOverflow

/-- Nonzero relevant sum forces a nonempty relevant set (empty sums vanish). -/
theorem relevant_nonempty_of_LRelevant_ne_zero
    (P : LiouvilleTwinPartition) {k : ℕ}
    (h : LRelevant P k ≠ 0) : (P.relevant k).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  exact h (by simp [LRelevant, hne])

/-- The concrete gradual ledger for route #8:
    mass = |LRelevant|, capacity = a chosen bound. -/
noncomputable def ledger (P : LiouvilleTwinPartition) (cap : ℕ → ℤ) :
    GradualCarrierLedger where
  mass := fun k => |LRelevant P k|
  capacity := cap

/-- Elements of any relevant set are nonzero (they live in `Icc 1 k`). -/
theorem mem_relevant_ne_zero (P : LiouvilleTwinPartition)
    {k n : ℕ} (h : n ∈ P.relevant k) : n ≠ 0 := by
  have hmem : n ∈ Finset.Icc 1 k := by
    rw [← P.union_eq k]
    exact Finset.mem_union_left _ h
  have h1 := (Finset.mem_Icc.mp hmem).1
  omega

/-- **P2.1** At a first crossing with nonnegative capacity, the relevant set
    at `k` is nonempty: a concrete carrier exists. Pure bookkeeping. -/
theorem crossing_gives_carrier
    (P : LiouvilleTwinPartition) (cap : ℕ → ℤ) (hcap : ∀ k, 0 ≤ cap k)
    {N k : ℕ} (C : FirstOverflowCrossing (ledger P cap) N k) :
    (P.relevant k).Nonempty := by
  have hcr : 0 < |LRelevant P k| - cap k := C.crosses
  have hck := hcap k
  have hpos : 0 < |LRelevant P k| := by linarith
  exact relevant_nonempty_of_LRelevant_ne_zero P (abs_pos.mp hpos)

#print axioms crossing_gives_carrier

/-- **P2.2** A COMPLETE non-vacuous `GradualRankProjectionCertificate` for the
    |LRelevant|-ledger: carriers are the actual relevant integers, and the
    visibility map is the honest arithmetic jump Ω n < Ω (2n).
    Both fields (B) and (C) of route #8 discharge for this ledger. -/
def certificate (P : LiouvilleTwinPartition) (cap : ℕ → ℤ)
    (hcap : ∀ k, 0 ≤ cap k) :
    GradualRankProjectionCertificate (ledger P cap) where
  UnpairedCarrierAt := fun k => {n : ℕ // n ∈ P.relevant k}
  first_crossing_creates_unpaired := fun {N k} C => by
    obtain ⟨n, hn⟩ := crossing_gives_carrier P cap hcap C
    exact ⟨⟨n, hn⟩⟩
  unpaired_visible_rank := fun {k} u =>
    { beforeRank := (cardFactors u.1 : ℤ)
      afterRank := (cardFactors (2 * u.1) : ℤ)
      jump := by
        have h0 : u.1 ≠ 0 := mem_relevant_ne_zero P u.2
        have h2 : cardFactors (2 * u.1) = cardFactors 2 + cardFactors u.1 :=
          cardFactors_mul (by norm_num) h0
        rw [h2, cardFactors_apply_prime Nat.prime_two]
        push_cast
        omega }

#print axioms certificate

/-- The relevant part of the empty range `Icc 1 0` is empty, so its sum is 0. -/
theorem LRelevant_zero (P : LiouvilleTwinPartition) : LRelevant P 0 = 0 := by
  have hsub : P.relevant 0 ⊆ Finset.Icc 1 0 := by
    rw [← P.union_eq 0]
    exact Finset.subset_union_left
  have hempty : P.relevant 0 = ∅ := by
    have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    rw [hIcc] at hsub
    exact Finset.subset_empty.mp hsub
  simp [LRelevant, hempty]

/-- **P2.A (window bookkeeping)** A relevant violation yields a gradual overflow
    window of the |LRelevant|-ledger against any constant capacity `c ≥ 0`. -/
theorem window_exists (P : LiouvilleTwinPartition) (c : ℤ) (hc : 0 ≤ c)
    (hRel : RelevantLiouvilleViolation P) :
    ∃ N : ℕ, GradualOverflowWindow (ledger P (fun _ => c)) N := by
  obtain ⟨ε, hε, hbig⟩ := hRel
  have hCpos : (0 : ℝ) < (c : ℝ) + 1 := by
    have hcast : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    linarith
  obtain ⟨X, hX⟩ := hbig ((c : ℝ) + 1) hCpos
  -- X ≠ 0: at X = 0 both sides of the violation inequality are 0.
  have hXne : X ≠ 0 := by
    rintro rfl
    rw [LRelevant_zero P] at hX
    have hz : ((0 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + ε) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (by linarith)
    rw [hz] at hX
    simp at hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
    have h1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr hXne
    exact_mod_cast h1
  have hp1 : (1 : ℝ) ≤ (X : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 / 2 : ℝ) + ε) := (Real.one_rpow _).symm
      _ ≤ (X : ℝ) ^ ((1 / 2 : ℝ) + ε) :=
          Real.rpow_le_rpow (by norm_num) hX1 (by linarith)
  have hclt : (c : ℝ) < |(LRelevant P X : ℝ)| := by
    have hmul : ((c : ℝ) + 1) * 1 ≤ ((c : ℝ) + 1) * ((X : ℝ) ^ ((1 / 2 : ℝ) + ε)) :=
      mul_le_mul_of_nonneg_left hp1 (le_of_lt hCpos)
    rw [mul_one] at hmul
    linarith
  have hcltZ : c < |LRelevant P X| := by
    have hcast : (c : ℝ) < ((|LRelevant P X| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      exact hclt
    exact_mod_cast hcast
  refine ⟨X, ?_, ?_⟩
  · -- initial_safe : defect 0 ≤ 0
    show |LRelevant P 0| - c ≤ 0
    rw [LRelevant_zero P]
    simp only [abs_zero, zero_sub, neg_nonpos]
    exact hc
  · -- final_overflow : 0 < defect X
    show 0 < |LRelevant P X| - c
    linarith

#print axioms window_exists

open Classical in
/-- **P2.2b** The full gradual route certificate for the |LRelevant|-ledger:
    pieces (A) window bookkeeping, (B) rank visibility, (C) first-crossing
    carrier all discharge, honestly, from repo objects alone. -/
noncomputable def routeCertificate (P : LiouvilleTwinPartition)
    (c : ℤ) (hc : 0 ≤ c) :
    GradualProjectionRouteCertificate where
  G :=
    { RelevantOverflow := RelevantLiouvilleViolation P
      L := ledger P (fun _ => c)
      N := if h : RelevantLiouvilleViolation P
        then (window_exists P c hc h).choose else 0
      window_of_overflow := fun h => by
        rw [dif_pos h]
        exact (window_exists P c hc h).choose_spec }
  P := certificate P (fun _ => c) (fun _ => hc)

#print axioms routeCertificate

/-- The natural system's jump is unconditionally true (as in P1). -/
theorem liouvilleRankSystem_has_jump :
    EuclidsPath.RankJumpBridge.TwinCarrierEnergyJump
      EuclidsPath.RankJumpBridge.LiouvilleRankSystem := by
  refine ⟨{ before := ⟨1, one_ne_zero⟩
            after := ⟨2, by norm_num⟩
            rank_changes := ?_
            sign_changes := ?_ }⟩
  · show cardFactors 1 ≠ cardFactors 2
    rw [cardFactors_one, cardFactors_apply_prime Nat.prime_two]
    omega
  · show liouville 1 ≠ liouville 2
    rw [liouville_apply one_ne_zero,
      liouville_apply (by norm_num : (2 : ℕ) ≠ 0),
      cardFactors_one, cardFactors_apply_prime Nat.prime_two]
    norm_num

/-- **P2.2c** Through the repo's own bridge, the gradual route certificate
    yields a full `TwinCarrierPairing` — BUT only because the endpoint map
    `hJ` discards the rank-jump witness (the natural system's jump is a
    theorem).  The witness produced by (A)+(B)+(C) does no work here. -/
noncomputable def pairingViaGradualRoute (P : LiouvilleTwinPartition)
    (c : ℤ) (hc : 0 ≤ c) :
    TwinCarrierPairing P EuclidsPath.RankJumpBridge.LiouvilleRankSystem :=
  EuclidsPath.RiemannRankProjectionBridge.twinCarrierPairing_of_gradualRoute
    P EuclidsPath.RankJumpBridge.LiouvilleRankSystem
    (fun {_X} n => ⟨n.1, mem_relevant_ne_zero P n.2⟩)
    (fun _ _ => False)
    (fun _ _ h => h.elim)
    (routeCertificate P c hc)
    (fun h => h)
    (fun _ => liouvilleRankSystem_has_jump)

#print axioms pairingViaGradualRoute

/-- **P2.3 (HONESTY: `paired` is inert)** Any encode map plus the bare
    implication `RelevantViolation → Jump` already builds a full pairing,
    with `paired := fun _ _ => False` discharging the sign law vacuously. -/
def pairing_of_bare_implication (P : LiouvilleTwinPartition)
    (S : EuclidsPath.RankJumpBridge.RankParitySystem)
    (encode : ∀ {X : ℕ}, {n : ℕ // n ∈ P.relevant X} → S.State)
    (h : RelevantLiouvilleViolation P → TwinCarrierEnergyJump S) :
    TwinCarrierPairing P S where
  encode := encode
  paired := fun _ _ => False
  paired_flips_sign := fun _ _ hf => hf.elim
  unpaired_gives_jump := h

#print axioms pairing_of_bare_implication

/-- Converse: a pairing yields exactly that implication back. So modulo the
    (free) encode map, piece (C) IS the implication `RelevantViolation → Jump`. -/
theorem pairing_reduces_to_jump_field (P : LiouvilleTwinPartition)
    (S : EuclidsPath.RankJumpBridge.RankParitySystem)
    (Pair : TwinCarrierPairing P S) :
    RelevantLiouvilleViolation P → TwinCarrierEnergyJump S :=
  Pair.unpaired_gives_jump

#print axioms pairing_reduces_to_jump_field

/-- **P2.4 (THE WALL)** For any TwinSystem usable downstream — i.e. jump-free,
    which `jump_to_factory` forces (`jumpToFactory_iff_no_jump`) — a pairing is
    exactly `¬ RelevantLiouvilleViolation P`. -/
theorem wall_relevant (P : LiouvilleTwinPartition)
    (S : EuclidsPath.RankJumpBridge.RankParitySystem)
    (hNoJump : ¬ TwinCarrierEnergyJump S)
    (Pair : TwinCarrierPairing P S) :
    ¬ RelevantLiouvilleViolation P :=
  fun h => hNoJump (Pair.unpaired_gives_jump h)

#print axioms wall_relevant

/-- **P2.4b** …and with irrelevant cancellation it is exactly
    `¬ LiouvilleViolation`: the RH-strength Liouville bound
    `∀ ε > 0, ∃ C > 0, ∀ x, |L x| ≤ C·x^(1/2+ε)` (in cofinal form). This is
    the single statement carrying the whole weight of route #8. -/
theorem wall_global (P : LiouvilleTwinPartition)
    (S : EuclidsPath.RankJumpBridge.RankParitySystem)
    (hNoJump : ¬ TwinCarrierEnergyJump S)
    (Pair : TwinCarrierPairing P S)
    (hCancel : IrrelevantCancellation P) :
    ¬ EuclidsPath.DissipativeCascade.LiouvilleViolation :=
  fun hV => wall_relevant P S hNoJump Pair
    (relevantViolation_of_globalViolation P hCancel hV)

#print axioms wall_global

end PairingProbeP2
