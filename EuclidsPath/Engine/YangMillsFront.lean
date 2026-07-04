/-
  YangMillsFront — the GREEN (axiom-free) module of the Yang–Mills branch in
  the perpetual engine programme: a GAPLESS spectrum = a PERPETUAL ENGINE
  (excitations of arbitrarily small energy above the vacuum = an infinite
  multiplicative descent in ℝ); its refutation = the MASS GAP.

  HONEST BOUNDARY (loudly, as in NavierStokes): mathlib has NO gauge theory.
  `SpectralModel` — an abstract spectral model (Set ℝ + vacuum +
  nonnegativity); there is NO Yang–Mills content here beyond the intended future
  instantiation. The millennium problem is NOT solved and NOT claimed.

  Architecture:
    * the engine: `GaplessLadder` — a halving-ladder of energies (2·E' ≤ E),
      exactly the ℝ-counterexample `real_positive_work_not_wellfounded`
      (DissipativeCascade §2);
    * the quantization law `QuantizationLaw` (per-model 🔴 INPUT, NS-pattern, like
      EnergyBalanceLaw): each positive level carries an ℕ-rank,
      the multiplicative descent of energy reflects into a strict descent of rank;
    * the GREEN killer: ℕ-descent is impossible — the ROOT of the repository
      (`EuclidsPath.Engine.no_infinite_descent`, EPMI); hence
      `massGap_of_quantizationLaw` — a green conditional chain.

  INVERTED ASYMMETRY (disclosed, not forged, mirror of P/NP): the killer of the
  ladder is pure well-foundedness of ℕ, the hypothesis hNoEngine is NOT added;
  the concrete rank machine is genuinely consumed only in V3/§8.

  TRILEMMA of the fourth decree boundary — all verdicts machine-checked (§7):
    V1 the universal form is REFUTABLE (cookedGapless + cookedLadder + EPMI);
    V2 the existential form is ALREADY PROVEN (cookedGapped — the decree is vacuous);
    V3 the manifestation (Riemann mirror) form is INCOMPATIBLE with the accepted
       boundary: the ladder, unlike an off-critical zero, is green PRESENTABLE.
  COST COLLAPSE (§4): `quantizationLaw_iff_massGap` — the per-model law ⟺
  the gap GREEN and WITHOUT a boundary (the form of the condemned bridge
  `offCriticalBridge_iff_RH`; contrast:
  `manifestationLaw_iff_RH_of_boundary` requires a boundary). Therefore
  there is NO FOURTH FIELD: the missing piece is a data anchor (the real YM-spectrum),
  the lesson of SpectralAnchorAudit/P-NP. The module does NOT import the quarantine;
  there is no axiom/sorry — the verifier must show all declarations untainted.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.DissipativeCascade
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace YangMills

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
-- EPMI and OriginAnchorAudit are used QUALIFIED (collisions of State/Step/Bridge).

/-#############################################################################
  §1. Spectral model, gap, gaplessness
#############################################################################-/

/-- **D1. Abstract spectral model**: a set of energy levels with
    vacuum 0 and nonnegativity. `vacuum_mem` — a semantic anchor
    (0 = vacuum; makes the guard `E ≠ 0` in `MassGap` meaningful); in the
    conclusions it carries only the inhabitedness of cooked-models — its inertness is disclosed.
    NO YM-content (disclosed in the header). -/
structure SpectralModel where
  Energy : Set ℝ
  vacuum_mem : (0 : ℝ) ∈ Energy
  nonneg : ∀ E ∈ Energy, 0 ≤ E

/-- A positive (non-vacuum) state of the spectrum. -/
abbrev PositiveState (S : SpectralModel) : Type :=
  {E : ℝ // E ∈ S.Energy ∧ 0 < E}

/-- **D2. MASS GAP** (the Clay direction; here — only the abstract form):
    there exists Δ > 0 below all nonzero levels. -/
def MassGap (S : SpectralModel) : Prop :=
  ∃ Δ > 0, ∀ E ∈ S.Energy, E ≠ 0 → Δ ≤ E

/-- **D3. GAPLESSNESS = perpetual engine**: excitations of arbitrarily small
    positive energy above the vacuum. -/
def Gapless (S : SpectralModel) : Prop :=
  ∀ ε > 0, ∃ E ∈ S.Energy, 0 < E ∧ E < ε

/-- **L1: ¬gap ⟺ gaplessness** — the classical equivalence
    (`nonneg` is consumed in the transition E ≠ 0 ⟺ 0 < E). No choice is needed. -/
theorem not_massGap_iff_gapless (S : SpectralModel) :
    ¬ MassGap S ↔ Gapless S := by
  constructor
  · intro hNo ε hε
    by_contra hnone
    push_neg at hnone
    exact hNo ⟨ε, hε, fun E hE hne =>
      hnone E hE (lt_of_le_of_ne (S.nonneg E hE) (Ne.symm hne))⟩
  · rintro hG ⟨Δ, hΔ, hgap⟩
    obtain ⟨E, hE, hpos, hlt⟩ := hG Δ hΔ
    exact absurd (hgap E hE (ne_of_gt hpos)) (not_le.mpr hlt)

theorem massGap_iff_not_gapless (S : SpectralModel) :
    MassGap S ↔ ¬ Gapless S := by
  rw [← not_massGap_iff_gapless, not_not]

/-#############################################################################
  §2. THE ENGINE OBJECT: halving-ladder
#############################################################################-/

/-- **D4. GAPLESSNESS LADDER — a perpetual engine in ℝ**: an infinite
    sequence of positive levels with multiplicative descent
    `2·E(n+1) ≤ E(n)` (an analogue of `DescentStep` EPMI with A = 2, but over ℝ, where
    well-foundedness by itself does NOT work — exactly the ℝ-warning
    `real_positive_work_not_wellfounded`). -/
structure GaplessLadder (S : SpectralModel) where
  seq : ℕ → ℝ
  mem : ∀ n, seq n ∈ S.Energy
  pos : ∀ n, 0 < seq n
  halving : ∀ n, 2 * seq (n + 1) ≤ seq n

/-- A single choice step: a level below half of the current one. -/
noncomputable def ladderNext {S : SpectralModel} (hG : Gapless S)
    (p : PositiveState S) : PositiveState S :=
  ⟨(hG (p.1 / 2) (half_pos p.2.2)).choose,
   (hG (p.1 / 2) (half_pos p.2.2)).choose_spec.1,
   (hG (p.1 / 2) (half_pos p.2.2)).choose_spec.2.1⟩

theorem ladderNext_lt_half {S : SpectralModel} (hG : Gapless S)
    (p : PositiveState S) : (ladderNext hG p).1 < p.1 / 2 :=
  (hG (p.1 / 2) (half_pos p.2.2)).choose_spec.2.2

/-- The recursive choice sequence (`Classical.choice` is honestly visible). -/
noncomputable def ladderSeq {S : SpectralModel} (hG : Gapless S) :
    ℕ → PositiveState S
  | 0 => ⟨(hG 1 one_pos).choose, (hG 1 one_pos).choose_spec.1,
          (hG 1 one_pos).choose_spec.2.1⟩
  | n + 1 => ladderNext hG (ladderSeq hG n)

@[simp] theorem ladderSeq_succ {S : SpectralModel} (hG : Gapless S) (n : ℕ) :
    ladderSeq hG (n + 1) = ladderNext hG (ladderSeq hG n) := rfl

/-- **L2 (a witness of substantiveness, mirror of `offCriticalZero_of_not_RH`):**
    from gaplessness the ladder is CONSTRUCTED (by choice). -/
noncomputable def gaplessLadder_of_gapless {S : SpectralModel}
    (hG : Gapless S) : GaplessLadder S where
  seq := fun n => (ladderSeq hG n).1
  mem := fun n => (ladderSeq hG n).2.1
  pos := fun n => (ladderSeq hG n).2.2
  halving := fun n => by
    have h := ladderNext_lt_half hG (ladderSeq hG n)
    show 2 * (ladderSeq hG (n + 1)).1 ≤ (ladderSeq hG n).1
    rw [ladderSeq_succ]
    linarith

/-- The named form from ¬gap. -/
noncomputable def gaplessLadder_of_not_massGap {S : SpectralModel}
    (h : ¬ MassGap S) : GaplessLadder S :=
  gaplessLadder_of_gapless ((not_massGap_iff_gapless S).mp h)

/-- The ladder is majorized by a geometric progression. -/
theorem ladder_le_geometric {S : SpectralModel} (D : GaplessLadder S) :
    ∀ n : ℕ, D.seq n ≤ D.seq 0 * (1 / 2) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h := D.halving n
      have hpow : (0 : ℝ) < (1 / 2) ^ n := by positivity
      calc D.seq (n + 1) ≤ D.seq n / 2 := by linarith
        _ ≤ D.seq 0 * (1 / 2) ^ n / 2 := by linarith
        _ = D.seq 0 * (1 / 2) ^ (n + 1) := by ring

/-- **L3: ladder ⟹ gaplessness** (Archimedean descent,
    `exists_pow_lt_of_lt_one`): the ladder refutes EVERY candidate-Δ. -/
theorem gapless_of_ladder {S : SpectralModel} (D : GaplessLadder S) :
    Gapless S := by
  intro ε hε
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one (div_pos hε (D.pos 0)) (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨D.seq n, D.mem n, D.pos n, ?_⟩
  have h1 : D.seq 0 * (1 / 2) ^ n < ε := (lt_div_iff₀' (D.pos 0)).mp hn
  have h2 := ladder_le_geometric D n
  linarith

theorem not_massGap_of_ladder {S : SpectralModel} (D : GaplessLadder S) :
    ¬ MassGap S :=
  fun hM => (massGap_iff_not_gapless S).mp hM (gapless_of_ladder D)

/-- **L4 — the exact green characterization of the engine:** gaplessness ⟺
    nonemptiness of the type of ladders. -/
theorem gapless_iff_nonempty_ladder (S : SpectralModel) :
    Gapless S ↔ Nonempty (GaplessLadder S) :=
  ⟨fun h => ⟨gaplessLadder_of_gapless h⟩, fun ⟨D⟩ => gapless_of_ladder D⟩

/-#############################################################################
  §3. Quantization law and the EPMI-killer (hero chain, NS-pattern)
#############################################################################-/

/-- **D5. QUANTIZATION LAW — per-model 🔴 INPUT (NS-pattern, like
    `EnergyBalanceLaw`):** each positive state manifests on
    a natural rank, and the multiplicative descent of energy (2y ≤ x) reflects
    into a STRICT descent of rank. For the INTENDED (not constructed!) instantiation
    S = the real YM-spectrum this is precisely the residual physical input of the branch. -/
def QuantizationLaw (S : SpectralModel) : Prop :=
  ∃ rank : PositiveState S → ℕ,
    ∀ x y : PositiveState S, 2 * (y : ℝ) ≤ (x : ℝ) → rank y < rank x

/-- **L5 — the GREEN KILLER (ROOT OF THE REPOSITORY):** a quantized ladder =
    an infinite ℕ-descent = Euclid's perpetual engine; killed by
    `no_infinite_descent` (EPMI, A = 1). HONESTY (inverted
    asymmetry, mirror of P/NP): the killer is pure well-foundedness,
    hNoEngine is NOT added (it would be a false hypothesis). -/
theorem no_quantizedLadder {S : SpectralModel}
    (hQ : QuantizationLaw S) (D : GaplessLadder S) : False := by
  obtain ⟨rank, hrank⟩ := hQ
  exact EuclidsPath.Engine.no_infinite_descent (le_refl 1)
    (fun t => rank ⟨D.seq t, D.mem t, D.pos t⟩)
    (fun t => by
      show 1 * rank ⟨D.seq (t + 1), D.mem (t + 1), D.pos (t + 1)⟩ <
        rank ⟨D.seq t, D.mem t, D.pos t⟩
      rw [Nat.one_mul]
      exact hrank _ _ (D.halving t))

/-- **L6 — HERO (green conditional chain, NS-pattern):** the quantization law ⟹
    mass gap. ¬gap → ladder (choice) → ℕ-descent → EPMI-False. -/
theorem massGap_of_quantizationLaw (S : SpectralModel)
    (hQ : QuantizationLaw S) : MassGap S := by
  by_contra hNo
  exact no_quantizedLadder hQ (gaplessLadder_of_not_massGap hNo)

/-- **L7 (analogue of the Riemann L2):** a gapless quantized model does NOT
    exist. -/
theorem no_gapless_quantized_model :
    ¬ ∃ S : SpectralModel, Gapless S ∧ QuantizationLaw S := by
  rintro ⟨S, hG, hQ⟩
  exact no_quantizedLadder hQ (gaplessLadder_of_gapless hG)

/-#############################################################################
  §4. The cost mirror and its COLLAPSE (the decisive honesty audit)
#############################################################################-/

/-- **L8 (the reverse side — NOT vacuous, unlike the Riemann L5):**
    gap ⟹ quantization law. The rank: `Nat.log 2 ⌊E/Δ⌋₊` — the binary floor
    of a level above the threshold Δ. -/
theorem quantizationLaw_of_massGap (S : SpectralModel)
    (hM : MassGap S) : QuantizationLaw S := by
  obtain ⟨Δ, hΔ, hgap⟩ := hM
  refine ⟨fun x => Nat.log 2 ⌊(x : ℝ) / Δ⌋₊, ?_⟩
  intro x y hxy
  have hyΔ : Δ ≤ (y : ℝ) := hgap y.1 y.2.1 (ne_of_gt y.2.2)
  set m : ℕ := ⌊(y : ℝ) / Δ⌋₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Nat.le_floor (by push_cast; exact (one_le_div hΔ).mpr hyΔ)
  have hmle : (m : ℝ) ≤ (y : ℝ) / Δ := by
    rw [hm]; exact Nat.floor_le (div_pos y.2.2 hΔ).le
  have hmΔ : (m : ℝ) * Δ ≤ (y : ℝ) := (le_div_iff₀ hΔ).mp hmle
  have hcast : ((m * 2 : ℕ) : ℝ) ≤ (x : ℝ) / Δ := by
    rw [le_div_iff₀ hΔ]
    push_cast
    nlinarith [hxy, hmΔ]
  have hfloor : m * 2 ≤ ⌊(x : ℝ) / Δ⌋₊ := Nat.le_floor hcast
  calc Nat.log 2 m < Nat.log 2 m + 1 := Nat.lt_succ_self _
    _ = Nat.log 2 (m * 2) :=
        (Nat.log_mul_base (by norm_num) (by omega)).symm
    _ ≤ Nat.log 2 ⌊(x : ℝ) / Δ⌋₊ := Nat.log_mono_right hfloor

/-- **L9 — the MAIN AUDIT (collapse of the cost mirror):** the per-model law ⟺
    mass gap — GREEN and WITHOUT ANY BOUNDARY. This is the form of the CONDEMNED bridge
    (`offCriticalBridge_iff_RH`), and NOT of the Riemann mirror
    (`manifestationLaw_iff_RH_of_boundary` requires a boundary): to decree
    the law for a model = to decree its gap verbatim. Therefore a per-model
    decree field is impossible HONESTLY; the missing piece is a data anchor (the real
    YM-spectrum), Prop-nonvacuity is the wrong criterion (SpectralAnchorAudit). -/
theorem quantizationLaw_iff_massGap (S : SpectralModel) :
    QuantizationLaw S ↔ MassGap S :=
  ⟨massGap_of_quantizationLaw S, quantizationLaw_of_massGap S⟩

/-#############################################################################
  §5. Forged models (witnesses of the trilemma)
#############################################################################-/

/-- A forged GAPLESS model: `{0} ∪ {(1/2)^n}` — the spectral realization
    of the ℝ-warning `real_positive_work_not_wellfounded`. -/
noncomputable def cookedGapless : SpectralModel where
  Energy := insert (0 : ℝ) (Set.range fun n : ℕ => (1 / 2 : ℝ) ^ n)
  vacuum_mem := Set.mem_insert 0 _
  nonneg := by
    rintro E hE
    rcases Set.mem_insert_iff.mp hE with rfl | ⟨n, rfl⟩
    · exact le_refl 0
    · positivity

/-- Its EXPLICIT ladder (no choice — the engine is presented by construction;
    noncomputable — only because of ℝ-division in the data). -/
noncomputable def cookedLadder : GaplessLadder cookedGapless where
  seq := fun n => (1 / 2 : ℝ) ^ n
  mem := fun n => Set.mem_insert_of_mem _ ⟨n, rfl⟩
  pos := fun n => by positivity
  halving := fun n => le_of_eq (by ring)

theorem cookedGapless_gapless : Gapless cookedGapless :=
  gapless_of_ladder cookedLadder

theorem cookedGapless_not_massGap : ¬ MassGap cookedGapless :=
  not_massGap_of_ladder cookedLadder

theorem cookedGapless_no_quantizationLaw : ¬ QuantizationLaw cookedGapless :=
  fun hQ => no_quantizedLadder hQ cookedLadder

/-- A forged GAPPED model `{0, 1}`. -/
def cookedGapped : SpectralModel where
  Energy := {0, 1}
  vacuum_mem := Set.mem_insert 0 _
  nonneg := by
    rintro E hE
    rcases Set.mem_insert_iff.mp hE with rfl | hE1
    · exact le_refl 0
    · rw [Set.mem_singleton_iff] at hE1; rw [hE1]; norm_num

theorem cookedGapped_massGap : MassGap cookedGapped := by
  refine ⟨1, one_pos, ?_⟩
  rintro E hE hne
  rcases Set.mem_insert_iff.mp hE with rfl | hE1
  · exact absurd rfl hne
  · rw [Set.mem_singleton_iff] at hE1; rw [hE1]

/-- The law on the gapped model — VACUOUSLY (there is not a single halving-pair): rank ≡ 0
    goes through. Disclosed: this is why the V2-decree would add nothing. -/
theorem cookedGapped_quantizationLaw : QuantizationLaw cookedGapped := by
  refine ⟨fun _ => 0, ?_⟩
  rintro ⟨x, hx, hxpos⟩ ⟨y, hy, hypos⟩ hxy
  exfalso
  have hxy' : 2 * y ≤ x := hxy
  rcases Set.mem_insert_iff.mp hx with rfl | hx1
  · exact lt_irrefl _ hxpos
  rcases Set.mem_insert_iff.mp hy with rfl | hy1
  · exact lt_irrefl _ hypos
  rw [Set.mem_singleton_iff] at hx1 hy1
  rw [hx1, hy1] at hxy'
  norm_num at hxy'

/-- A pure-vacuum model `{0}`: the gap VACUOUSLY (the guard is empty) — Prop-nonvacuity
    as a criterion is again wrong (the lesson of SpectralAnchorAudit). -/
def vacuumOnlyModel : SpectralModel where
  Energy := {0}
  vacuum_mem := Set.mem_singleton 0
  nonneg := by
    rintro E hE
    rw [Set.eq_of_mem_singleton hE]

theorem vacuumOnly_massGap : MassGap vacuumOnlyModel :=
  ⟨1, one_pos, fun _E hE hne => absurd (Set.eq_of_mem_singleton hE) hne⟩

/-#############################################################################
  §6. Bridge to Navier–Stokes: why rank saves, not δ-dissipation
#############################################################################-/

/-- Reuse of the generic cascade machine: a uniformly-δ-dissipating
    ladder is impossible (`no_infinite_uniform_dissipative_cascade`). -/
theorem no_uniformlyDissipative_ladder {S : SpectralModel}
    (D : GaplessLadder S) (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ n : ℕ, δ ≤ D.seq n - D.seq (n + 1)) : False :=
  EuclidsPath.DissipativeCascade.no_infinite_uniform_dissipative_cascade
    (State := ℕ) (Step := fun m n => n = m + 1)
    D.seq (fun m n => D.seq m - D.seq n) δ hδ
    (fun {m n} h => by subst h; exact le_of_eq (by ring))
    (fun {m n} h => by subst h; exact hstep m)
    (fun n => (D.pos n).le)
    ⟨fun k => k, fun _ => rfl⟩

/-- **BUT: the cooked-ladder is NOT uniformly dissipative** — its steps (1/2)^(n+1)
    decay below every δ. Machine fixation: δ-quantization of dissipation
    (the NS-certificate) does NOT kill the ladder; only RANK quantization kills it
    (§3). The NS↔YM bridge is honest and structural: the common root is EPMI, the rescues
    are different. -/
theorem cookedLadder_not_uniformlyDissipative (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n : ℕ, δ ≤ cookedLadder.seq n - cookedLadder.seq (n + 1) := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2 : ℝ) < 1)
  have hstep := h n
  have heq : cookedLadder.seq n - cookedLadder.seq (n + 1)
      = (1 / 2 : ℝ) ^ (n + 1) := by
    show (1/2 : ℝ) ^ n - (1/2) ^ (n + 1) = (1/2) ^ (n + 1)
    ring
  have hlt : ((1 : ℝ) / 2) ^ (n + 1) < (1 / 2) ^ n := by
    have hp : (0:ℝ) < (1/2)^n := by positivity
    calc ((1:ℝ)/2)^(n+1) = (1/2)^n * (1/2) := by ring
      _ < (1/2)^n := by nlinarith
  rw [heq] at hstep
  linarith

/-#############################################################################
  §7. TRILEMMA of the fourth decree boundary — all verdicts machine-checked
#############################################################################-/

/-- **D6a. CANDIDATE 1 (the universal form of the fourth field).** -/
def YmQuantizationLawUniversal : Prop :=
  ∀ S : SpectralModel, QuantizationLaw S

/-- **D6b. CANDIDATE 2 (the existential form).** -/
def YmQuantizationLawExistential : Prop :=
  ∃ S : SpectralModel, QuantizationLaw S ∧ MassGap S

/-- **D6c. CANDIDATE 3 (the manifestation form, Riemann mirror):** the ladder
    manifests with an unpayable supply of flows on all resolved
    ledger-scales (the same object `DeviationFlowSupply` as in
    riemannBoundary). The abstract ladder does NOT carry arithmetic height —
    the law is bound to ALL scales; this D-freedom is exposed by the A3/A4 audits. -/
def LadderManifests {S : SpectralModel} (_D : GaplessLadder S) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def YmManifestationLaw : Prop :=
  ∀ (S : SpectralModel) (D : GaplessLadder S), LadderManifests D

/-- **V1: CANDIDATE 1 is GREEN-REFUTABLE** — its decree would make the quarantine
    contradictory. Witness: cookedGapless + cookedLadder + EPMI. The exact
    asymmetry with Riemann: an off-critical zero is green NOT presentable (that would be
    ¬RH), the cooked-ladder — is presented above by construction. -/
theorem ymLawUniversal_refuted : ¬ YmQuantizationLawUniversal :=
  fun h => no_quantizedLadder (h cookedGapless) cookedLadder

/-- **V2: CANDIDATE 2 is GREEN-PROVABLE** — the decree would be vacuous.
    Witness: cookedGapped (the law is vacuous, the gap is verbatim Δ = 1). -/
theorem ymLawExistential_green : YmQuantizationLawExistential :=
  ⟨cookedGapped, cookedGapped_quantizationLaw, cookedGapped_massGap⟩

/-- **V3: CANDIDATE 3 is INCOMPATIBLE WITH THE ACCEPTED BOUNDARY** (green conditional
    form, taint-free): the law + the existing decree node ⟹ False.
    The chain: the boundary gives a resolving projection (M0 = 1) → the law with
    the cooked-ladder supplies `DeviationFlowSupply` → L2
    (`no_deviationFlowSupply_at_resolved_scale`) burns it. Therefore the fourth
    field of this form would BLOW UP the quarantine — REJECTED. -/
theorem ymManifestationLaw_refutes_boundary
    (hLaw : YmManifestationLaw) : ¬ TheStrictLastStep00Obligation := by
  rintro ⟨A, projOf, hres⟩
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf 1) :=
    strictSemanticExtended_resolves_old (hres 1)
  exact no_deviationFlowSupply_at_resolved_scale (projOf 1) hResolves
    (hLaw cookedGapless cookedLadder A 1 (projOf 1) hResolves)

/-- Contraposition for readability: under the accepted boundary there is NO law. -/
theorem not_ymManifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) : ¬ YmManifestationLaw :=
  fun hLaw => ymManifestationLaw_refutes_boundary hLaw hBoundary

/-- **V3-characterization (mirror of the Riemann L6, SHARPENED):** the law ⟺
    "no ledger anywhere reconciles its books" — a global freeze. In Riemann
    the forward direction required a zero (the quantifier could be empty); here the quantifier
    is GREEN inhabited (cookedLadder), so the characterization is unconditional. -/
theorem ymManifestationLaw_iff_no_resolution :
    YmManifestationLaw ↔
      ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw A M0 proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw cookedGapless cookedLadder A M0 proj hres)
  · intro hFreeze S D A M0 proj hres
    exact ((hFreeze A M0 proj) hres).elim

/-#############################################################################
  §8. Split by scales (the boundary as a HYPOTHESIS — the quarantine is not imported)
#############################################################################-/

/-- **L10 (the lower scale, green witness of supply):** at A ≤ 4 the supply
    of deviations is REAL — the 5-adic chain gives an infinite admissible-family
    without a single twin-hypothesis (mirror of the Riemann L1: the manifestation object is
    not an empty form). -/
theorem smallScale_deviationSupply {A : ℕ} (hA : A ≤ 4) :
    DeviationFlowSupply A 1 :=
  ⟨Set.range (fiveAdicChainFlow hA),
   Set.infinite_range_of_injective (fiveAdicChainFlow_injective hA),
   fun F hF => by
     rcases hF with ⟨k, rfl⟩
     exact extendedFlow_admissible _⟩

/-- **L11 (the decree scale):** the accepted boundary (as a HYPOTHESIS) on its own
    A ≥ 5 REFUSES the supply at every M0 — in the world of the decree there is no infinite
    tower of excitations: its universe is "gapped" in the language of supplies.
    (A ≥ 5 — via the refuted small branch, mirror of the P/NP-split.) -/
theorem boundary_refuses_deviationSupply_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ, ¬ DeviationFlowSupply A M0 := by
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hA : 5 ≤ A := by
    by_contra hlt
    exact no_projection_resolves_at_smallScale (by omega) (projOf 1)
      (strictSemanticExtended_resolves_old (hres 1))
  exact ⟨A, hA, fun M0 =>
    no_deviationFlowSupply_at_resolved_scale (projOf M0)
      (strictSemanticExtended_resolves_old (hres M0))⟩

/-#############################################################################
  §9. Origin-anchor audits (instantiation of the condemning machine)
#############################################################################-/

/-- **A1 (bundling-audit, instantiation of `front_pair_iff_no_zero`):**
    Bridge∧Impossible for the family of manifestations ⟺ there are no ladders. -/
theorem ym_bundling_audit (S : SpectralModel) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun D : GaplessLadder S => LadderManifests D) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun D : GaplessLadder S => LadderManifests D)) ↔
      ¬ Nonempty (GaplessLadder S) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

/-- **A2 (asymmetry with Riemann, machine-checked):** on the forged model the bundle
    is REFUTED — the ladder is presented. In Riemann the bundle was saved by the
    unpresentability of the zero; here the Bridge-side CANNOT be decreed. -/
theorem ym_bundle_refuted_at_cooked :
    ¬ (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
         (fun D : GaplessLadder cookedGapless => LadderManifests D) ∧
       EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
         (fun D : GaplessLadder cookedGapless => LadderManifests D)) :=
  fun h => (ym_bundling_audit cookedGapless).mp h ⟨cookedLadder⟩

/-- **A3 (Z-free collapse, verbatim the lesson of SpectralAnchorAudit):** the family
    of manifestations is FREE of the ladder — it collapses to a single D-independent
    "atom"-question. -/
theorem ymLaw_freeCollapse (S : SpectralModel) :
    EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.FreeLawCollapse
      (fun D : GaplessLadder S => LadderManifests D)
      (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
          DeviationFlowSupply A M0) :=
  fun _D => Iff.rfl

/-- **A4:** therefore the family does not separate ladders — a free law carries no
    information about the deviation (the same reason it is not fit
    for a decree field). -/
theorem ymLaw_cannot_separate (S : SpectralModel) :
    ¬ EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.ZeroSeparating
        (fun D : GaplessLadder S => LadderManifests D) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.no_zero_separation_under_freeCollapse
    (ymLaw_freeCollapse S)

end YangMills
end EuclidsPath

-- Machine visibility of purity in the build-log
-- (expected [propext, Classical.choice, Quot.sound]):
#print axioms EuclidsPath.YangMills.massGap_of_quantizationLaw
#print axioms EuclidsPath.YangMills.quantizationLaw_iff_massGap
#print axioms EuclidsPath.YangMills.ymLawUniversal_refuted
#print axioms EuclidsPath.YangMills.ymLawExistential_green
#print axioms EuclidsPath.YangMills.ymManifestationLaw_refutes_boundary
#print axioms EuclidsPath.YangMills.boundary_refuses_deviationSupply_at_decreed_scale
