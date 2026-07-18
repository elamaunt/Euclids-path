/-
  GeometricTypeIIMachineEnergy — THE GATE-PROTECTION STEP: the abstract
  𝔈-slots of the wall's faces receive a CONCRETE MACHINE REFERENT, and the
  free-slot hole is recorded as a machine disclosure.

  ORIGIN.  Wall-assault campaign (this session): sixteen attack designs were
  generated and adversarially verified; three independent refutations killed
  designs that instantiated the faces' energy slot with self-chosen surrogate
  energies (family means, smoothed defects, kernel masses).  All three
  exploited the SAME hole: the registered face Props
  (`CRE`, `SemiprimeShortRestriction`, `HigherConductorDispersion`,
  `LowFreqRootCoherence`) quantify over an ARBITRARY function `𝔈 : ℝ → ℝ`,
  so they are SATISFIABLE VACUOUSLY (𝔈 = 0).  The campaign synthesis ranked
  closing this hole as the single most valuable honest step — cheaper than
  every attack and the only one that protects the §110 gate itself.

  WHAT THIS MODULE DOES.
    1. Defines the canonical machine energy `machineE`: the SQUARED μ-signed
       collective window defect of the CRT square roots of unity over
       squarefree conductors coprime to 6 — the dossier's 𝔈 (§52/§97,
       Appendix E) in the repo's own vocabulary (`PairRoughRemainder` applied
       to the true root-class window defects), with the ω-slices
       `machineE₂` (semiprime conductors, face C) and `machineE₃`
       (ω ≥ 3 conductors, face D).
    2. Proves the sanity layer that makes the referent visibly nonvacuous
       and finite: each root-class defect has absolute value ≤ 1
       (`abs_rootClassDefect_le_one`), each conductor carries exactly
       `2^ω(q)` root classes (`card_natRoots_eq_pow_omega` — the pure-ℕ
       bridge to the repo's `sq_roots_card_prod`), `2^ω(q) ≤ q`
       (`pow_omega_le_self_of_squarefree`), and the explicit envelope
       `machineE x ≤ (Σ_{q ∈ conductors} 2^{ω(q)})²` (`machineE_le_envelope`).
    3. Registers the CANONICAL INSTANTIATIONS `MachineCRE`,
       `MachineSemiprimeShortRestriction`, `MachineHigherConductorDispersion`
       (abbreviations of the registered Props at the machine referent — the
       same open targets, now machine-adjudicable), and records the
       free-slot disclosure as FOUR THEOREMS: every face Prop holds at
       𝔈 = 0 (`CRE_holds_of_zero_energy` and siblings).  Any future §110
       claim on these faces must name its 𝔈; a claim at a self-chosen 𝔈 is
       hereby machine-documented as potentially vacuous.

  NUMERIC GROUNDING (pre-pass, this session): at N = M = 20/50/120 every
  root-class defect has |·| ≤ 1, every conductor has exactly 2^ω root
  classes with 2^ω ≤ q, and the signed remainder is −1.114/−1.883/−2.291
  against envelopes 13/31/93 — the cancellation the faces assert is visible
  numerically and is NOT proved here (that is exactly the open content).

  DISCLOSURES.
    * This module PROVES no face and CLOSES no face: it grounds the targets.
      The vacuity theorems are disclosures, not progress; the envelope is
      trivial (absolute values), summability-blind, and parity-blind.
    * Face E's canonical low-frequency referent (the dyadic-block object) is
      NOT defined here — it lands with the hyperbola-reciprocity module
      (campaign SPEC 1), which reduces its dyadic slices exactly.
    * The canonical `TypeIIProgram` instance is henceforth to be read with
      `𝔈 = machineE`; a program instance with another 𝔈 must disclose it.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIMap
import EuclidsPath.Engine.GeometricTypeIIWallMap
import EuclidsPath.Engine.GeometricTypeIIRoots
import EuclidsPath.Engine.GeometricTypeIIBrunTwin

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### Layer 1: the concrete machine energy -/

/-- The window defect of one residue class: `#{m ∈ [1,M] : m ≡ v (mod q)} − M/q`.
The exact object whose signed aggregation over CRT root classes is the
dossier's 𝔈. -/
noncomputable def rootClassDefect (M q v : ℕ) : ℝ :=
  (((Finset.Icc 1 M).filter fun m => m % q = v).card : ℝ) - (M : ℝ) / q

/-- The pure-ℕ root classes of a conductor: `{v < q : v² ≡ 1 (mod q)}`. -/
def natRoots (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun v => (v * v) % q = 1 % q)

theorem mem_natRoots {q v : ℕ} :
    v ∈ natRoots q ↔ v < q ∧ (v * v) % q = 1 % q := by
  unfold natRoots
  rw [Finset.mem_filter, Finset.mem_range]

/-- The signed root shift of one conductor: the sum of window defects over
its CRT square roots of unity. -/
noncomputable def rootShift (M q : ℕ) : ℝ :=
  ∑ v ∈ natRoots q, rootClassDefect M q v

/-- The conductor set: squarefree, coprime to 6, in `[1, N]`. -/
def conductors (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun q => Squarefree q ∧ Nat.Coprime q 6)

theorem mem_conductors {N q : ℕ} :
    q ∈ conductors N ↔ (1 ≤ q ∧ q ≤ N) ∧ Squarefree q ∧ Nat.Coprime q 6 := by
  unfold conductors
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- Face-C slice: semiprime conductors (`ω(q) = 2`). -/
def conductors₂ (N : ℕ) : Finset ℕ :=
  (conductors N).filter (fun q => q.primeFactors.card = 2)

/-- Face-D slice: higher conductors (`ω(q) ≥ 3`). -/
def conductors₃ (N : ℕ) : Finset ℕ :=
  (conductors N).filter (fun q => 3 ≤ q.primeFactors.card)

/-- **THE MACHINE ENERGY** — the canonical referent of the faces' 𝔈-slot:
the squared μ-signed collective root-class window defect, at window and
conductor level `⌊x⌋` (the repo's `PairRoughRemainder` at the true defects). -/
noncomputable def machineE (x : ℝ) : ℝ :=
  (PairRoughRemainder (rootShift ⌊x⌋₊) (conductors ⌊x⌋₊)) ^ 2

/-- The face-C machine energy (semiprime conductors only). -/
noncomputable def machineE₂ (x : ℝ) : ℝ :=
  (PairRoughRemainder (rootShift ⌊x⌋₊) (conductors₂ ⌊x⌋₊)) ^ 2

/-- The face-D machine energy (`ω ≥ 3` conductors only). -/
noncomputable def machineE₃ (x : ℝ) : ℝ :=
  (PairRoughRemainder (rootShift ⌊x⌋₊) (conductors₃ ⌊x⌋₊)) ^ 2

/-! ### Layer 2: the sanity layer (nonvacuous, finite, at the right scale) -/

theorem machineE_nonneg (x : ℝ) : 0 ≤ machineE x := sq_nonneg _

theorem machineE₂_nonneg (x : ℝ) : 0 ≤ machineE₂ x := sq_nonneg _

theorem machineE₃_nonneg (x : ℝ) : 0 ≤ machineE₃ x := sq_nonneg _

/-- Each root-class window defect is at most `1` in absolute value — the
true defects are POINTWISE tiny; all content is in the signed aggregation. -/
theorem abs_rootClassDefect_le_one {M q v : ℕ} (hq : 0 < q) (hv : v < q) :
    |rootClassDefect M q v| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := residue_class_bracket hq hv M
  have hdivle : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / q := Nat.cast_div_le
  have hmod : (M : ℝ) / q < ((M / q : ℕ) : ℝ) + 1 := by
    have hmq : M % q < q := Nat.mod_lt _ hq
    have hsplit : (M : ℝ) = (q : ℝ) * ((M / q : ℕ) : ℝ) + ((M % q : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod M q).symm
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    rw [div_lt_iff₀ hq0]
    have : ((M % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hmq
    nlinarith
  have hloR : ((M / q : ℕ) : ℝ)
      ≤ (((Finset.Icc 1 M).filter fun m => m % q = v).card : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (((Finset.Icc 1 M).filter fun m => m % q = v).card : ℝ)
      ≤ ((M / q : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhi
  rw [abs_le]
  constructor
  · unfold rootClassDefect
    linarith
  · unfold rootClassDefect
    linarith

/-- The ZMod bridge: the pure-ℕ root classes biject with the `C² = 1`
solutions in `ZMod q`. -/
theorem card_natRoots_eq {q : ℕ} [NeZero q] :
    (natRoots q).card
      = (Finset.univ.filter fun C : ZMod q => C ^ 2 = 1).card := by
  classical
  refine Finset.card_nbij' (fun v => (v : ZMod q)) (fun C => C.val)
    ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_coe, mem_natRoots] at hv
    show ((v : ZMod q)) ∈ _
    rw [Finset.mem_coe]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h1 : ((v * v : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hv.2
    push_cast at h1
    rw [sq]
    exact h1
  · intro C hC
    rw [Finset.mem_coe] at hC
    have hCsq := (Finset.mem_filter.mp hC).2
    have hvlt : C.val < q := ZMod.val_lt C
    show C.val ∈ _
    rw [Finset.mem_coe, mem_natRoots]
    refine ⟨hvlt, ?_⟩
    have hcast : ((C.val * C.val : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, ← sq]
      exact hCsq
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  · intro v hv
    rw [Finset.mem_coe, mem_natRoots] at hv
    exact ZMod.val_cast_of_lt hv.1
  · intro C _
    exact ZMod.natCast_rightInverse C

/-- **`2^ω` root classes per conductor**: for a squarefree conductor coprime
to 6, the number of square roots of unity is exactly `2^{ω(q)}` (the repo's
`sq_roots_card_prod` through the pure-ℕ bridge). -/
theorem card_natRoots_eq_pow_omega {q : ℕ} (hq1 : 1 ≤ q)
    (hsq : Squarefree q) (hco : Nat.Coprime q 6) :
    (natRoots q).card = 2 ^ q.primeFactors.card := by
  classical
  have : NeZero q := ⟨by omega⟩
  rw [card_natRoots_eq]
  refine sq_roots_card_prod q.primeFactors ?_ q ?_
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, ?_⟩
    -- p ∣ q and q coprime to 6 ⟹ p ∉ {2, 3} ⟹ 2 < p
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro h
      subst h
      have h2q : Nat.Coprime 2 6 := Nat.Coprime.coprime_dvd_left hpd hco
      norm_num [Nat.coprime_comm] at h2q
    have hp3 : p ≠ 3 := by
      intro h
      subst h
      have h3q : Nat.Coprime 3 6 := Nat.Coprime.coprime_dvd_left hpd hco
      norm_num [Nat.coprime_comm] at h3q
    have := hpp.two_le
    omega
  · exact (Nat.prod_primeFactors_of_squarefree hsq).symm

/-- `2^{ω(q)} ≤ q` for squarefree `q ≥ 1` — the envelope is polynomial. -/
theorem pow_omega_le_self_of_squarefree {q : ℕ} (_hq1 : 1 ≤ q)
    (hsq : Squarefree q) : 2 ^ q.primeFactors.card ≤ q := by
  calc 2 ^ q.primeFactors.card
      = ∏ _p ∈ q.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ q.primeFactors, p :=
        Finset.prod_le_prod (fun _ _ => by omega)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ = q := Nat.prod_primeFactors_of_squarefree hsq

/-- The root shift of one conductor is at most its root count: pointwise
defects are ≤ 1. -/
theorem abs_rootShift_le {M q : ℕ} (hq : 0 < q) :
    |rootShift M q| ≤ ((natRoots q).card : ℝ) := by
  calc |rootShift M q|
      ≤ ∑ v ∈ natRoots q, |rootClassDefect M q v| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ natRoots q, (1 : ℝ) := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [mem_natRoots] at hv
        exact abs_rootClassDefect_le_one hq hv.1
    _ = ((natRoots q).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **THE EXPLICIT ENVELOPE**: the machine energy is finite and sits below
the squared unsigned root count — everything the faces assert is the SAVING
below this envelope. -/
theorem machineE_le_envelope (x : ℝ) :
    machineE x
      ≤ (∑ q ∈ conductors ⌊x⌋₊, (2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
  have habs : |PairRoughRemainder (rootShift ⌊x⌋₊) (conductors ⌊x⌋₊)|
      ≤ ∑ q ∈ conductors ⌊x⌋₊, (2 : ℝ) ^ q.primeFactors.card := by
    unfold PairRoughRemainder
    calc |∑ q ∈ conductors ⌊x⌋₊,
          (ArithmeticFunction.moebius q : ℝ) * rootShift ⌊x⌋₊ q|
        ≤ ∑ q ∈ conductors ⌊x⌋₊,
          |(ArithmeticFunction.moebius q : ℝ) * rootShift ⌊x⌋₊ q| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ conductors ⌊x⌋₊, (2 : ℝ) ^ q.primeFactors.card := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [mem_conductors] at hq
          obtain ⟨⟨hq1, _⟩, hqsq, hqco⟩ := hq
          have hq0 : 0 < q := hq1
          have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| = 1 := by
            rw [ArithmeticFunction.moebius_apply_of_squarefree hqsq]
            push_cast
            rw [abs_pow, abs_neg, abs_one, one_pow]
          rw [abs_mul, hμ, one_mul]
          calc |rootShift ⌊x⌋₊ q| ≤ ((natRoots q).card : ℝ) :=
                abs_rootShift_le hq0
            _ = (2 : ℝ) ^ q.primeFactors.card := by
                rw [card_natRoots_eq_pow_omega hq1 hqsq hqco]
                push_cast
                ring
  have henv0 : (0 : ℝ) ≤ ∑ q ∈ conductors ⌊x⌋₊, (2 : ℝ) ^ q.primeFactors.card :=
    Finset.sum_nonneg fun q _ => by positivity
  unfold machineE
  rw [sq_abs (PairRoughRemainder _ _) |>.symm]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-! ### Layer 3: the canonical instantiations and the free-slot disclosure -/

/-- 🔴 **THE CANONICAL CRE** — the registered target `CRE` read at the
machine referent.  This is the SAME open target as before, now
machine-adjudicable: a §110 claim on CRE must move THIS quantity. -/
abbrev MachineCRE : Prop := CRE machineE

/-- 🔴 **THE CANONICAL FACE C** — `SemiprimeShortRestriction` at the
semiprime-conductor machine energy. -/
abbrev MachineSemiprimeShortRestriction : Prop :=
  SemiprimeShortRestriction machineE₂

/-- 🔴 **THE CANONICAL FACE D** — `HigherConductorDispersion` at the
`ω ≥ 3` machine energy. -/
abbrev MachineHigherConductorDispersion : Prop :=
  HigherConductorDispersion machineE₃

/-- **FREE-SLOT DISCLOSURE (CRE).**  The shape-Prop holds VACUOUSLY at
`𝔈 = 0`: three campaign designs died exactly by instantiating the slot with
self-chosen surrogates.  Machine record of the hole; any CRE claim must name
its 𝔈 (canonically `machineE`). -/
theorem CRE_holds_of_zero_energy : CRE (fun _ => 0) := by
  intro B
  refine ⟨1, one_pos, fun x hx => ?_⟩
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx0 : (0 : ℝ) ≤ x := by linarith
  positivity

/-- **FREE-SLOT DISCLOSURE (face C).** -/
theorem semiprimeShortRestriction_holds_of_zero_energy :
    SemiprimeShortRestriction (fun _ => 0) := by
  intro B
  refine ⟨1, one_pos, fun x hx => ?_⟩
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx0 : (0 : ℝ) ≤ x := by linarith
  positivity

/-- **FREE-SLOT DISCLOSURE (face D).** -/
theorem higherConductorDispersion_holds_of_zero_energy :
    HigherConductorDispersion (fun _ => 0) := by
  intro B
  refine ⟨1, one_pos, fun x hx => ?_⟩
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx0 : (0 : ℝ) ≤ x := by linarith
  positivity

/-- **FREE-SLOT DISCLOSURE (face E).** -/
theorem lowFreqRootCoherence_holds_of_zero_energy :
    LowFreqRootCoherence (fun _ => 0) := by
  intro B
  refine ⟨1, one_pos, fun x hx => ?_⟩
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx0 : (0 : ℝ) ≤ x := by linarith
  positivity

end TypeII
end Geometric
end EuclidsPath
