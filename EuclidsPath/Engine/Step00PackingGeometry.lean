import EuclidsPath.Engine.Step00GainLayer
import EuclidsPath.Engine.Step00TwinJacobsthalWall

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Packing geometry — bidirectional repacking, the collision form of twins (all green)

Numbers as volumes: `Box(n)` is the factorization box (the ordered-exponent state of
`Step00OrderedExponentGeometry`); a number is REPACKABLE when it admits a rectangle
(`∃ a b ≥ 2, n = a·b`).  DISCLOSURE (house rule): pointwise, `Repackable ⟺ ¬Prime ⟺ 2 ≤ Ω`
— vocabulary, zero content; the content of the packing model is the DYNAMICS along ±1.

* **Total repacking** (`support_renewal_succ`): consecutive integers share no prime direction —
  a single increment demolishes EVERY side of the box.  The geometric heart of the model is a
  theorem, not a picture.
* **The centered bidirectional form**: the stable center `6m` is always repackable
  (`center_always_repackable`) with packing dimension ≥ 2 (`packDim_center_ge_two`), and the
  two wings are the two DIRECTIONAL repackings from it.  **`twin_collision`**: a twin center is
  exactly a repackable stable center flanked by two unrepackable directional defects.
  DISCLOSURE: the center conjunct is free and the equivalence is definitional dressing of
  "both wings prime" — recorded as vocabulary, not progress (cf. `activeSieveSafe_iff_twinCenterZ`).
* **Three-phase competition law**: per clock `q ≥ 5` the residue classes of `m` split
  `1/1/1/(q−3)` — strike-left / strike-right / strike-center / neutral (`center_strike`,
  `neutral_card`); the center competes with the wings for one residue slot per clock.
* **The truncated-dimension control ladder** `truncDim B n` (distinct clocks ≤ B dividing `n`):
  kernel-decidable, monotone in `B`, `P_B`-periodic (`truncDim_periodic` — the `clean_shift`
  pattern), bounded by `ω`, and welded to the sieve stack by the keystone
  `clean_iff_truncDim_wings_eq_zero`: cleanliness at scale `A` is exactly "both directional
  repackings have zero truncated dimension at level `A`".  Per the ledger discipline (L4
  precedent) `truncDim` enters vocabulary and kernel census only — no named hypothesis until
  the harness verdicts (L33–L38) say otherwise.
* Kernel census by pure `decide`: `φ(210) = 48` zero-dimension residues at `B = 7`; `15` and
  `1485` doubly-clean wing counts per period at `B = 7, 13` (cross-checked externally by the
  exact CRT layer of tools/packing_walk_harness.py before kernel verification).

No `sorry`, no new axiom, no `native_decide`; standard axioms only.
-/

namespace EuclidsPath
namespace PackingGeometry

open EuclidsPath.Residuals
open EuclidsPath.CleanGraph
open EuclidsPath.OrderedExponent
open EuclidsPath.TwinJacobsthalWall
open ArithmeticFunction
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

/-! ### Section 1 — the repackable vocabulary (disclosure lemmas) -/

/-- A volume admits a rectangle. -/
def Repackable (n : ℕ) : Prop := ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b

/-- DISCLOSURE: pointwise, repackability is exactly compositeness. -/
theorem repackable_iff_not_prime {n : ℕ} (hn : 2 ≤ n) : Repackable n ↔ ¬ n.Prime := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩ hp
    rcases hp.eq_one_or_self_of_dvd a ⟨b, rfl⟩ with h1 | hself
    · omega
    · have : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb
      omega
  · intro hp
    refine ⟨n.minFac, n / n.minFac, (Nat.minFac_prime (by omega)).two_le, ?_, ?_⟩
    · exact le_trans (Nat.minFac_prime (by omega)).two_le
        (Nat.minFac_le_div (by omega) hp)
    · exact (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm

/-- DISCLOSURE: the grade face — repackable = total degree at least 2. -/
theorem repackable_iff_two_le_cardFactors {n : ℕ} (hn : 2 ≤ n) :
    Repackable n ↔ 2 ≤ Ω n := by
  rw [repackable_iff_not_prime hn]
  constructor
  · intro hp
    have hpos : 0 < Ω n := cardFactors_pos_iff_one_lt.mpr (by omega)
    rcases Nat.lt_or_ge (Ω n) 2 with h | h
    · exact absurd (cardFactors_eq_one_iff_prime.mp (by omega)) hp
    · exact h
  · intro h hp
    have := cardFactors_eq_one_iff_prime.mpr hp
    omega

/-! ### Section 2 — the centered bidirectional form -/

/-- The stable center is always repackable: `6m = 2 · 3m`. -/
theorem center_always_repackable {m : ℕ} (hm : 1 ≤ m) : Repackable (6 * m) :=
  ⟨2, 3 * m, le_refl 2, by omega, by ring⟩

/-- The stable center has packing dimension at least 2 (sides 2 and 3 always present). -/
theorem packDim_center_ge_two {m : ℕ} (hm : 1 ≤ m) : 2 ≤ ω (6 * m) := by
  rw [omega_eq_card_primeFactors]
  rw [show (2 : ℕ) = 1 + 1 by rfl, Nat.add_one_le_iff]
  refine Finset.one_lt_card.mpr ⟨2, ?_, 3, ?_, by omega⟩
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ⟨3 * m, by ring⟩, by positivity⟩
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, ⟨2 * m, by ring⟩, by positivity⟩

/-- **The collision form of twins.**  A twin center is exactly a repackable stable center
    flanked by two unrepackable directional defects.  DISCLOSURE: the center conjunct is free
    (`center_always_repackable`) and the wing conjuncts are definitionally "both wings prime"
    (`repackable_iff_not_prime`) — this is the packing VOCABULARY for `TwinCenterZ`, not new
    content; the graded face of the same collision is `wingGain_eq_zero_iff`. -/
theorem twin_collision {m : ℕ} (hm : 1 ≤ m) :
    TwinCenterZ m ↔
      Repackable (6 * m) ∧ ¬ Repackable (6 * m - 1) ∧ ¬ Repackable (6 * m + 1) := by
  have hL : 2 ≤ 6 * m - 1 := by omega
  have hR : 2 ≤ 6 * m + 1 := by omega
  rw [repackable_iff_not_prime hL, repackable_iff_not_prime hR, not_not, not_not]
  exact ⟨fun h => ⟨center_always_repackable hm, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

/-- **Total repacking**: a single increment shares no prime direction with its predecessor —
    every side of the box is demolished by `+1`. -/
theorem support_renewal_succ (n : ℕ) :
    Disjoint (idxSupport n) (idxSupport (n + 1)) := by
  rw [Finset.disjoint_left]
  intro i hin hin1
  rw [mem_idxSupport_iff, expVec] at hin hin1
  have hd : Nat.nth Nat.Prime i ∣ n := Nat.dvd_of_factorization_pos hin
  have hd1 : Nat.nth Nat.Prime i ∣ (n + 1) := Nat.dvd_of_factorization_pos hin1
  have h1 : Nat.nth Nat.Prime i ∣ 1 := (Nat.dvd_add_right hd).mp hd1
  have := Nat.le_of_dvd (by norm_num) h1
  have := (Nat.prime_nth_prime i).two_le
  omega

section Phases

variable {q : ℕ} [Fact q.Prime]

private theorem six_ne_zero' (h5 : 5 ≤ q) : (6 : ZMod q) ≠ 0 := by
  have hq : q.Prime := Fact.out
  intro h
  have hdvd : q ∣ 6 := by
    have := (ZMod.natCast_eq_zero_iff 6 q).mp (by exact_mod_cast h)
    exact this
  have := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases q
  · exact absurd hdvd (by norm_num)
  · exact absurd hq (by norm_num)

/-- The center's strike phase: clock `q ≥ 5` strikes the stable center exactly on the residue
    zero — the third phase of the per-clock competition. -/
theorem center_strike (h5 : 5 ≤ q) {m : ℕ} :
    q ∣ 6 * m ↔ (m : ZMod q) = 0 := by
  have h6 := six_ne_zero' h5
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' h6
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- **The three-phase competition law**: per clock `q ≥ 5` exactly `q − 3` residue classes are
    neutral — one class strikes the center, one each strikes the two wings, and the three
    strike phases are pairwise distinct. -/
theorem neutral_card (h5 : 5 ≤ q) :
    (Finset.univ.filter fun r : ZMod q =>
      6 * r ≠ 0 ∧ 6 * r - 1 ≠ 0 ∧ 6 * r + 1 ≠ 0).card = q - 3 := by
  classical
  have h6 := six_ne_zero' h5
  have hL : ∀ r : ZMod q, 6 * r - 1 = 0 ↔ r = (6 : ZMod q)⁻¹ := by
    intro r
    rw [sub_eq_zero]
    constructor
    · intro h
      exact mul_left_cancel₀ h6 (h.trans (mul_inv_cancel₀ h6).symm)
    · intro h
      rw [h, mul_inv_cancel₀ h6]
  have hR : ∀ r : ZMod q, 6 * r + 1 = 0 ↔ r = -(6 : ZMod q)⁻¹ := by
    intro r
    constructor
    · intro h
      have h' : 6 * r = 6 * (-(6 : ZMod q)⁻¹) := by
        rw [mul_neg, mul_inv_cancel₀ h6]
        linear_combination h
      exact mul_left_cancel₀ h6 h'
    · intro h
      rw [h, mul_neg, mul_inv_cancel₀ h6]
      ring
  have hC : ∀ r : ZMod q, 6 * r = 0 ↔ r = 0 := by
    intro r
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h6
      · exact h'
    · intro h
      rw [h, mul_zero]
  have hinv : (6 : ZMod q)⁻¹ ≠ 0 := inv_ne_zero h6
  have hanti : (6 : ZMod q)⁻¹ ≠ -(6 : ZMod q)⁻¹ :=
    EuclidsPath.TwoEngineOscillation.strike_phases_antipodal h5
  have hbad : (Finset.univ.filter fun r : ZMod q =>
      6 * r = 0 ∨ 6 * r - 1 = 0 ∨ 6 * r + 1 = 0)
      = {(0 : ZMod q), (6 : ZMod q)⁻¹, -(6 : ZMod q)⁻¹} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hC r, hL r, hR r]
  have hcongr : (Finset.univ.filter fun r : ZMod q =>
      6 * r ≠ 0 ∧ 6 * r - 1 ≠ 0 ∧ 6 * r + 1 ≠ 0)
      = Finset.univ.filter fun r : ZMod q =>
        ¬ (6 * r = 0 ∨ 6 * r - 1 = 0 ∨ 6 * r + 1 = 0) := by
    apply Finset.filter_congr
    intro r _
    tauto
  rw [hcongr, Finset.filter_not, hbad, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, ZMod.card]
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨fun h => hinv h.symm, fun h => (neg_ne_zero.mpr hinv) h.symm⟩),
    Finset.card_pair hanti]

end Phases

/-! ### Section 3 — the truncated-dimension control ladder -/

/-- Truncated packing dimension: distinct clocks up to `B` dividing `n`.
    Kernel-decidable by construction; vocabulary and census only (ledger discipline L4). -/
def truncDim (B n : ℕ) : ℕ :=
  ((Finset.range (B + 1)).filter fun q => q.Prime ∧ q ∣ n).card

theorem truncDim_mono_scale {B B' n : ℕ} (h : B ≤ B') : truncDim B n ≤ truncDim B' n := by
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hr
    omega), hp⟩

theorem truncDim_le_omega {B n : ℕ} (hn : n ≠ 0) : truncDim B n ≤ ω n := by
  rw [omega_eq_card_primeFactors]
  apply Finset.card_le_card
  intro q hq
  obtain ⟨-, hp, hd⟩ := Finset.mem_filter.mp hq
  exact Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩

/-- The ladder is `P`-periodic once every clock ≤ `B` divides `P` — the decidable shadow. -/
theorem truncDim_periodic {B P : ℕ} (hdvd : ∀ q : ℕ, q.Prime → q ≤ B → q ∣ P) (n : ℕ) :
    truncDim B (n + P) = truncDim B n := by
  unfold truncDim
  congr 1
  apply Finset.filter_congr
  intro q hq
  have hqB : q ≤ B := by
    have := Finset.mem_range.mp hq
    omega
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp, ?_⟩
    have he : n + P = P + n := by omega
    rw [he] at hd
    exact (Nat.dvd_add_right (hdvd q hp hqB)).mp hd
  · rintro ⟨hp, hd⟩
    refine ⟨hp, ?_⟩
    have he : n + P = P + n := by omega
    rw [he]
    exact (Nat.dvd_add_right (hdvd q hp hqB)).mpr hd

/-- Wing shift: the wings' truncated dimensions are `P`-periodic in the center index. -/
theorem truncDim_wing_shift {B P m : ℕ} (hdvd : ∀ q : ℕ, q.Prime → q ≤ B → q ∣ 6 * P)
    (hm : 1 ≤ m) :
    truncDim B (6 * (m + P) - 1) = truncDim B (6 * m - 1) ∧
      truncDim B (6 * (m + P) + 1) = truncDim B (6 * m + 1) := by
  constructor
  · have he : 6 * (m + P) - 1 = (6 * m - 1) + 6 * P := by omega
    rw [he]
    exact truncDim_periodic hdvd (6 * m - 1)
  · have he : 6 * (m + P) + 1 = (6 * m + 1) + 6 * P := by omega
    rw [he]
    exact truncDim_periodic hdvd (6 * m + 1)

/-- The truncated face of `packDim_center_ge_two`. -/
theorem two_le_truncDim_center {B m : ℕ} (hB : 3 ≤ B) (hm : 1 ≤ m) :
    2 ≤ truncDim B (6 * m) := by
  unfold truncDim
  rw [show (2 : ℕ) = 1 + 1 by rfl, Nat.add_one_le_iff]
  refine Finset.one_lt_card.mpr ⟨2, ?_, 3, ?_, by omega⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.prime_two, ⟨3 * m, by ring⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.prime_three, ⟨2 * m, by ring⟩⟩

/-- **The keystone bridge**: cleanliness at scale `A` is exactly "both directional repackings
    have zero truncated dimension at level `A`" — the ladder is welded onto the whole
    `Clean`/`PeriodCert`/`WitnessChain` stack. -/
theorem clean_iff_truncDim_wings_eq_zero {A m : ℕ} :
    Clean A m ↔ truncDim A (6 * m - 1) = 0 ∧ truncDim A (6 * m + 1) = 0 := by
  unfold truncDim
  rw [Finset.card_eq_zero, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    constructor
    · intro q hq ⟨hp, hd⟩
      exact h q hp (by have := Finset.mem_range.mp hq; omega) (Or.inl hd)
    · intro q hq ⟨hp, hd⟩
      exact h q hp (by have := Finset.mem_range.mp hq; omega) (Or.inr hd)
  · rintro ⟨hL, hR⟩ q hp hqA hor
    rcases hor with hd | hd
    · exact hL (Finset.mem_range.mpr (by omega)) ⟨hp, hd⟩
    · exact hR (Finset.mem_range.mpr (by omega)) ⟨hp, hd⟩

/-! ### Section 4 — kernel census (constants cross-checked by the exact CRT layer) -/

example : truncDim 7 210 = 4 := by decide

/-- `φ(210) = 48` residues of full period `210` carry zero truncated dimension at `B = 7`. -/
theorem truncCensus_7 :
    ((Finset.range 210).filter fun r => truncDim 7 r = 0).card = 48 := by decide

/-- Doubly-clean wing count per period at `B = 7`: `15 = 3 · 5` (the `(q−2)` product). -/
theorem truncCensus_wings_7 :
    ((Finset.Icc 1 35).filter fun m =>
      truncDim 7 (6 * m - 1) = 0 ∧ truncDim 7 (6 * m + 1) = 0).card = 15 := by decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- Doubly-clean wing count per period at `B = 13`: `1485 = 3 · 5 · 9 · 11`. -/
theorem truncCensus_wings_13 :
    ((Finset.Icc 1 5005).filter fun m =>
      truncDim 13 (6 * m - 1) = 0 ∧ truncDim 13 (6 * m + 1) = 0).card = 1485 := by decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- The clean census at scale 13, derived through the keystone bridge — no second scan. -/
theorem cleanCensus_13 :
    ((Finset.Icc 1 5005).filter fun m => Clean 13 m).card = 1485 := by
  have h : ∀ m ∈ Finset.Icc 1 5005, Clean 13 m ↔
      (truncDim 13 (6 * m - 1) = 0 ∧ truncDim 13 (6 * m + 1) = 0) :=
    fun m _ => clean_iff_truncDim_wings_eq_zero
  rw [Finset.filter_congr h]
  exact truncCensus_wings_13

end PackingGeometry
end EuclidsPath
