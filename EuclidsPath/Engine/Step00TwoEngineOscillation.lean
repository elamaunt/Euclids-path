import EuclidsPath.Engine.Step00OrderedExponentGeometry
import EuclidsPath.Engine.Carrier

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Two-engine oscillation — collision, phase and sign laws of the wing pair (all green)

The two wings `6m − 1`, `6m + 1` are two coupled engines.  Their oscillation is governed by laws
that ATTACH TO ℕ (they are theorems about the actual integers, not postulates of a free orthogonal
space — the design constraint of this layer):

* **Collision laws** — the engines are orthogonal in the only sense that survives the trip to ℕ:
  no clock `q ≥ 3` strikes both wings at once (`no_wing_collision`, on top of `Engine.Carrier`),
  the wings are coprime (`wing_coprime`), and their prime supports are disjoint
  (`wing_primeFactors_disjoint`, `wing_idxSupport_disjoint` — the fermionic exclusion between the
  two engines: no shared prime direction, so the joint exterior state never degenerates).
* **Phase laws** — each clock `q ≥ 5` strikes each wing `q`-periodically (`strike_periodic`), on
  exactly one residue phase per wing (`strike_phase_left/right`: the phases are `±(6 : ZMod q)⁻¹`),
  the two phases are antipodal and distinct (`strike_phases_antipodal`), leaving exactly `q − 2`
  admissible classes per period (`admissible_card`) — the local Hardy–Littlewood factor, and the
  per-clock source of the measured interference constant `∏_{q≥5}(1 − 1/(q−1)²)` (ledger law L2).
* **Sign oscillation** — the two engines change sign forever and never land on zero: the pair
  `signPair m = ((−1)^{Ω(6m−1)}, (−1)^{Ω(6m+1)})` has nonzero components (`signPair_ne_zero`),
  and each single-engine corner is visited infinitely often, ELEMENTARILY — on explicit prime-power
  families in the two progressions (`leftSign_neg/pos_infinitely_often`,
  `rightSign_neg/pos_infinitely_often`; powers of `5` and `7 mod 6`, no Dirichlet input).
* **The honesty ladder** (`twin_corner_grading`): the twin event is the graded sub-state `Ω = 1`
  inside the sign corner `(−1, −1)`.  Whether the JOINT corner `(−1,−1)` recurs is Chowla-adjacent
  (sign patterns of Liouville at `n, n+2`; known in the literature via Matomäki–Radziwiłł–Tao /
  Tao–Teräväinen, far beyond present formalisation) — we do NOT state it in Lean; the twin
  conjecture is its graded refinement.  Measured (ledger L1): the sign walk is flat at every scale
  while the graded correlation of the wings survives — the geometry must ride the grades.

The perpetual-engine prohibition itself is already green upstream (`no_perpetualEngine`).
-/

namespace EuclidsPath
namespace TwoEngineOscillation

open EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament
open EuclidsPath.OrderedExponent
open ArithmeticFunction
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

/-! ### Collision laws: the two engines never share a strike or a direction -/

/-- **No collision**: no clock `q ≥ 3` strikes both wings at once. -/
theorem no_wing_collision {m q : ℕ} (hm : 1 ≤ m) (hq : 2 < q) :
    ¬ (q ∣ (6 * m - 1) ∧ q ∣ (6 * m + 1)) := fun ⟨h1, h2⟩ =>
  EuclidsPath.Engine.no_large_shared_divisor hm hq h2 h1

/-- The wings are coprime: any common divisor divides `2`, and both wings are odd. -/
theorem wing_coprime {m : ℕ} (hm : 1 ≤ m) : Nat.Coprime (6 * m - 1) (6 * m + 1) := by
  have hd2 : Nat.gcd (6 * m - 1) (6 * m + 1) ∣ 2 :=
    EuclidsPath.Engine.twin_sides_shared_dvd_two hm
      (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
  · exact h
  · exfalso
    have h2L : 2 ∣ (6 * m - 1) := h ▸ Nat.gcd_dvd_left _ _
    omega

/-- **Fermionic exclusion between the engines**: the wings share no prime direction. -/
theorem wing_primeFactors_disjoint {m : ℕ} (hm : 1 ≤ m) :
    Disjoint (6 * m - 1).primeFactors (6 * m + 1).primeFactors :=
  (wing_coprime hm).disjoint_primeFactors

/-- The exclusion in ordered-index coordinates: the index supports are disjoint, so the joint
    exterior state `E(6m−1) ∧ E(6m+1)` never collapses on a shared direction. -/
theorem wing_idxSupport_disjoint {m : ℕ} (hm : 1 ≤ m) :
    Disjoint (idxSupport (6 * m - 1)) (idxSupport (6 * m + 1)) := by
  rw [Finset.disjoint_left]
  intro i hiL hiR
  rw [mem_idxSupport_iff, expVec] at hiL hiR
  have hdL : Nat.nth Nat.Prime i ∣ (6 * m - 1) := Nat.dvd_of_factorization_pos hiL
  have hdR : Nat.nth Nat.Prime i ∣ (6 * m + 1) := Nat.dvd_of_factorization_pos hiR
  have h2 : Nat.nth Nat.Prime i ∣ 2 :=
    EuclidsPath.Engine.twin_sides_shared_dvd_two hm hdR hdL
  have heq : Nat.nth Nat.Prime i = 2 :=
    (Nat.prime_dvd_prime_iff_eq (Nat.prime_nth_prime i) Nat.prime_two).mp h2
  rw [heq] at hdL
  omega

/-! ### Phase laws: `q`-periodic strikes on antipodal phases, `q − 2` survivors per period -/

/-- **Oscillation period**: each clock `q` strikes each wing `q`-periodically in `m`. -/
theorem strike_periodic {q : ℕ} (m : ℕ) (hm : 1 ≤ m) :
    (q ∣ (6 * (m + q) - 1) ↔ q ∣ (6 * m - 1)) ∧
    (q ∣ (6 * (m + q) + 1) ↔ q ∣ (6 * m + 1)) := by
  constructor
  · have he : 6 * (m + q) - 1 = 6 * q + (6 * m - 1) := by omega
    rw [he, Nat.dvd_add_right (dvd_mul_left q 6)]
  · have he : 6 * (m + q) + 1 = 6 * q + (6 * m + 1) := by omega
    rw [he, Nat.dvd_add_right (dvd_mul_left q 6)]

section Phases

variable {q : ℕ} [Fact q.Prime]

private theorem six_ne_zero (h5 : 5 ≤ q) : (6 : ZMod q) ≠ 0 := by
  have hq : q.Prime := Fact.out
  intro h
  have hdvd : q ∣ 6 := by
    have := (ZMod.natCast_eq_zero_iff 6 q).mp (by exact_mod_cast h)
    exact this
  have := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases q
  · exact absurd hdvd (by norm_num)
  · exact absurd hq (by norm_num)

private theorem two_ne_zero' (h5 : 5 ≤ q) : (2 : ZMod q) ≠ 0 := by
  have hq : q.Prime := Fact.out
  intro h
  have hdvd : q ∣ 2 := by
    have := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast h)
    exact this
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **Left strike phase**: clock `q ≥ 5` strikes the left wing exactly on the residue phase
    `m ≡ (6)⁻¹ (mod q)`. -/
theorem strike_phase_left (h5 : 5 ≤ q) {m : ℕ} (hm : 1 ≤ m) :
    q ∣ (6 * m - 1) ↔ (m : ZMod q) = (6 : ZMod q)⁻¹ := by
  have h6 := six_ne_zero h5
  have hcast : ((6 * m - 1 : ℕ) : ZMod q) = 6 * (m : ZMod q) - 1 := by
    have h1 : (1 : ℕ) ≤ 6 * m := by omega
    push_cast [Nat.cast_sub h1]
    ring
  rw [← ZMod.natCast_eq_zero_iff, hcast, sub_eq_zero]
  constructor
  · intro h
    have := mul_left_cancel₀ h6 (h.trans (mul_inv_cancel₀ h6).symm)
    exact this
  · intro h
    rw [h, mul_inv_cancel₀ h6]

/-- **Right strike phase**: clock `q ≥ 5` strikes the right wing exactly on the antipodal phase
    `m ≡ −(6)⁻¹ (mod q)`. -/
theorem strike_phase_right (h5 : 5 ≤ q) {m : ℕ} (hm : 1 ≤ m) :
    q ∣ (6 * m + 1) ↔ (m : ZMod q) = -(6 : ZMod q)⁻¹ := by
  have h6 := six_ne_zero h5
  have hcast : ((6 * m + 1 : ℕ) : ZMod q) = 6 * (m : ZMod q) + 1 := by push_cast; ring
  rw [← ZMod.natCast_eq_zero_iff, hcast]
  constructor
  · intro h
    have h' : 6 * (m : ZMod q) = 6 * (-(6 : ZMod q)⁻¹) := by
      rw [mul_neg, mul_inv_cancel₀ h6]
      linear_combination h
    exact mul_left_cancel₀ h6 h'
  · intro h
    rw [h, mul_neg, mul_inv_cancel₀ h6]
    ring

/-- **Phase antipodality**: the two strike phases of a clock `q ≥ 5` are distinct — the machine
    form of "the engines' forbidden phases never coincide" (equivalently `no_wing_collision`,
    now localised per period). -/
theorem strike_phases_antipodal (h5 : 5 ≤ q) :
    (6 : ZMod q)⁻¹ ≠ -(6 : ZMod q)⁻¹ := by
  have h6 := six_ne_zero h5
  have h2 := two_ne_zero' h5
  intro h
  have hinv : (6 : ZMod q)⁻¹ ≠ 0 := inv_ne_zero h6
  have h20 : (2 : ZMod q) * (6 : ZMod q)⁻¹ = 0 := by linear_combination h
  rcases mul_eq_zero.mp h20 with h' | h'
  · exact h2 h'
  · exact hinv h'

/-- **The local oscillation law**: per period, exactly `q − 2` residue phases survive both
    engines' strikes — the Hardy–Littlewood local factor `(q−2)/q` of the interference product. -/
theorem admissible_card (h5 : 5 ≤ q) :
    (Finset.univ.filter fun r : ZMod q =>
      6 * r - 1 ≠ 0 ∧ 6 * r + 1 ≠ 0).card = q - 2 := by
  classical
  have h6 := six_ne_zero h5
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
  have hbad : (Finset.univ.filter fun r : ZMod q => 6 * r - 1 = 0 ∨ 6 * r + 1 = 0)
      = {(6 : ZMod q)⁻¹, -(6 : ZMod q)⁻¹} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hL r, hR r]
  have hcongr : (Finset.univ.filter fun r : ZMod q => 6 * r - 1 ≠ 0 ∧ 6 * r + 1 ≠ 0)
      = Finset.univ.filter fun r : ZMod q => ¬ (6 * r - 1 = 0 ∨ 6 * r + 1 = 0) := by
    apply Finset.filter_congr
    intro r _
    tauto
  rw [hcongr, Finset.filter_not, hbad, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, ZMod.card]
  have hne := strike_phases_antipodal h5
  rw [Finset.card_pair hne]

end Phases

/-! ### Sign oscillation: the four-corner walk, never zero, single corners visited elementarily -/

/-- The sign pair of the two engines — the parity shadow of the center's graded state. -/
def signPair (m : ℕ) : ℤ × ℤ := ((-1) ^ Ω (6 * m - 1), (-1) ^ Ω (6 * m + 1))

/-- **The engines never land on zero.** -/
theorem signPair_ne_zero (m : ℕ) : (signPair m).1 ≠ 0 ∧ (signPair m).2 ≠ 0 :=
  ⟨pow_ne_zero _ (by norm_num), pow_ne_zero _ (by norm_num)⟩

theorem signPair_of_twin {m : ℕ} (h : TwinCenterZ m) : signPair m = (-1, -1) := by
  have h1 : Ω (6 * m - 1) = 1 := cardFactors_eq_one_iff_prime.mpr h.1
  have h2 : Ω (6 * m + 1) = 1 := cardFactors_eq_one_iff_prime.mpr h.2
  simp [signPair, h1, h2]

private theorem odd_pow_five_mod_six (k : ℕ) : (5 * 25 ^ k) % 6 = 5 := by
  have h25 : (25 : ℕ) ^ k % 6 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [Nat.mul_mod, h25]

private theorem pow_seven_mod_six (k : ℕ) : (7 : ℕ) ^ k % 6 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private theorem five_mul_25_pow (k : ℕ) : 5 * 25 ^ k = 5 ^ (2 * k + 1) := by
  rw [pow_succ, pow_mul]
  norm_num
  ring

/-- The left engine visits sign `−1` infinitely often — elementarily, on odd powers of `5`
    (`5^{2k+1} ≡ 5 (mod 6)` is a left wing with odd `Ω`; no Dirichlet input). -/
theorem leftSign_neg_infinitely_often :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ (-1 : ℤ) ^ Ω (6 * m - 1) = -1 := by
  intro N
  set k := 6 * N + 6 with hk
  set e := 5 * 25 ^ k with he
  have hmod : e % 6 = 5 := odd_pow_five_mod_six k
  have hgt : k < 25 ^ k := Nat.lt_pow_self (by norm_num)
  have hebig : 6 * N + 6 < e := by
    have h1 : 25 ^ k ≤ 5 * 25 ^ k := by omega
    omega
  refine ⟨(e + 1) / 6, by omega, ?_⟩
  have h6m : 6 * ((e + 1) / 6) - 1 = e := by omega
  rw [h6m, he, five_mul_25_pow, cardFactors_apply_prime_pow (by norm_num)]
  exact Odd.neg_one_pow ⟨k, by ring⟩

/-- The left engine visits sign `+1` infinitely often — on `5 · 7^{2j+1} ≡ 5 (mod 6)`,
    which has even `Ω = 2j + 2`. -/
theorem leftSign_pos_infinitely_often :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ (-1 : ℤ) ^ Ω (6 * m - 1) = 1 := by
  intro N
  set k := 6 * N + 6 with hk
  set e := 5 * 7 ^ (2 * k + 1) with he
  have h7 : (7 : ℕ) ^ (2 * k + 1) % 6 = 1 := pow_seven_mod_six _
  have hmod : e % 6 = 5 := by
    rw [he, Nat.mul_mod, h7]
  have hgt : 2 * k + 1 < 7 ^ (2 * k + 1) := Nat.lt_pow_self (by norm_num)
  have hebig : 6 * N + 6 < e := by
    have h1 : 7 ^ (2 * k + 1) ≤ 5 * 7 ^ (2 * k + 1) := by omega
    omega
  refine ⟨(e + 1) / 6, by omega, ?_⟩
  have h6m : 6 * ((e + 1) / 6) - 1 = e := by omega
  rw [h6m, he, cardFactors_mul (by norm_num) (by positivity),
    cardFactors_apply_prime (by norm_num), cardFactors_apply_prime_pow (by norm_num)]
  exact Even.neg_one_pow ⟨k + 1, by ring⟩

/-- The right engine visits sign `−1` infinitely often — on odd powers of `7`
    (`7^{2k+1} ≡ 1 (mod 6)` is a right wing with odd `Ω`). -/
theorem rightSign_neg_infinitely_often :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ (-1 : ℤ) ^ Ω (6 * m + 1) = -1 := by
  intro N
  set k := 6 * N + 6 with hk
  set e := 7 ^ (2 * k + 1) with he
  have hmod : e % 6 = 1 := pow_seven_mod_six _
  have hgt : 2 * k + 1 < e := Nat.lt_pow_self (by norm_num)
  have hebig : 6 * N + 6 < e := by omega
  refine ⟨(e - 1) / 6, by omega, ?_⟩
  have h6m : 6 * ((e - 1) / 6) + 1 = e := by omega
  rw [h6m, he, cardFactors_apply_prime_pow (by norm_num)]
  exact Odd.neg_one_pow ⟨k, by ring⟩

/-- The right engine visits sign `+1` infinitely often — on even powers of `7`. -/
theorem rightSign_pos_infinitely_often :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ (-1 : ℤ) ^ Ω (6 * m + 1) = 1 := by
  intro N
  set k := 6 * N + 6 with hk
  set e := 7 ^ (2 * k) with he
  have hmod : e % 6 = 1 := pow_seven_mod_six _
  have hgt : 2 * k < e := Nat.lt_pow_self (by norm_num)
  have hebig : 6 * N + 6 < e := by omega
  refine ⟨(e - 1) / 6, by omega, ?_⟩
  have h6m : 6 * ((e - 1) / 6) + 1 = e := by omega
  rw [h6m, he, cardFactors_apply_prime_pow (by norm_num)]
  exact Even.neg_one_pow ⟨k, by ring⟩

/-- **The honesty ladder.**  The twin event is the graded sub-state `Ω = 1` of the sign corner
    `(−1, −1)`.  Recurrence of the CORNER is Chowla-adjacent (sign patterns of Liouville at
    consecutive shifts — Tao–Teräväinen territory, not formalised, not assumed); recurrence of
    the graded SUB-STATE is the twin conjecture.  This lemma displays where the parity level ends
    and the graded level begins. -/
theorem twin_corner_grading (m : ℕ) :
    TwinCenterZ m ↔
      signPair m = (-1, -1) ∧ Ω (6 * m - 1) = 1 ∧ Ω (6 * m + 1) = 1 := by
  constructor
  · intro h
    exact ⟨signPair_of_twin h, cardFactors_eq_one_iff_prime.mpr h.1,
      cardFactors_eq_one_iff_prime.mpr h.2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨cardFactors_eq_one_iff_prime.mp h1, cardFactors_eq_one_iff_prime.mp h2⟩

end TwoEngineOscillation
end EuclidsPath
