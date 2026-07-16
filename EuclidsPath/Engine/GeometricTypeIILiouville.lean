/-
  GeometricTypeIILiouville — the Liouville normal form and the one-wing twin criterion: a SECOND
  explicit 🔴 route to twins, parallel to `CRE`.

  ORIGIN (parity_wall Prime-Chaos session dossier §10 / §11 / §12 / §13). On the `X^{1/3}`-rough set
  every `n ≤ X` has `Ω(n) ∈ {1,2}`, so `1_ℙ(n) = ρ_y(n)(1 − λ(n))/2` (§10, `λ = (−1)^Ω`).  Expanding
  the two-wing product gives the three-residual Liouville form `T = ¼(A − L_− − L_+ + L_±)` (§11) and
  the semiprime-corner form `T = A − B_− − B_+ + C`, `L_± = 2B_± − A` (§12).  Since `C ≥ 0`,
  `T ≥ −½(L_− + L_+)`; hence if the pair-rough count is positive and the summed one-wing Liouville
  bias is negative (`L_− + L_+ < 0`), then `T > 0` — infinitely many twin centers.

  This module builds the SECOND named twin target (mirroring `twins_of_typeII`): the open analytic
  input is `OneWingTarget` (pair-rough positivity + negative parity bias, cofinally), and the
  reduction to `IsTwinCenter` is machine-checked and axiom-clean.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `prime_liouville_form` — `1_ℙ(n) = (1 − (−1)^{Ω(n)})/2` for `Ω(n) ∈ {1,2}` (§10);
    * `one_wing_lower` — `T ≥ −½(L_− + L_+)` (the §12 corner bound);
    * `twinCenter_of_oneWing` — a window with `C ≥ 0` and `L_− + L_+ < 0` contains a twin center;
    * `twins_of_oneWing` — `OneWingProgram ⟹ ∀ N, ∃ m > N, IsTwinCenter m` (green-conditional, the
      SECOND 🔴 target).

  DISCLOSURE. `OneWingTarget` is an open analytic input (a named `Prop`, not a `sorry`); the
  heuristic `1 : log 2` margin (§13) is NOT a proved asymptotic.  Nothing here proves twins.
  twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Step00_Overview
import EuclidsPath.Engine.Residuals

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ## The Liouville normal form on the rough set (§10) -/

/-- **Prime–Liouville form (§10).** On the rough set (`Ω(n) ∈ {1,2}`), the prime indicator is
    `1_ℙ(n) = (1 − (−1)^{Ω(n)})/2`: primes have `Ω = 1` (`λ = −1`), semiprimes `Ω = 2` (`λ = +1`). -/
theorem prime_liouville_form {n : ℕ} (hn : cardFactors n = 1 ∨ cardFactors n = 2) :
    (if n.Prime then (1 : ℝ) else 0) = (1 - (-1) ^ (cardFactors n)) / 2 := by
  rcases hn with h | h
  · rw [h, if_pos (cardFactors_eq_one_iff_prime.mp h)]; norm_num
  · have hnp : ¬ n.Prime := by
      intro hp
      rw [cardFactors_eq_one_iff_prime.mpr hp] at h
      exact absurd h (by norm_num)
    rw [h, if_neg hnp]; norm_num

/-! ## The one-wing corner bound (§12) -/

/-- **One-wing corner bound (§12).** `T ≥ −½(L_− + L_+)`, using `T = A − B_− − B_+ + C`, `C ≥ 0`,
    and `L_± = 2B_± − A`. -/
theorem one_wing_lower {A Bm Bp C Lm Lp T : ℝ}
    (hT : T = A - Bm - Bp + C) (hC : 0 ≤ C) (hLm : Lm = 2 * Bm - A) (hLp : Lp = 2 * Bp - A) :
    -(1 / 2) * (Lm + Lp) ≤ T := by
  rw [hT, hLm, hLp]; linarith

/-! ## The one-wing twin criterion and the reduction (§12) -/

/-- **One-wing window criterion (§12).** A window whose twin count satisfies the corner form
    `T = A − B_− − B_+ + C` with `C ≥ 0` and negative summed parity bias `L_− + L_+ < 0` contains a
    twin center. -/
theorem twinCenter_of_oneWing {I : Finset ℕ} {A Bm Bp C Lm Lp : ℝ}
    (hLm : Lm = 2 * Bm - A) (hLp : Lp = 2 * Bp - A) (hC : 0 ≤ C) (hbias : Lm + Lp < 0)
    (hTcount : ((I.filter (fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime)).card : ℝ)
      = A - Bm - Bp + C) :
    ∃ m ∈ I, IsTwinCenter m := by
  have hbb : Bm + Bp < A := by rw [hLm, hLp] at hbias; linarith
  have hpos : (0 : ℝ)
      < ((I.filter (fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime)).card : ℝ) := by
    rw [hTcount]; linarith
  have hcard : 0 < (I.filter (fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime)).card := by
    exact_mod_cast hpos
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2⟩

/-- **The one-wing target (§12).** The open analytic input: cofinally there is a window above `N`
    whose twin count meets the semiprime-corner form with `C ≥ 0` and negative summed parity bias.
    A named `Prop`, NOT a `sorry`. -/
def OneWingTarget : Prop :=
  ∀ N : ℕ, ∃ (I : Finset ℕ) (A Bm Bp C Lm Lp : ℝ),
    (∀ m ∈ I, N < m) ∧ Lm = 2 * Bm - A ∧ Lp = 2 * Bp - A ∧ 0 ≤ C ∧ Lm + Lp < 0 ∧
    ((I.filter (fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime)).card : ℝ) = A - Bm - Bp + C

/-- **Cofinal twins from the one-wing target (§12).** -/
theorem twinCenters_cofinal_of_oneWing (H : OneWingTarget) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsTwinCenter m := by
  intro N
  obtain ⟨I, A, Bm, Bp, C, Lm, Lp, hN, hLm, hLp, hC, hbias, hTcount⟩ := H N
  obtain ⟨m, hmI, htwin⟩ := twinCenter_of_oneWing hLm hLp hC hbias hTcount
  exact ⟨m, hN m hmI, htwin⟩

/-- The second Type-II twin program: the one-wing Liouville route. -/
structure OneWingProgram where
  target : OneWingTarget

/-- **Twins from the one-wing program (§12).** 🟢 CONDITIONAL: the one-wing Liouville criterion
    yields infinitely many twin centers.  This is the SECOND explicit 🔴 target (parallel to `CRE`):
    pair-rough positivity together with a negative one-wing Liouville bias. -/
theorem twins_of_oneWing (H : OneWingProgram) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsTwinCenter m :=
  twinCenters_cofinal_of_oneWing H.target

/-! ## Grounding the rough hypothesis in actual integers (§10)

The `Ω(n) ∈ {1,2}` hypothesis of `prime_liouville_form` is now DISCHARGED from real arithmetic:
`n < y³` with all prime factors `> y` forces `Ω(n) ≤ 2` (three factors, each `> y`, would exceed
`y³`), and `n < y²` forces primality.  This is exact bookkeeping: it grounds the dichotomy on the
actual rough set and NOTHING MORE — it carries NO information about the SIGN or the size of the
one-wing Liouville bias `L₋ + L₊`; the open content of `OneWingTarget` (pair-rough positivity plus
the negative bias) is untouched and is NOT made more plausible by this grounding. -/

/-- A product of naturals, each `> y`, is at least `(y+1)^length`. -/
private theorem le_prod_of_forall_lt {y : ℕ} :
    ∀ l : List ℕ, (∀ x ∈ l, y < x) → (y + 1) ^ l.length ≤ l.prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x t ih =>
    intro h
    rw [List.prod_cons, List.length_cons, pow_succ]
    have hx : y + 1 ≤ x := h x List.mem_cons_self
    have ht := ih fun z hz => h z (List.mem_cons_of_mem x hz)
    calc (y + 1) ^ t.length * (y + 1) ≤ t.prod * x := Nat.mul_le_mul ht hx
      _ = x * t.prod := Nat.mul_comm _ _

/-- **Rough numbers below `y³` have `Ω ≤ 2` (§10).** If `1 < n < y³` and every prime factor of
    `n` exceeds `y`, then `Ω(n) ≤ 2`: three prime factors, each `> y`, would force `n > y³`. -/
theorem rough_omega_le_two {y n : ℕ} (hn1 : 1 < n) (hn3 : n < y ^ 3)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n → y < p) :
    cardFactors n ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  have hn0 : n ≠ 0 := by omega
  have hall : ∀ x ∈ n.primeFactorsList, y < x := fun x hx =>
    hrough x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx)
  have hprod : n.primeFactorsList.prod = n := Nat.prod_primeFactorsList hn0
  have hge : (y + 1) ^ n.primeFactorsList.length ≤ n := by
    calc (y + 1) ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
        le_prod_of_forall_lt _ hall
      _ = n := hprod
  have hlen : cardFactors n = n.primeFactorsList.length := ArithmeticFunction.cardFactors_apply
  have h3 : 3 ≤ n.primeFactorsList.length := by omega
  have hpow : y ^ 3 < (y + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hmono : (y + 1) ^ 3 ≤ (y + 1) ^ n.primeFactorsList.length :=
    Nat.pow_le_pow_right (by omega) h3
  omega

/-- **Rough numbers below `y²` are prime (§10).** Reuses `Residuals.oldfree_below_sq_prime`. -/
theorem prime_of_rough_small {y n : ℕ} (hn2 : 2 ≤ n) (hny : n < y ^ 2)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n → y < p) : n.Prime := by
  rw [pow_two] at hny
  exact Residuals.oldfree_below_sq_prime hn2 hny
    (fun q hq hqy hdvd => absurd (hrough q hq hdvd) (by omega))

/-- **The rough Liouville dichotomy, grounded (§10).** On the ACTUAL rough set
    (`1 < n < y³`, all prime factors `> y`) the prime indicator equals `(1 − (−1)^{Ω(n)})/2` —
    the `Ω ∈ {1,2}` hypothesis of `prime_liouville_form` is discharged from real arithmetic. -/
theorem rough_liouville_dichotomy {y n : ℕ} (hn1 : 1 < n) (hn3 : n < y ^ 3)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n → y < p) :
    (if n.Prime then (1 : ℝ) else 0) = (1 - (-1) ^ (cardFactors n)) / 2 := by
  apply prime_liouville_form
  have h2 := rough_omega_le_two hn1 hn3 hrough
  have h1 : 1 ≤ cardFactors n := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hmem : p ∈ n.primeFactorsList :=
      (Nat.mem_primeFactorsList (by omega)).mpr ⟨hp, hpd⟩
    have hlen : cardFactors n = n.primeFactorsList.length := ArithmeticFunction.cardFactors_apply
    have : 0 < n.primeFactorsList.length := List.length_pos_of_mem hmem
    omega
  omega

/-! ## The corner-form discharge: target B shrinks to ONE sign condition (§12 / §68)

The registered target `OneWingTarget` bundles six conjuncts.  Below, five of them are discharged
CONSTRUCTIVELY: the corner-form count identity `T = |I| − B₋ − B₊ + C` is exact inclusion–exclusion
over ANY finite window, `C ≥ 0` is a cardinality, and the `L`-relations are definitional.  The
surviving open content of target B is exactly ONE analytic sign condition — cofinally there is a
window above `N` with FEWER composite wings than window points (`B₋ + B₊ < |I|`, i.e. the mean
composite-wing count is below 1; on the rough set this IS the negative Liouville bias
`L₋ + L₊ < 0`).

HONESTY. The intended windows are the PAIR-ROUGH sets (where every wing has `Ω ∈ {1,2}`, composite
means semiprime, and the dossier's `1 : log 2` heuristic margin makes the sign condition the
plausible open content); for RAW windows the condition is expected to FAIL for large `N` (prime
density decays) — choosing a good window family is part of the open problem, not discharged here.
This is a §110 criterion-C event on the REGISTERED target B: to close `OneWingTarget` it now
suffices to prove the single sign condition.  No equivalence is claimed, and no new open `Prop`
is introduced (the sign condition is a PREMISE of a theorem, phrased in the target's own
vocabulary). -/

/-- **The corner-form count identity (§12).** Exact inclusion–exclusion over ANY finite window:
    `#twin = |I| − B₋ − B₊ + C` with `B∓` the composite-wing counts and `C` the both-composite
    count. -/
theorem window_corner_identity (I : Finset ℕ) :
    ((I.filter fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℝ)
      = (I.card : ℝ)
        - ((I.filter fun m => ¬ (6 * m - 1).Prime).card : ℝ)
        - ((I.filter fun m => ¬ (6 * m + 1).Prime).card : ℝ)
        + ((I.filter fun m => ¬ (6 * m - 1).Prime ∧ ¬ (6 * m + 1).Prime).card : ℝ) := by
  classical
  have hcast : ∀ (P : ℕ → Prop) (_ : DecidablePred P),
      ((I.filter P).card : ℝ) = ∑ m ∈ I, (if P m then (1 : ℝ) else 0) := by
    intro P hP
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcast _ _, hcast _ _, hcast _ _, hcast _ _]
  have hcard : (I.card : ℝ) = ∑ _m ∈ I, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h1 : (6 * m - 1).Prime <;> by_cases h2 : (6 * m + 1).Prime <;> simp [h1, h2]

/-- **Target B shrinks to one sign condition (§12/§68, criterion C on a registered target).**
    If cofinally there is a window above `N` whose composite-wing counts satisfy
    `B₋ + B₊ < |I|` (mean composite-wing count `< 1` — on the rough set, exactly the negative
    Liouville bias `L₋ + L₊ < 0`), then `OneWingTarget` holds.  All other conjuncts of the
    target are discharged constructively by `window_corner_identity`. -/
theorem oneWingTarget_of_sign
    (H : ∀ N : ℕ, ∃ I : Finset ℕ, (∀ m ∈ I, N < m) ∧
      (I.filter fun m => ¬ (6 * m - 1).Prime).card
        + (I.filter fun m => ¬ (6 * m + 1).Prime).card < I.card) :
    OneWingTarget := by
  intro N
  obtain ⟨I, hN, hsign⟩ := H N
  classical
  refine ⟨I, (I.card : ℝ),
    ((I.filter fun m => ¬ (6 * m - 1).Prime).card : ℝ),
    ((I.filter fun m => ¬ (6 * m + 1).Prime).card : ℝ),
    ((I.filter fun m => ¬ (6 * m - 1).Prime ∧ ¬ (6 * m + 1).Prime).card : ℝ),
    2 * ((I.filter fun m => ¬ (6 * m - 1).Prime).card : ℝ) - (I.card : ℝ),
    2 * ((I.filter fun m => ¬ (6 * m + 1).Prime).card : ℝ) - (I.card : ℝ),
    hN, rfl, rfl, by positivity, ?_, ?_⟩
  · -- the sign condition
    have hs : ((I.filter fun m => ¬ (6 * m - 1).Prime).card : ℝ)
        + ((I.filter fun m => ¬ (6 * m + 1).Prime).card : ℝ) < (I.card : ℝ) := by
      exact_mod_cast hsign
    linarith
  · -- the corner-form count identity
    exact window_corner_identity I

/-! ## The surviving remainder of target B, in its canonical Liouville form

On PAIR-ROUGH windows (both wings with `Ω ∈ {1,2}` — discharged from real arithmetic by
`rough_omega_le_two` in the critical range) the sign condition of `oneWingTarget_of_sign` is
LITERALLY the negative two-wing Liouville bias: `Σ_{m∈I} λ(6m−1) + Σ_{m∈I} λ(6m+1) < 0` with
`λ = (−1)^Ω`.  This is the dossier's §12/§68 form of residual B, now the SINGLE surviving
analytic statement of the one-wing route.

HONESTY. This is Chowla-adjacent strength — a signed two-point correlation of `λ` along the
twin configuration, the purest known form of the parity wall on route B.  Rewriting the sign
condition in the canonical `λ`-vocabulary does NOT make it easier; it makes it impossible to
misread.  No new open `Prop`; the premise is a hypothesis of a theorem. -/

/-- **Rough-window Liouville sum.** On a rough wing (`Ω ∈ {1,2}` pointwise),
    `Σ_{m∈I} (−1)^{Ω(w m)} = 2·#{composite wings} − |I|`. -/
theorem rough_window_liouville_sum (I : Finset ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ I, cardFactors (w m) = 1 ∨ cardFactors (w m) = 2) :
    ∑ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (w m))
      = 2 * ((I.filter fun m => ¬ (w m).Prime).card : ℤ) - I.card := by
  classical
  have hpt : ∀ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (w m))
      = 2 * (if ¬ (w m).Prime then (1 : ℤ) else 0) - 1 := by
    intro m hm
    rcases hw m hm with h1 | h2
    · have hprime : (w m).Prime := cardFactors_eq_one_iff_prime.mp h1
      rw [h1, if_neg (not_not_intro hprime)]
      norm_num
    · have hnp : ¬ (w m).Prime := by
        intro hp
        rw [cardFactors_eq_one_iff_prime.mpr hp] at h2
        exact absurd h2 (by norm_num)
      rw [h2, if_pos hnp]
      norm_num
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Target B in its canonical Liouville form (the surviving remainder).** If cofinally there is
    a pair-rough window above `N` with NEGATIVE two-wing Liouville bias
    `Σ λ(6m−1) + Σ λ(6m+1) < 0`, then `OneWingTarget` holds.  Together with
    `oneWingTarget_of_sign` and `twins_of_oneWing`, the whole one-wing route to twins now rests
    on this ONE signed correlation statement. -/
theorem oneWingTarget_of_liouville_bias
    (H : ∀ N : ℕ, ∃ I : Finset ℕ, (∀ m ∈ I, N < m) ∧
      (∀ m ∈ I, (cardFactors (6 * m - 1) = 1 ∨ cardFactors (6 * m - 1) = 2)
              ∧ (cardFactors (6 * m + 1) = 1 ∨ cardFactors (6 * m + 1) = 2)) ∧
      (∑ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)))
        + (∑ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (6 * m + 1))) < 0) :
    OneWingTarget := by
  apply oneWingTarget_of_sign
  intro N
  obtain ⟨I, hN, hrough, hbias⟩ := H N
  refine ⟨I, hN, ?_⟩
  have h1 := rough_window_liouville_sum I (fun m => 6 * m - 1) (fun m hm => (hrough m hm).1)
  have h2 := rough_window_liouville_sum I (fun m => 6 * m + 1) (fun m hm => (hrough m hm).2)
  have hsum : (2 * ((I.filter fun m => ¬ (6 * m - 1).Prime).card : ℤ) - I.card)
      + (2 * ((I.filter fun m => ¬ (6 * m + 1).Prime).card : ℤ) - I.card) < 0 := by
    rw [← h1, ← h2]
    exact hbias
  have hZ : ((I.filter fun m => ¬ (6 * m - 1).Prime).card : ℤ)
      + ((I.filter fun m => ¬ (6 * m + 1).Prime).card : ℤ) < (I.card : ℤ) := by
    linarith
  exact_mod_cast hZ

end TypeII
end Geometric
end EuclidsPath
