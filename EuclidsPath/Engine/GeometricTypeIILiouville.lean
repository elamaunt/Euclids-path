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

end TypeII
end Geometric
end EuclidsPath
