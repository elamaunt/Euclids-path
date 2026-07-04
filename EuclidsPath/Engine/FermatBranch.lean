/-
  FermatBranch — honest bridge Fermat ↔ twins: minus-side, quadratic
  chain, twin instances up to 65537.

  ⚠️ MAIN HONESTY: infinitely many Fermat primes does NOT follow from the twin-prime
  hypothesis — neither trivially nor by any known method. Moreover, the heuristic sign
  here is OPPOSITE to Mersenne: only F₀–F₄ are known to be prime, while F₅–F₃₂ are
  provably composite, so the input FermatTwinCentersUnbounded is most likely FALSE.
  The implication "twins ⟹ Fermat" is NOT claimed here
  (marker NoTwinsToFermatImplicationClaimed).

  WHAT IS PROVEN (mathlib Nat.fermatNumber, std axioms, no sorry):
    * fermatNumber_mod_six / six_mul_fermatCenter — EMBEDDING into the programme language:
      for k ≥ 1 the Fermat number F_k = 2^(2^k) + 1 ≡ 5 (mod 6) — the MINUS-side
      of the center c_k = (F_k + 1)/6 (contrast with Mersenne: plus-side there);
      k = 0 is excluded (F₀ = 3 does not lie on the grid 6m ± 1);
    * isTwinCenter_fermatCenter_iff — twin-criterion of the Fermat center:
      c_k is a twin-center ⟺ F_k and F_k + 2 are both prime;
    * fermat_twin_instances — concrete Fermat twin primes: k = 1 gives (5, 7),
      k = 2 gives (17, 19), k = 4 gives (65537, 65539) — both prime; this is the
      strongest concrete localization of twins in the programme;
    * fermat_twin_non_instance — k = 3 does NOT give a pair: F₃ + 2 = 259 = 7·37;
    * fermatCenter_chain — the center chain is QUADRATIC: c' = 6c² − 4c + 1,
      written without subtraction as c' + 4c = 6c² + 1; unlike the linear
      chain 5c + 1 for prime divisors, it carries no identity with a fixed prime divisor;
    * twinLowersInfinite_of_fermatTwins — the ONLY honest direction,
      and it goes the OTHER way: ∞ Fermat twins ⟹ twin-prime conjecture.
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.FermatBranch

open EuclidsPath

/-- Fermat center: `c_k = (F_k + 1) / 6` (for `k ≥ 1` the division is exact). -/
def fermatCenter (k : ℕ) : ℕ := (Nat.fermatNumber k + 1) / 6

/-- **MINUS-SIDE (proven):** for `k ≥ 1` the Fermat number `F_k ≡ 5 (mod 6)` —
    it lives on the minus-side of the grid `6m − 1` (contrast with Mersenne: plus). -/
theorem fermatNumber_mod_six {k : ℕ} (hk : 1 ≤ k) :
    Nat.fermatNumber k % 6 = 5 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpow : (2 : ℕ) ^ 2 ^ (j + 1) = 4 ^ 2 ^ j := by
    have hexp : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
    rw [hexp, pow_mul]
    norm_num
  have h43 : 4 ^ 2 ^ j % 3 = 1 := by
    have h := Nat.pow_mod 4 (2 ^ j) 3
    simpa using h
  have hmod3 : Nat.fermatNumber (j + 1) % 3 = 2 := by
    show (2 ^ 2 ^ (j + 1) + 1) % 3 = 2
    rw [hpow]
    omega
  have hmod2 : Nat.fermatNumber (j + 1) % 2 = 1 :=
    Nat.odd_iff.mp (Nat.odd_fermatNumber _)
  omega

/-- **EMBEDDING INTO THE PROGRAMME LANGUAGE (proven):** for `k ≥ 1` the division in the center
    is exact: `6·c_k = F_k + 1`. -/
theorem six_mul_fermatCenter {k : ℕ} (hk : 1 ≤ k) :
    6 * fermatCenter k = Nat.fermatNumber k + 1 := by
  have h5 := fermatNumber_mod_six hk
  unfold fermatCenter
  omega

/-- Fermat number as the MINUS-side of the center: `F_k = 6·c_k − 1` for `k ≥ 1`. -/
theorem fermatNumber_eq_sixCenter_sub_one {k : ℕ} (hk : 1 ≤ k) :
    Nat.fermatNumber k = 6 * fermatCenter k - 1 := by
  have h := six_mul_fermatCenter hk
  omega

/-- Positivity of the center: `c_k ≥ 1` for `k ≥ 1`. -/
theorem fermatCenter_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ fermatCenter k := by
  have h := six_mul_fermatCenter hk
  have h3 := Nat.three_le_fermatNumber k
  omega

/-- **TWIN-CRITERION OF THE FERMAT CENTER (proven):** the center `c_k` is a twin-center ⟺
    `F_k` and `F_k + 2` are both prime. The Fermat number is the LOWER member of the pair. -/
theorem isTwinCenter_fermatCenter_iff {k : ℕ} (hk : 1 ≤ k) :
    IsTwinCenter (fermatCenter k) ↔
      (Nat.fermatNumber k).Prime ∧ (Nat.fermatNumber k + 2).Prime := by
  have heq := six_mul_fermatCenter hk
  have h3 := Nat.three_le_fermatNumber k
  unfold IsTwinCenter
  have hlo : 6 * fermatCenter k - 1 = Nat.fermatNumber k := by omega
  have hhi : 6 * fermatCenter k + 1 = Nat.fermatNumber k + 2 := by omega
  rw [hlo, hhi]

/-- `c_1 = 1`: pair `(5, 7)`. -/
theorem fermatCenter_one : fermatCenter 1 = 1 := by
  norm_num [fermatCenter, Nat.fermatNumber]

/-- `c_2 = 3`: pair `(17, 19)`. -/
theorem fermatCenter_two : fermatCenter 2 = 3 := by
  norm_num [fermatCenter, Nat.fermatNumber]

/-- `c_3 = 43`: NOT a twin-center (259 = 7·37, see below). -/
theorem fermatCenter_three : fermatCenter 3 = 43 := by
  norm_num [fermatCenter, Nat.fermatNumber]

/-- Concrete Fermat twin primes: `k = 1` gives the pair `(5, 7)`, `k = 2` — `(17, 19)`,
    `k = 4` — `(65537, 65539)`: both prime, the strongest concrete
    localization of twins in the programme. -/
theorem fermat_twin_instances :
    IsTwinCenter (fermatCenter 1) ∧ IsTwinCenter (fermatCenter 2) ∧
      IsTwinCenter (fermatCenter 4) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isTwinCenter_fermatCenter_iff (by norm_num)]
    constructor <;> norm_num [Nat.fermatNumber]
  · rw [isTwinCenter_fermatCenter_iff (by norm_num)]
    constructor <;> norm_num [Nat.fermatNumber]
  · rw [isTwinCenter_fermatCenter_iff (by norm_num)]
    constructor <;> norm_num [Nat.fermatNumber]

/-- **HONESTY (failure at `k = 3`):** `c_3 = 43` is NOT a twin-center:
    `F_3 + 2 = 259 = 7·37` is composite. Fermat twins are not automatic. -/
theorem fermat_twin_non_instance : ¬ IsTwinCenter (fermatCenter 3) := by
  rw [isTwinCenter_fermatCenter_iff (by norm_num)]
  rintro ⟨-, h⟩
  norm_num [Nat.fermatNumber] at h

/-- **QUADRATIC CENTER CHAIN (proven):** `c_{k+1} = 6·c_k² − 4·c_k + 1`,
    written without subtraction: `c_{k+1} + 4·c_k = 6·c_k² + 1`. Unlike the
    linear chain `5c + 1` for prime divisors, the quadratic chain carries no
    identity with a fixed prime divisor. -/
theorem fermatCenter_chain {k : ℕ} (hk : 1 ≤ k) :
    fermatCenter (k + 1) + 4 * fermatCenter k = 6 * fermatCenter k ^ 2 + 1 := by
  have h1 := six_mul_fermatCenter hk
  have h2 := six_mul_fermatCenter (show 1 ≤ k + 1 by omega)
  have h4 := Nat.three_le_fermatNumber k
  -- We move to ℤ: the mathlib recurrence `F_{k+1} = (F_k − 1)² + 1` contains
  -- Nat-subtraction; we lift it away via `1 ≤ F_k`.
  have h3 : (Nat.fermatNumber (k + 1) : ℤ) =
      ((Nat.fermatNumber k : ℤ) - 1) ^ 2 + 1 := by
    have h := Nat.fermatNumber_succ k
    zify [show 1 ≤ Nat.fermatNumber k by omega] at h
    exact h
  have h1' : 6 * (fermatCenter k : ℤ) = (Nat.fermatNumber k : ℤ) + 1 := by
    exact_mod_cast h1
  have h2' : 6 * (fermatCenter (k + 1) : ℤ) =
      (Nat.fermatNumber (k + 1) : ℤ) + 1 := by
    exact_mod_cast h2
  have hFk : (Nat.fermatNumber k : ℤ) = 6 * (fermatCenter k : ℤ) - 1 := by
    linarith
  have hFk1 : (Nat.fermatNumber (k + 1) : ℤ) =
      6 * (fermatCenter (k + 1) : ℤ) - 1 := by
    linarith
  rw [hFk, hFk1] at h3
  have hZ : (fermatCenter (k + 1) : ℤ) + 4 * (fermatCenter k : ℤ) =
      6 * (fermatCenter k : ℤ) ^ 2 + 1 := by
    nlinarith [h3]
  exact_mod_cast hZ

/-- Strict growth of centers starting from `k = 1` (from the strict growth of Fermat numbers). -/
theorem fermatCenter_strictMono_from_one {k : ℕ} (hk : 1 ≤ k) :
    fermatCenter k < fermatCenter (k + 1) := by
  have h1 := six_mul_fermatCenter hk
  have h2 := six_mul_fermatCenter (show 1 ≤ k + 1 by omega)
  have hlt : Nat.fermatNumber k < Nat.fermatNumber (k + 1) :=
    Nat.fermatNumber_strictMono (by omega)
  omega

/-- Unboundedness of Fermat twin primes (INPUT hypothesis, much stronger than twins;
    heuristically most likely FALSE: only F₀–F₄ are prime, F₅–F₃₂ are composite). -/
def FermatTwinCentersUnbounded : Prop :=
  ∀ N : ℕ, ∃ k : ℕ, 1 ≤ k ∧ N < Nat.fermatNumber k ∧
    (Nat.fermatNumber k).Prime ∧ (Nat.fermatNumber k + 2).Prime

/-- **HONEST DIRECTION (proven):** Fermat twins ⟹ twins.
    This is the ONLY trivial implication between the two topics — and it goes THIS way. -/
theorem twinLowersInfinite_of_fermatTwins
    (H : FermatTwinCentersUnbounded) : TwinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k, hk1, hgt, h1, h2⟩ := H B
  have hmem : Nat.fermatNumber k ∈ TwinLowers := by
    show IsTwinPair (Nat.fermatNumber k)
    exact ⟨h1, h2⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- **HONESTY (coverage):** the implication `twins ⟹ Fermat` is NOT claimed,
    NOT proven, and NOT known to mathematics: twins yield ∞ twin-centers, but
    say nothing about the doubly-exponentially rare Fermat centers; moreover,
    the heuristic sign here is REVERSED (F₅–F₃₂ are composite). The converse
    implication is trivial and proven above. -/
abbrev NoTwinsToFermatImplicationClaimed : Prop := True

theorem noTwinsToFermatImplicationClaimed :
    NoTwinsToFermatImplicationClaimed := trivial

#print axioms six_mul_fermatCenter
#print axioms isTwinCenter_fermatCenter_iff
#print axioms fermat_twin_instances
#print axioms fermatCenter_chain
#print axioms twinLowersInfinite_of_fermatTwins

end EuclidsPath.FermatBranch
