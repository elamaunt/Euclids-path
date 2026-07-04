/-
  Model four-corner (fractal negative association). Prose: prose/20_Fractality.md.

  Derivation from the fractal structure: under ± symmetry (equal weight on each side) and exclusivity
  (a prime divides ≤ 1 side, `Carrier.no_large_shared_divisor`) the rank generating function is the
  product `∏(c+w(x+y))`, i.e. a function of `s=x+y`. Then the coefficients are
      N_{ij} = Q_{i+j} · C(i+j, i),     Q_k = coeff. of s^k.
  In the equilibrium model (n primes, weight w): Q_k = C(n,k)·w^k, and the four-corner
      N₀₀·N₃₃ ≤ N₀₃·N₃₀
  reduces to the binomial `20·C(n,6) ≤ C(n,3)²` (20 = C(6,3) — constant from R_CRT=20e₆/e₃²).

  The proof is ELEMENTARY (the "choose-within-choose" identity + monotonicity). No distribution/sieve.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/--
  **Binomial four-corner.** For all `n`: `20·C(n,6) ≤ C(n,3)²` (for `n<6` the left side is 0).
  Key: `C(n,6)·C(6,3) = C(n,3)·C(n−3,3)` (choose-within-choose) and `C(n−3,3) ≤ C(n,3)`.
-/
theorem four_corner_binom (n : ℕ) : 20 * n.choose 6 ≤ (n.choose 3) ^ 2 := by
  have hid : n.choose 6 * (6 : ℕ).choose 3 = n.choose 3 * (n - 3).choose (6 - 3) :=
    Nat.choose_mul (by norm_num)
  have h20 : (6 : ℕ).choose 3 = 20 := by decide
  have hsub : (6 : ℕ) - 3 = 3 := by norm_num
  rw [h20, hsub] at hid
  -- hid : n.choose 6 * 20 = n.choose 3 * (n-3).choose 3
  have hmono : (n - 3).choose 3 ≤ n.choose 3 := Nat.choose_le_choose 3 (Nat.sub_le n 3)
  calc 20 * n.choose 6 = n.choose 6 * 20 := by ring
    _ = n.choose 3 * (n - 3).choose 3 := hid
    _ ≤ n.choose 3 * n.choose 3 := by gcongr
    _ = (n.choose 3) ^ 2 := by ring

/--
  **Model four-corner** (equilibrium symmetric exclusive model, weight `w`).
  Ledger: `N₀₀ = 1`, `N₀₃ = N₃₀ = C(n,3)·w³`, `N₃₃ = 20·C(n,6)·w⁶`. Then `N₀₀·N₃₃ ≤ N₀₃·N₃₀`.
-/
theorem model_four_corner (n w : ℕ) :
    1 * (20 * n.choose 6 * w ^ 6) ≤ (n.choose 3 * w ^ 3) * (n.choose 3 * w ^ 3) := by
  have key : 20 * n.choose 6 ≤ (n.choose 3) ^ 2 := four_corner_binom n
  calc 1 * (20 * n.choose 6 * w ^ 6) = (20 * n.choose 6) * w ^ 6 := by ring
    _ ≤ (n.choose 3) ^ 2 * w ^ 6 := by gcongr
    _ = (n.choose 3 * w ^ 3) * (n.choose 3 * w ^ 3) := by ring

/--
  **Singularity is unreachable (strict positivity).** For `n ≥ 7`: `20·C(n,6) < C(n,3)²`
  STRICTLY. Equality `D=0` (equilibrium/independence = "the perpetual engine runs") is only possible in
  the degenerate case (few primes); at a non-trivial layer (`n ≥ 7`) the positivity is strict.
  Key to strictness: `C(n−3,3) < C(n,3)` (Pascal: `C(n,3) = C(n−1,2) + C(n−1,3)`, `C(n−1,2) > 0`).
-/
theorem four_corner_binom_strict {n : ℕ} (hn : 7 ≤ n) :
    20 * n.choose 6 < (n.choose 3) ^ 2 := by
  have hid : n.choose 6 * (6 : ℕ).choose 3 = n.choose 3 * (n - 3).choose (6 - 3) :=
    Nat.choose_mul (by norm_num)
  rw [show (6 : ℕ).choose 3 = 20 from by decide, show (6 : ℕ) - 3 = 3 from by norm_num] at hid
  have hpos : 0 < n.choose 3 := Nat.choose_pos (by omega)
  have hpascal : (n - 1).choose 2 + (n - 1).choose 3 = n.choose 3 := by
    rw [← Nat.choose_succ_succ (n - 1) 2]; congr 1; omega
  have hlt : (n - 3).choose 3 < n.choose 3 := by
    have h1 : (n - 3).choose 3 ≤ (n - 1).choose 3 := Nat.choose_le_choose 3 (by omega)
    have h2 : 0 < (n - 1).choose 2 := Nat.choose_pos (by omega)
    omega
  have heq : 20 * n.choose 6 = n.choose 3 * (n - 3).choose 3 := by omega
  rw [heq]
  calc n.choose 3 * (n - 3).choose 3 < n.choose 3 * n.choose 3 :=
        mul_lt_mul_of_pos_left hlt hpos
    _ = (n.choose 3) ^ 2 := by ring

end EuclidsPath
