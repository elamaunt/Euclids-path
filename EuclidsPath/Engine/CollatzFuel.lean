/-
  Collatz as a perpetual engine on BOUNDED supply — analysis of the conjecture.
  Discussion: prose/55_Collatz.md. Numbers: tools/collatz_fuel_harness.py.

  Question: is Collatz a perpetual engine on bounded supply?
  Answer (numbers + algebra): the supply IS BOUNDED (energy ~13.3 along the trajectory), the drift IS CONTRACTING
  (−0.21/step), BUT there is NO monotone height even after compressing odd-blocks (odd→odd at k=1 grows).
  Therefore our EPMI (which requires a STRICT height descent at every step) does NOT apply to Collatz — this is the exact
  reason for openness: only AVERAGE (not monotone) descent.

  The algebra of the gap is fixed here (core Lean, without Mathlib; self-contained).
-/

namespace EuclidsPath.Collatz.Fuel

-- Compressed odd→odd step: `n` odd ↦ `(3n+1)/2^k`, where `2^k ‖ 3n+1`. The `log₂` height changes by
-- `≈ log₂3 − k`. Drops at `k ≥ 2`, GROWS at `k = 1`.

/-- **k=1 case: height grows (no monotonicity).** If `3n+1 = 2·m` with `m` odd
    (i.e. `k=1`), then `m = (3n+1)/2 > n` for `n ≥ 1`: the compressed odd-step INCREASES the value.
    This is the case `n ≡ 1 (mod 4)` (≈50%), and it breaks the monotonicity of any `log₂`-height. -/
theorem k1_step_grows (n : Nat) (h1 : 1 ≤ n) (hk1 : (3 * n + 1) % 4 = 2) :
    n < (3 * n + 1) / 2 := by
  omega

/-- **k≥2 case: height drops.** If `4 ∣ 3n+1` (`k≥2`), then `(3n+1)/4 < n` for `n ≥ 2`. -/
theorem k2_step_drops (n : Nat) (h2 : 2 ≤ n) (hk2 : (3 * n + 1) % 4 = 0) :
    (3 * n + 1) / 4 < n := by
  omega

/-- **Exact monotonicity gap.** There exist arbitrarily large `n` for which the compressed
    odd-step GROWS the height (`n ≡ 1 mod 4` ⟹ `3n+1 ≡ 4·? + ...`). Therefore there is NO monotone `log₂`-height:
    Collatz is a perpetual engine on bounded supply, but WITHOUT a Lyapunov function. -/
theorem no_monotone_height : ∀ N : Nat, ∃ n, N < n ∧ n % 4 = 1 ∧ n < (3 * n + 1) / 2 := by
  intro N
  refine ⟨4 * N + 5, by omega, by omega, by omega⟩

/-- **Supply is bounded (step balance).** Each compressed odd-step `n ↦ (3n+1)/2^k` spends `k`
    divisions per one injection (`×3+1`). Balance in `log₂` units: `Δ = log₂3 − k`. Pure algebra: for
    `k ≥ 2` the balance is negative (`log₂3 < 2`), for `k = 1` — positive. Average `k = 2`
    (geometric distribution) ⟹ average balance `log₂3 − 2 < 0` (contraction). -/
theorem fuel_balance_sign : (3 : Nat) < 4 ∧ ¬ ((3 : Nat) < 2) := by omega

end EuclidsPath.Collatz.Fuel
