/-
  Collatz as a SPECIAL CASE of Euclid's perpetual engine — structural facts (core Lean, no Mathlib).
  Discussion: prose/55_Collatz.md. Numbers: tools/collatz_engine_harness.py.

  Euclid's engine: EVERY step is a strict descent `A·h' < h` (A≥1) ⟹ `no_infinite_descent` ⟹ ALWAYS
  halts; height is `StrictAnti` ⟹ never returns (no cycle).

  Collatz (accelerated map `T`): even step `n↦n/2` — descent EXACTLY by 2 (boundary, not strict at A=2);
  odd step `n↦(3n+1)/2` — ASCENT (fuel injection «+1»). Hence Collatz does NOT satisfy
  the strict-descent premise — so its termination is OPEN (unlike Euclid's engine).

  Self-contained (core Lean, no import): duplicates of `T` with other Collatz files are intentional.
-/

namespace EuclidsPath.Collatz.Engine

/-- Accelerated Collatz map: even `n↦n/2`, odd `n↦(3n+1)/2` (the forced division is inlined). -/
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- **Even step — descent EXACTLY by 2** (`2·(n/2)=n`): this is the BOUNDARY of the engine's descent (`A·h'=h`, not `<`).
    For any `A>2` the even step would not be a descent; at `A=2` it sits exactly on the boundary. -/
theorem even_marginal (n : Nat) (h : n % 2 = 0) : 2 * (n / 2) = n := by omega

/-- **Odd step — ASCENT of the raw value («+1» = fuel):** `n < 3n+1`. -/
theorem odd_raw_ascends (n : Nat) : n < 3 * n + 1 := by omega

/-- **The odd accelerated step also ascends:** `(3n+1)/2 > n` for `n ≥ 1`. Fuel injected. -/
theorem odd_accel_ascends (n : Nat) (h1 : 1 ≤ n) (h : n % 2 = 1) : n < (3 * n + 1) / 2 := by omega

/-- **Collatz is NOT a strict engine:** on odd `n≥1` the step is NOT a descent (`¬ (T n < n)`).
    Hence `no_infinite_descent` does NOT apply to Collatz — termination is not guaranteed by the law. -/
theorem not_descent_on_odd (n : Nat) (h1 : 1 ≤ n) (h : n % 2 = 1) : ¬ (T n < n) := by
  unfold T; rw [if_neg (show ¬ (n % 2 = 0) by omega)]; omega

/-- **Fuel balance:** one multiplication by 3 cannot be cancelled by ONE halving (`2 < 3`), at least two are needed
    (`3 ≤ 4 = 2²`). Therefore for descent we need halvings/triplings > log₂3 ≈ 1.585 (numerically ≈ 2.016). -/
theorem one_tripling_needs_two_halvings : ¬ (3 ≤ 2) ∧ (3 ≤ 2 * 2) := by omega

/-- **Trivial cycle = HALT state of the engine:** `1 → 2 → 1` (absorbing minimum).
    Any FOREIGN cycle would be a perpetual engine (return), forbidden by `engine_never_returns`
    ONLY under strict descent — which Collatz lacks, so the absence of foreign cycles is OPEN. -/
theorem trivial_halt_cycle : T 1 = 2 ∧ T 2 = 1 := by decide

end EuclidsPath.Collatz.Engine
