/-
  "The engine does not work backward at two points": an exact fact about exclusivity.
  Prose: prose/23_NoBackward.md.

  Numerical reconnaissance (tools/RESULTS_rank2.md): the score matrix `N_ij ≈ rank-1` (independence
  `r₋ ⊥ r₊`), and four-corner = sign of the rank-2 correction, ROBUSTLY negative at all scales,
  because `Cov(r₋,r₊) < 0` everywhere. The source of this sign is EXACT exclusivity: a prime divides
  at most one side (`Carrier.no_large_shared_divisor`, `shared gcd ∣ 2`).

  Here the exact mechanism is recorded: under exclusivity `X_p·Y_p = 0` the diagonal (same prime on
  both sides = "moving backward at one point") VANISHES, and the product `(Σ X)(Σ Y)` is entirely
  off-diagonal. This is precisely "the engine does not work backward at two points": no self-transition 2→2.

  Everything uses finite sums (Finset). No analysis / distribution / sieve.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/-- **The diagonal vanishes (exclusivity).** If for every prime `X_p·Y_p = 0` (divides ≤ 1 side),
    then the sum of "self"-terms `Σ_p X_p·Y_p = 0` — no backward movement at one point. -/
theorem exclusive_diag_zero {ι : Type*} (s : Finset ι) (X Y : ι → ℕ)
    (hexcl : ∀ i ∈ s, X i * Y i = 0) :
    ∑ i ∈ s, X i * Y i = 0 :=
  Finset.sum_eq_zero hexcl

/--
  **The engine does not work backward at two points.** Under exclusivity `X_p·Y_p = 0` the product
  of ranks `(Σ_p X_p)·(Σ_q Y_q)` is entirely OFF-DIAGONAL:
  `(Σ X)·(Σ Y) = Σ_i Σ_{j≠i} X_i·Y_j`. The diagonal (self-) term is absent.
  This is the exact source of the negative association `(r₋,r₊)` (numerically `Cov < 0` everywhere).
-/
theorem exclusive_no_backward {ι : Type*} [DecidableEq ι] (s : Finset ι) (X Y : ι → ℕ)
    (hexcl : ∀ i ∈ s, X i * Y i = 0) :
    (∑ i ∈ s, X i) * (∑ j ∈ s, Y j) = ∑ i ∈ s, ∑ j ∈ s.erase i, X i * Y j := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum, ← Finset.add_sum_erase s (fun j => X i * Y j) hi, hexcl i hi, zero_add]

end EuclidsPath
