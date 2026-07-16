/-
  GeometricTypeIIConductor — exact-conductor resummation and the degree-two connected core.

  ORIGIN (parity_wall Prime-Chaos session dossier §41 / §42 / §45 / §48 / §49 / §50). After the
  exact-conductor resummation kills all principal extensions (§45), the hard remainder decomposes by
  chaos degree.  Prime conductors (`c = p`) are controlled by the large sieve; composite-singleton
  sectors are algebraically ABSENT (§48).  The MINIMAL connected core is the degree-two exact
  conductor `c = pq` (§49) — this is the current center of the parity wall (§66).  Its spectral
  sizes (§50) sit on the same threshold as the global chaos: the `S₂`-mass is the SQUARE of the
  divergent `Σ 1/(p−2)`, while the `S₄`-mass is the SQUARE of the convergent `Σ 1/(p−2)³`.  The
  Pythagorean divisor partition (§41/§42) distributes the mass over balanced factorizations with
  nonnegative weights and `μ(u)μ(v) = μ(d)`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `degree_two_S2_mass` — `Σ_{p,q} 1/((p−2)(q−2)) = (Σ_p 1/(p−2))²` (diverges: the wall);
    * `degree_two_S4_mass` — `Σ_{p,q} 1/((p−2)³(q−2)³) = (Σ_p 1/(p−2)³)²` (converges: summable budget);
    * `pythagorean_two` — the degree-two divisor partition `2 log p log q = (log p+log q)² − S₂`;
    * `degreeTwoCore` — the minimal connected core (named structural object, sign `+` since μ(pq)=+1).

  DISCLOSURE. The degree-two connected core `R^{[2]}` is the current 🔴 wall center; its short
  Type-II restriction is open (§51). twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The degree-two spectral masses (§50) -/

/-- **Degree-two S₂-mass (§50).** `Σ_{p,q} 1/((p−2)(q−2)) = (Σ_p 1/(p−2))²`.  Since `Σ_p 1/(p−2)`
    diverges over the primes, this degree-two mass is UNBOUNDED — the wall sits here. -/
theorem degree_two_S2_mass (P : Finset ℕ) :
    ∑ p ∈ P, ∑ q ∈ P, 1 / (((p : ℝ) - 2) * ((q : ℝ) - 2)) = (∑ p ∈ P, 1 / ((p : ℝ) - 2)) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  rw [one_div_mul_one_div]

/-- **Degree-two S₄-mass (§50).** `Σ_{p,q} 1/((p−2)³(q−2)³) = (Σ_p 1/(p−2)³)²`.  Since `Σ_p 1/(p−2)³`
    converges, this degree-two mass is BOUNDED — a summable local budget. -/
theorem degree_two_S4_mass (P : Finset ℕ) :
    ∑ p ∈ P, ∑ q ∈ P, 1 / (((p : ℝ) - 2) ^ 3 * ((q : ℝ) - 2) ^ 3)
      = (∑ p ∈ P, 1 / ((p : ℝ) - 2) ^ 3) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  rw [one_div_mul_one_div]

/-! ## The Pythagorean divisor partition, degree two (§41 / §42) -/

/-- **Degree-two Pythagorean partition (§41).** For `d = pq` the ordered factorizations carry
    `Σ_{uv=d} log u log v = 2 log p log q = (log p + log q)² − ((log p)² + (log q)²)`; the trivial
    pairs `(1,d),(d,1)` carry zero weight. -/
theorem pythagorean_two (a b : ℝ) : 2 * (a * b) = (a + b) ^ 2 - (a ^ 2 + b ^ 2) := by ring

/-- **Signed partition sign (§42).** For a squarefree `d = uv` with coprime `u,v`,
    `μ(u)μ(v) = μ(uv)`, so the Pythagorean weights carry the sign `μ(d)` unchanged. -/
theorem signed_partition_sign {u v : ℕ} (h : Nat.Coprime u v) :
    ArithmeticFunction.moebius u * ArithmeticFunction.moebius v = ArithmeticFunction.moebius (u * v) :=
  (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h).symm

/-! ## The minimal connected core (§49) -/

/-- **The degree-two connected core (§49).** `R^{[2]} = Σ_{p<q} 1/((p−2)(q−2)) · W(p,q)`, where
    `W(p,q) = Σ_{χ_p≠1, χ_q≠1} η(χ_pχ_q) A(χ_pχ_q) B(χ_pχ_q)` is the fully connected character
    coefficient.  The sign is `+` (since `μ(pq) = +1`).  This is the minimal connected core and the
    current center of the parity wall — a named structural object, its short Type-II restriction
    being the open target (§51). -/
noncomputable def degreeTwoCore (P : Finset ℕ) (W : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P, (if p < q then 1 / (((p : ℝ) - 2) * ((q : ℝ) - 2)) * W p q else 0)

end TypeII
end Geometric
end EuclidsPath
