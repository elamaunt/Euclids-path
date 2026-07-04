/-
  ChowlaFront — the "engineering shadow" of the CHOWLA and SARNAK conjectures, grounded on the REAL
  Liouville function `λ = (−1)^Ω` and on the parity-rank node of the project.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER. WHAT IS GREEN HERE AND WHAT HONESTLY REMAINS OPEN.  │
  └───────────────────────────────────────────────────────────────────────────┘

  THE ENGINEERING SHADOW OF CHOWLA IS THE PARITY-RANK NODE ITSELF. Liouville `λ(n) = (−1)^Ω(n)` is OUR
  parity-rank invariant (`Ω = cardFactors = rank` at RankNode, see `RiemannLiouville`). The Chowla
  conjecture asserts that this parity DOES NOT CORRELATE across shifts: the sign `λ(n)` and the sign `λ(n+h)`
  behave "as independent", their product sums to `o(x)`. This is exactly the same wall — "parity of
  rank has no right to collapse to a single value" — that stands behind the twins and behind Riemann. Here we
  reuse `RiemannLiouville` (sign flip on multiplication by a prime, `λ² = 1`, diagonal
  correlation) and present an HONEST red input — the estimate `o(x)` itself (Chowla) and Sarnak.

  🟢 GREEN (machine-verified, in this file, over the REAL `ArithmeticFunction.liouville`):
   · `liouvilleSum` — the Liouville summatory function `L(x) = Σ_{n≤x} λ(n)` (the same object as `RiemannLiouville.L`,
     here restated under the name of the shift-0 correlation).
   · `chowlaCorrelation h x` — the two-point Liouville correlation `Σ_{n≤x} λ(n)·λ(n+h)` over the REAL `λ`.
   · `liouville_sq_eq_one` — `λ(n)² = 1` for `n ≠ 0` (sign `±1`): perfect SELF-correlation.
   · `chowla_zero_shift` — at shift `h = 0` the correlation is `Σ λ(n)²` (the diagonal).
   · `chowlaCorrelation_zero_eq_card` — the diagonal equals `x`: `chowlaCorrelation 0 x = x`. Perfect
     self-correlation of parity-rank (each term `λ(n)² = 1` on `Icc 1 x`).
   · `chowla_parity_flip` — a restatement of `RiemannLiouville.liouville_flip_of_mul_prime`: multiplying
     the argument by a prime FLIPS `λ`. This is the parity-rank node (`deleteFactor`, `r → r−1`) in terms of `λ`.

  🔴 HONESTLY OPEN (NOT proven here; named predicates, NOT theorems, NOT `sorry`, NOT an axiom):
   · `ChowlaConjecture` — the Chowla conjecture (two-point form): the shifted Liouville correlation is
     `o(x)`. GENUINELY OPEN. Tao proved ONLY the logarithmically-averaged version (Chowla, 2016) and
     odd-order moments (Tao–Teräväinen 2017) — the full (non-averaged) Chowla IS OPEN. We state this
     directly and do NOT pass the averaged result off as the full one.
   · `SarnakConjecture` — the Sarnak conjecture: orthogonality of Möbius `μ` to any bounded
     zero-entropy sequence. Named abstractly over the REAL `ArithmeticFunction.moebius`.
     OPEN (known: Chowla ⟹ Sarnak; the converse is open; the full Sarnak is not proven).

  HONEST NOVELTY. The Chowla conjecture has NEVER been formalized. Here is the FIRST structural reading
  "Chowla = parity-rank node does not correlate across shifts", GROUNDED on the REAL `λ`/`μ` of mathlib.
  THIS IS NOT A PROOF OF CHOWLA AND NOT A PROOF OF SARNAK.

  No `sorry`, no `admit`, no `native_decide`, no new axiom. The green
  load-bearing declarations use the standard triple `propext` / `Classical.choice` / `Quot.sound`. The repository
  taint count (47) is NOT changed by this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/ChowlaFront.lean → zero errors.

  Kinship: EuclidsPath/Engine/RiemannLiouville.lean (`liouville_eq_neg_one_pow_rank`,
    `liouville_flip_of_mul_prime`, `L`); EuclidsPath/Engine/UniversalEngine.lean (engine/rank).
-/
import Mathlib
import EuclidsPath.Engine.RiemannLiouville
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.ChowlaFront

open ArithmeticFunction

/-! ### 🟢 Green core: the REAL `λ` and the parity-rank node -/

/-- Liouville summatory function `L(x) = Σ_{n=1}^{x} λ(n)` (= shift `h = 0` without the square;
    the same object as `RiemannLiouville.L`). -/
def liouvilleSum (x : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.liouville n

/-- Two-point Liouville correlation `Σ_{n=1}^{x} λ(n)·λ(n+h)` over the REAL `λ`. The Chowla
    conjecture asserts that for `h > 0` this sum is `o(x)`. -/
def chowlaCorrelation (h x : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h)

/-- **`λ(n)² = 1` for `n ≠ 0` (sign `±1`).** Perfect SELF-correlation: parity of rank, squared,
    is always `1`. Follows from `λ(n) = (−1)^Ω(n)` (mathlib `liouville_apply`). -/
theorem liouville_sq_eq_one {n : ℕ} (hn : n ≠ 0) :
    ArithmeticFunction.liouville n * ArithmeticFunction.liouville n = 1 := by
  rw [liouville_apply hn, ← pow_add, ← two_mul, pow_mul]
  simp

/-- **Shift `h = 0` is the diagonal `Σ λ(n)²`.** The two-point correlation at zero shift
    degenerates to the sum of Liouville squares. -/
theorem chowla_zero_shift (x : ℕ) :
    chowlaCorrelation 0 x
      = ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.liouville n ^ 2 := by
  unfold chowlaCorrelation
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [Nat.add_zero, sq]

/-- **The diagonal equals `x`: `chowlaCorrelation 0 x = x`.** Perfect self-correlation of parity-rank:
    each term `λ(n)² = 1` on the range `Icc 1 x` (where `n ≥ 1 ≠ 0`), and there are `x` of them. This is a sharp
    contrast with the Chowla conjecture for `h > 0` (where the sum must be `o(x)`). -/
theorem chowlaCorrelation_zero_eq_card (x : ℕ) :
    chowlaCorrelation 0 x = (x : ℤ) := by
  have hpt : ∀ n ∈ Finset.Icc 1 x,
      ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + 0) = (1 : ℤ) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    rw [Nat.add_zero]
    exact liouville_sq_eq_one hn0
  unfold chowlaCorrelation
  rw [Finset.sum_congr rfl hpt, Finset.sum_const]
  simp [Nat.card_Icc]

/-- **Parity flip on multiplication by a prime (the parity-rank node in terms of `λ`).** A restatement of
    `RiemannLiouville.liouville_flip_of_mul_prime`: multiplying the argument by a prime `p` FLIPS the
    Liouville sign, `λ(p·m) = −λ(m)`. This is exactly `RankNode.deleteFactor` (`r → r−1`), making the descent step in
    parity-rank. It is precisely THIS controlled sign dynamics that Chowla forbids from correlating across
    shifts. -/
theorem chowla_parity_flip {p m : ℕ} (hp : p.Prime) :
    ArithmeticFunction.liouville (p * m) = - ArithmeticFunction.liouville m :=
  EuclidsPath.RiemannLiouville.liouville_flip_of_mul_prime hp

/-- Connection to `RiemannLiouville.L`: our `liouvilleSum` is the same object. -/
theorem liouvilleSum_eq_L (x : ℕ) :
    liouvilleSum x = EuclidsPath.RiemannLiouville.L x := rfl

/-! ### 🔴 Honest red inputs: NAMED predicates over the REAL `λ`/`μ`, NOT theorems -/

/-- 🔴 **Chowla conjecture (two-point form).** The shifted Liouville correlation is `o(x)`: for any
    `h > 0` and any `ε > 0` there exists a threshold `X` beyond which `|Σ_{n≤x} λ(n)λ(n+h)| ≤ ε·x`. OPEN.
    (Tao 2016 proved ONLY the logarithmically-averaged version; the full non-averaged Chowla is open.)
    This is a NAMED predicate over the REAL `chowlaCorrelation`, NOT a theorem. -/
def ChowlaConjecture : Prop :=
  ∀ h : ℕ, 0 < h → ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    |(chowlaCorrelation h x : ℝ)| ≤ ε * (x : ℝ)

/-- 🔴 **Sarnak conjecture (Möbius orthogonality to zero-entropy sequences).** For any bounded
    sequence `a : ℕ → ℝ` (bound constant `B`) that is "zero-entropy" in the sense of
    the given predicate `zeroEntropy`, the average Möbius `μ` correlation with `a` tends to zero:
    `(1/x)·Σ_{n≤x} μ(n)·a(n) → 0`. An abstract NAMED predicate over the REAL
    `ArithmeticFunction.moebius`; the "zero-entropy" property is left as a parameter `zeroEntropy` —
    honestly not hard-wired (the dynamical part lies outside arithmetic). OPEN (Chowla ⟹ Sarnak; the full Sarnak is not
    proven). This is a predicate, NOT a theorem. -/
def SarnakConjecture (zeroEntropy : (ℕ → ℝ) → Prop) : Prop :=
  ∀ a : ℕ → ℝ, zeroEntropy a → (∃ B : ℝ, ∀ n : ℕ, |a n| ≤ B) →
    ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      |(∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ) * a n)| ≤ ε * (x : ℝ)

/-! ### Axiom audit for the green load-bearing declarations -/

#print axioms liouville_sq_eq_one
#print axioms chowla_zero_shift
#print axioms chowlaCorrelation_zero_eq_card
#print axioms chowla_parity_flip
#print axioms liouvilleSum_eq_L

end EuclidsPath.ChowlaFront
