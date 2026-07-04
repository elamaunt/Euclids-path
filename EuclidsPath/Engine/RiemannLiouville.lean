/-
  RH via Liouville equivalence (arithmetic bridge on ℤ). Prose: prose/31_RiemannLiouville.md.

  Idea (faster than "engine → zeros"): take a READY arithmetic statement equivalent to RH and
  decompose IT in our theory — then its truth = RH automatically.

  Chosen: **Liouville equivalence.** `λ(n) = (−1)^Ω(n)` (`ArithmeticFunction.liouville`, mathlib),
  and RH ⟺ `L(x) = Σ_{n≤x} λ(n) = O(x^{1/2+ε})`.

  WHY it fits our apparatus: `λ(n) = (−1)^cardFactors n` — and `cardFactors` = number of
  prime factors = OUR `rank` at RankNode! And our `deleteFactor` (rank r→r−1) FLIPS `λ`. That is,
  product-rank descent is the dynamics of the Liouville sign, and RH ⟺ balance of those signs (`L` is small).

  Here: the link `λ = (−1)^rank` (from mathlib), the statement `LiouvilleRH` (RH equivalent on ℤ), and
  the branch `RH ⟸ LiouvilleBound` via an explicit bridge. `LiouvilleBound` — the arithmetic named input
  that our rank apparatus must decompose (sign balance ⟺ rank balance).
-/
import Mathlib
import EuclidsPath.Engine.ProductCore

set_option autoImplicit false

namespace EuclidsPath.RiemannLiouville

open ArithmeticFunction Finset

/-- Liouville summatory function `L(x) = Σ_{n=1}^{x} λ(n)`. -/
def L (x : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 x, liouville n

/--
  **Link λ = (−1)^rank (from mathlib).** `liouville n = (−1)^Ω(n)`, and `Ω(n) = cardFactors n` — the
  number of prime factors = OUR rank. Hence the Liouville sign = `(−1)^rank`. -/
theorem liouville_eq_neg_one_pow_rank {n : ℕ} (hn : n ≠ 0) :
    liouville n = (-1) ^ (cardFactors n) :=
  liouville_apply hn

/-- **A prime has λ = −1 (from mathlib).** Bridge for deleteFactor. -/
theorem liouville_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp]; norm_num

/--
  **Sign flip on factor removal (our deleteFactor ↔ λ).** If `n = p·m` (`p` prime),
  then `λ(n) = −λ(m)`: removing one factor (our rank r→r−1) flips the Liouville sign. This is exactly
  `RankNode.deleteFactor` in terms of `λ`. Proved via mathlib multiplicativity `liouville_apply_mul`
  (unconditional — holds even when `m = 0`), so the hypothesis `m ≠ 0` is NOT needed. -/
theorem liouville_flip_of_mul_prime {p m : ℕ} (hp : p.Prime) :
    liouville (p * m) = - liouville m := by
  rw [liouville_apply_mul, liouville_prime hp]; ring

/-- **Version for the deleteFactor step.** If the engine says `n = p·m`, removing `p` flips λ. -/
theorem liouville_flip_of_deleteFactor_eq {n p m : ℕ} (hp : p.Prime) (hdel : n = p * m) :
    liouville n = - liouville m := by
  subst n; exact liouville_flip_of_mul_prime hp

/-! ### Liouville RH equivalence and the branch -/

/-- `LiouvilleBound`: `L(x) = O(x^{1/2+ε})` for all `ε>0` — the ARITHMETIC equivalent of RH on ℤ.
    (Classical theorem: RH ⟺ this bound. Here — as the target statement.) -/
def LiouvilleBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, |(L x : ℝ)| ≤ C * (x : ℝ) ^ (1/2 + ε)

/--
  **Liouville bridge (H_L) — classical equivalence.** `LiouvilleBound ⟺ RH`. This is a KNOWN
  theorem of analytic number theory (not yet in mathlib). Here — as an explicit named-input bridge,
  so that the RH branch is conditional on it (we do not postulate RH; we postulate the classical equivalence).
  `RiemannHypothesis` — from **mathlib** (official formulation via zeros of `riemannZeta`), NOT a
  hand-rolled def. -/
def LiouvilleRHBridge : Prop := LiouvilleBound ↔ RiemannHypothesis

/--
  **RH from Liouville bound (conditional branch).** If the classical bridge `LiouvilleRHBridge` is given and
  `LiouvilleBound` is proved (in our theory — via rank balance), then RH. All the analysis lives in the bridge;
  the arithmetic (`LiouvilleBound`) is what our rank apparatus must decompose. -/
theorem riemann_of_liouville_bound (bridge : LiouvilleRHBridge) (hbound : LiouvilleBound) :
    RiemannHypothesis :=
  bridge.mp hbound

end EuclidsPath.RiemannLiouville
