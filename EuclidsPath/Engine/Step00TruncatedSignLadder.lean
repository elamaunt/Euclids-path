import EuclidsPath.Engine.Step00PackingGeometry

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Truncated sign ladder — capped multiplicity, the sign step law and its flip loci (all green)

`cappedVal K q n` counts the exponents `1 ≤ j ≤ K` with `q^j ∣ n` — the multiplicity of `q`
in `n` capped at `K`, kernel-decidable by construction (the kernel path avoids `padicValNat`
and `Nat.factorization` entirely).  Summing over the clocks `q ≤ B` gives the doubly truncated
degree `truncOmega B K n` and its sign `truncSign B K n = (−1)^{truncOmega B K n}`.

* At `K = 1` the ladder degenerates to the distinct-clock count of the packing layer:
  `truncOmega B 1 n = truncDim B n` (`truncOmega_one_eq_truncDim`) — multiplicity-blind.
* Every finite rung is LAWFUL: `P`-periodic once `q^K ∣ P` for every clock `q ≤ B`
  (`cappedVal_periodic`, `truncOmega_periodic`, `truncSign_periodic` — the `clean_shift`
  pattern one level up), and it extends across a prime gap by ONE factored sign step
  (`truncOmega_extend`, `truncSign_step`, `truncSign_step_one`).
* Every rung is SIGN-FLIPPING on explicit loci: at `K = 1` the flip loci of a new clock
  `q' ≥ 5` on the two wings and the center are exactly the three strike phases
  `(6)⁻¹, −(6)⁻¹, 0` of the oscillation layer (`truncSign_flip_left/right/center`).
* Law preservation across a pair of clocks: `admissible_card_pair` — the `(q₁−2)(q₂−2)`
  product form of the local law; the kernel instance `admissibleCount_11` and the arithmetic
  glue below chain the disclosed censuses `15 → 135 → 1485` by the `(q−2)` extension law.

## S5 DISCLOSURE (the wall, stated honestly)

The full Liouville sign `λ(n) = (−1)^{Ω(n)}` is the limit of this ladder ONLY along growing
caps `K → ∞` (jointly with `B → ∞`).  At `K = 1` the pointwise limit in `B` alone is
`(−1)^{ω(n)}`, which DIFFERS from `λ` on every non-squarefree `n`
(`truncSign_one_not_lambda`: at `n = 12` the `K = 1` ladder says `+1`, Liouville says `−1`).
Every finite rung of the ladder is lawful and sign-flipping — periodic, factored, with
explicit flip loci — but the wall is exactly the exchange of the limit with the law: no Lean
statement about the limit object is made, and no rung claims to approximate `λ`.

No `sorry`, no new axiom, no `native_decide`; standard axioms only.
-/

namespace EuclidsPath
namespace TruncatedSignLadder

open EuclidsPath.PackingGeometry
open EuclidsPath.TwoEngineOscillation
open EuclidsPath.OrderedExponent
open ArithmeticFunction
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

/-! ### Section 1 — capped valuation and the doubly truncated degree -/

/-- Capped valuation: the number of exponents `1 ≤ j ≤ K` with `q^j ∣ n` — the multiplicity
    of `q` in `n` capped at `K`.  Kernel-decidable; no `padicValNat`, no `Nat.factorization`. -/
def cappedVal (K q n : ℕ) : ℕ := ((Finset.Icc 1 K).filter fun j => q ^ j ∣ n).card

/-- At cap `1` the valuation is the divisibility indicator. -/
theorem cappedVal_one (q n : ℕ) : cappedVal 1 q n = if q ∣ n then 1 else 0 := by
  unfold cappedVal
  rw [Finset.Icc_self, Finset.filter_singleton, pow_one]
  split_ifs with h
  · exact Finset.card_singleton 1
  · exact Finset.card_empty

/-- Doubly truncated degree: multiplicities capped at `K`, clocks capped at `B`. -/
def truncOmega (B K n : ℕ) : ℕ :=
  ((Finset.range (B + 1)).filter Nat.Prime).sum fun q => cappedVal K q n

/-- At cap `K = 1` the ladder degenerates to the truncated packing dimension of the packing
    layer — the multiplicity-blind rung. -/
theorem truncOmega_one_eq_truncDim (B n : ℕ) : truncOmega B 1 n = truncDim B n := by
  unfold truncOmega truncDim
  rw [Finset.sum_congr rfl fun q _ => cappedVal_one q n, ← Finset.card_filter,
    Finset.filter_filter]

/-- Truncated sign: the ladder's rung `(B, K)` of the Liouville-shaped sign. -/
def truncSign (B K n : ℕ) : ℤ := (-1) ^ truncOmega B K n

theorem truncSign_ne_zero (B K n : ℕ) : truncSign B K n ≠ 0 :=
  pow_ne_zero _ (by norm_num)

theorem truncSign_eq_one_or_neg_one (B K n : ℕ) :
    truncSign B K n = 1 ∨ truncSign B K n = -1 := by
  unfold truncSign
  rcases Nat.even_or_odd (truncOmega B K n) with h | h
  · exact Or.inl (Even.neg_one_pow h)
  · exact Or.inr (Odd.neg_one_pow h)

/-- **MANDATORY DISCLOSURE.**  The cap `K = 1` is multiplicity-blind and is NOT a
    `λ`-approximation: at `n = 12 = 2² · 3` every rung `truncSign B 1 12` with `B ≥ 3` says
    `+1` (two distinct clocks), while the Liouville sign `(−1)^{Ω(12)} = (−1)³ = −1`.  The
    pointwise limit of the `K = 1` row is `(−1)^ω`, not `λ`; only growing caps reach `λ`,
    and no statement about that limit is made in Lean. -/
theorem truncSign_one_not_lambda :
    truncSign 3 1 12 = 1 ∧ ((-1 : ℤ)) ^ Ω (12 : ℕ) = -1 := by
  constructor
  · decide
  · rw [cardFactors_twelve]; norm_num

/-! ### Section 2 — periodicity: every rung is lawful -/

/-- The capped valuation is `P`-periodic once `q^K ∣ P`: for each `j ≤ K`,
    `q^j ∣ q^K ∣ P`, so the indicator of `q^j ∣ ·` is `P`-periodic. -/
theorem cappedVal_periodic {K q P : ℕ} (h : q ^ K ∣ P) (n : ℕ) :
    cappedVal K q (n + P) = cappedVal K q n := by
  unfold cappedVal
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hjK : j ≤ K := (Finset.mem_Icc.mp hj).2
  have hdvd : q ^ j ∣ P := (pow_dvd_pow q hjK).trans h
  have he : n + P = P + n := by omega
  rw [he]
  exact Nat.dvd_add_right hdvd

/-- The doubly truncated degree is `P`-periodic once every clock `q ≤ B` divides `P` to the
    `K`-th power — the decidable shadow, one cap level above `truncDim_periodic`. -/
theorem truncOmega_periodic {B K P : ℕ}
    (hdvd : ∀ q : ℕ, q.Prime → q ≤ B → q ^ K ∣ P) (n : ℕ) :
    truncOmega B K (n + P) = truncOmega B K n := by
  unfold truncOmega
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqr, hqp⟩ := Finset.mem_filter.mp hq
  exact cappedVal_periodic (hdvd q hqp (by have := Finset.mem_range.mp hqr; omega)) n

/-- The truncated sign inherits the periodicity of its rung. -/
theorem truncSign_periodic {B K P : ℕ}
    (hdvd : ∀ q : ℕ, q.Prime → q ≤ B → q ^ K ∣ P) (n : ℕ) :
    truncSign B K (n + P) = truncSign B K n := by
  unfold truncSign
  rw [truncOmega_periodic hdvd n]

/-! ### Section 3 — the step law: one new clock, one factored sign step -/

/-- **The step theorem.**  When `q'` is the next clock after `B` (no prime strictly between),
    the truncated degree at scale `q'` is the degree at scale `B` plus one capped valuation:
    the ladder climbs one clock at a time. -/
theorem truncOmega_extend {B q' : ℕ} (hq' : q'.Prime) (hBq : B < q')
    (hgap : ∀ p : ℕ, p.Prime → B < p → p ≤ q' → p = q') (K n : ℕ) :
    truncOmega q' K n = truncOmega B K n + cappedVal K q' n := by
  unfold truncOmega
  have hset : (Finset.range (q' + 1)).filter Nat.Prime
      = insert q' ((Finset.range (B + 1)).filter Nat.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hpr, hpp⟩
      rcases Nat.lt_or_ge p (B + 1) with h | h
      · exact Or.inr ⟨h, hpp⟩
      · exact Or.inl (hgap p hpp (by omega) (by omega))
    · rintro (rfl | ⟨hpr, hpp⟩)
      · exact ⟨by omega, hq'⟩
      · exact ⟨by omega, hpp⟩
  have hnotmem : q' ∉ (Finset.range (B + 1)).filter Nat.Prime := by
    simp only [Finset.mem_filter, Finset.mem_range]
    rintro ⟨h, -⟩
    omega
  rw [hset, Finset.sum_insert hnotmem]
  exact Nat.add_comm _ _

/-- The sign form of the step: one new clock contributes one factored sign. -/
theorem truncSign_step {B q' : ℕ} (hq' : q'.Prime) (hBq : B < q')
    (hgap : ∀ p : ℕ, p.Prime → B < p → p ≤ q' → p = q') (K n : ℕ) :
    truncSign q' K n = truncSign B K n * (-1) ^ cappedVal K q' n := by
  unfold truncSign
  rw [truncOmega_extend hq' hBq hgap K n, pow_add]

/-- At cap `1` the sign step is a pure divisibility flip. -/
theorem truncSign_step_one {B q' : ℕ} (hq' : q'.Prime) (hBq : B < q')
    (hgap : ∀ p : ℕ, p.Prime → B < p → p ≤ q' → p = q') (n : ℕ) :
    truncSign q' 1 n = truncSign B 1 n * (if q' ∣ n then -1 else 1) := by
  rw [truncSign_step hq' hBq hgap 1 n, cappedVal_one]
  split_ifs with h
  · norm_num
  · norm_num

/-! ### Section 4 — flip loci: the sign step flips exactly on the strike phases -/

section FlipLoci

variable {B q' : ℕ} [Fact q'.Prime]

/-- **Left flip locus.**  On the left wing `6m − 1` the new clock `q'` flips the `K = 1` sign
    exactly on the left strike phase `m ≡ (6)⁻¹ (mod q')`. -/
theorem truncSign_flip_left (h5 : 5 ≤ q') (hBq : B < q')
    (hgap : ∀ p : ℕ, p.Prime → B < p → p ≤ q' → p = q') {m : ℕ} (hm : 1 ≤ m) :
    truncSign q' 1 (6 * m - 1)
      = truncSign B 1 (6 * m - 1)
        * (if (m : ZMod q') = (6 : ZMod q')⁻¹ then -1 else 1) := by
  rw [truncSign_step_one Fact.out hBq hgap (6 * m - 1)]
  congr 1
  exact if_congr (strike_phase_left h5 hm) rfl rfl

/-- **Right flip locus.**  On the right wing `6m + 1` the flip sits on the antipodal phase
    `m ≡ −(6)⁻¹ (mod q')`. -/
theorem truncSign_flip_right (h5 : 5 ≤ q') (hBq : B < q')
    (hgap : ∀ p : ℕ, p.Prime → B < p → p ≤ q' → p = q') {m : ℕ} (hm : 1 ≤ m) :
    truncSign q' 1 (6 * m + 1)
      = truncSign B 1 (6 * m + 1)
        * (if (m : ZMod q') = -(6 : ZMod q')⁻¹ then -1 else 1) := by
  rw [truncSign_step_one Fact.out hBq hgap (6 * m + 1)]
  congr 1
  exact if_congr (strike_phase_right h5 hm) rfl rfl

/-- **Center flip locus.**  On the stable center `6m` the flip sits on the third phase
    `m ≡ 0 (mod q')` — the three flip loci are the three strike phases of the competition
    law, so the sign ladder rides the same per-clock geometry as the sieve stack. -/
theorem truncSign_flip_center (h5 : 5 ≤ q') (hBq : B < q')
    (hgap : ∀ p : ℕ, p.Prime → B < p → p ≤ q' → p = q') {m : ℕ} :
    truncSign q' 1 (6 * m)
      = truncSign B 1 (6 * m) * (if (m : ZMod q') = 0 then -1 else 1) := by
  rw [truncSign_step_one Fact.out hBq hgap (6 * m)]
  congr 1
  exact if_congr (center_strike h5) rfl rfl

end FlipLoci

/-! ### Section 5 — law preservation: the `(q−2)` product across a pair of clocks -/

/-- **Law preservation, pair form.**  Across two clocks the admissible phases factorize:
    exactly `(q₁ − 2)(q₂ − 2)` of the `q₁ q₂` joint phases survive both engines' strikes at
    both clocks — the two-clock representative of the Hardy–Littlewood product law. -/
theorem admissible_card_pair {q₁ q₂ : ℕ} [Fact q₁.Prime] [Fact q₂.Prime]
    (h₁ : 5 ≤ q₁) (h₂ : 5 ≤ q₂) :
    ((Finset.univ : Finset (ZMod q₁ × ZMod q₂)).filter fun r =>
      (6 * r.1 - 1 ≠ 0 ∧ 6 * r.1 + 1 ≠ 0) ∧ (6 * r.2 - 1 ≠ 0 ∧ 6 * r.2 + 1 ≠ 0)).card
      = (q₁ - 2) * (q₂ - 2) := by
  classical
  have hprod : ((Finset.univ : Finset (ZMod q₁ × ZMod q₂)).filter fun r =>
        (6 * r.1 - 1 ≠ 0 ∧ 6 * r.1 + 1 ≠ 0) ∧ (6 * r.2 - 1 ≠ 0 ∧ 6 * r.2 + 1 ≠ 0))
      = (Finset.univ.filter fun a : ZMod q₁ => 6 * a - 1 ≠ 0 ∧ 6 * a + 1 ≠ 0) ×ˢ
        (Finset.univ.filter fun b : ZMod q₂ => 6 * b - 1 ≠ 0 ∧ 6 * b + 1 ≠ 0) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [hprod, Finset.card_product, admissible_card h₁, admissible_card h₂]

/-! ### Section 6 — kernel census: disclosed instances of the `(q−2)` extension law

The interval CRT form of the extension (an `admissibleCount_extend` theorem equating the
count over the extended period with `(q'−2)` times the count over the base period) is NOT
formalised here; in its place the chain `15 → 135 → 1485` is disclosed as kernel INSTANCES:
`truncCensus_wings_7 = 15` (packing layer), `admissibleCount_11 = 135` below, and
`truncCensus_wings_13 = 1485` (packing layer), glued by the `(q−2)` arithmetic. -/

set_option maxRecDepth 8000 in
/-- Doubly-clean wing count per period at `B = 11`: `135 = 3 · 5 · 9` — the middle rung of
    the disclosed chain `15 → 135 → 1485` (cross-checked externally by the exact CRT layer
    of tools/packing_walk_harness.py before kernel verification). -/
theorem admissibleCount_11 :
    ((Finset.Icc 1 385).filter fun m =>
      truncDim 11 (6 * m - 1) = 0 ∧ truncDim 11 (6 * m + 1) = 0).card = 135 := by decide

/- Disclosed INSTANCES of the `(q−2)`-extension law chaining `truncCensus_wings_7 → 13`:
`135 = 15 · (11 − 2)` and `1485 = 135 · (13 − 2)` — arithmetic glue between the three kernel
censuses, NOT a proved extension theorem. -/
example : (135 : ℕ) = 15 * (11 - 2) := by norm_num
example : (1485 : ℕ) = 135 * (13 - 2) := by norm_num

/-- Signed kernel census at `B = 7`: on `19` of the `35` centers per period the two wings
    carry EQUAL `K = 1` truncated signs (product `+1`); the other `16` split.  Note
    `19 = 35 − 16`: the even-sum locus of the pair `(truncDim 7 wings)` — a kernel-checked
    data point of the sign walk, not a law. -/
theorem signedCensus_7 :
    ((Finset.Icc 1 35).filter fun m =>
      truncSign 7 1 (6 * m - 1) * truncSign 7 1 (6 * m + 1) = 1).card = 19 := by decide

/-
Axiom audit (checked via a scratch `#print axioms` file outside the repo, then deleted):
every declaration of this file depends on at most [propext, Classical.choice, Quot.sound]
— the three standard axioms.  No `sorry`, no `step00FirstCause`, no `native_decide`
(`Lean.ofReduceBool` / `Lean.trustCompiler` absent).
-/

end TruncatedSignLadder
end EuclidsPath
