/-
  ChowlaEpistemic — EPISTEMIC COMPLEMENT of the Chowla/Sarnak front (chapter 54).
  Mirror of PNPFirstCause / LehmerEpistemic (NOT the Collatz variant: Chowla has no
  decree and never had one — Chowla is not among the four boundaries of step00FirstCause,
  the file is entirely green).
  Green front: Engine/ChowlaFront.lean (λ² = 1, diagonal = x, parity flip).

  WHAT THIS IS. "Solving the parity-shift node from inside" = presenting a COMPLETE internal
  solution of the sign dynamics of λ, i.e. a parity collapse: a tail on which the Liouville sign
  is CONSTANT (`PerfectParityCollapse`: ∃ N, ∀ m ≥ N, λ(m) = λ(N)) — the only
  form in which a finite internal system could "know" the parity behaviour of the rank
  in full. This self-destructs NOT by substitution P ∧ ¬P but by a genuine
  flip-wall: doubling the argument FLIPS the sign (λ(2m) = −λ(m), reuse of
  `chowla_parity_flip` at p = 2 — NOT a third copy of `liouville_flip_of_mul_prime`,
  CORR §4), and λ² = 1 forbids the sign from being zero — the tail constant perishes on
  the very first doubling (`no_parityCollapse_of_flip`). The same currency as the pigeonhole
  `no_fullPayment_of_unboundedSupply` for P/NP and the Northcott wall for Lehmer.

  CONSUMPTION, NOT DECORATION (CORR §1). The wall lemma `no_parityCollapse_of_flip`
  is PARAMETRISED by the flip supply: it takes `flip : ∀ m, λ(2m) = −λ(m)` as a hypothesis
  and consumes it in a contradiction. Therefore `no_internalisedChowlaGround` is
  `fun H => no_parityCollapse_of_flip H.beyondOwnHorizon H.ground`: BOTH fields are
  load-bearing at the term level (exact mirror of
  `no_fullPayment_of_unboundedSupply H.beyondOwnHorizon H.resolves`).

  HONEST BOUNDARIES (mandatory, by the sceptic's verdict):
  (1) The field `beyondOwnHorizon` is a provable green fact (`liouville_doubling_flip`),
      so the structure `InternalisedChowlaGround` is EXTENSIONALLY equivalent to
      a single field `ground` — disclosed machine-wise by the lemma
      `internalisedChowlaGround_iff_collapse`. The payment for the contradiction is REAL
      (flip + λ² = 1, not a tautology), but the bundle is weaker than the P/NP reference,
      where BOTH legs are independent non-trivial predicates.
  (2) The bundle covers ONLY the collapse mode (deterministic tail constancy of the sign).
      For a statistical refutation of Chowla (correlation of order c·x WITHOUT a deterministic
      law) the bundle degenerates: the green fact "deviation ⟹ engine" does NOT exist,
      and constructing it is open mathematics, essentially Chowla itself. Hence the summary
      name contains NO "engine": here the wall is honestly the flip-wall
      (`chowla_locked_behind_flip_wall`); there is no engine fact for Chowla in the repo.
  (3) This is model-internal epistemics of the parity-shift node, NOT a proof
      and NOT a refutation of the Chowla/Sarnak conjectures: the red gates `ChowlaConjecture` /
      `SarnakConjecture` remain red; NOTHING is asserted about them.
  (4) This is NOT Gödel: no independence — only flip-self-destruction of
      internal self-grounding.

  🟢 GREEN HERE (everything over the REAL `ArithmeticFunction.liouville`):
   · `liouville_doubling_flip` — λ(2m) = −λ(m) (reuse of `chowla_parity_flip`, p = 2);
   · `liouville_no_doubling_fixpoint` — there is NO m ≠ 0 with λ(2m) = λ(m);
   · `no_parityCollapse_of_flip` / `no_parityCollapse` — perfect parity collapse
     (tail constancy of λ) is impossible;
   · `chowlaCorrelation_parity` — correlation ≡ x (mod 2): sum of x terms ±1;
     corollary `chowlaCorrelation_ne_zero_of_odd` — zero is UNREACHABLE on the odd
     slice (pointwise rigidity of the red gate's value: "o(x)" cannot
     identically be zero);
   · `liouville_two_pow` — λ(2^k) = (−1)^k: unbounded supply of BOTH signs
     (`liouville_attains_both_signs_cofinally`) — sign dynamics are non-degenerate;
   · epistemic package: `no_internalisedChowlaGround`, `chowlaCause_unknowable`,
     summary `chowla_locked_behind_flip_wall`.

  No sorry, no new axiom, no native_decide; the quarantine
  (CausalClosureAxiom) is NOT imported. All green load-bearing declarations use the standard
  triple propext / Classical.choice / Quot.sound. The repository taint (47) is NOT
  changed by this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/ChowlaEpistemic.lean

  Lineage: Engine/ChowlaFront.lean (green core + red gates),
    Engine/RiemannLiouville.lean (flip at the source), Engine/PNPFirstCause.lean and
    Engine/TwinNodeEpistemic.lean / Engine/LehmerEpistemic.lean (epistemic references).
-/
import EuclidsPath.Engine.ChowlaFront

set_option autoImplicit false

namespace EuclidsPath.ChowlaFront.Epistemic

open ArithmeticFunction

/-! ## Flip-wall: sign dynamics of λ under doubling (🟢) -/

/-- 🟢 **Flip supply under doubling.** Multiplying the argument by 2 FLIPS the Liouville sign:
    `λ(2m) = −λ(m)` for ALL `m` (at `m = 0` both sides are zero). Reuse of
    `chowla_parity_flip` at `p = 2` (which itself is a restatement of
    `RiemannLiouville.liouville_flip_of_mul_prime`; a third copy is NOT spawned, CORR §4).
    Role: inexhaustible "fuel" of the flip-wall — the field `beyondOwnHorizon` below. -/
theorem liouville_doubling_flip (m : ℕ) :
    ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m :=
  chowla_parity_flip Nat.prime_two

/-- 🟢 **Perfect collapse under doubling is pointwise impossible.** There is NO `m ≠ 0`
    with `λ(2m) = λ(m)`: the flip gives `λ(2m) = −λ(m)`, and `λ² = 1` forbids the sign from
    being zero. The first hard Chowla-type fact: the parity of the rank must oscillate
    already along doublings. -/
theorem liouville_no_doubling_fixpoint {m : ℕ} (hm : m ≠ 0) :
    ArithmeticFunction.liouville (2 * m) ≠ ArithmeticFunction.liouville m := by
  rw [liouville_doubling_flip m]
  intro hEq
  have hzero : ArithmeticFunction.liouville m = 0 := by omega
  have hsq := liouville_sq_eq_one hm
  rw [hzero] at hsq
  norm_num at hsq

/-! ## (a) Parity collapse and its impossibility (🟢) -/

/-- **Perfect parity collapse** — the "complete internal solution" of the parity-shift node:
    there exists a tail on which the Liouville sign is CONSTANT
    (`∃ N, ∀ m ≥ N, λ(m) = λ(N)`). The only form in which a finite internal system could
    "know" the parity behaviour of the rank in full. This is the ground of the epistemic
    bundle below; the Chowla conjecture asserts MUCH more (uncorrelation across all shifts),
    so impossibility of collapse is merely the finite germ — NOT a solution of the conjecture. -/
def PerfectParityCollapse : Prop :=
  ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
    ArithmeticFunction.liouville m = ArithmeticFunction.liouville N

/-- 🟢 **FLIP-WALL (load-bearing, parametrised by the supply — CORR §1).** Any
    flip supply `∀ m, λ(2m) = −λ(m)` destroys perfect parity collapse:
    in the constancy tail take `m ≥ max(N,1)` — then `λ(2m) = λ(N) = λ(m)`
    by constancy, but `λ(2m) = −λ(m)` by the flip, so `λ(m) = 0` against
    `λ(m)² = 1`. The flip supply is CONSUMED by the contradiction (not decoration) —
    exact analogue of the pigeonhole `no_fullPayment_of_unboundedSupply` for P/NP. -/
theorem no_parityCollapse_of_flip
    (flip : ∀ m : ℕ,
      ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m) :
    PerfectParityCollapse → False := by
  rintro ⟨N, hN⟩
  have hm1 : 1 ≤ max N 1 := le_max_right N 1
  have hmN : N ≤ max N 1 := le_max_left N 1
  have hm0 : max N 1 ≠ 0 := by omega
  have e1 := hN (max N 1) hmN
  have e2 := hN (2 * max N 1) (by omega)
  have e3 := flip (max N 1)
  have hzero : ArithmeticFunction.liouville (max N 1) = 0 := by omega
  have hsq := liouville_sq_eq_one hm0
  rw [hzero] at hsq
  norm_num at hsq

/-- 🟢 **Perfect parity collapse is impossible (unconditionally).** The flip supply is
    a theorem (`liouville_doubling_flip`), so the wall fires without hypotheses:
    tail constancy of the Liouville sign does NOT exist. -/
theorem no_parityCollapse : PerfectParityCollapse → False :=
  no_parityCollapse_of_flip liouville_doubling_flip

/-! ## (b) Green correlation arithmetic: parity and unreachability of zero (🟢) -/

/-- 🟢 **Correlation ≡ x (mod 2).** Each term `λ(n)·λ(n+h)` on `Icc 1 x` is `±1`
    (both λ are signs, `λ² = 1`), so the term ≡ 1 (mod 2) and the sum of `x` terms has
    parity `x`. Pointwise rigidity of the red gate `ChowlaConjecture`. -/
theorem chowlaCorrelation_parity (h x : ℕ) :
    (2 : ℤ) ∣ (chowlaCorrelation h x - (x : ℤ)) := by
  have hdef : chowlaCorrelation h x
      = ∑ n ∈ Finset.Icc 1 x,
          ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) := rfl
  have hx : (x : ℤ) = ∑ _n ∈ Finset.Icc 1 x, (1 : ℤ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [hdef, hx, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  have hnh0 : n + h ≠ 0 := by omega
  have hsq : (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h))
      * (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h)) = 1 := by
    rw [mul_mul_mul_comm, liouville_sq_eq_one hn0, liouville_sq_eq_one hnh0, one_mul]
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hsq) with ht | ht
  · rw [ht]; exact ⟨0, by ring⟩
  · rw [ht]; exact ⟨-1, by ring⟩

/-- 🟢 The same parity in `Even` form: `chowlaCorrelation h x − x` is even. -/
theorem chowlaCorrelation_sub_even (h x : ℕ) :
    Even (chowlaCorrelation h x - (x : ℤ)) := by
  obtain ⟨c, hc⟩ := chowlaCorrelation_parity h x
  exact ⟨c, by omega⟩

/-- 🟢 **Zero is unreachable on the odd slice.** For odd `x` the correlation is NOT equal
    to zero: the sum of an odd number of terms `±1` is odd. The "o(x)" of the red gate
    cannot identically be zero — the correlation must oscillate (cheap but genuine
    deduction; mirror of `oddLandauPrime_even_k` for Landau). -/
theorem chowlaCorrelation_ne_zero_of_odd {h x : ℕ} (hx : Odd x) :
    chowlaCorrelation h x ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := chowlaCorrelation_parity h x
  obtain ⟨j, hj⟩ := hx
  rw [h0] at hc
  omega

/-! ## (c) Unbounded supply of both signs (🟢) -/

/-- 🟢 **`λ(2^k) = (−1)^k`.** Powers of two supply both Liouville signs in pure form:
    `Ω(2^k) = k` (mathlib `cardFactors_apply_prime_pow`), so the sign is exactly
    `(−1)^k`. Style of `liouville_prime` from `RiemannLiouville`. -/
theorem liouville_two_pow (k : ℕ) :
    ArithmeticFunction.liouville (2 ^ k) = (-1 : ℤ) ^ k := by
  rw [liouville_apply (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)),
    cardFactors_apply_prime_pow Nat.prime_two]

/-- 🟢 **Both signs are attained cofinally.** Arbitrarily far out there are both `λ = 1`
    (even powers of two) and `λ = −1` (odd powers): sign dynamics are non-degenerate,
    the flip supply is infinite. Green analogue of
    `UnboundedCertificateSupply` for P/NP — honest contrast to the impossibility of
    collapse (`no_parityCollapse`). -/
theorem liouville_attains_both_signs_cofinally (N : ℕ) :
    (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = 1) ∧
    (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = -1) := by
  constructor
  · refine ⟨2 ^ (2 * N), ?_, ?_⟩
    · exact le_trans (by omega : N ≤ 2 * N) (Nat.le_of_lt Nat.lt_two_pow_self)
    · rw [liouville_two_pow]
      exact Even.neg_one_pow ⟨N, by ring⟩
  · refine ⟨2 ^ (2 * N + 1), ?_, ?_⟩
    · exact le_trans (by omega : N ≤ 2 * N + 1) (Nat.le_of_lt Nat.lt_two_pow_self)
    · rw [liouville_two_pow]
      exact Odd.neg_one_pow ⟨N, by ring⟩

/-! ## (d) Model: internal solution = self-grounding beyond one's own horizon -/

/-- **Internal self-grounding of the parity-shift node solution.** The system
    simultaneously (a) holds the COMPLETE internal solution — parity collapse,
    tail constancy of the sign (`ground`), and (b) sees the flip dynamics of the sign
    under doubling (`beyondOwnHorizon`).

    SUBSTANTIVENESS: the contradiction is supplied by the flip-wall
    `no_parityCollapse_of_flip`, which CONSUMES both fields at the term level
    (CORR §1) — not Collatz's `fun H => H.b H.g`.
    HONEST CAVEAT: `beyondOwnHorizon` is a provable green fact
    (`liouville_doubling_flip`), so the structure is extensionally equivalent to
    bare `ground` (machine-wise: `internalisedChowlaGround_iff_collapse`) — the payment
    is real, but the second leg is free by construction; this is weaker than the P/NP
    reference, where both legs are independent non-trivial predicates. -/
structure InternalisedChowlaGround : Prop where
  ground : PerfectParityCollapse
  beyondOwnHorizon : ∀ m : ℕ,
    ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m

/-- "Internal knowledge of the Chowla cause" = internal self-grounding of the node solution. -/
abbrev InternalKnowledgeOfChowlaCause : Prop := InternalisedChowlaGround

/-- 🟢 Self-grounding self-destructs — the flip-wall consumes BOTH fields:
    `no_parityCollapse_of_flip H.beyondOwnHorizon H.ground` (exact mirror of
    `no_fullPayment_of_unboundedSupply H.beyondOwnHorizon H.resolves` for P/NP). -/
theorem no_internalisedChowlaGround : InternalisedChowlaGround → False :=
  fun H => no_parityCollapse_of_flip H.beyondOwnHorizon H.ground

/-- 🟢 **"CANNOT BE KNOWN FROM INSIDE" — THEOREM** (mirror of `pnpCause_unknowable` /
    `lehmerCause_unknowable` / `collatzCause_unknowable`): a complete internal
    solution of the parity-shift node is impossible. NOT an assertion about the
    Chowla/Sarnak conjectures themselves — their red gates are untouched. -/
theorem chowlaCause_unknowable : ¬ InternalKnowledgeOfChowlaCause :=
  no_internalisedChowlaGround

/-- 🟢 **Machine honesty (form disclosure):** the field `beyondOwnHorizon` is a theorem,
    so the bundle is extensionally equivalent to a single field `ground`.
    Substantiveness lives NOT in the independence of the legs but in the PRICE of the
    contradiction: flip + `λ² = 1` (`no_parityCollapse_of_flip`) — real arithmetic, not
    the tautology P ∧ ¬P. Mirror of `internalisedPNPGround_semantically_selfNegating`. -/
theorem internalisedChowlaGround_iff_collapse :
    InternalisedChowlaGround ↔ PerfectParityCollapse :=
  ⟨fun H => H.ground, fun hg => ⟨hg, liouville_doubling_flip⟩⟩

/-! ## Summary: the node is locked behind the flip-wall (🟢) -/

/-- 🟢 **Final epistemic status of the parity-shift node** (mirror of
    `pnp_locked_behind_engine_status` WITHOUT the decree conjunct — Chowla has no
    boundary of step00FirstCause; the name honestly contains NO "engine": there is no
    engine fact for Chowla in the repo; the wall here is flip + `λ² = 1`):
    (1) the flip supply under doubling is inexhaustible (theorem);
    (2) both signs are attained cofinally — the supply is non-degenerate (theorem);
    (3) the node is unknowable from inside (theorem);
    (4) perfect parity collapse is impossible (theorem);
    (5) the correlation is never zero on odd slices (theorem) —
        the "o(x)" of the red gate cannot identically be zero.
    The red gates `ChowlaConjecture`/`SarnakConjecture` remain red. -/
theorem chowla_locked_behind_flip_wall :
    (∀ m : ℕ,
      ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m) ∧
    (∀ N : ℕ, (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = 1) ∧
      (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = -1)) ∧
    (¬ InternalKnowledgeOfChowlaCause) ∧
    (PerfectParityCollapse → False) ∧
    (∀ h x : ℕ, Odd x → chowlaCorrelation h x ≠ 0) :=
  ⟨liouville_doubling_flip,
   liouville_attains_both_signs_cofinally,
   chowlaCause_unknowable,
   no_parityCollapse,
   fun _h _x hx => chowlaCorrelation_ne_zero_of_odd hx⟩

/-! ## Axiom audit: the entire module is green (standard triple), repo taint does NOT change -/
#print axioms liouville_doubling_flip
#print axioms liouville_no_doubling_fixpoint
#print axioms no_parityCollapse_of_flip
#print axioms no_parityCollapse
#print axioms chowlaCorrelation_parity
#print axioms chowlaCorrelation_sub_even
#print axioms chowlaCorrelation_ne_zero_of_odd
#print axioms liouville_two_pow
#print axioms liouville_attains_both_signs_cofinally
#print axioms no_internalisedChowlaGround
#print axioms chowlaCause_unknowable
#print axioms internalisedChowlaGround_iff_collapse
#print axioms chowla_locked_behind_flip_wall

end EuclidsPath.ChowlaFront.Epistemic
