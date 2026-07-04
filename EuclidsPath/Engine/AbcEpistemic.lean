/-
  AbcEpistemic — EPISTEMIC COMPLEMENT of the abc-front (mirror of PNPFirstCause;
  NOT a Collatz variant: abc has no decree and never had one — abc is not among the four
  boundaries of step00FirstCause, the file is fully green). Green front: Engine/AbcFront.lean
  (Mason–Stothers, radical, red gate AbcConjecture).

  WHAT IS HERE (four layers):

  (a) 🟢 Radical toolkit: `natRad_pow` (rad(n^k) = rad(n) for k ≠ 0),
      `natRad_mul_of_coprime` (multiplicativity on coprimes),
      `natRad_mul_dvd`, `natRad_prime` — thin wrappers over the real
      `UniqueFactorizationMonoid.radical_pow` / `radical_mul` / `radical_mul_dvd`
      (Mathlib/RingTheory/Radical/Basic.lean) via `Nat.coprime_iff_isRelPrime`;
      `natRad_prime` goes through `Nat.Prime.primeFactors` (without the normalize step).

  (b) 🟢 NAIVE abc (ε = 0) IS FALSE — mechanically: `abc_exponent_one_counterexample`
      (triple 1 + 8 = 9, rad(1·8·9) = rad(72) = 6 < 9) and the UNBOUNDED quality
      supply `unboundedQualitySupplyExponentOne` — family a = 1,
      c = 3^(2^(k+1)), b = c − 1 with induction 2^(k+3) ∣ 3^(2^(k+1)) − 1 (base
      k = 0: 3² − 1 = 8 = 2³; CORR index shift accounted for: with base 2^(k+2) ∣ 3^(2^k)−1
      the statement is false at k = 0) and multiplicativity of the radical. This is a green
      fact paid for by real mathematics: "c / rad(abc) is unbounded" — the exact
      integer opposite of the polynomial `polynomial_abc_no_escape`.

  (c) 🟢 `polynomial_flt_shadow` — a named polynomial mirror of the arrow
      abc ⟹ FLT: quote of the REAL `Polynomial.flt` (mathlib derives it from
      `Polynomial.flt_catalan`, and that from Mason–Stothers `Polynomial.abc`).
      Over polynomials the arrow is green; over the integers the same arrow is locked behind
      the red gate `AbcConjecture` — here it is NOT claimed.

  (d) 🟢 Epistemic linkage (PNPFirstCause style): `LinearAbcLaw K` —
      uniform LINEAR quality law at ε = 0 (∀ triples, c ≤ K·rad(abc));
      `InternalisedAbcGround` (ground : ∃ K, LinearAbcLaw K / beyondOwnHorizon :
      unbounded supply), `no_internalisedAbcGround`, `abcCause_unknowable`.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONESTY — MANDATORY HEADER (per the skeptic's verdict).             │
  └───────────────────────────────────────────────────────────────────────────┘

  1. THIS IS EPISTEMICS OF THE NAIVE FORM (ε = 0), NOT OF abc ITSELF. `ground` here is NOT
     the open gate `AbcConjecture`, but its naive ε = 0-strengthening (the linear law
     `∃ K, LinearAbcLaw K`). The linkage says: "linear internal grounding
     of quality is impossible — all the openness of abc lives in the ε-slack", and this is a TRUTH
     WEAKER than the epistemics of AbcConjecture itself. For the real gate (ε > 0)
     the analogous linkage DEGENERATES into a tautology: a green (1+ε)-supply does not
     exist and need not exist — classically only
     subpolynomial escapes of Stewart–Tijdeman are known, and an unbounded (1+ε)-supply
     would contradict abc itself. The real red gate `AbcConjecture` is NOT TOUCHED by this
     file: not proven, not refuted, not used as a fact.

  2. MACHINE HONESTY OF THE FORM (Chowla/PNP style): the field `beyondOwnHorizon` is a
     PROVABLE green fact, so the structure `InternalisedAbcGround`
     is semantically equivalent to the pair "law ∧ ¬law"
     (`internalisedAbcGround_semantically_selfNegating`). The substance lives
     NOT in the form of the structure, but in what the contradiction is PAID with: induction
     2^(k+3) ∣ 3^(2^(k+1)) − 1 + multiplicativity of the radical + honest
     pigeonhole instantiation `no_linearAbcLaw_of_unboundedSupply` — exactly the mechanics
     of P/NP (`no_fullPayment_of_unboundedSupply`), not a bare P ∧ ¬P.

  3. NOT Gödel (no independence is claimed — only
     pigeonhole self-destruction of internal self-grounding), NOT a solution of abc,
     NOT a transfer of Mason–Stothers to ℤ (the marker `noPolynomialToIntegerAbcClaimed`
     remains in force).

  No `sorry`, no new axiom, no `native_decide`; the quarantine
  (Engine/CausalClosureAxiom) is NOT imported. Everything is the standard triple
  (`propext` / `Classical.choice` / `Quot.sound`). The repository taint (47) is NOT changed by
  this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/AbcEpistemic.lean
-/

import EuclidsPath.Engine.AbcFront

set_option autoImplicit false

namespace EuclidsPath.AbcFront

/-!
################################################################################
  (a) 🟢 Radical toolkit — pow / mul, thin wrappers over mathlib
################################################################################
-/

/-- **🟢 (PROVEN): radical of a power** — `rad(a^k) = rad(a)` for `k ≠ 0`. A thin
    wrapper over the real `UniqueFactorizationMonoid.radical_pow`
    (Mathlib/RingTheory/Radical/Basic.lean). -/
theorem natRad_pow (a : ℕ) {k : ℕ} (hk : k ≠ 0) : natRad (a ^ k) = natRad a :=
  UniqueFactorizationMonoid.radical_pow a hk

/-- **🟢 (PROVEN): multiplicativity of the radical on coprimes** —
    `rad(a·b) = rad(a)·rad(b)` for `Nat.Coprime a b`. A wrapper over the real
    `UniqueFactorizationMonoid.radical_mul` (which takes `IsRelPrime` WITHOUT
    nonzero hypotheses); the coprimality bridge is `Nat.coprime_iff_isRelPrime`. -/
theorem natRad_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    natRad (a * b) = natRad a * natRad b :=
  UniqueFactorizationMonoid.radical_mul (Nat.coprime_iff_isRelPrime.mp h)

/-- **🟢 (PROVEN): submultiplicativity of the radical (without any hypotheses)** —
    `rad(a·b) ∣ rad(a)·rad(b)`. Quote of `UniqueFactorizationMonoid.radical_mul_dvd`. -/
theorem natRad_mul_dvd (a b : ℕ) : natRad (a * b) ∣ natRad a * natRad b :=
  UniqueFactorizationMonoid.radical_mul_dvd

/-- **🟢 (PROVEN): the radical of a prime is itself.** We go through the explicit formula
    `natRad_eq_prod_primeFactors` and `Nat.Prime.primeFactors` (`p.primeFactors = {p}`),
    bypassing the normalize step `radical_of_prime` (CORR remark about `normalize = id` on ℕ). -/
theorem natRad_prime {p : ℕ} (hp : p.Prime) : natRad p = p := by
  rw [natRad_eq_prod_primeFactors, hp.primeFactors, Finset.prod_singleton]

/-!
################################################################################
  (b) 🟢 Naive abc (ε = 0) is mechanically false: a counterexample and an unbounded supply
################################################################################
-/

/-- **🟢 (PROVEN): naive abc at ε = 0 IS FALSE — a concrete counterexample.**
    Triple `1 + 8 = 9`: `rad(1·8·9) = rad(72) = rad(2³·3²) = 2·3 = 6 < 9`.
    The bound `c ≤ rad(abc)` (without ε-margin) is refuted mechanically: ε in the red
    gate `AbcConjecture` is not decoration. The radical computation is done entirely through
    toolkit (a), without `native_decide`. -/
theorem abc_exponent_one_counterexample :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b ∧
      natRad (a * b * c) < c := by
  refine ⟨1, 8, 9, Nat.one_pos, by norm_num, by norm_num,
    Nat.coprime_one_left 8, ?_⟩
  have hfac : (1 * 8 * 9 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
  have hcop : Nat.Coprime (2 ^ 3) (3 ^ 2) := by norm_num
  rw [hfac, natRad_mul_of_coprime hcop,
    natRad_pow 2 (by norm_num : (3 : ℕ) ≠ 0),
    natRad_pow 3 (by norm_num : (2 : ℕ) ≠ 0),
    natRad_prime Nat.prime_two, natRad_prime Nat.prime_three]
  norm_num

/-- **🟢 Binary pumping (induction carrying the family):**
    `3^(2^(k+1)) = 2^(k+3)·m + 1` with positive `m`. Base `k = 0`:
    `3² = 2³·1 + 1`; step — squaring `(2^(k+3)·m + 1)² = 2^(k+4)·m' + 1` with
    `m' = 2^(k+2)·m² + m`. The additive form is chosen instead of ℕ-subtraction.
    CORR accounted for: the index is shifted (for the form `2^(k+2) ∣ 3^(2^k) − 1` the base `k = 0`
    is false: `4 ∤ 2`). -/
theorem three_pow_two_pow_eq_two_pow_mul_add_one (k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ 3 ^ 2 ^ (k + 1) = 2 ^ (k + 3) * m + 1 := by
  induction k with
  | zero => exact ⟨1, Nat.one_pos, by norm_num⟩
  | succ n ih =>
    obtain ⟨m, hm, hEq⟩ := ih
    refine ⟨2 ^ (n + 2) * m ^ 2 + m,
      Nat.lt_of_lt_of_le hm (Nat.le_add_left m _), ?_⟩
    have hsplit : (3 : ℕ) ^ 2 ^ (n + 1 + 1) = (3 ^ 2 ^ (n + 1)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    rw [hsplit, hEq]
    ring

/-- **🟢 Divisibility form of the pumping (CORR formulation):**
    `2^(k+3) ∣ 3^(2^(k+1)) − 1` for all `k ≥ 0`. A direct consequence of the additive
    form `three_pow_two_pow_eq_two_pow_mul_add_one`. -/
theorem two_pow_dvd_three_pow_two_pow_sub_one (k : ℕ) :
    2 ^ (k + 3) ∣ 3 ^ 2 ^ (k + 1) - 1 := by
  obtain ⟨m, -, hEq⟩ := three_pow_two_pow_eq_two_pow_mul_add_one k
  exact ⟨m, by rw [hEq, Nat.add_sub_cancel]⟩

/-- **Unbounded quality supply at ε = 0** (named Prop): for
    EVERY linear horizon `K` there exists an honest abc-triple whose quality
    breaks through the horizon — `K·rad(a·b·c) < c`. Analogue of `UnboundedCertificateSupply`
    in P/NP: the `beyondOwnHorizon` side of the epistemic linkage. -/
def UnboundedQualitySupplyExponentOne : Prop :=
  ∀ K : ℕ, ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b ∧
    K * natRad (a * b * c) < c

/-- **🟢 (PROVEN): THE QUALITY SUPPLY AT ε = 0 IS UNBOUNDED.** Family
    `a = 1`, `c = 3^(2^(K+1))`, `b = c − 1 = 2^(K+3)·m`:
    `rad(b·c) = rad(b)·3 ≤ 2m·3`, hence `K·rad(abc) ≤ 6Km < 2^(K+3)·m < c`
    (the last strict step is `6K < 2^(K+3)`, i.e. `K < 2^K`).
    Paid for by the induction `three_pow_two_pow_eq_two_pow_mul_add_one` and
    multiplicativity of the radical — NOT a stub. The classic "c/rad(abc) is unbounded"
    becomes green: over ℤ at ε = 0 the quality escape is REAL — the exact
    opposite of the polynomial `polynomial_abc_no_escape`.
    HONESTLY: against real abc (ε > 0) this family does NOT work and need not
    — all the openness of the gate lives in the ε-slack. -/
theorem unboundedQualitySupplyExponentOne : UnboundedQualitySupplyExponentOne := by
  intro K
  obtain ⟨m, hm, hEq⟩ := three_pow_two_pow_eq_two_pow_mul_add_one K
  refine ⟨1, 2 ^ (K + 3) * m, 3 ^ 2 ^ (K + 1), Nat.one_pos,
    mul_pos (pow_pos (by norm_num) (K + 3)) hm, ?_,
    Nat.coprime_one_left _, ?_⟩
  · rw [hEq]; exact Nat.add_comm 1 _
  · -- K · rad(1·b·c) < c for b = 2^(K+3)·m, c = 3^(2^(K+1)) = b + 1
    have hbc : Nat.Coprime (2 ^ (K + 3) * m) (3 ^ 2 ^ (K + 1)) := by
      rw [hEq]
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    have hcrad : natRad (3 ^ 2 ^ (K + 1)) = 3 := by
      rw [natRad_pow 3 (pow_ne_zero _ (by norm_num)),
        natRad_prime Nat.prime_three]
    have h2rad : natRad (2 ^ (K + 3)) = 2 := by
      rw [natRad_pow 2 (by omega : K + 3 ≠ 0), natRad_prime Nat.prime_two]
    -- rad(b) ≤ 2·m: submultiplicativity + rad(2^(K+3)) = 2 + rad(m) ≤ m
    have hbrad : natRad (2 ^ (K + 3) * m) ≤ 2 * m := by
      have hd : natRad (2 ^ (K + 3) * m) ∣ natRad (2 ^ (K + 3)) * natRad m :=
        natRad_mul_dvd _ _
      rw [h2rad] at hd
      have hle : natRad (2 ^ (K + 3) * m) ≤ 2 * natRad m :=
        Nat.le_of_dvd (mul_pos (by norm_num) (natRad_pos m)) hd
      exact hle.trans (Nat.mul_le_mul (Nat.le_refl 2) (natRad_le_self hm.ne'))
    -- strict horizon step: 6K < 2^(K+3) (from K < 2^K)
    have h6K : 6 * K < 2 ^ (K + 3) := by
      have h1 : K < 2 ^ K := Nat.lt_two_pow_self
      calc 6 * K ≤ 8 * K := Nat.mul_le_mul (by norm_num) (Nat.le_refl K)
        _ < 8 * 2 ^ K := mul_lt_mul_of_pos_left h1 (by norm_num)
        _ = 2 ^ (K + 3) := by rw [pow_add]; ring
    rw [one_mul, natRad_mul_of_coprime hbc, hcrad]
    calc K * (natRad (2 ^ (K + 3) * m) * 3)
        ≤ K * (2 * m * 3) :=
          Nat.mul_le_mul (Nat.le_refl K) (Nat.mul_le_mul hbrad (Nat.le_refl 3))
      _ = 6 * K * m := by ring
      _ < 2 ^ (K + 3) * m := mul_lt_mul_of_pos_right h6K hm
      _ < 2 ^ (K + 3) * m + 1 := Nat.lt_succ_self _
      _ = 3 ^ 2 ^ (K + 1) := hEq.symm

/-!
################################################################################
  (c) 🟢 Polynomial mirror of the arrow abc ⟹ FLT
################################################################################
-/

section PolynomialShadow

open Polynomial

/-- **🟢 FLT SHADOW OVER POLYNOMIALS (PROVEN; polynomial mirror of the arrow
    abc ⟹ FLT).** Over a field `k` with `(n : k) ≠ 0`, `n ≥ 3`: coprime
    nonzero `a, b, c : k[X]` with `a^n + b^n = c^n` are forced to be constants.
    A pure quote of the REAL `Polynomial.flt` (Mathlib/NumberTheory/FLT/Polynomial.lean);
    mathlib derives it from `Polynomial.flt_catalan`, and that from Mason–Stothers
    `Polynomial.abc` (our green anchor `polynomial_abc_shadow`).
    HONESTLY: over polynomials the arrow "abc-world ⟹ FLT" is green; over ℤ the same arrow
    is locked behind the red gate `AbcConjecture` and here it is NOT claimed
    (`noPolynomialToIntegerAbcClaimed`). The first bridge of the abc-front to the neighbouring
    FLT-branch (`BealFront.polynomial_fermat_catalan_shadow` — the Catalan form;
    here — specifically the FLT special case). -/
theorem polynomial_flt_shadow
    {k : Type*} [Field k]
    {n : ℕ} (hn : 3 ≤ n) (chn : (n : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  Polynomial.flt hn chn ha hb hc hab heq

end PolynomialShadow

/-!
################################################################################
  (d) 🟢 Epistemic linkage (PNPFirstCause style) — for the NAIVE ε = 0-form
################################################################################
-/

namespace Epistemic

/-- **Uniform linear quality law at ε = 0** (naive ε = 0-strengthening
    of abc): ONE constant `K` linearly grounds all coprime triples —
    `c ≤ K·rad(a·b·c)`. HONESTLY: this is NOT the gate `AbcConjecture` (there `K(ε)` at
    exponent `1 + ε`, ε > 0) — it is its naive linear form, and exactly that
    is refuted green below. -/
def LinearAbcLaw (K : ℕ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
    c ≤ K * natRad (a * b * c)

/-- **🟢 (PROVEN): the naive law `K = 1` is refuted by a single witness** —
    the triple `1 + 8 = 9` from `abc_exponent_one_counterexample`. -/
theorem naiveAbcLaw_refuted : ¬ LinearAbcLaw 1 := by
  intro hlaw
  obtain ⟨a, b, c, ha, hb, hsum, hcop, hlt⟩ := abc_exponent_one_counterexample
  have hle : c ≤ 1 * natRad (a * b * c) := hlaw a b c ha hb hsum hcop
  rw [one_mul] at hle
  exact absurd hle (not_le.mpr hlt)

/-- **🟢 PIGEONHOLE INSTANTIATION (load-bearing, mirror of `no_fullPayment_of_unboundedSupply`
    in P/NP):** the unbounded quality supply is incompatible with ANY uniform
    linear law — the supply at horizon `K` hits law `K` head-on.
    Both arguments are load-bearing: the lemma is parameterized by the supply (Chowla's CORR
    style), not hardwired under a proven fact. -/
theorem no_linearAbcLaw_of_unboundedSupply
    (hsup : UnboundedQualitySupplyExponentOne)
    (hlaw : ∃ K : ℕ, LinearAbcLaw K) : False := by
  obtain ⟨K, hK⟩ := hlaw
  obtain ⟨a, b, c, ha, hb, hsum, hcop, hlt⟩ := hsup K
  exact absurd (hK a b c ha hb hsum hcop) (not_le.mpr hlt)

/-- **🟢 (PROVEN): there is NO linear quality law for any `K`** —
    paid for by the proven supply `unboundedQualitySupplyExponentOne`.
    HONESTLY: the NAIVE (ε = 0) form is refuted; the real gate `AbcConjecture`
    (ε > 0) is not touched — there such a supply does not exist and need not. -/
theorem no_linearAbcLaw (K : ℕ) : ¬ LinearAbcLaw K :=
  fun hK => no_linearAbcLaw_of_unboundedSupply
    unboundedQualitySupplyExponentOne ⟨K, hK⟩

/-- **Internal self-grounding of linear quality grounding.** The machine
    simultaneously (a) holds a uniform linear quality law for SOME
    horizon `K` (`ground`) and (b) sees its own unbounded quality
    supply past EVERY horizon (`beyondOwnHorizon`).
    HONESTY (mandatory, Chowla/PNP style): `beyondOwnHorizon` is a PROVABLE
    green fact (`unboundedQualitySupplyExponentOne`), so the structure
    is semantically equivalent to the pair "law ∧ ¬law"
    (`internalisedAbcGround_semantically_selfNegating` below). The substance
    lives in the PAYMENT of the contradiction: induction `2^(k+3) ∣ 3^(2^(k+1)) − 1` +
    multiplicativity of the radical + pigeonhole `no_linearAbcLaw_of_unboundedSupply`.
    And this is epistemics of the NAIVE ε = 0-form: about `AbcConjecture` itself — nothing. -/
structure InternalisedAbcGround : Prop where
  ground : ∃ K : ℕ, LinearAbcLaw K
  beyondOwnHorizon : UnboundedQualitySupplyExponentOne

/-- "Internal knowledge of the abc cause" = internal self-grounding of linear
    quality grounding (naive ε = 0-form). -/
abbrev InternalKnowledgeOfAbcCause : Prop := InternalisedAbcGround

/-- **🟢 Self-grounding self-destructs** — both fields are load-bearing: `ground`
    gives horizon `K`, `beyondOwnHorizon` hits exactly it (pigeonhole
    `no_linearAbcLaw_of_unboundedSupply`, NOT ex falso). GREEN. -/
theorem no_internalisedAbcGround : InternalisedAbcGround → False :=
  fun H => no_linearAbcLaw_of_unboundedSupply H.beyondOwnHorizon H.ground

/-- **"CANNOT BE KNOWN FROM INSIDE" — THEOREM** (mirror of `pnpCause_unknowable`,
    `collatzCause_unknowable`, `twinNode_unknowable`): internal linear
    self-grounding of quality is impossible. GREEN, without hypotheses.
    HONEST CAVEAT (mandatory): this is epistemics of the NAIVE form (ε = 0);
    the real abc-gate (`AbcConjecture`, ε > 0) is NOT solved by this, NOT
    refuted and in no way touched — for it the analogous linkage
    degenerates (Stewart–Tijdeman: only subpolynomial escapes are known;
    an unbounded (1+ε)-supply would contradict abc itself). -/
theorem abcCause_unknowable : ¬ InternalKnowledgeOfAbcCause :=
  no_internalisedAbcGround

/-- **Self-grounding is semantically "law ∧ ¬law" (machine honesty,
    mirror of `internalisedPNPGround_semantically_selfNegating`):** since
    `beyondOwnHorizon` is provable, the fields are provably exact complements, and the structure
    is equivalent to the contradictory pair. The substance lives NOT in the form, but in the
    payment: family `3^(2^(k+1))` + multiplicativity of the radical + pigeonhole.
    The reverse arrow is ex falso (honestly). -/
theorem internalisedAbcGround_semantically_selfNegating :
    InternalisedAbcGround ↔
      ((∃ K : ℕ, LinearAbcLaw K) ∧ ¬ (∃ K : ℕ, LinearAbcLaw K)) :=
  ⟨fun H => ⟨H.ground, no_linearAbcLaw_of_unboundedSupply H.beyondOwnHorizon⟩,
   fun h => (h.2 h.1).elim⟩

/-- Final epistemic status of the abc-horizon (mirror of
    `pnp_locked_behind_engine_status`, WITHOUT the decree conjunct — abc has no boundary in
    `step00FirstCause` and should not have one): the quality supply at ε = 0 is
    unbounded (theorem) / there is no linear law for any `K` (theorem) /
    internal self-grounding is impossible (theorem) / the implication "polynomial
    abc ⟹ integer" is honestly NOT claimed (marker; the red gate
    `AbcConjecture` itself lives in AbcFront and remains OPEN). The polynomial
    side of the pair is `polynomial_abc_no_escape` (escape forbidden) against
    `unboundedQualitySupplyExponentOne` (over ℤ at ε = 0 escape is REAL). -/
theorem abc_locked_behind_engine_status :
    UnboundedQualitySupplyExponentOne ∧
    (∀ K : ℕ, ¬ LinearAbcLaw K) ∧
    (¬ InternalKnowledgeOfAbcCause) ∧
    NoPolynomialToIntegerAbcClaimed :=
  ⟨unboundedQualitySupplyExponentOne, no_linearAbcLaw, abcCause_unknowable,
   noPolynomialToIntegerAbcClaimed⟩

end Epistemic

/-!
################################################################################
  SUMMARY (LOUD HONEST)

  🟢 PROVEN HERE (standard axiom triple):
     · toolkit: natRad_pow, natRad_mul_of_coprime, natRad_mul_dvd, natRad_prime;
     · naive abc (ε = 0) is false: abc_exponent_one_counterexample (1+8=9),
       naive law K=1 refuted (naiveAbcLaw_refuted);
     · quality supply is unbounded: unboundedQualitySupplyExponentOne
       (family 3^(2^(k+1)), induction two_pow_dvd_three_pow_two_pow_sub_one);
     · no linear law for any K (no_linearAbcLaw);
     · polynomial mirror abc ⟹ FLT: polynomial_flt_shadow (quote of Polynomial.flt);
     · epistemics of the naive form: no_internalisedAbcGround, abcCause_unknowable,
       internalisedAbcGround_semantically_selfNegating, abc_locked_behind_engine_status.

  🔴 NOT TOUCHED (open, as before): AbcConjecture (integer abc, ε > 0).
     The epistemic linkage above is about the NAIVE ε = 0-form; for the real gate
     it degenerates (Stewart–Tijdeman), and we do NOT hide this.

  No sorry / native_decide / new axiom; the quarantine is not imported;
  taint 47 is unchanged.
################################################################################
-/

#print axioms natRad_pow
#print axioms natRad_mul_of_coprime
#print axioms natRad_mul_dvd
#print axioms natRad_prime
#print axioms abc_exponent_one_counterexample
#print axioms three_pow_two_pow_eq_two_pow_mul_add_one
#print axioms two_pow_dvd_three_pow_two_pow_sub_one
#print axioms unboundedQualitySupplyExponentOne
#print axioms polynomial_flt_shadow
#print axioms Epistemic.naiveAbcLaw_refuted
#print axioms Epistemic.no_linearAbcLaw_of_unboundedSupply
#print axioms Epistemic.no_linearAbcLaw
#print axioms Epistemic.no_internalisedAbcGround
#print axioms Epistemic.abcCause_unknowable
#print axioms Epistemic.internalisedAbcGround_semantically_selfNegating
#print axioms Epistemic.abc_locked_behind_engine_status

end EuclidsPath.AbcFront
