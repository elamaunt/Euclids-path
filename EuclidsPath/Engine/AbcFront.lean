/-
  AbcFront — the "shadow engine" of the ABC conjecture, anchored to the REAL proven
  Mason–Stothers theorem (polynomial abc) in mathlib.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER — WHAT IS PROVED HERE AND WHAT IS HONESTLY NOT PROVED.    │
  └───────────────────────────────────────────────────────────────────────────┘

  1. 🟢 POLYNOMIAL abc IS PROVED. Over a field `k`, for NON-zero pairwise coprime
     `a, b, c : k[X]` with `a + b + c = 0`, the Mason–Stothers theorem gives a RIGID
     boundary: either the degree of each of `a, b, c` is strictly less than the degree of
     the radical `rad(a·b·c)`, or all three derivatives are zero (degenerate case). This
     is EXACTLY the "engine reading" of abc: "quality" cannot escape to infinity —
     finiteness / rigid boundary is built into the algebra itself. We do NOT re-prove this
     — we CITE the real `Polynomial.abc` from
     `Mathlib/NumberTheory/FLT/MasonStothers.lean` (authors: Jineon Baek, Seewoo Lee).
     Our contribution is a clean wrapper `polynomial_abc_shadow` that gives the "engine"
     reading of the same theorem.

  2. 🟢 INTEGER OBJECTS ARE REAL, NOT STUBS. The radical of a natural number is
     `natRad n = UniqueFactorizationMonoid.radical n` (coincides with `Nat.radical`).
     Proved small green facts: `natRad` divides `n` (`radical_dvd_self`),
     `natRad n = ∏ p ∈ n.primeFactors, p` (`Nat.radical_eq_prod_primeFactors`),
     `0 < natRad n`. The integer side (`Int.radical`) is also real:
     `Int.radical_pos`, `Int.radical_natCast`.

  3. 🔴 INTEGER abc IS OPEN. The ABC conjecture over ℤ (`AbcConjecture`) is an HONEST
     named `Prop` over the REAL `UniqueFactorizationMonoid.radical`, and it is NOT
     proved. Mochizuki's claim (IUT theory) has NOT been accepted by the mathematical
     community as a proof; no prizes for abc have been awarded; no general
     proof exists. The polynomial analogue is formalised (that is our green
     anchor) — integer abc is NOT formalised and NOT proved.

  4. HONEST NOVELTY. The deep mathematics (Mason–Stothers) is from mathlib. This module's
     contribution: the "engine" reading of the proved polynomial boundary + an honest named
     gate for the integer open conjecture over the real radical. This is
     FORMALISATION / CITATION, NOT a proof of abc.

  No `sorry`, no `admit`, no `native_decide`, no new axiom. Green wrappers use the
  standard triple (`propext` / `Classical.choice` / `Quot.sound`). The gate
  `AbcConjecture` is a `def : Prop`; it is NOT proved. The repository's toll (47) is
  unchanged.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/AbcFront.lean → zero errors.

  Kinship: EuclidsPath/Engine/UniversalEngine.lean (`PerpetualEngine`, the governing
    separation line — the same "engine" reading of finiteness / rigid boundary).
-/
import Mathlib
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.AbcFront

open Polynomial UniqueFactorizationMonoid

/-!
################################################################################
  🟢 GREEN CORE — REAL ANCHOR: polynomial abc (Mason–Stothers)
################################################################################
-/

/-- **🟢 ABC SHADOW ON POLYNOMIALS (PROVED, Mason–Stothers).**
    Over a field `k`, for NON-zero pairwise coprime `a, b, c : k[X]` with `a + b + c = 0`:
    either the degree of EACH of `a, b, c` is strictly less than the degree of `rad(a·b·c)`
    (rigid quality boundary — "the engine cannot escape"), or all three
    derivatives are zero (degenerate case).

    This is a clean wrapper over the REAL `Polynomial.abc` from mathlib
    (`Mathlib/NumberTheory/FLT/MasonStothers.lean`): the proof is
    `Polynomial.abc …`; we merely give it an "engine" name. The radical is
    `Polynomial.radical = UniqueFactorizationMonoid.radical` on `k[X]`. -/
theorem polynomial_abc_shadow
    {k : Type*} [Field k] [DecidableEq k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree) ∨
      (derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0) :=
  Polynomial.abc ha hb hc hab hsum

/-- **🟢 "No infinite escape" (engine reading).** In the NON-degenerate
    case (at least one derivative non-zero), polynomial abc forces
    the degree of each summand to lie STRICTLY BELOW the degree of the radical of the product:
    a rigid finite boundary built into the algebra. Also a citation of `Polynomial.abc`. -/
theorem polynomial_abc_no_escape
    {k : Type*} [Field k] [DecidableEq k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0)
    (hnondeg : ¬ (derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0)) :
    a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree :=
  (polynomial_abc_shadow ha hb hc hab hsum).resolve_right hnondeg

/-!
################################################################################
  🟢 GREEN INTEGER OBJECTS — real radical, not a stub
################################################################################
-/

/-- The radical of a natural number as a genuine mathlib object
    (`UniqueFactorizationMonoid.radical`, coincides with `Nat.radical`). -/
noncomputable def natRad (n : ℕ) : ℕ := UniqueFactorizationMonoid.radical n

/-- **🟢 (PROVED):** the radical divides its number — `natRad n ∣ n`. Citation of
    `UniqueFactorizationMonoid.radical_dvd_self`; the radical is real. -/
theorem natRad_dvd_self (n : ℕ) : natRad n ∣ n :=
  UniqueFactorizationMonoid.radical_dvd_self

/-- **🟢 (PROVED):** explicit formula for the radical — the product of prime divisors.
    Citation of `Nat.radical_eq_prod_primeFactors`. -/
theorem natRad_eq_prod_primeFactors (n : ℕ) :
    natRad n = ∏ p ∈ n.primeFactors, p :=
  Nat.radical_eq_prod_primeFactors

/-- **🟢 (PROVED):** positivity of the radical — `0 < natRad n`. Citation of
    `Nat.radical_pos`. -/
theorem natRad_pos (n : ℕ) : 0 < natRad n :=
  Nat.radical_pos n

/-- **🟢 (PROVED):** for `n ≠ 0` the radical does not exceed the number itself — `natRad n ≤ n`.
    Citation of `Nat.radical_le_self_iff`. -/
theorem natRad_le_self {n : ℕ} (hn : n ≠ 0) : natRad n ≤ n :=
  Nat.radical_le_self_iff.mpr hn

/-- **🟢 (PROVED):** the integer radical is also real — `0 < Int.radical z`.
    Citation of `Int.radical_pos`; reference to `Int.radical`. -/
theorem intRad_pos (z : ℤ) : 0 < UniqueFactorizationMonoid.radical z :=
  Int.radical_pos z

/-- **🟢 (PROVED):** consistency of the integer and natural radicals —
    `radical (n : ℤ) = radical n`. Citation of `Int.radical_natCast`. -/
theorem intRad_natCast (n : ℕ) :
    UniqueFactorizationMonoid.radical (n : ℤ)
      = ((UniqueFactorizationMonoid.radical n : ℕ) : ℤ) :=
  Int.radical_natCast

/-!
################################################################################
  🔴 HONEST GATE — INTEGER abc (named Prop, NOT proved)
################################################################################
-/

/-- 🔴 **ABC Conjecture (integers): OPEN.** For coprime `a + b = c`,
    for any `ε > 0` the number `c` is bounded by `K · rad(a·b·c)^(1+ε)` with constant
    `K = K(ε)`. The radical is the REAL `UniqueFactorizationMonoid.radical` on ℕ.

    HONESTLY: this is NOT proved. Mochizuki's claim (IUT) has NOT been accepted by the community;
    no prizes have been awarded; there is no general proof. The polynomial analogue
    (Mason–Stothers) is proved and cited above as the green anchor — but the
    integer case does NOT transfer here. This is a `def : Prop`; we do NOT
    prove it and do NOT use it as a fact. -/
def AbcConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c →
    Nat.Coprime a b →
      (c : ℝ) ≤ K * ((UniqueFactorizationMonoid.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-- **🟢 HONESTY (scope):** we do NOT claim `AbcConjecture` as a theorem and do NOT
    derive it from polynomial abc. The polynomial boundary `polynomial_abc_shadow`
    is PROVED; integer `AbcConjecture` remains OPEN. A marker that the
    implication "polynomial abc ⟹ integer abc" is NOT claimed here. -/
abbrev NoPolynomialToIntegerAbcClaimed : Prop := True

theorem noPolynomialToIntegerAbcClaimed : NoPolynomialToIntegerAbcClaimed := trivial

/-!
################################################################################
  SUMMARY (LOUD HONEST)
################################################################################

  🟢 REAL ANCHOR (cited, NOT re-derived):
     · `Polynomial.abc` (Mason–Stothers, `Mathlib/NumberTheory/FLT/MasonStothers.lean`)
       — wrapped as `polynomial_abc_shadow` / `polynomial_abc_no_escape`;
     · `UniqueFactorizationMonoid.radical` / `Nat.radical` / `Int.radical`
       (`Mathlib/RingTheory/Radical/…`) — `natRad*`, `intRad*`.

  🟢 GENUINELY NEW (in this module, a thin layer):
     · the "engine" reading of the proved polynomial boundary (no infinite
       quality escape = finiteness built into the algebra);
     · `natRad` and its small green facts (divisibility, formula, positivity);
     · the honest named gate `AbcConjecture` over the REAL radical.

  🔴 OPEN (NOT proved, NOT formalised):
     · integer abc (`AbcConjecture`). Mochizuki's IUT has NOT been accepted; no prizes
       awarded. This is a `def : Prop`, not a theorem.

  No `sorry`/`admit`/`native_decide`/new axiom. The repository's toll (47) is unchanged.
-/

#print axioms polynomial_abc_shadow
#print axioms polynomial_abc_no_escape
#print axioms natRad_dvd_self
#print axioms natRad_eq_prod_primeFactors
#print axioms natRad_pos
#print axioms natRad_le_self
#print axioms intRad_pos
#print axioms intRad_natCast
#print axioms noPolynomialToIntegerAbcClaimed

end EuclidsPath.AbcFront
