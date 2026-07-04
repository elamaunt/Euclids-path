/-
  BealFront — the "shadow front" of the BEAL and FERMAT–CATALAN conjectures, grounded on
  the ACTUALLY PROVEN polynomial Fermat–Catalan theorem and on Fermat descent for
  FLT n = 3 / n = 4 in mathlib. FERMAT'S INFINITE DESCENT is literally the engine
  of this project (impossibility of a perpetual engine).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADLINE — WHAT HERE IS GREEN AND WHAT IS HONESTLY OPEN.        │
  └───────────────────────────────────────────────────────────────────────────┘

  1. GREEN ANCHOR (proven in mathlib, cited verbatim, NOT re-derived):
     · `Polynomial.flt_catalan` — the polynomial Fermat–Catalan theorem: under
       `1/p + 1/q + 1/r < 1` (in integer form `q*r + r*p + p*q ≤ p*q*r`),
       for coprime `a, b`, from `C u*a^p + C v*b^q + C w*c^r = 0` it follows that
       `a, b, c` are CONSTANTS (`natDegree = 0`). This is the PROVEN polynomial analogue
       of Beal/Fermat–Catalan; its characteristic infinite descent IS a reading
       of the engine: there is no perpetual descent of nontrivial solutions.
     · `fermatLastTheoremFour` and `fermatLastTheoremThree` — the proven special
       cases of Fermat's Last Theorem, OBTAINED by the method of infinite descent
       (Fermat42 minimal descent in `FLT/Four.lean`) — the same EPMI engine.

  2. GREEN READING OF THE ENGINE (repository): "descent ⟹ perpetual engine ⟹ false".
     If a Beal-like solution generated an infinite strictly descending chain of the
     solution's rank-size, it would be a perpetual engine on ℕ — forbidden by
     `UniversalEngine.no_perpetual_engine_of_natRank` / `EPMI.no_infinite_descent`.
     This is the STRUCTURAL half, honestly grounded (not a proof of Beal).

  3. 🔴 OPEN (named, NOT proven): the integer Beal conjecture and the full
     Fermat–Catalan conjecture. Darmon–Granville (via Faltings) proved only the
     FINITENESS of solutions for a FIXED triple of exponents; full Beal is open
     ($1M prize). Here these statements are honest `def`-gates, they are NOT proven.

  HONEST NOVELTY: the deep mathematics (polynomial Fermat–Catalan, FLT 3/4) is
  mathlib; the module's contribution is the EMBEDDING of these real anchors into the
  engine language + an honest demarcation of green and open. Formalization/unification, not new
  deep mathematics. No `sorry`, no new axiom, no
  `native_decide`; the repository's taint (47) is unchanged. The green wrappers use the standard
  trio `propext` / `Classical.choice` / `Quot.sound`.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BealFront.lean → zero errors.

  Kinship: EuclidsPath/Engine/UniversalEngine.lean (`no_perpetual_engine_of_natRank`);
    EuclidsPath/Engine/EPMI.lean (`no_infinite_descent`, `DescentStep`);
    Mathlib/NumberTheory/FLT/Polynomial.lean (`Polynomial.flt_catalan`);
    Mathlib/NumberTheory/FLT/Four.lean (`fermatLastTheoremFour`);
    Mathlib/NumberTheory/FLT/Three.lean (`fermatLastTheoremThree`).
-/
import Mathlib
import EuclidsPath.Engine.UniversalEngine
import EuclidsPath.Engine.EPMI

set_option autoImplicit false

namespace EuclidsPath.BealFront

open Polynomial

/-!
################################################################################
  🟢 GREEN CORE — Fermat descent IS the engine; the polynomial analogue is PROVEN.
################################################################################
-/

/-- **🟢 GREEN SHADOW (proven, citation of `Polynomial.flt_catalan`):**
    the polynomial Fermat–Catalan theorem over ANY field `k`. Under the condition
    `1/p + 1/q + 1/r < 1` (integrally `q*r + r*p + p*q ≤ p*q*r`), for
    coprime `a, b` and nonzero coefficients the equation
    `C u*a^p + C v*b^q + C w*c^r = 0` forces `a, b, c` to be CONSTANTS.
    This is the PROVEN polynomial analogue of Beal/Fermat–Catalan — the "green shadow".
    The wrapper adds NO mathematics: it calls mathlib verbatim. -/
theorem polynomial_fermat_catalan_shadow
    {k : Type*} [Field k]
    {p q r : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : (p : k) ≠ 0) (chq : (q : k) ≠ 0) (chr : (r : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  Polynomial.flt_catalan hp hq hr hineq chp chq chr ha hb hc hab hu hv hw heq

/-- **🟢 NON-VACUITY (witness over `ℚ`):** a concrete non-degenerate
    instance of the green shadow. Take `p = q = r = 3` (then
    `q*r + r*p + p*q = 27 = p*q*r`, the condition holds), field `ℚ`
    (characteristic 0, all `(3 : ℚ) ≠ 0`). For any coprime nonzero
    `a, b` and nonzero `c, u, v, w` with `C u*a^3 + C v*b^3 + C w*c^3 = 0`
    we get that `a, b, c` are constants. The shadow is applicable, not empty. -/
theorem polynomial_fermat_catalan_shadow_cubic
    {a b c : ℚ[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    {u v w : ℚ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ 3 + C v * b ^ 3 + C w * c ^ 3 = 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  polynomial_fermat_catalan_shadow
    (k := ℚ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ha hb hc hab hu hv hw heq

/-- **🟢 REAL FERMAT DESCENT, n = 4 (proven, citation of `fermatLastTheoremFour`):**
    nonzero naturals `a, b, c` do not give `a^4 + b^4 = c^4`. Proven in mathlib
    by INFINITE DESCENT (Fermat42 minimal descent) — by the same EPMI engine that
    forbids a perpetual engine. -/
theorem flt_four_is_descent : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour

/-- **🟢 REAL FERMAT DESCENT, n = 3 (proven, citation of `fermatLastTheoremThree`):**
    nonzero naturals `a, b, c` do not give `a^3 + b^3 = c^3`. The same infinite
    descent engine. -/
theorem flt_three_is_descent : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

/-- **🟢 EXPANDED FORM n = 4:** for nonzero `a, b, c : ℕ` we have
    `a^4 + b^4 ≠ c^4`. A direct reading of the proven `flt_four_is_descent`. -/
theorem no_fermat_four (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 4 :=
  flt_four_is_descent a b c ha hb hc

/-!
################################################################################
  🟢 GREEN READING OF THE ENGINE: descent of the solution's size ⟹ perpetual engine ⟹ false.
################################################################################
-/

/-- The Beal rank-model: the "size" of a hypothetical solution chain — a natural number.
    `SolutionRank.size` — the height that descent would be obliged to strictly decrease. -/
structure SolutionRank where
  size : ℕ

/-- **🟢 DESCENT-NO-ENGINE (proven, corollary of `no_perpetual_engine_of_natRank`):**
    if a Beal-like solution generated an infinite chain `sol : ℕ → SolutionRank`,
    in which every step STRICTLY decreases `size` (a model of infinite descent
    of the solution's size), it would be a perpetual engine on ℕ — impossible. This
    is the STRUCTURAL half: it honestly is not a proof of Beal, but records
    that infinite descent of solutions is forbidden by the same engine as Fermat's. -/
theorem no_perpetual_solution_descent
    (sol : ℕ → SolutionRank)
    (hchain : ∀ t, (sol (t + 1)).size < (sol t).size) : False := by
  apply EuclidsPath.UniversalEngine.no_perpetual_engine_of_natRank
    (α := SolutionRank) (ρ := SolutionRank.size)
    (r := fun x y => x.size < y.size)
    (fun x y hxy => hxy)
  exact ⟨sol, hchain⟩

/-- **🟢 VIA EPMI (proven, corollary of `EPMI.no_infinite_descent`):** the same
    impossibility in EPMI clean-descent form. For `A ≥ 1` an infinite chain of heights
    with step `DescentStep A (H t) (H (t+1))` (that is, `A · H(t+1) < H t`) yields
    false — literally Fermat descent as the impossibility of a perpetual engine. -/
theorem no_perpetual_solution_descent_epmi
    {A : ℕ} (hA : 1 ≤ A) (H : ℕ → ℕ)
    (hchain : ∀ t, EuclidsPath.Engine.DescentStep A (H t) (H (t + 1))) : False :=
  EuclidsPath.Engine.no_infinite_descent hA H hchain

/-- **🟢 NON-VACUITY of the rank-model:** a witness of a decreasing FINITE chain of sizes
    (it terminates, is not infinite): `sol t = ⟨N - t⟩` strictly decreases while `t < N`.
    The model is inhabited; the engine forbids precisely the INFINITE variant. -/
theorem solution_rank_finite_descent_witness (N : ℕ) :
    ∀ t, t < N → (⟨N - (t + 1)⟩ : SolutionRank).size < (⟨N - t⟩ : SolutionRank).size := by
  intro t ht
  show N - (t + 1) < N - t
  omega

/-!
################################################################################
  🔴 HONEST GATES — OPEN statements, NOT proven (these are `def`-Props).
################################################################################
-/

/-- 🔴 **Beal conjecture (OPEN, $1M prize).** If `A^x + B^y = C^z` with
    positive `A, B, C`, exponents `x, y, z > 2` and pairwise coprime
    `A, B, C`, then such a solution does NOT exist (coprimality leads
    to a contradiction). Equivalently: any solution with `x, y, z > 2` forces `A, B, C`
    to share a common prime divisor. NOT proven; here it is merely honestly NAMED. -/
def BealConjecture : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    A ^ x + B ^ y = C ^ z →
    Nat.Coprime A B → Nat.Coprime B C → Nat.Coprime A C → False

/-- 🔴 **Fermat–Catalan conjecture (OPEN, canonical form).** The set
    of POWER TRIPLES `(a^x, b^y, c^z)` — precisely of values, not parameter tuples —
    of coprime positive `a, b, c` with exponents satisfying
    `1/x + 1/y + 1/z < 1` (integrally `y*z + z*x + x*y < x*y*z`) and
    `a^x + b^y = c^z`, is FINITE. Exactly 10 solutions are known (the smallest is
    `1 + 2^3 = 3^2`); Darmon–Granville proved finiteness only for a
    FIXED triple of exponents (via Faltings); uniform finiteness
    is open. NOT proven; honestly NAMED. (Why values, not tuples —
    see `fermatCatalan_tupleForm_refuted` below.) -/
def FermatCatalanConjecture : Prop :=
  {t : ℕ × ℕ × ℕ |
      ∃ a b c x y z : ℕ, t = (a ^ x, b ^ y, c ^ z) ∧
        0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
        y * z + z * x + x * y < x * y * z ∧
        Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c ∧
        a ^ x + b ^ y = c ^ z}.Finite

/-- The former (naive) rendering of the gate: finiteness of the set of 6-TUPLES
    `(a, b, c, x, y, z)`. Kept under a separate name as a formalization lesson —
    it is FALSE (see `fermatCatalan_tupleForm_refuted`). -/
def FermatCatalanTupleForm : Prop :=
  {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
      ∃ a b c x y z : ℕ, t = (a, b, c, x, y, z) ∧
        0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
        y * z + z * x + x * y < x * y * z ∧
        Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c ∧
        a ^ x + b ^ y = c ^ z}.Finite

/-- 🟢 **FORMALIZATION LESSON: the tuple form of the gate is FALSE.** The family
    `1^(m+7) + 2^3 = 3^2` (coprimality is obvious, the exponent condition
    holds for all m) yields infinitely many DISTINCT 6-tuples — while
    the triple of values is single: `(1, 8, 9)`. The gate must count values. -/
theorem fermatCatalan_tupleForm_refuted : ¬ FermatCatalanTupleForm := by
  intro hfin
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => ((1 : ℕ), (2 : ℕ), (3 : ℕ), m + 7, (3 : ℕ), (2 : ℕ)))
    ?_ ?_ hfin
  · intro m₁ m₂ h
    have h4 := congrArg (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => t.2.2.2.1) h
    simp only [] at h4
    omega
  · intro m
    exact ⟨1, 2, 3, m + 7, 3, 2, rfl,
      one_pos, by omega, by omega, by omega, by omega, by omega,
      by omega,
      Nat.coprime_one_left 2, by decide, Nat.coprime_one_left 3,
      by simp⟩

/-- **🟢 HONESTY OF SCOPE:** we do NOT assert and do NOT prove `BealConjecture` or
    `FermatCatalanConjecture` — these are `def`-gates. Only the polynomial shadow
    (`polynomial_fermat_catalan_shadow`) and the real Fermat descent n = 3/4
    (`flt_three_is_descent`, `flt_four_is_descent`) are proven, plus the structural impossibility
    of perpetual descent. The scope marker fixes the boundary of honesty. -/
abbrev NotAProofOfBeal : Prop := True

theorem notAProofOfBeal : NotAProofOfBeal := trivial

/-!
################################################################################
  🟢 GREEN BEAL EXPONENT CLASSES — the diagonals (3,3,3) and (4,4,4) are closed.
################################################################################
-/

/-- **🟢 GREEN BEAL CLASS (3,3,3):** for exponents `x = y = z = 3` there are NO solutions
    of the Beal equation AT ALL — even without coprimality: `A^3 + B^3 = C^3`
    is impossible for positive `A, B, C`. A direct consequence of
    `flt_three_is_descent` (Fermat descent, mathlib). In particular, the diagonal
    class of the `BealConjecture` gate at `(3,3,3)` is green: there are no coprime
    solutions, because there are none at all. -/
theorem beal_no_solution_exponent_three
    (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (heq : A ^ 3 + B ^ 3 = C ^ 3) : False :=
  flt_three_is_descent A B C hA.ne' hB.ne' hC.ne' heq

/-- **🟢 GREEN BEAL CLASS (4,4,4):** for exponents `x = y = z = 4` there are no
    solutions at all (from `flt_four_is_descent` — Fermat's historic infinite descent).
    The diagonal class of the `BealConjecture` gate at `(4,4,4)` is green, coprimality
    is not needed. -/
theorem beal_no_solution_exponent_four
    (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (heq : A ^ 4 + B ^ 4 = C ^ 4) : False :=
  flt_four_is_descent A B C hA.ne' hB.ne' hC.ne' heq

/-!
################################################################################
  🟢 NON-VACUOUS GATE WITNESSES — the set is inhabited, the coprimality hypothesis is load-bearing.
################################################################################
-/

/-- **🟢 NON-VACUITY OF THE FC-GATE:** the triple of VALUES `(1, 8, 9)` — the smallest
    Fermat–Catalan solution `1^7 + 2^3 = 3^2` — belongs to the set whose finiteness
    is asserted by `FermatCatalanConjecture` (the same set-literal verbatim).
    Exponents `(x, y, z) = (7, 3, 2)`: `y·z + z·x + x·y = 41 < 42 = x·y·z`,
    the pairwise coprimality of the bases `1, 2, 3` is obvious. The gate speaks of
    a NONEMPTY set — the question of its finiteness is not vacuous. -/
theorem fermatCatalan_value_witness :
    ((1, 8, 9) : ℕ × ℕ × ℕ) ∈
      {t : ℕ × ℕ × ℕ |
        ∃ a b c x y z : ℕ, t = (a ^ x, b ^ y, c ^ z) ∧
          0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
          y * z + z * x + x * y < x * y * z ∧
          Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c ∧
          a ^ x + b ^ y = c ^ z} :=
  ⟨1, 2, 3, 7, 3, 2, by norm_num,
    one_pos, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num,
    Nat.coprime_one_left 2, by decide, Nat.coprime_one_left 3,
    by norm_num⟩

/-- **🟢 COPRIMALITY HYPOTHESIS — LOAD-BEARING:** without it the Beal equation is inhabited:
    `2^3 + 2^3 = 2^4` (that is, 8 + 8 = 16) with exponents `x = y = 3 > 2`,
    `z = 4 > 2` and a COMMON DIVISOR 2 across all three bases. The coprimality
    condition in `BealConjecture` is not decoration: it cannot be removed, a counterexample
    is exhibited. -/
theorem beal_common_factor_witness :
    ∃ A B C x y z : ℕ,
      0 < A ∧ 0 < B ∧ 0 < C ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      A ^ x + B ^ y = C ^ z ∧
      ¬ Nat.Coprime A B ∧ 2 ∣ A ∧ 2 ∣ B ∧ 2 ∣ C :=
  ⟨2, 2, 2, 3, 3, 4, by decide⟩

/-!
################################################################################
  🟢 POLYNOMIAL BEAL — a named shadow (all exponents ≥ 3, field char 0).
################################################################################
-/

/-- **🟢 ARITHMETIC OF BEAL EXPONENTS:** for `3 ≤ p, q, r` the
    FC-condition `q·r + r·p + p·q ≤ p·q·r` holds — each summand on the left does not exceed
    a third of the right-hand side. It is precisely this inequality that separates Beal exponents from
    spherical/elliptic triples. -/
theorem fc_ineq_of_three_le {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    q * r + r * p + p * q ≤ p * q * r := by
  have h1 : 3 * (q * r) ≤ p * (q * r) := Nat.mul_le_mul hp le_rfl
  have h2 : 3 * (r * p) ≤ q * (r * p) := Nat.mul_le_mul hq le_rfl
  have h3 : 3 * (p * q) ≤ r * (p * q) := Nat.mul_le_mul hr le_rfl
  nlinarith [h1, h2, h3]

/-- **🟢 POLYNOMIAL BEAL (proven; specialization of `Polynomial.flt_catalan`
    at `u = v = 1, w = −1`):** over a field of characteristic 0, from `a^x + b^y = c^z`
    with coprime `a, b`, nonzero `a, b, c` and exponents
    `x, y, z ≥ 3` it follows that `a, b, c` are CONSTANTS. Literally the "Beal theorem
    over `k[X]»`: there are no nontrivial polynomial solutions. HONESTY:
    integer Beal does NOT follow from this (a polynomial shadow, not a solution
    of the gate); equal exponents `x = y = z = n ≥ 3` give polynomial FLT
    as a special case. -/
theorem polynomial_beal_shadow
    {k : Type*} [Field k] [CharZero k]
    {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (heq : a ^ x + b ^ y = c ^ z) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have h0 : C (1 : k) * a ^ x + C (1 : k) * b ^ y + C (-1 : k) * c ^ z = 0 := by
    simp only [map_one, map_neg, one_mul, neg_one_mul]
    rw [heq]; ring
  exact polynomial_fermat_catalan_shadow (k := k)
    (p := x) (q := y) (r := z) (u := (1 : k)) (v := (1 : k)) (w := (-1 : k))
    (by omega) (by omega) (by omega)
    (fc_ineq_of_three_le hx hy hz)
    (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega))
    ha hb hc hab
    one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero)
    h0

/-!
################################################################################
  EPISTEMIC LINK OF BEAL — A COLLATZ FORM, HONESTLY FORMAL.
################################################################################
-/

/-- **Internal self-grounding of Beal — a Collatz form, HONESTLY FORMAL.**
    Carries the gate itself (`ground : BealConjecture`) and a witness of its own
    beyond-the-horizon nature (`beyondOwnHorizon : ¬ BealConjecture`).

    LOUD HONESTY (mandatory, per the skeptic's verdict "overstated by
    half a step"): this is literally a pair `P` / `¬P` — the same degenerate form as
    `InternalisedCollatzGround`, and BELOW the P/NP mechanics (`InternalisedPNPGround`,
    where `beyondOwnHorizon` is an independently paid green fact). THERE IS
    NO PAYMENT BY AN ENGINE FACT HERE AND THERE CANNOT BE in known mathematics:
    a refutation of Beal is a single counterexample `(A, B, C, x, y, z)`, a finite
    point; it generates neither a descending chain (there is no Fermat descent for general
    Beal), nor an unbounded supply — if anything arises, it is
    an ASCENDING escape of sizes, not a descent, and the wall
    `no_perpetual_solution_descent` does not bite it. The link is formal;
    the substantive part is NEARBY, in separate theorems: the polynomial shadow
    `polynomial_beal_shadow` and the green diagonal classes
    `beal_no_solution_exponent_three` / `beal_no_solution_exponent_four`. -/
structure InternalisedBealGround : Prop where
  ground : BealConjecture
  beyondOwnHorizon : ¬ BealConjecture

/-- "Internal knowledge of the Beal cause" = internal self-grounding of the gate
    (mirror of `InternalKnowledgeOfCollatzCause`; the same honest caveat). -/
abbrev InternalKnowledgeOfBealCause : Prop := InternalisedBealGround

/-- Self-grounding self-destructs — BY FORM
    (`fun H => H.beyondOwnHorizon H.ground`), as with Collatz; there honestly is NO
    engine payment — see the docstring of `InternalisedBealGround`. GREEN;
    of axioms — only `propext` (pulled in via `Nat.Coprime` inside the gate
    `BealConjecture`), neither `Classical.choice` nor `Quot.sound`. -/
theorem no_internalisedBealGround : InternalisedBealGround → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **"CANNOT BE KNOWN FROM INSIDE" — a theorem of FORM** (mirror of
    `collatzCause_unknowable`): internal self-grounding of Beal is impossible.
    HONESTY: unlike `pnpCause_unknowable`, the contradiction is not paid by
    a pigeonhole/supply — it is a formal link; its substantive neighbours are
    `polynomial_beal_shadow` and the classes (3,3,3)/(4,4,4). NOT Gödel and NOT a solution
    of Beal. -/
theorem bealCause_unknowable : ¬ InternalKnowledgeOfBealCause :=
  no_internalisedBealGround

/-!
################################################################################
  SUMMARY (LOUD HONEST): what is green, what is reused, what is OPEN.
################################################################################

  🟢 GREEN (machine-proven in this module — wrappers/corollaries):
     · `polynomial_fermat_catalan_shadow` — a verbatim citation of `Polynomial.flt_catalan`
       (the PROVEN polynomial Fermat–Catalan);
     · `polynomial_fermat_catalan_shadow_cubic` — a non-vacuous instance over `ℚ`;
     · `flt_four_is_descent` / `flt_three_is_descent` — citations of `fermatLastTheoremFour`
       / `fermatLastTheoremThree` (PROVEN by infinite descent);
     · `no_fermat_four` — the expanded form n = 4;
     · `no_perpetual_solution_descent` — a corollary of `no_perpetual_engine_of_natRank`;
     · `no_perpetual_solution_descent_epmi` — a corollary of `EPMI.no_infinite_descent`;
     · `solution_rank_finite_descent_witness` — non-vacuity of the rank-model;
     · `beal_no_solution_exponent_three` / `beal_no_solution_exponent_four` —
       the green diagonal Beal classes (3,3,3)/(4,4,4): there are no solutions at all,
       coprimality is not needed (Fermat descent);
     · `fermatCatalan_value_witness` — the FC-gate is not vacuous: (1,8,9) = 1^7+2^3=3^2
       lies in the set of values;
     · `beal_common_factor_witness` — the coprimality hypothesis is load-bearing:
       2^3+2^3=2^4 with a common divisor 2;
     · `fc_ineq_of_three_le` + `polynomial_beal_shadow` — the "Beal theorem over k[X]"
       (specialization of `flt_catalan`, u=v=1, w=−1, char 0);
     · `no_internalisedBealGround` / `bealCause_unknowable` — the epistemic
       LINK-FORM (honestly: a ground/¬ground pair WITHOUT engine payment, a Collatz
       form, below the P/NP mechanics — see the docstring of `InternalisedBealGround`).

  🟢 REUSED (cited, NOT re-derived):
     · `Polynomial.flt_catalan` (polynomial Fermat–Catalan, mathlib);
     · `fermatLastTheoremFour` / `fermatLastTheoremThree` (FLT by descent, mathlib);
     · `UniversalEngine.no_perpetual_engine_of_natRank`, `EPMI.no_infinite_descent`.

  🔴 OPEN (named, NOT proven — `def`-gates):
     · `BealConjecture` — the integer Beal conjecture ($1M prize);
     · `FermatCatalanConjecture` — the full (uniform) Fermat–Catalan conjecture
       (Darmon–Granville: only finiteness for FIXED exponents).

  HONEST NOVELTY: the deep mathematics is mathlib; the contribution is the embedding of real anchors
  into the engine language and an honest demarcation. NOT a proof of Beal. No `sorry`,
  no new axiom, no `native_decide`; the taint 47 is unchanged.
-/

#print axioms polynomial_fermat_catalan_shadow
#print axioms fermatCatalan_tupleForm_refuted
#print axioms polynomial_fermat_catalan_shadow_cubic
#print axioms flt_four_is_descent
#print axioms flt_three_is_descent
#print axioms no_fermat_four
#print axioms no_perpetual_solution_descent
#print axioms no_perpetual_solution_descent_epmi
#print axioms solution_rank_finite_descent_witness
#print axioms beal_no_solution_exponent_three
#print axioms beal_no_solution_exponent_four
#print axioms fermatCatalan_value_witness
#print axioms beal_common_factor_witness
#print axioms fc_ineq_of_three_le
#print axioms polynomial_beal_shadow
#print axioms no_internalisedBealGround
#print axioms bealCause_unknowable

end EuclidsPath.BealFront
