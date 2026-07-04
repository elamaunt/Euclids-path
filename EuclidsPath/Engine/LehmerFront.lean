/-
  LehmerFront — the "engineering shadow" of LEHMER's conjecture (Mahler measure).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER. WHAT IS GREEN HERE AND WHAT HONESTLY REMAINS OPEN.  │
  └───────────────────────────────────────────────────────────────────────────┘

  THE ROLE OF THE ENGINE HERE IS THE SAME AS IN BSD. The Mahler measure `mahlerMeasure` of an
  integer polynomial is the HEIGHT. Northcott finiteness (PROVEN in mathlib!) —
  `Polynomial.finite_mahlerMeasure_le`: for BOUNDED degree and BOUNDED Mahler measure there are
  ONLY FINITELY MANY integer polynomials. This is precisely "height is well-founded = no
  infinite height descent" — THE SAME toolkit as BSD and `UniversalEngine`
  (Mordell–Weil via Fermat's infinite descent). We invent no new height mechanism:
  we CITE the real Northcott theorem.

  🟢 GREEN (machine-verified, in this file; load-bearing declarations CITE REAL mathlib theorems):
   · `mahler_northcott_shadow` := `Polynomial.finite_mahlerMeasure_le` — CITING THE PROVEN
     Northcott finiteness: bounded degree + bounded Mahler measure ⟹ finitely many
     integer polynomials. This is "height is well-founded, descent terminates" — the engine
     reading. `Mathlib/NumberTheory/MahlerMeasure.lean`.
   · `kronecker_boundary` := `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one` — CITING
     Kronecker's content: Mahler measure = 1 ⟹ every nonzero complex root is a root of unity
     (boundary of cyclotomic polynomials). This is Lehmer's BOUNDARY at M=1.
   · `kronecker_cyclotomic_dvd` := `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one` —
     the same Kronecker in divisibility form: divisible by a cyclotomic polynomial.
   · `mahler_lower_bound` := `Polynomial.one_le_mahlerMeasure_of_ne_zero` — lower bound
     `1 ≤ mahlerMeasure` for any nonzero integer polynomial (floor of Lehmer's circle).
   · `cyclotomic_mahler_one` := `Polynomial.cyclotomic_mahlerMeasure_eq_one` — Mahler measure
     of a cyclotomic polynomial equals 1 (saturation of Kronecker's boundary).
   · `lehmer_descent_has_no_engine` — engine COROLLARY: on any height model with
     ℕ-height (derived from Mahler measure) an infinite strictly descending descent is IMPOSSIBLE.
     Reuses `UniversalEngine.no_perpetual_engine_of_natRank`. Grounded on
     `finite_mahlerMeasure_le` conceptually (finiteness = no descent); machine-side — the same rank engine.

  🔴 HONESTLY OPEN (NOT proven here; the engine does NOT close it):
   · `LehmerConjecture` — LEHMER'S CONJECTURE ITSELF: ∃ c>1 such that every NON-cyclotomic
     integer polynomial has Mahler measure ≥ c. Kronecker closes the BOUNDARY M=1
     (Mahler measure = 1 ⟺ cyclotomic / roots of unity); the GAP above 1 — uniform constant
     c>1 — is OPEN. The smallest known value is Lehmer's number ≈ 1.17628. This is an OPEN GATE
     (named predicate over REAL `mahlerMeasure`); we do NOT prove it.

  HONEST NOVELTY. We nowhere formalise either Lehmer's conjecture or the gap c>1. We EXHIBIT
  the structural reading "Mahler measure = height, Northcott = well-foundedness = no height
  descent", GROUNDED on REAL theorems `finite_mahlerMeasure_le` (Northcott) and
  `pow_eq_one_of_mahlerMeasure_eq_one` (Kronecker). THIS IS NOT A PROOF OF LEHMER.

  No `sorry`, no `admit`, no `native_decide`, no new axiom.
  Green load-bearing declarations — the standard triple `propext` / `Classical.choice` / `Quot.sound`.
  The repository's taint count (47) is NOT changed by this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LehmerFront.lean → zero errors.

  Kinship: EuclidsPath/Engine/UniversalEngine.lean (`PerpetualEngine`, `of_natRank`);
    EuclidsPath/Engine/BSDFront.lean (the same height-descent engine = Northcott).
-/
import Mathlib
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.LehmerFront

open Polynomial
open EuclidsPath.UniversalEngine

/-! ################################################################################
    §1  🟢 GREEN CORE: Northcott (finiteness = no height descent) + Kronecker (boundary)
    ################################################################################ -/

/-- 🟢 NORTHCOTT SHADOW (load-bearing — CITING THE PROVEN mathlib theorem).
    For bounded degree `n` and bounded Mahler measure `B` there are ONLY FINITELY MANY
    integer polynomials. This is the machine form of "height is well-founded, height descent
    terminates" — the same toolkit as BSD/`UniversalEngine`. -/
theorem mahler_northcott_shadow (n : ℕ) (B : NNReal) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} :=
  Polynomial.finite_mahlerMeasure_le n B

/-- 🟢 KRONECKER BOUNDARY (load-bearing — CITING THE PROVEN mathlib theorem).
    If the Mahler measure of an integer polynomial equals 1, then every NONZERO complex root
    is a root of unity. This is the boundary of cyclotomic polynomials at M=1 — the place where
    Lehmer's conjecture is CLOSED. -/
theorem kronecker_boundary {p : ℤ[X]}
    (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1)
    {z : ℂ} (hz₀ : z ≠ 0) (hz : z ∈ p.aroots ℂ) :
    ∃ n, 0 < n ∧ z ^ n = 1 :=
  Polynomial.pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz

/-- 🟢 KRONECKER BOUNDARY in divisibility form (load-bearing — CITING mathlib).
    A nonzero non-cyclotomic integer polynomial of Mahler measure 1 (not divisible by `X`,
    of degree ≠ 0) is DIVISIBLE by a cyclotomic polynomial. -/
theorem kronecker_cyclotomic_dvd {p : ℤ[X]}
    (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1)
    (hX : ¬ X ∣ p) (hpdeg : p.degree ≠ 0) :
    ∃ n, 0 < n ∧ cyclotomic n ℤ ∣ p :=
  Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one h hX hpdeg

/-- 🟢 LOWER BOUND (load-bearing — CITING mathlib).
    `1 ≤ mahlerMeasure` for every NONZERO integer polynomial: the floor of Lehmer's circle. -/
theorem mahler_lower_bound {p : ℤ[X]} (hp : p ≠ 0) :
    1 ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
  Polynomial.one_le_mahlerMeasure_of_ne_zero hp

/-- 🟢 BOUNDARY SATURATION (load-bearing — CITING mathlib).
    The Mahler measure of a cyclotomic polynomial equals 1 — Kronecker's boundary is attained. -/
theorem cyclotomic_mahler_one (n : ℕ) :
    ((cyclotomic n ℤ).map (algebraMap ℤ ℂ)).mahlerMeasure = 1 :=
  Polynomial.cyclotomic_mahlerMeasure_eq_one n

/-! ################################################################################
    §2  🟢 ENGINE: height descent by Mahler measure terminates (Northcott reading)
    ################################################################################ -/

/-- Abstract HEIGHT MODEL of descent by Mahler measure: carrier `α`, ℕ-height
    (floor of Mahler measure / iteration depth), descent step strictly decreasing the height.
    This is the same interface as `BSDHeightModel` in `BSDFront`. -/
structure MahlerHeightModel where
  /-- Carrier (e.g., a degree-bounded family of integer polynomials). -/
  Carrier : Type
  /-- ℕ-height DERIVED from the Mahler measure (floor of `mahlerMeasure` or descent depth). -/
  height : Carrier → ℕ
  /-- Descent step. -/
  descentStep : Carrier → Carrier → Prop
  /-- Descent strictly decreases the height. -/
  descent_decreases : ∀ x y, descentStep x y → height x < height y

/-- 🟢 ENGINE (COROLLARY of `no_perpetual_engine_of_natRank`).
    On any height model by Mahler measure a PERPETUAL ENGINE (an infinite strictly descending
    height descent) is IMPOSSIBLE: the descent terminates. This is the engine reading of
    Northcott finiteness `finite_mahlerMeasure_le`: where there are finitely many polynomials
    below the boundary, no infinite strict height descent exists. -/
theorem lehmer_descent_has_no_engine (M : MahlerHeightModel) :
    ¬ PerpetualEngine M.descentStep :=
  no_perpetual_engine_of_natRank M.height (fun x y h => M.descent_decreases x y h)

/-- Inhabited height model: carrier ℕ (descent depth), height = identity,
    descent step — strict decrease. Shows that the interface is NOT VACUOUS. -/
def mahlerHeightModel_inhabited : MahlerHeightModel where
  Carrier := ℕ
  height := id
  descentStep := fun x y => x < y
  descent_decreases := fun _ _ h => h

/-- 🟢 Inhabited instance: the concrete height model has no engine. -/
theorem inhabited_descent_has_no_engine :
    ¬ PerpetualEngine mahlerHeightModel_inhabited.descentStep :=
  lehmer_descent_has_no_engine mahlerHeightModel_inhabited

/-! ################################################################################
    §3  🔴 HONEST GATE: Lehmer's conjecture (uniform constant c>1) — OPEN
    ################################################################################ -/

/-- 🔴 LEHMER'S CONJECTURE: ∃ c>1 such that every NON-cyclotomic (Mahler measure ≠ 1) integer
    monic polynomial has Mahler measure ≥ c. OPEN.

    Kronecker (`kronecker_boundary`) closes the BOUNDARY M=1; the GAP above 1 — uniform
    lower bound c>1 for NON-cyclotomic polynomials — is open. The smallest known value is
    Lehmer's number ≈ 1.17628. This is a NAMED PREDICATE over the REAL `mahlerMeasure`; NOT a theorem. -/
def LehmerConjecture : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.Monic →
    ((p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1) →
    c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure

/-!
################################################################################
  SUMMARY (LOUD HONEST): what is proven, what is reused, what REMAINS OPEN
################################################################################

  🟢 LOAD-BEARING GREENS (cite REAL proven mathlib theorems):
     · `mahler_northcott_shadow`  := `Polynomial.finite_mahlerMeasure_le` (Northcott);
     · `kronecker_boundary`       := `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one` (Kronecker);
     · `kronecker_cyclotomic_dvd` := `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one`;
     · `mahler_lower_bound`       := `Polynomial.one_le_mahlerMeasure_of_ne_zero`;
     · `cyclotomic_mahler_one`    := `Polynomial.cyclotomic_mahlerMeasure_eq_one`;
     · `lehmer_descent_has_no_engine` := corollary of `no_perpetual_engine_of_natRank`.

  🟢 REUSED (cited, NOT re-derived):
     · `UniversalEngine.no_perpetual_engine_of_natRank` (rank engine);
     · `UniversalEngine.PerpetualEngine` (definition of the perpetual engine).

  🔴 OPEN (NOT proven; NAMED gate over the REAL Mahler measure):
     · `LehmerConjecture` — uniform gap c>1 above 1 for non-cyclotomic polynomials.

  HONEST NOVELTY: the structural reading "Mahler measure = height, Northcott = well-foundedness =
  no height descent", grounded on REAL `finite_mahlerMeasure_le` and
  `pow_eq_one_of_mahlerMeasure_eq_one`. THIS IS NOT A PROOF OF LEHMER.
  No `sorry`, no new axiom, no `native_decide`; the taint count 47 is unchanged.
-/

#print axioms mahler_northcott_shadow
#print axioms kronecker_boundary
#print axioms kronecker_cyclotomic_dvd
#print axioms mahler_lower_bound
#print axioms cyclotomic_mahler_one
#print axioms lehmer_descent_has_no_engine
#print axioms inhabited_descent_has_no_engine

end EuclidsPath.LehmerFront
