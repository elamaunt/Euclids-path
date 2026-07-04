/-
  LehmerBoundedDegree — LEHMER AT BOUNDED DEGREE: a gap above 1 exists
  for EACH fixed degree n (the constant DEPENDS on n).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER: THIS IS NOT LEHMER'S CONJECTURE.                      │
  │  The constant c = c(n) DEPENDS on the degree n. UNIFORMITY IN n —          │
  │  a single c > 1 for ALL degrees at once — IS the open Lehmer conjecture.   │
  └───────────────────────────────────────────────────────────────────────────┘

  IDEA (fully green, machine-verified): for a fixed degree n the set of Mahler
  measures in the window (1, 2] is the image of a FINITE set of polynomials
  (Northcott, `Polynomial.finite_mahlerMeasure_le`, bound B = 2). A finite
  non-empty set of real numbers has a minimum; it is strictly greater than 1
  (every element of the window is > 1). Hence no measure lies below the minimum:
  the interval (1, c(n)) is EMPTY. If the window is empty, c = 2 works. This is
  a COMPACTNESS argument well known to the classics:
  "Lehmer at bounded degree is trivial by Northcott." The full weight of the
  conjecture lies in c(n) possibly tending to 1 as n → ∞; nobody can forbid this.

  🟢 GREEN (machine-verified in this file; load-bearing lemmas CITE real mathlib):
   · `measureWindow_finite` — the window {natDegree ≤ n, 1 < measure ≤ 2} is finite;
     direct corollary of `LehmerFront.mahler_northcott_shadow` :=
     `Polynomial.finite_mahlerMeasure_le` (Northcott, PROVED in mathlib).
   · `lehmer_gap_at_bounded_degree` — ∃ c ∈ (1, 2]: NO integer polynomial of
     degree ≤ n has Mahler measure in the interval (1, c).
     Minimum of a finite set via `Set.exists_min_image`.
   · `lehmer_at_bounded_degree` — GOAL: ∀ n ∃ c > 1: every p with natDegree ≤ n
     and measure > 1 has measure ≥ c OR measure > 2.
   · `mahlerMeasure_neg` — the Mahler measure is sign-blind: M(-p) = M(p)
     (via `mahlerMeasure_mul` and `mahlerMeasure_const`; this specific lemma is
     absent in mathlib v4.31, so we derive it in place).
   · `uniformLehmerGap_iff_all_degrees` — GOAL-RENAMING AUDIT (machine iff, like
     `offCriticalBridge_iff_RH`): the data anchor `UniformLehmerGap` is EQUIVALENT
     to "one constant for all degrees at once" — i.e. the anchor IS the uniform
     version of our theorem, and its name smuggles no hidden progress.
   · `uniformLehmerGap_of_lehmerConjecture` — bridge: the monic formulation
     `LehmerFront.LehmerConjecture` implies the anchor `UniformLehmerGap`
     (case analysis on the leading coefficient: |lc| ≥ 2 gives measure ≥ 2 by
     `leadingCoeff_le_mahlerMeasure`; lc = ±1 reduces to monic ±p).

  🔴 HONESTLY OPEN (NOT proved; named data-anchor):
   · `UniformLehmerGap` — UNIFORM gap: ∃ c > 1 (one constant for ALL degrees),
     with no Mahler measures in (1, c). This is Lehmer's conjecture in gap form.
     WHAT MATHEMATICS MUST PROVIDE: a lower bound c(n) ≥ c₀ > 1 independent of n;
     the best known unconditional result — Dobrowolski (1979):
     c(n) ≥ 1 + c·(log log n / log n)³ → 1, which is INSUFFICIENT. In mathlib v4.31
     there is neither Dobrowolski's theorem nor anything stronger; there is no name
     of the form `Polynomial.lehmer_conjecture` (proof_wanted). The candidate
     constant is the Mahler measure of Lehmer's polynomial ≈ 1.17628.

  HONEST NOVELTY. We do NOT prove Lehmer and do NOT approach it: the theorem
  `lehmer_at_bounded_degree` is a folklore corollary of Northcott; its value here
  is the machine-precise fixation of the EXACT boundary between green (each n
  separately) and red (all n at once). This is NOT a solution and NOT a Gödelian trick.

  No `sorry`, no `admit`, no `native_decide`, no new axiom. All exports use the
  standard triple `propext` / `Classical.choice` / `Quot.sound`. The repository
  taint count (47) is NOT changed by this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LehmerBoundedDegree.lean
    → zero errors.

  Related: EuclidsPath/Engine/LehmerFront.lean (Northcott shadow, Kronecker, gate
    `LehmerConjecture`); Mathlib/NumberTheory/MahlerMeasure.lean (Northcott);
    Mathlib/Analysis/Polynomial/MahlerMeasure.lean (measure definition, type ℝ).
-/
import Mathlib
import EuclidsPath.Engine.LehmerFront

set_option autoImplicit false

namespace EuclidsPath.LehmerBoundedDegree

open Polynomial

/-! ################################################################################
    §1  🟢 NORTHCOTT WINDOW: integer polynomials of degree ≤ n with Mahler measure in (1, 2] — finite
    ################################################################################ -/

/-- LEHMER WINDOW at degree ≤ `n`: integer polynomials with Mahler measure strictly
    between 1 and 2 (2 included). The Mahler measure here is the REAL-valued
    `Polynomial.mahlerMeasure` (type ℝ) of the complexification, as in `LehmerFront`.
    The entire Lehmer question lives in this window: no measure below 1
    (`mahler_lower_bound`), measure exactly 1 — Kronecker. -/
def measureWindow (n : ℕ) : Set ℤ[X] :=
  {p : ℤ[X] | p.natDegree ≤ n ∧
    1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2}

@[simp] theorem mem_measureWindow {n : ℕ} {p : ℤ[X]} :
    p ∈ measureWindow n ↔ p.natDegree ≤ n ∧
      1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 :=
  Iff.rfl

/-- 🟢 WINDOW IS FINITE (load-bearing — Northcott). Direct corollary of
    `LehmerFront.mahler_northcott_shadow` := `Polynomial.finite_mahlerMeasure_le`
    at bound B = 2: bounded degree + measure ≤ 2 ⟹ finitely many. -/
theorem measureWindow_finite (n : ℕ) : (measureWindow n).Finite := by
  refine (LehmerFront.mahler_northcott_shadow n 2).subset ?_
  intro p hp
  rw [mem_measureWindow] at hp
  exact ⟨hp.1, by exact_mod_cast hp.2.2⟩

/-! ################################################################################
    §2  🟢 GOAL: a gap above 1 at fixed degree (the constant DEPENDS on n!)
    ################################################################################ -/

/-- 🟢 GAP AT BOUNDED DEGREE (empty-interval form).
    For each `n` there exists `c ∈ (1, 2]` such that NO integer polynomial of
    degree ≤ `n` has Mahler measure in the open interval `(1, c)`.

    PROOF: the window `(1, 2]` is finite (Northcott); if it is non-empty, we take
    the polynomial of minimal measure (`Set.exists_min_image`) — its measure is `c`;
    if empty, `c = 2` works.

    ⚠️ HONEST: `c = c(n)` DEPENDS on `n`. A single `c` for all `n` — the open
    Lehmer conjecture (`UniformLehmerGap` below). THIS IS NOT LEHMER. -/
theorem lehmer_gap_at_bounded_degree (n : ℕ) :
    ∃ c : ℝ, 1 < c ∧ c ≤ 2 ∧ ∀ p : ℤ[X], p.natDegree ≤ n →
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ∉ Set.Ioo 1 c := by
  by_cases hne : (measureWindow n).Nonempty
  · -- window non-empty: minimum measure over the finite window
    obtain ⟨p₀, hp₀, hmin⟩ :=
      Set.exists_min_image (measureWindow n)
        (fun p : ℤ[X] => (p.map (Int.castRingHom ℂ)).mahlerMeasure)
        (measureWindow_finite n) hne
    rw [mem_measureWindow] at hp₀
    refine ⟨(p₀.map (Int.castRingHom ℂ)).mahlerMeasure, hp₀.2.1, hp₀.2.2, ?_⟩
    intro p hdeg hmem
    obtain ⟨h1, h2⟩ := hmem
    have hp_mem : p ∈ measureWindow n := by
      rw [mem_measureWindow]
      exact ⟨hdeg, h1, (h2.trans_le hp₀.2.2).le⟩
    exact absurd (hmin p hp_mem) (not_le.mpr h2)
  · -- window empty: any polynomial with measure in (1, 2) would lie in the window
    refine ⟨2, one_lt_two, le_refl 2, ?_⟩
    intro p hdeg hmem
    obtain ⟨h1, h2⟩ := hmem
    exact hne ⟨p, by rw [mem_measureWindow]; exact ⟨hdeg, h1, h2.le⟩⟩

/-- 🟢 MODULE GOAL: for each degree `n` there exists `c > 1` such that every
    integer polynomial `p` with `natDegree p ≤ n` and Mahler measure > 1 has Mahler
    measure ≥ `c` OR Mahler measure > 2. Equivalently (see
    `lehmer_gap_at_bounded_degree`): NO measure lies in the interval `(1, c)`.

    ⚠️ LOUD AND HONEST: THIS IS NOT LEHMER'S CONJECTURE. The constant `c = c(n)`
    depends on the degree `n`; the fact at fixed `n` is a folklore corollary of
    Northcott finiteness (`Polynomial.finite_mahlerMeasure_le`). Lehmer's conjecture
    is UNIFORMITY IN `n`: a single `c > 1` for all degrees at once (data anchor
    `UniformLehmerGap`); it IS OPEN, and this file does NOT close it. -/
theorem lehmer_at_bounded_degree (n : ℕ) :
    ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.natDegree ≤ n →
      1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure →
      c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure ∨
      2 < (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨c, hc1, _, hgap⟩ := lehmer_gap_at_bounded_degree n
  refine ⟨c, hc1, fun p hdeg h1 => ?_⟩
  by_cases hcle : c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure
  · exact Or.inl hcle
  · exact absurd (Set.mem_Ioo.mpr ⟨h1, not_le.mp hcle⟩) (hgap p hdeg)

/-! ################################################################################
    §3  🔴 DATA ANCHOR: uniformity in n (= Lehmer itself) + machine audit for goal renaming
    ################################################################################ -/

/-- 🔴 DATA ANCHOR (OPEN): UNIFORM Lehmer gap — there exists ONE constant `c > 1`
    (independent of degree!) such that no integer polynomial has Mahler measure in
    `(1, c)`. This is Lehmer's conjecture in gap form.

    WHAT MATHEMATICS MUST PROVIDE: a lower bound on `c(n)` from
    `lehmer_gap_at_bounded_degree` that is INDEPENDENT of `n`. The best known
    unconditional result — Dobrowolski (1979): `c(n) ≥ 1 + c·(log log n / log n)³`,
    which tends to 1 and does NOT close the anchor. In mathlib v4.31 there is neither
    Dobrowolski's theorem nor Smith's (for non-reciprocal polynomials), nor any
    `Polynomial.lehmer_*` (proof_wanted). The candidate is the Mahler measure of
    Lehmer's polynomial `X¹⁰+X⁹-X⁷-X⁶-X⁵-X⁴-X³+X+1` ≈ 1.17628.
    We do NOT prove this Prop. -/
def UniformLehmerGap : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X],
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ∉ Set.Ioo 1 c

/-- 🟢 GOAL-RENAMING AUDIT (machine iff, like `offCriticalBridge_iff_RH`).
    The anchor `UniformLehmerGap` is EQUIVALENT to the statement "one constant can be
    chosen for all degrees at once in `lehmer_gap_at_bounded_degree`". That is, the
    anchor IS EXACTLY the uniform version of our green theorem; its name carries no
    hidden content: naming it is not the same as proving it. -/
theorem uniformLehmerGap_iff_all_degrees :
    UniformLehmerGap ↔
      ∃ c : ℝ, 1 < c ∧ ∀ n : ℕ, ∀ p : ℤ[X], p.natDegree ≤ n →
        (p.map (Int.castRingHom ℂ)).mahlerMeasure ∉ Set.Ioo 1 c := by
  constructor
  · rintro ⟨c, hc, hgap⟩
    exact ⟨c, hc, fun _ p _ => hgap p⟩
  · rintro ⟨c, hc, hgap⟩
    exact ⟨c, hc, fun p => hgap p.natDegree p le_rfl⟩

/-! ################################################################################
    §4  🟢 BRIDGE TO LehmerFront: the monic formulation implies the anchor
    ################################################################################ -/

/-- 🟢 The Mahler measure is sign-blind: `M(-p) = M(p)`. In mathlib v4.31 this lemma
    is absent (though `mahlerMeasure_mul` and `mahlerMeasure_const` exist); we derive
    it: `-p = C(-1)·p`, and the constant factor contributes `‖-1‖ = 1`. -/
theorem mahlerMeasure_neg (p : ℂ[X]) : (-p).mahlerMeasure = p.mahlerMeasure := by
  have h : (-p : ℂ[X]) = Polynomial.C (-1 : ℂ) * p := by
    rw [map_neg, map_one, neg_one_mul]
  rw [h, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_const]
  simp

/-- 🟢 BRIDGE (when the anchor holds the front closes — in both directions of the formulation).
    The monic formulation of Lehmer's conjecture from `LehmerFront.LehmerConjecture`
    IMPLIES the anchor `UniformLehmerGap` for ALL integer polynomials.

    Case analysis: for a non-zero `p` the leading coefficient `lc ≠ 0`. If `|lc| ≥ 2`,
    then the measure ≥ `‖lc‖` ≥ 2 (`Polynomial.leadingCoeff_le_mahlerMeasure`) — outside
    the window `(1, min c 2)`. If `lc = 1`, `p` is monic — `LehmerConjecture` applies.
    If `lc = -1`, `-p` is monic, and the measure is sign-blind (`mahlerMeasure_neg`). -/
theorem uniformLehmerGap_of_lehmerConjecture
    (h : LehmerFront.LehmerConjecture) : UniformLehmerGap := by
  obtain ⟨c, hc1, hLeh⟩ := h
  refine ⟨min c 2, lt_min hc1 one_lt_two, ?_⟩
  intro p hmem
  obtain ⟨h1, h2⟩ := hmem
  obtain ⟨h2c, h2two⟩ := lt_min_iff.mp h2
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, Polynomial.mahlerMeasure_zero] at h1
    linarith
  -- leading coefficient of the complexification — cast of the integer leading coefficient
  have hlc_map : (p.map (Int.castRingHom ℂ)).leadingCoeff = (p.leadingCoeff : ℂ) := by
    rw [Polynomial.leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int]
    exact eq_intCast _ _
  have habs : (|p.leadingCoeff| : ℝ) ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
    have hnorm := Polynomial.leadingCoeff_le_mahlerMeasure (p.map (Int.castRingHom ℂ))
    rw [hlc_map] at hnorm
    calc (|p.leadingCoeff| : ℝ) = ‖(p.leadingCoeff : ℂ)‖ := by
          rw [Complex.norm_intCast]
      _ ≤ _ := hnorm
  rcases lt_or_ge |p.leadingCoeff| 2 with hsmall | hbig
  · -- |lc| = 1: p or -p is monic, apply the monic formulation
    have hlc1 : |p.leadingCoeff| = 1 := by
      have hge : 1 ≤ |p.leadingCoeff| :=
        Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hp0)
      omega
    rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hlc1 with hlc | hlc
    · -- lc = 1: p is monic
      have hMon : p.Monic := hlc
      have := hLeh p hMon h1.ne'
      linarith
    · -- lc = -1: -p is monic, the measure is the same
      have hMon : (-p).Monic := by
        show (-p).leadingCoeff = 1
        rw [Polynomial.leadingCoeff_neg, hlc, neg_neg]
      have hmapneg : ((-p).map (Int.castRingHom ℂ)) = -(p.map (Int.castRingHom ℂ)) :=
        Polynomial.map_neg _
      have hμneg : ((-p).map (Int.castRingHom ℂ)).mahlerMeasure
          = (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
        rw [hmapneg, mahlerMeasure_neg]
      have hne1 : ((-p).map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1 := by
        rw [hμneg]; exact h1.ne'
      have hge := hLeh (-p) hMon hne1
      rw [hμneg] at hge
      linarith
  · -- |lc| ≥ 2: measure ≥ 2, the window (1, min c 2) is unreachable
    have h2le : (2 : ℝ) ≤ (|p.leadingCoeff| : ℝ) := by exact_mod_cast hbig
    linarith

/-!
################################################################################
  SUMMARY (LOUD HONEST): what is proved, what is reused, what REMAINS OPEN
################################################################################

  🟢 LOAD-BEARING GREEN (this file):
     · `measureWindow_finite`          — the window (1, 2] is finite (Northcott);
     · `lehmer_gap_at_bounded_degree`  — ∃ c(n) ∈ (1, 2]: the interval (1, c(n)) is empty;
     · `lehmer_at_bounded_degree`      — GOAL: measure ≥ c(n) or measure > 2;
     · `mahlerMeasure_neg`             — M(-p) = M(p);
     · `uniformLehmerGap_iff_all_degrees` — audit: anchor = uniform version;
     · `uniformLehmerGap_of_lehmerConjecture` — bridge from the monic formulation.

  🟢 REUSED (cited, NOT re-derived):
     · `LehmerFront.mahler_northcott_shadow` := `Polynomial.finite_mahlerMeasure_le`;
     · `Set.exists_min_image` (minimum of a finite set);
     · `Polynomial.mahlerMeasure_mul`, `mahlerMeasure_const`,
       `leadingCoeff_le_mahlerMeasure`, `leadingCoeff_map_of_injective`.

  🔴 OPEN (named data-anchor; NOT proved, NOT closed by the engine):
     · `UniformLehmerGap` — one constant c > 1 for ALL degrees = Lehmer's conjecture.
       The audit `uniformLehmerGap_iff_all_degrees` shows: the anchor IS EXACTLY
       the uniform version of the green theorem; goal renaming is excluded machine-precisely.

  HONEST NOVELTY: ZERO mathematical novelty (folklore corollary of Northcott);
  the value is the machine-precise fixation of the EXACT boundary green/red: each n
  separately — trivial, all n at once — Lehmer. THIS IS NOT A SOLUTION AND NOT GODEL.
  No `sorry`, no new axiom, no `native_decide`;
  the repository taint count (47) is NOT changed by this file.
-/

#print axioms measureWindow_finite
#print axioms lehmer_gap_at_bounded_degree
#print axioms lehmer_at_bounded_degree
#print axioms uniformLehmerGap_iff_all_degrees
#print axioms mahlerMeasure_neg
#print axioms uniformLehmerGap_of_lehmerConjecture

end EuclidsPath.LehmerBoundedDegree
