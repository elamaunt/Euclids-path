/-
  LehmerEpistemic — EPISTEMIC COMPLEMENT of the Lehmer conjecture (Mahler measure).
  Mirror of PNPFirstCause (NOT the Collatz variant: Lehmer has no decree and never had one —
  Lehmer does not enter the four boundaries of `step00FirstCause`; the file is entirely green).
  Green front: Engine/LehmerFront.lean (Northcott, Kronecker, perpetual engine).

  WHAT THIS IS. "Solving Lehmer from inside a finite horizon" = keeping an UNBOUNDED
  family of polynomials under ONE finite Northcott horizon `mahlerBox n B`
  (degree ≤ n, Mahler measure ≤ B): field `resolves` — injective supply payment by the
  finite horizon, field `beyondOwnHorizon` — genuine infiniteness of the family.
  The contradiction is paid by TWO real theorems: finiteness of the horizon — REAL
  Northcott (`mahler_northcott_shadow` = `Polynomial.finite_mahlerMeasure_le`,
  genuine number theory, not a constructed graph), and the pigeonhole — the real
  `Set.infinite_of_injective_forall_mem` (no injection of an infinite set into a finite one —
  the same well-foundedness wall as `no_perpetual_engine_on_nat`).

  HONESTY (CORR accounted for). (1) The binding is BARER than for P/NP: there the fields
  are separated by a real payment notion (`FullRankCertificatePayment`), here between the
  fields there is exactly ONE step — pigeonhole collapses them into "Infinite vs Finite".
  Yet more substantial than Collatz (which literally reads `fun H => H.beyondOwnHorizon H.ground`):
  the contradiction here is carried by EXTERNAL green theorems (Northcott + pigeonhole),
  not by the fields themselves.
  The weight of substance is borne by the unconditional `lehmer_supply_below_horizon_impossible`
  (the finiteness side is DISCHARGED by real Northcott, not assumed by the conjecture) and
  the conjecture-linked `lehmer_refutation_escapes_every_horizon` (a refutation of
  Lehmer is forced to traverse ALL degree horizons) — without them the bare wrapper would
  be a tautology. (2) This is model-internal epistemics, NOT a solution to the Lehmer conjecture:
  nothing is asserted about the open uniform gap c > 1 (`LehmerConjecture`, Lehmer number ≈ 1.17628)
  — the red gate stays red. (3) This is NOT Gödel:
  no independence is claimed — only pigeonhole self-destruction of the internal
  self-justification. (4) Bonus content: `lehmer_at_bounded_degree` — an honest
  SPECIAL CASE of the conjecture: on every finite degree horizon the gap EXISTS;
  all openness of Lehmer is the escape of degree beyond every horizon.

  No sorry, no new axiom, no native_decide, quarantine is NOT
  imported. The repository taint (47) is NOT changed by this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LehmerEpistemic.lean
-/

import EuclidsPath.Engine.LehmerFront

set_option autoImplicit false

namespace EuclidsPath.LehmerFront.Epistemic

open Polynomial
open EuclidsPath.LehmerFront
open EuclidsPath.UniversalEngine

/-! ## Horizon: Northcott box (🟢) -/

/-- **Northcott box**: integer polynomials of degree ≤ `n` with Mahler measure ≤ `B` —
    the finite-fuel horizon of Lehmer's internal solver. -/
def mahlerBox (n : ℕ) (B : NNReal) : Set ℤ[X] :=
  {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B}

/-- 🟢 The box is FINITE — this is the real Northcott (`mahler_northcott_shadow` =
    `Polynomial.finite_mahlerMeasure_le`), genuine number theory, not a construction. -/
theorem mahlerBox_finite (n : ℕ) (B : NNReal) : (mahlerBox n B).Finite :=
  mahler_northcott_shadow n B

/-! ## Pigeonhole wall: unbounded supply does not fit below the horizon (🟢) -/

/-- 🟢 **PIGEONHOLE WALL (unconditional, load-bearing).** There is no injection of `ℕ` into the Northcott box:
    an unbounded supply of polynomials CANNOT be kept below a single finite horizon.
    Here the finiteness side is DISCHARGED by real Northcott (not assumed by the conjecture), and
    the contradiction is supplied by the real pigeonhole `Set.infinite_of_injective_forall_mem` —
    the analogue of `no_fullPayment_of_unboundedSupply` for P/NP. -/
theorem lehmer_supply_below_horizon_impossible (n : ℕ) (B : NNReal) :
    ¬ ∃ f : ℕ → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B := by
  rintro ⟨f, hinj, hmem⟩
  exact (mahlerBox_finite n B).not_infinite
    (Set.infinite_of_injective_forall_mem hinj hmem)

/-! ## Special case of the conjecture: gap on every finite horizon (🟢) -/

/-- 🟢 **LEHMER AT BOUNDED DEGREE (honest special case of the conjecture).** On every
    degree horizon `n` the gap EXISTS: there is `c > 1` such that every monic
    integer polynomial of degree ≤ `n` with Mahler measure ≠ 1 has measure ≥ `c`.
    Scheme: the Northcott catalogue with cap 2 is finite; the minimum of measures over the catalogue is strictly
    greater than 1 (floor `mahler_lower_bound` + ≠ 1); outside the catalogue the measure > 2. Formally visible:
    all openness of Lehmer is the escape of degree beyond EVERY finite horizon. -/
theorem lehmer_at_bounded_degree (n : ℕ) :
    ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.Monic → p.natDegree ≤ n →
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1 →
      c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  classical
  -- finite Northcott catalogue of candidates below cap 2
  have hfin : Set.Finite {p : ℤ[X] | p.Monic ∧ p.natDegree ≤ n ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1} := by
    apply (mahler_northcott_shadow n 2).subset
    rintro p ⟨-, hdeg, hle, -⟩
    exact ⟨hdeg, by simpa using hle⟩
  by_cases hne : Set.Nonempty {p : ℤ[X] | p.Monic ∧ p.natDegree ≤ n ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1}
  · -- catalogue non-empty: minimum of measures over the finite catalogue yields the gap
    obtain ⟨p₀, hp₀S, hp₀min⟩ := Set.exists_min_image _
      (fun p : ℤ[X] => (p.map (Int.castRingHom ℂ)).mahlerMeasure) hfin hne
    obtain ⟨hp₀monic, -, -, hp₀ne⟩ := hp₀S
    have hp₀gt : 1 < (p₀.map (Int.castRingHom ℂ)).mahlerMeasure :=
      lt_of_le_of_ne (mahler_lower_bound hp₀monic.ne_zero) (Ne.symm hp₀ne)
    refine ⟨min ((p₀.map (Int.castRingHom ℂ)).mahlerMeasure) 2,
      lt_min hp₀gt one_lt_two, ?_⟩
    intro p hmonic hdeg hne1
    by_cases hle2 : (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2
    · exact le_trans (min_le_left _ _) (hp₀min p ⟨hmonic, hdeg, hle2, hne1⟩)
    · exact le_trans (min_le_right _ _) (not_le.mp hle2).le
  · -- catalogue empty: every candidate has measure > 2, gap c := 2
    refine ⟨2, one_lt_two, ?_⟩
    intro p hmonic hdeg hne1
    by_contra hlt
    exact hne ⟨p, hmonic, hdeg, (not_le.mp hlt).le, hne1⟩

/-- 🟢 **REFUTATION TRAVERSES EVERY HORIZON** (conjecture-linked carrier;
    analogue of `nonHalting_carries_perpetual_engine` for Collatz). If Lehmer is false, then
    for every `n` and every `ε > 0` there exists a monic polynomial of degree > `n`
    with Mahler measure in `(1, 1+ε)`: refuting witnesses are FORCED to escape every
    finite degree horizon — below the horizon the gap exists
    (`lehmer_at_bounded_degree`). -/
theorem lehmer_refutation_escapes_every_horizon (hL : ¬ LehmerConjecture) :
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ p : ℤ[X], p.Monic ∧ n < p.natDegree ∧
      1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure < 1 + ε := by
  intro n ε hε
  obtain ⟨c₀, hc₀, hgap⟩ := lehmer_at_bounded_degree n
  have hc : (1 : ℝ) < min c₀ (1 + ε) := lt_min hc₀ (by linarith)
  unfold LehmerConjecture at hL
  push Not at hL
  obtain ⟨p, hmonic, hne1, hlt⟩ := hL (min c₀ (1 + ε)) hc
  have h1lt : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
    lt_of_le_of_ne (mahler_lower_bound hmonic.ne_zero) (Ne.symm hne1)
  refine ⟨p, hmonic, ?_, h1lt, lt_of_lt_of_le hlt (min_le_right _ _)⟩
  by_contra hdeg
  push Not at hdeg
  exact absurd (hgap p hmonic hdeg hne1)
    (not_le.mpr (lt_of_lt_of_le hlt (min_le_left _ _)))

/-! ## Model: internal solution = self-justification beyond its own horizon -/

/-- **Internal self-justification of the Lehmer solution at a finite horizon.** The solver
    simultaneously (a) PAYS injectively the entire family with the finite Northcott horizon
    (`resolves`) and (b) that family is GENUINELY INFINITE (`beyondOwnHorizon`).

    HONEST CAVEAT (CORR): the binding is BARER than for P/NP — between the fields there is exactly ONE step
    (pigeonhole collapses them into "Infinite vs Finite"); for P/NP between the fields stands
    a real payment notion. Substantiality is paid not by the independence of the sides, but by
    the COST of the contradiction: it is borne by external green theorems — the real Northcott
    (`mahler_northcott_shadow`) and the real pigeonhole
    (`Set.infinite_of_injective_forall_mem`), not by the fields themselves against each other (as in
    Collatz). -/
structure InternalisedLehmerGround (ι : Type) (n : ℕ) (B : NNReal) : Prop where
  resolves : ∃ f : ι → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B
  beyondOwnHorizon : Infinite ι

/-- "Internal knowledge of the Lehmer cause" = internal self-justification of the solution. -/
abbrev InternalKnowledgeOfLehmerCause (ι : Type) (n : ℕ) (B : NNReal) : Prop :=
  InternalisedLehmerGround ι n B

/-- Concrete honest instance: supply indexed by `ℕ`. -/
abbrev InternalLehmerDecision (n : ℕ) (B : NNReal) : Prop :=
  InternalisedLehmerGround ℕ n B

/-! ## Core: self-justification self-destructs = perpetual engine wall (🟢) -/

/-- 🟢 Self-justification self-destructs: an infinite family cannot be injected
    into a finite Northcott box. The contradiction is supplied by Northcott + pigeonhole
    (mirror of `no_internalisedPNPGround`, where it was supplied by
    `no_fullPayment_of_unboundedSupply`). -/
theorem no_internalisedLehmerGround {ι : Type} {n : ℕ} {B : NNReal} :
    InternalisedLehmerGround ι n B → False := by
  rintro ⟨⟨f, hinj, hmem⟩, hinf⟩
  exact (mahlerBox_finite n B).not_infinite
    (@Set.infinite_of_injective_forall_mem ι _ hinf _ f hinj hmem)

/-- 🟢 **"UNKNOWABLE FROM INSIDE" — THEOREM** (mirror of `pnpCause_unknowable` /
    `collatzCause_unknowable`): an internal finite-horizon solution to Lehmer
    is impossible. NOT a statement about the conjecture itself: the gap `c > 1` remains open. -/
theorem lehmerCause_unknowable {ι : Type} {n : ℕ} {B : NNReal} :
    ¬ InternalKnowledgeOfLehmerCause ι n B :=
  no_internalisedLehmerGround

/-- 🟢 **THE SAME PERPETUAL ENGINE CONTRADICTION:** impossibility of an internal solution to
    Lehmer AND impossibility of a perpetual engine on ℕ — ONE well-foundedness wall
    (injection of the infinite into the finite = ℕ-descent without a floor). -/
theorem internalLehmerDecision_carries_perpetual_engine {ι : Type} {n : ℕ} {B : NNReal} :
    (InternalisedLehmerGround ι n B → False) ∧
      ¬ PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  ⟨no_internalisedLehmerGround, no_perpetual_engine_on_nat⟩

/-- Ex-falso companion ("carries the engine"): from the self-justification (already false) one derives
    the perpetual engine on ℕ as well. HONESTY: route is ex falso; the load-bearing part is
    the impossibility itself (`no_internalisedLehmerGround`). -/
theorem internalisedLehmerGround_builds_engine {ι : Type} {n : ℕ} {B : NNReal} :
    InternalisedLehmerGround ι n B → PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  fun H => (no_internalisedLehmerGround H).elim

/-- SUBSTANTIAL DICHOTOMY (no ex falso in the statement): either the cause is unknowable
    from inside, or the unbounded supply fits below the horizon. The left disjunct is
    a theorem. -/
theorem unknowable_or_lehmer_horizonPayable (n : ℕ) (B : NNReal) :
    (¬ InternalKnowledgeOfLehmerCause ℕ n B) ∨
      ∃ f : ℕ → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B :=
  Or.inl lehmerCause_unknowable

/-! ## Summary: solution is locked behind the engine; verification, not derivation (🟢) -/

/-- 🟢 **"SOLUTION LOCKED BEHIND THE ENGINE" (mirror of
    `pnp_no_internal_decision_without_engine`):**
    (1) REFUTING below a finite horizon = injection of the infinite into the finite =
        engine wall (`lehmer_supply_below_horizon_impossible`);
    (2) SELF-JUSTIFYING the solution from inside — self-destructs
        (`no_internalisedLehmerGround`);
    (3) the only engine-free path is external VERIFICATION: on every horizon the
        gap is found by enumerating the finite Northcott catalogue
        (`lehmer_at_bounded_degree`); only the escape beyond ALL horizons
        remains open (red `LehmerConjecture`).
    Gödelian independence is NOT asserted and the conjecture itself is NOT solved. -/
theorem lehmer_no_internal_decision_without_engine (n : ℕ) (B : NNReal) :
    (¬ ∃ f : ℕ → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B) ∧
    (InternalisedLehmerGround ℕ n B → False) ∧
    (∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.Monic → p.natDegree ≤ n →
        (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1 →
        c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure) :=
  ⟨lehmer_supply_below_horizon_impossible n B,
   no_internalisedLehmerGround,
   lehmer_at_bounded_degree n⟩

/-- 🟢 Final epistemic status of Lehmer (mirror of `pnp_locked_behind_engine_status`,
    WITHOUT the decree conjunct — Lehmer has no `step00FirstCause` boundary):
    horizon is finite (Northcott, theorem) / no perpetual engine on the height model (theorem) /
    solving from inside is impossible (theorem) / a refutation of the conjecture would traverse all horizons
    (conditional theorem; `LehmerConjecture` itself remains the open red gate). -/
theorem lehmer_locked_behind_engine_status (n : ℕ) (B : NNReal) :
    (mahlerBox n B).Finite ∧
    (¬ PerpetualEngine mahlerHeightModel_inhabited.descentStep) ∧
    (¬ InternalLehmerDecision n B) ∧
    (¬ LehmerConjecture → ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ p : ℤ[X],
        p.Monic ∧ m < p.natDegree ∧
        1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
        (p.map (Int.castRingHom ℂ)).mahlerMeasure < 1 + ε) :=
  ⟨mahlerBox_finite n B,
   inhabited_descent_has_no_engine,
   lehmerCause_unknowable,
   fun hL => lehmer_refutation_escapes_every_horizon hL⟩

/-! ## Axiom audit: the whole module is green (standard triple), repository taint does NOT change -/
#print axioms mahlerBox_finite
#print axioms lehmer_supply_below_horizon_impossible
#print axioms lehmer_at_bounded_degree
#print axioms lehmer_refutation_escapes_every_horizon
#print axioms no_internalisedLehmerGround
#print axioms lehmerCause_unknowable
#print axioms internalLehmerDecision_carries_perpetual_engine
#print axioms internalisedLehmerGround_builds_engine
#print axioms unknowable_or_lehmer_horizonPayable
#print axioms lehmer_no_internal_decision_without_engine
#print axioms lehmer_locked_behind_engine_status

end EuclidsPath.LehmerFront.Epistemic
