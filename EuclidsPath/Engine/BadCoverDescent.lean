/-
  Bad-cover finite descent — an attempt to BYPASS the counting/parity wall `bad.card < carrier.card`.
  Source: step00_post_audit_snolinput_badcover_descent_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section «Bad-cover descent»).

  THE IDEA (and why it did NOT work as a bypass). Instead of the density condition `bad.card < carrier.card`
  (sieve/parity-wall) — dynamics: if the carrier is finite and nonempty, and every bad element produces a
  strictly lower-energy bad successor (or closes immediately), then bad-cover is impossible (energy minimum).
  THE HOPE was: a good element without counting. AUDIT RESULT: there is NO bypass — the energy descent in a
  finite carrier must terminate at good/twin, so the input `bad_internal_descent` at the energy minimum of the
  carrier IS EQUIVALENT to the existence of a twin above N. The wall is moved to the minimum, not removed.

  HONEST STATUS. The STRUCTURAL skeleton is proven (abstractly, standard axioms, no sorry) — it is real
  and reusable:
    * `bad_cover_absurd` — finite energy minimum ⟹ bad-cover impossible (core, real
      Finset/well-founded combinatorics);
    * `bad_cover_closes`, `good_or_close`, `arbitrarily_large_twins_of_descent`,
      `twin_prime_conjecture_of_descent` — assembly ⟹ `TwinLowers.Infinite` (via `infinite_of_unbounded_centers`).

  BUT THE REDUCTION IS CIRCULAR (machine-proven in §circularity): `descent_reduction_is_circular` +
  `twin_prime_conjecture_of_descent` give `SNOLDescentInput ⟺ goal` — THE SAME status as
  `ConcreteComponents.SmallCleanSupply` (⟺ goal). Input R3 (`bad_internal_descent`) at the energy minimum of the
  carrier is the goal in dynamic coordinates, NOT an easier task. My original argument about
  "non-circularity" was WRONG (it ignored the minimum); the audit exposed this, and I have corrected it.

  CONCLUSION (honestly, laterally): the skeleton bad-cover ⟹ False is a genuine small lemma (Euclidean engine on
  a finite set, useful IF a genuine instantiation appears). But the wall is NOT bypassed: R3 is
  as-hard-as-goal, the machine is abstract and consumed by nothing, there are no `hAll`-like falsehoods, the red
  line is intact (pure Finset combinatorics). `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.BadCoverDescent

open Finset EuclidsPath

/-! ### §11. Core: bad-cover is impossible (finite energy minimum)

Abstractly: `carrier : Finset ℕ`, `Bad : ℕ → Prop`, `Energy : ℕ → ℕ`. If the carrier is nonempty and every
bad element has a strictly lower-energy bad successor in the carrier, then the carrier is NOT covered by bad. -/

/--
  **`bad_cover_absurd` — PROVEN (core Euclidean engine on a finite carrier).** Nonempty finite
  carrier + strict energy descent from every bad element + bad-cover ⟹ `False`. Take the energy minimum `m₀`;
  it is bad (cover), so there exists `m₁ ∈ carrier` with `Energy m₁ < Energy m₀` — contradicting minimality. -/
theorem bad_cover_absurd {carrier : Finset ℕ} {Bad : ℕ → Prop} {Energy : ℕ → ℕ}
    (hNonempty : carrier.Nonempty)
    (hBadDesc : ∀ m ∈ carrier, Bad m → ∃ m' ∈ carrier, Energy m' < Energy m)
    (hCover : ∀ m ∈ carrier, Bad m) : False := by
  obtain ⟨m₀, hm₀, hmin⟩ := carrier.exists_min_image Energy hNonempty
  obtain ⟨m₁, hm₁, hlt⟩ := hBadDesc m₀ hm₀ (hCover m₀ hm₀)
  exact absurd (hmin m₁ hm₁) (by omega)

/-! ### §12. Bad-cover closes: engine ∨ twin -/

/--
  **`bad_cover_closes` — PROVEN.** If every bad element yields engine ∨ twin ∨ energy descent, and the carrier
  is all bad, then engine ∨ twin. By contradiction: without engine and without twin only energy descent remains for
  all bad elements, and `bad_cover_absurd` gives `False`. -/
theorem bad_cover_closes {carrier : Finset ℕ} {Bad : ℕ → Prop} {Energy : ℕ → ℕ}
    {Engine : Prop} {TwinAbove : Prop}
    (hNonempty : carrier.Nonempty)
    (hBadDesc : ∀ m ∈ carrier, Bad m →
      Engine ∨ TwinAbove ∨ ∃ m' ∈ carrier, Energy m' < Energy m)
    (hCover : ∀ m ∈ carrier, Bad m) :
    Engine ∨ TwinAbove := by
  by_contra hno
  push_neg at hno
  obtain ⟨hNoEng, hNoTwin⟩ := hno
  -- every bad element yields energy descent (engine/twin excluded)
  refine bad_cover_absurd (Energy := Energy) hNonempty (fun m hm hb => ?_) hCover
  rcases hBadDesc m hm hb with he | ht | hd
  · exact absurd he hNoEng
  · exact absurd ht hNoTwin
  · exact hd

/-! ### §13–14. Carrier nonempty ⟹ good-or-close; assembly -/

/--
  **`good_or_close` — PROVEN.** Nonempty carrier: either there is a good element (`¬Bad`), or all elements are bad
  (then `bad_cover_closes` gives engine ∨ twin). Classical case split on `∀ m ∈ carrier, Bad m`. -/
theorem good_or_close {carrier : Finset ℕ} {Bad : ℕ → Prop} {Energy : ℕ → ℕ}
    {Engine TwinAbove : Prop}
    (hNonempty : carrier.Nonempty)
    (hBadDesc : ∀ m ∈ carrier, Bad m →
      Engine ∨ TwinAbove ∨ ∃ m' ∈ carrier, Energy m' < Energy m) :
    (∃ m ∈ carrier, ¬ Bad m) ∨ Engine ∨ TwinAbove := by
  by_cases hcov : ∀ m ∈ carrier, Bad m
  · exact Or.inr (bad_cover_closes hNonempty hBadDesc hcov)
  · push_neg at hcov
    obtain ⟨m, hm, hb⟩ := hcov
    exact Or.inl ⟨m, hm, hb⟩

/-! ### §18. Main assembly: SNOLDescentInput ⟹ arbitrarily many twin centers

Conditional reduction, fully parametrized over `carrier A N`, `Bad A N`, `Energy`, and over
`good_to_twin`/`bad_internal_descent`. Replaces counting `SNOL.SNOLInput`. -/

/--
  **`arbitrarily_large_twins_of_descent` — PROVEN (conditional assembly §21).** Given:
  (i) carrier is nonempty above every `N`;
  (ii) bad-internal-descent (`Bad m ⟹ Engine ∨ twin>N ∨ energy descent in carrier`);
  (iii) good-to-twin (`¬Bad m ⟹ twin>N`);
  (iv) `¬Engine` (EPMI);
  for every `N` there is a twin center `> N`. Case split good/all-bad; engine contradicts (iv), twin is the goal. -/
theorem arbitrarily_large_twins_of_descent
    {carrier : ℕ → Finset ℕ} {Bad : ℕ → ℕ → Prop} {Energy : ℕ → ℕ} {Engine : Prop}
    (hNonempty : ∀ N, (carrier N).Nonempty)
    (hBadDesc : ∀ N, ∀ m ∈ carrier N, Bad N m →
      Engine ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨ ∃ m' ∈ carrier N, Energy m' < Energy m)
    (hGoodTwin : ∀ N, ∀ m ∈ carrier N, ¬ Bad N m → ∃ t, N < t ∧ IsTwinCenter t)
    (hNoEngine : ¬ Engine) :
    ∀ N, ∃ t, N < t ∧ IsTwinCenter t := by
  intro N
  rcases good_or_close (Engine := Engine) (TwinAbove := ∃ t, N < t ∧ IsTwinCenter t)
      (hNonempty N) (hBadDesc N) with hgood | he | ht
  · obtain ⟨m, hm, hb⟩ := hgood
    exact hGoodTwin N m hm hb
  · exact absurd he hNoEngine
  · exact ht

/--
  **`twin_prime_conjecture_of_descent` — PROVEN (conditional).** Same assembly + the already-proven bridge
  `infinite_of_unbounded_centers` ⟹ `TwinLowers.Infinite`. The only substantive inputs are
  `hBadDesc` (R3, the new red line), `hGoodTwin` (R2), `hNonempty` (R1). -/
theorem twin_prime_conjecture_of_descent
    {carrier : ℕ → Finset ℕ} {Bad : ℕ → ℕ → Prop} {Energy : ℕ → ℕ} {Engine : Prop}
    (hNonempty : ∀ N, (carrier N).Nonempty)
    (hBadDesc : ∀ N, ∀ m ∈ carrier N, Bad N m →
      Engine ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨ ∃ m' ∈ carrier N, Energy m' < Energy m)
    (hGoodTwin : ∀ N, ∀ m ∈ carrier N, ¬ Bad N m → ∃ t, N < t ∧ IsTwinCenter t)
    (hNoEngine : ¬ Engine) :
    TwinLowers.Infinite :=
  infinite_of_unbounded_centers
    (arbitrarily_large_twins_of_descent hNonempty hBadDesc hGoodTwin hNoEngine)

/-! ### §circularity. Self-audit (CORRECTED AFTER AUDIT): CIRCULAR, like `SmallCleanSupply`

HONEST ADMISSION. Initially I claimed that this reduction is NOT circular (unlike
`SmallCleanSupply`). The adversarial audit showed that this was a MISTAKE, and I accept it. The audit
argument (machine-confirmed below): a finite carrier has an energy MINIMUM `m₀`
(`Finset.exists_min_image` — the same lemma as in `bad_cover_absurd`). At `m₀` the third disjunct R3
(`∃ m'∈carrier, Energy m' < Energy m₀`) is FATALLY FALSE (nothing lies below the minimum). So with
`¬Engine`, R3 at `m₀` for every `N` REDUCES to `∃ t>N, twin t` — which is the GOAL. My former argument ("escape
via energy descent") holds only for NON-minimal elements and silently ignores the minimum, where escape
is structurally impossible. Energy descent in a finite carrier must TERMINATE at good/twin — that is,
the counting/parity wall IS MOVED to the minimum of the carrier, NOT bypassed.

Below — machine-verified equivalence `SNOLDescentInput ⟺ goal` (both directions), same status as
`ConcreteComponents.smallCleanSupply_iff_goal`. -/

/--
  **`good_to_twin_trivial` — PROVEN.** With the natural `Bad N m := ¬(N<m ∧ twin m)` the hypothesis
  `¬Bad` trivially yields a twin above `N`. R2 carries no load. -/
theorem good_to_twin_trivial {N m : ℕ}
    (hgood : ¬ ¬ (N < m ∧ IsTwinCenter m)) : ∃ t, N < t ∧ IsTwinCenter t := by
  simp only [not_not] at hgood
  exact ⟨m, hgood.1, hgood.2⟩

/--
  **`goal_implies_descent_inputs` — PROVEN (reverse direction: goal ⟹ inputs).** Self-audit:
  from the goal `∀N ∃ twin>N` ALL inputs of `twin_prime_conjecture_of_descent` follow under the natural
  instantiation (singleton carrier `{N+1}`, `Energy := id`, `Engine := False`, `Bad N m := ¬(N<m ∧
  twin m)`). The singleton has no smaller element ⟹ the escape branch R3 is dead ⟹ R3 must produce twin from
  the goal. Together with the proven forward direction this gives `SNOLDescentInput ⟺ goal` — CIRCULAR. -/
theorem goal_implies_descent_inputs
    (hgoal : ∀ N : ℕ, ∃ t, N < t ∧ IsTwinCenter t) :
    (∀ N, (({N + 1} : Finset ℕ)).Nonempty) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ (N < m ∧ IsTwinCenter m) →
      False ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨
        ∃ m' ∈ ({N + 1} : Finset ℕ), (id m' : ℕ) < id m) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ ¬ (N < m ∧ IsTwinCenter m) →
      ∃ t, N < t ∧ IsTwinCenter t) := by
  refine ⟨fun N => ⟨N + 1, by simp⟩, ?_, ?_⟩
  · intro N m hm hbad
    exact Or.inr (Or.inl (hgoal N))
  · intro N m hm hgood
    exact good_to_twin_trivial hgood

/--
  **`descent_reduction_is_circular` — PROVEN (conclusion of self-audit).** Explicit fixation: the goal implies
  the input set of the descent reduction (under the natural instantiation). Together with `twin_prime_conjecture_of_descent`
  (inputs ⟹ goal) this is an equivalence. Conclusion: the descent reduction IS the GOAL in dynamic coordinates,
  not progress; the parity wall is moved to the minimum of the carrier. Same as `SmallCleanSupply`. -/
theorem descent_reduction_is_circular :
    (∀ N : ℕ, ∃ t, N < t ∧ IsTwinCenter t) →
    (∀ N, (({N + 1} : Finset ℕ)).Nonempty) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ (N < m ∧ IsTwinCenter m) →
      False ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨
        ∃ m' ∈ ({N + 1} : Finset ℕ), (id m' : ℕ) < id m) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ ¬ (N < m ∧ IsTwinCenter m) →
      ∃ t, N < t ∧ IsTwinCenter t) :=
  goal_implies_descent_inputs

end EuclidsPath.BadCoverDescent
