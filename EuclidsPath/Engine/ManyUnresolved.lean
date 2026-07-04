/-
  ManyUnresolved — the route "infinitely many unresolved terminals ⟹ signature collision ⟹ Engine".
  Source: step00_manyunresolved_signature_collision_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section «Many-unresolved collision»).

  IDEA (difference from earlier routes). Earlier routes closed ONE terminal locally — and in rank-0 it
  always collapsed to "present a twin" = goal (ObstructionClosure, audit). Here the approach is different:
  instead of closing one terminal, close a MASS family via pigeonhole + local determinism. Scheme:
    NoNewTwinAbove N ⟹ ∞ high starts ⟹ (many old-absorbed ∨ many unresolved) ⟹ Engine ∨ TwinAbove.

  PROVEN HERE: the abstract COMBINATORIAL skeleton (standard axioms, no sorry, no prime arithmetic):
    * `infinite_split` — ∞ set covered by two classes ⟹ one class is ∞ (§5);
    * `infinite_two_same_sig` — ∞ set + map into Fintype ⟹ two DISTINCT elements with equal signature (§9);
    * `many_unresolved_force_close` — given U4 (same-sig ⟹ Close) ∞ unresolved ⟹ Close (§11);
    * `close_of_highStarts` — full assembly (§12): outcome split + old-branch + unresolved-branch ⟹ Close;
    * `forall_goal_of_engine` — dismissing the engine branch under ¬Engine ⟹ ∀N ∃twin>N ⟹ `TwinLowers.Infinite` (§13).

  FOUR INPUTS (U1–U4) on which the route's LIFE depends — stated here as EXPLICIT hypotheses:
    U1 `hFixedStarts`  : ∀N ∃A, ∞ high starts (CRT at fixed A, NOT density-below-A²);
    U2 `hOutcome`      : high start ⟹ old-absorbed ∨ unresolved ∨ Close (WITHOUT `SNOL.SNOLInput`);
    U3 `[Finite Sig]`  : finite signature of the unresolved terminal (does NOT store m/path/genealogy);
    U4 `hSameSig`      : two DISTINCT starts with equal signature ⟹ Close (via local determinism, NOT twin).

  HONEST BOUNDARY (corrected after audit — route is CIRCULAR, like the previous six). The skeleton is
  pure combinatorics and is proven. But the route is NOT alive:
    * U4 (`hSameSig`) is circular NOT only in the terminal but in EVERY genuine-collision branch. The
      initial claim "non-terminal cases close via `active_component_determinism`/
      `oldPeel_component_determinism`" is WRONG (audit): those lemmas prove SOMETHING ELSE — one-step
      determinism over a COMMON base `V` (two predecessors of ONE `V` coincide under equal label via
      separating scale). They (a) are not even imported/applied here, and (b) do NOT take two DISTINCT
      starts `m₁≠m₂` and do NOT yield `Close`. And pigeonhole-collision into a finite codomain does NOT
      give a common base — the direction is opposite. Hence U4 is an unproven input in all branches.
    * Machine-wise: `goal_implies_U4` — the goal discharges U4 ⟹ U4 at-least-as-hard-as goal; the
      converse is the hypothesis itself. Most transparent in a rank-0 clean prime-sided terminal: the
      only `Close` = "present a twin" = goal (as `ObstructionClosure`, `smallCleanSupply_iff_goal`).
    * U2 (outcome-split old-absorbed/unresolved) REQUIRES counting: knowing that the unresolved class is
      infinite at a fixed scale — which is exactly `bad.card < carrier.card` = `SNOL.SNOLInput`. U2
      shifts the wall, it does not break through.
    * U1: `carrier_nonempty_above` yields ONE clean center above N (honest CRT, no density), but
      `hFixedStarts` requires an INFINITE family at a fixed scale — which the single-center fact does NOT give.
  The route gives a more precise localisation (wall = U2-split + U4-collision) but does NOT close. `Step00`
  remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ManyUnresolved

open Set EuclidsPath

/-! ### §5. Infinite outcome split -/

/--
  **`infinite_split` — PROVEN.** An infinite set `S` each of whose elements belongs to class `P` or
  `Q` splits so that at least one class is infinite. Pure combinatorics (the union of two
  finite sets would be finite). -/
theorem infinite_split {α : Type*} (S : Set α) (hS : S.Infinite)
    (P Q : α → Prop) (hcov : ∀ x ∈ S, P x ∨ Q x) :
    {x ∈ S | P x}.Infinite ∨ {x ∈ S | Q x}.Infinite := by
  by_contra h
  push_neg at h
  obtain ⟨hP, hQ⟩ := h
  have hsub : S ⊆ {x ∈ S | P x} ∪ {x ∈ S | Q x} := by
    intro x hx; rcases hcov x hx with hp | hq
    · exact Or.inl ⟨hx, hp⟩
    · exact Or.inr ⟨hx, hq⟩
  exact hS ((hP.union hQ).subset hsub)

/-! ### §9. Infinite set + finite signature ⟹ collision -/

/--
  **`infinite_two_same_sig` — PROVEN (pigeonhole §9).** An infinite set `S` and a map `sig : α → Sig` into
  a finite type yield two DISTINCT elements with equal signature. (Otherwise `sig` is injective on `S` ⟹ `S`
  is finite.) -/
theorem infinite_two_same_sig {α : Type*} {Sig : Type*} [Finite Sig]
    (S : Set α) (hS : S.Infinite) (sig : α → Sig) :
    ∃ x₁ ∈ S, ∃ x₂ ∈ S, x₁ ≠ x₂ ∧ sig x₁ = sig x₂ := by
  by_contra h
  push_neg at h
  have hinj : Set.InjOn sig S := fun a ha b hb hab => by
    by_contra hne; exact h a ha b hb hne hab
  exact hS (Set.Finite.of_finite_image (Set.toFinite _) hinj)

/-! ### §11. Many unresolved ⟹ Close (via U4)

Abstractly: `HighStart`, `Unresolved`, `Sig` are parameters; `sig : subtype → Sig`. `ManyUnresolved` is
the infiniteness of the set of high-start-unresolved points. Under U4 (equal signature for distinct starts ⟹ Close), collision
yields Close. -/

/--
  **`many_unresolved_force_close` — PROVEN (given U4).** If the set of unresolved high-starts
  is infinite, the signature is finite, and equal signature for DISTINCT starts yields `Close`, then `Close`. Assembled
  from `infinite_two_same_sig`. All non-triviality lies in `hSameSig` (U4). -/
theorem many_unresolved_force_close {Sig : Type*} [Finite Sig] {Close : Prop}
    (U : ℕ → Prop) (sig : ℕ → Sig)
    (hMany : {m : ℕ | U m}.Infinite)
    (hSameSig : ∀ m₁ m₂, U m₁ → U m₂ → m₁ ≠ m₂ → sig m₁ = sig m₂ → Close) :
    Close := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hne, hsig⟩ := infinite_two_same_sig {m : ℕ | U m} hMany sig
  exact hSameSig m₁ m₂ hm₁ hm₂ hne hsig

/-! ### §12. Full diagnostic reduction -/

/--
  **`close_of_highStarts` — PROVEN (assembly §12).** Given:
    * infinitely many high starts,
    * outcome coverage (`hOutcome`: every high start is old-absorbed ∨ unresolved ∨ Close),
    * old-branch closure (`hOldCloses`: many old-absorbed ⟹ Close),
    * unresolved-branch closure (`hUnrCloses`: many unresolved ⟹ Close),
  we obtain `Close`. Case analysis via `infinite_split` on outcomes (the Close case is caught if at least one start
  yields Close). -/
theorem close_of_highStarts {Close : Prop}
    (HighStart OldAbsorbed Unresolved : ℕ → Prop)
    (hInf : {m : ℕ | HighStart m}.Infinite)
    (hOutcome : ∀ m, HighStart m → OldAbsorbed m ∨ Unresolved m ∨ Close)
    (hOldCloses : {m : ℕ | HighStart m ∧ OldAbsorbed m}.Infinite → Close)
    (hUnrCloses : {m : ℕ | HighStart m ∧ Unresolved m}.Infinite → Close) :
    Close := by
  -- if Close is reached at some start — done immediately
  by_cases hc : ∃ m, HighStart m ∧ Close
  · obtain ⟨m, _, hcl⟩ := hc; exact hcl
  · push_neg at hc
    -- otherwise every high start is old-absorbed ∨ unresolved
    have hcov : ∀ m ∈ {m : ℕ | HighStart m}, OldAbsorbed m ∨ Unresolved m := by
      intro m hm
      rcases hOutcome m hm with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hc m hm)
    rcases infinite_split {m : ℕ | HighStart m} hInf OldAbsorbed Unresolved hcov with hO | hU
    · exact hOldCloses hO
    · exact hUnrCloses hU

/-! ### §13. Final assembly over N and dismissing the engine -/

/--
  **`forall_goal_of_engine` — PROVEN (conditional assembly §13).** Given U1 (∞ high starts at a fixed scale)
  and closure of all branches in `CloseAt := Engine ∨ ∃ t>N, twin`, under `¬Engine` we obtain `∀N ∃twin>N`.
  The engine branch is dismissed by `hNoEngine`. -/
theorem forall_goal_of_engine {Engine : ℕ → Prop}
    (HighStart OldAbsorbed Unresolved : ℕ → ℕ → ℕ → Prop)
    (hFixedStarts : ∀ N, ∃ A, {m : ℕ | HighStart A N m}.Infinite)
    (hOutcome : ∀ A N, ∀ m, HighStart A N m →
      OldAbsorbed A N m ∨ Unresolved A N m ∨ (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hOldCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ OldAbsorbed A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hUnrCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ Unresolved A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hNoEngine : ∀ A, ¬ Engine A) :
    ∀ N, ∃ t, N < t ∧ IsTwinCenter t := by
  intro N
  obtain ⟨A, hInf⟩ := hFixedStarts N
  have hclose : Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t :=
    close_of_highStarts (Close := Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t)
      (HighStart A N) (OldAbsorbed A N) (Unresolved A N)
      hInf (hOutcome A N) (hOldCloses A N) (hUnrCloses A N)
  rcases hclose with he | ht
  · exact absurd he (hNoEngine A)
  · exact ht

/--
  **`twin_prime_conjecture_of_engine` — PROVEN (conditional).** Same assembly + the proven bridge
  `infinite_of_unbounded_centers` ⟹ `TwinLowers.Infinite`. -/
theorem twin_prime_conjecture_of_engine {Engine : ℕ → Prop}
    (HighStart OldAbsorbed Unresolved : ℕ → ℕ → ℕ → Prop)
    (hFixedStarts : ∀ N, ∃ A, {m : ℕ | HighStart A N m}.Infinite)
    (hOutcome : ∀ A N, ∀ m, HighStart A N m →
      OldAbsorbed A N m ∨ Unresolved A N m ∨ (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hOldCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ OldAbsorbed A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hUnrCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ Unresolved A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hNoEngine : ∀ A, ¬ Engine A) :
    TwinLowers.Infinite :=
  infinite_of_unbounded_centers
    (forall_goal_of_engine HighStart OldAbsorbed Unresolved
      hFixedStarts hOutcome hOldCloses hUnrCloses hNoEngine)

/-! ### §U4. Self-audit (corrected after audit): U4 is circular in all genuine-collision branches

Honest assessment of input U4 (`hSameSig`), corrected by adversarial audit. Initially I claimed
that NON-TERMINAL cases of U4 close via `active_component_determinism`/`oldPeel_component_determinism`.
This is WRONG, and I accept that. Those lemmas prove SOMETHING ELSE: one-step determinism over a COMMON base `V` (two
predecessors of ONE `V` coincide under equal label — separating scale). They do NOT take two DISTINCT
starts `m₁≠m₂`, do NOT yield `Close`, and are not even imported here. Pigeonhole-collision into a finite codomain of
a common base does NOT follow — the direction is opposite. Hence U4 is an unproven input EVERYWHERE, not only in the
terminal.

Machine-wise (`goal_implies_U4`): the goal discharges U4 ⟹ U4 at-least-as-hard-as goal. Most transparent in a
rank-0 clean prime-sided terminal: the only `Close` = "present a twin" = goal (fine-vs-coarse
trilemma: fine signature determines `m` ⟹ not finite ⟹ ⊥U3; finite coarse signature does not distinguish starts
⟹ ⊥U4). Same status as `smallCleanSupply_iff_goal` / `descent_reduction_is_circular`. -/

/--
  **`goal_implies_U4` — PROVEN (self-audit: U4 at-least-as-hard-as goal).** The goal `∃t>N, twin`
  trivially discharges input U4 (`Close` = goal). Hence U4 is no easier than the goal in ALL genuine-collision
  branches (not only the terminal); the route is circular, like the previous six. -/
theorem goal_implies_U4 {N : ℕ} (hgoal : ∃ t, N < t ∧ IsTwinCenter t)
    {Sig : Type} (U : ℕ → Prop) (sig : ℕ → Sig) :
    ∀ m₁ m₂, U m₁ → U m₂ → m₁ ≠ m₂ → sig m₁ = sig m₂ → (∃ t, N < t ∧ IsTwinCenter t) :=
  fun _ _ _ _ _ _ => hgoal

/-! ### §E. Higher-energy incompatibility theorem (4 channels — generalisation)

The brick `higher_energy_incompatibility` generalises `close_of_highStarts` to FOUR channels, adding
an explicit `DescentSeed` (forbidden infinite legal descent, killed by EPMI). The theorem is a pure
combinatorial incompatibility: an infinite family of high-starts cannot avoid all four
channels. This IS PROVABLE and is NOT circular AS A COMBINATORIAL STATEMENT.

HONESTLY (what this does NOT change): the new `DescentSeed` channel closes trivially (`hNoDescent`, EPMI) and
does NOT add an escape. The substantive inputs are the same `hOutcome` (U2) and `hUnresolvedManyCloses` (U4/E3),
which the adversarial audit (`w16s8jc2v`) has already flagged: U2 requires counting (= `SNOL.SNOLInput`), U4
is circular in all genuine-collision branches (`goal_implies_U4`). The generalisation to 4 channels is sound, but
does not move the wall. -/

/-- §5. Auxiliary: `S ⊆ A ∪ B`, `S` infinite ⟹ `A` or `B` infinite. -/
theorem infinite_or_infinite_of_subset_union {α : Type*} {S A B : Set α}
    (hInf : S.Infinite) (hSub : S ⊆ A ∪ B) : A.Infinite ∨ B.Infinite := by
  by_contra h
  push_neg at h
  obtain ⟨hA, hB⟩ := h
  exact hInf ((hA.union hB).subset hSub)

/--
  **`higher_energy_incompatibility_on_euclidean_path` — PROVEN (4-channel incompatibility; this is a
  COMBINATORIAL SHELL, does NOT move the wall — the load lies in unproven U2/U4).**
  Infinite family of high-starts + outcome coverage by four channels (Close / DescentSeed /
  OldAbsorbed / Unresolved) + prohibition of Descent (EPMI) + closure of both mass branches ⟹ `¬Close`
  is impossible (`False`). Pure combinatorics: under `¬Close` and `¬DescentSeed` every high-start is
  old-absorbed ∨ unresolved, infiniteness gives an infinite mass branch, which closes — contradicting
  `hNoClose`. Sound and NOT circular as a statement; the load lies in U2 (`hOutcome`) and U4
  (`hUnresolvedManyCloses`), see §E. -/
theorem higher_energy_incompatibility_on_euclidean_path
    (HighStart OldAbsorbed Unresolved DescentSeed : ℕ → Prop) (Close : Prop)
    (hInfStarts : Set.Infinite {m : ℕ | HighStart m})
    (hOutcome : ∀ m, HighStart m → Close ∨ DescentSeed m ∨ OldAbsorbed m ∨ Unresolved m)
    (hNoDescent : ∀ m, DescentSeed m → False)
    (hOldManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ OldAbsorbed m} → Close)
    (hUnresolvedManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ Unresolved m} → Close)
    (hNoClose : ¬ Close) : False := by
  have hCover : {m : ℕ | HighStart m} ⊆
      {m : ℕ | HighStart m ∧ OldAbsorbed m} ∪ {m : ℕ | HighStart m ∧ Unresolved m} := by
    intro m hm
    rcases hOutcome m hm with hC | hD | hO | hU
    · exact absurd hC hNoClose
    · exact absurd (hNoDescent m hD) not_false
    · exact Or.inl ⟨hm, hO⟩
    · exact Or.inr ⟨hm, hU⟩
  rcases infinite_or_infinite_of_subset_union hInfStarts hCover with hOld | hUnr
  · exact hNoClose (hOldManyCloses hOld)
  · exact hNoClose (hUnresolvedManyCloses hUnr)

/-! ### §7. Step00 specialisation: `CloseAt` and dismissing two preconditions -/

/-- `CloseAt A M0 N := Engine A ∨ ∃ t>N, twin`. -/
def CloseAt (Engine : ℕ → Prop) (A N : ℕ) : Prop :=
  Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t

/-- **`noClose_of_noEngine_noNew` — PROVEN.** `¬Engine` + "no twin above N" ⟹ `¬CloseAt`. -/
theorem noClose_of_noEngine_noNew {Engine : ℕ → Prop} {A N : ℕ}
    (hNoEngine : ¬ Engine A) (hNoNew : ¬ ∃ t, N < t ∧ IsTwinCenter t) :
    ¬ CloseAt Engine A N := by
  rintro (hE | hT)
  · exact hNoEngine hE
  · exact hNoNew hT

/--
  **`higher_energy_incompatibility_step00` — PROVEN (specialisation §7; shell, does NOT move the wall).**
  Under `¬Engine A` and "no twin above N" the four channels are incompatible ⟹ `False`. This is a CONTRAPOSITIVE
  packaging: inputs U2/U4 remain unproven (U2 = counting = `SNOL.SNOLInput`, U4 is circular). `twin_prime_conjecture`
  does NOT follow — all the load lies in the uninstantiated inputs. -/
theorem higher_energy_incompatibility_step00 {Engine : ℕ → Prop} {A N : ℕ}
    (HighStart OldAbsorbed Unresolved DescentSeed : ℕ → Prop)
    (hInfStarts : Set.Infinite {m : ℕ | HighStart m})
    (hOutcome : ∀ m, HighStart m →
      CloseAt Engine A N ∨ DescentSeed m ∨ OldAbsorbed m ∨ Unresolved m)
    (hNoDescent : ∀ m, DescentSeed m → False)
    (hOldManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ OldAbsorbed m} → CloseAt Engine A N)
    (hUnresolvedManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ Unresolved m} → CloseAt Engine A N)
    (hNoEngine : ¬ Engine A)
    (hNoNew : ¬ ∃ t, N < t ∧ IsTwinCenter t) : False :=
  higher_energy_incompatibility_on_euclidean_path
    HighStart OldAbsorbed Unresolved DescentSeed (CloseAt Engine A N)
    hInfStarts hOutcome hNoDescent hOldManyCloses hUnresolvedManyCloses
    (noClose_of_noEngine_noNew hNoEngine hNoNew)

end EuclidsPath.ManyUnresolved
