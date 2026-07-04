/-
  Labelled fan-in patch for GlobalOldAbsorption — Step00 final node, version v2.
  Source: step00_labelled_fanin_patch_ru_2026-07-01.md (a prose specification).
  Prose: prose/24_BoundaryDecomp.md (to update), README.

  ARCHITECTURAL PATCH: replace the impossible path `InfiniteNodeableCenters ⟹ CoreCollision ⟹ Engine`
  (impossible, because the separating scale makes CoreSig INJECTIVE — no collisions) with a path via
  labelled fan-in over REAL arithmetic steps:

    GlobalOldAbsorption ⟹ LabelledFanIn ∨ InfiniteLegalDescent      (dichotomy — König)
    ¬InfiniteLegalDescent                                            (EPMI)
    LabelledFanIn ⟹ EuclideanEngine                                 (local label determinism)

  HONEST STATUS (audit inside the file):
  What is PROVEN here (abstractly, standard axioms):
    * the dichotomy under the EXPLICIT input `no_labelled_fanin ⟹ InfiniteLegalDescent` (König via
      dependent choice) — the König construction itself;
    * `labelledFanIn_to_engine` from `LocalLabelDeterminism` — pure logic;
    * `localLabelDeterminism` from `BoundaryLabelDeterminism` + `SNOLLabelDeterminism` + separating scale
      — case-split assembly;
    * `globalAbsorption_to_engine` — final packaging.
  What REMAINS AN INPUT (hypotheses, NOT proven — the new localization of the node):
    * `BoundaryLabelDeterminism` — that a boundary code determines the predecessor ∨ engine
      (requires `boundaryStep_normalForm` — the normal form of a boundary step, NOT proven);
    * `SNOLLabelDeterminism` — the same for SNOL (= SNOLHall ⟹ engine, the old SNOL wall);
    * finite `EdgeSig` — for fixed A: finiteness of codes (plausible, but each code type
      must be exhibited as finite — not done abstractly).

  CONCLUSION (v3, brick `step00_hkonig_label_tree_closure...`, 2026-07-01): the patch still does NOT close
  Step00, BUT the node has narrowed SUBSTANTIALLY. The key difference of v3 from v2: **the König branch is NOW PROVEN**
  (`absorption_labelled_dichotomy` — a genuine theorem, not an input). Exactly ONE substantive
  wall remains — `hComp`, and more precisely its SNOL case `hHallSeed`:
    • PROVEN (König closed, §7): `GlobalOldAbsorption` + finiteness of the absorbers + a finite alphabet
      of labels ⟹ `LabelledFanIn ∨ InfiniteLegalDescent`. The method — state-level backward König: the invariant
      `ManyRoute V` (∞ sources reach V), pigeonhole over the FINITE predecessors (`preds_finite`
      from ¬fanin + finite Lbl), iteration via dependent choice. Mathlib's König is NOT needed — only two
      infinite-fiber pigeonholes. The false premise of v1 "every state has a predecessor" no longer
      figures anywhere.
    • WHAT REMAINS (the sole substantive input): `hComp = ComponentDeterminism`, whose four
      exact components (active/oldPeel/boundary/corridor) are instantiation arithmetic, while the fifth (`snol`)
      reduces (§24, `snol_kindDeterminism_of_normalForm` — the assembly is PROVEN) to `hHallSeed`: "a SNOL
      hall-seed with distinct predecessors ⟹ engine". This is EXACTLY the old SNOL/Hall wall, the same
      load as `pump` in `BoundaryDecomp.global_absorber_forces_engine`.
    • NOT EXHIBITED: the binding of `σ`/`RealStep`/`edgeSig` to the concrete graph `6m±1`/`TwinCenterZ`
      (the machine is abstract); `hOldFin`/`[Finite Lbl]`/`hAll` — plausible, but in this abstract
      form they are accepted instantiation assumptions.
  Proven without axioms: `labelledFanIn_to_engine`, `descent_from_manyRoute`, `localLabelDeterminism`,
  `componentDeterminism_of_components`, `snol_kindDeterminism_of_normalForm`. The red line is NOT crossed
  (no probabilities/density — König is purely combinatorial). Step00.twin_prime_conjecture remains
  `sorry` — the node is not closed, but reduced to a single SNOL implication.

  CONCLUSION v4 (brick `snol_hallseed_strict_closure`, 2026-07-01; refined by audit): the SNOL wall is reduced to
  the MORE LIGHTLY stated law `SNOLHallSeedRegenerates` (seed ⟹ return-path — strictly lighter than the old
  seed⇒engine wall), but the load does NOT compress "to a single lemma". Key new facts (§26–27):
    • MACHINE-CHECKED NO-GO (`snolHallSeed_bare_no_go`): the bare non-injectivity of a SNOL label does NOT yield
      engine (a concrete 3-state model where the seed exists, but there is no descent). Honesty is built into the type.
    • PROVEN closure of SNOL under the regeneration law: `snolHallSeed_to_engine_of_regeneration`
      (axiom-free), `snol_kindDeterminism_of_regeneration`. Mechanism: seed `Uᵢ→V` + return `V→⁺Uᵢ`
      = a non-empty cycle `Uᵢ→⁺Uᵢ`, forbidden by the engine (`no_cycle_of_height`, a single orientation of height).
    • IMPORTANT CAVEAT (`regen_under_hdrop_kills_seed`, PROVEN): under the same `hdrop` that closes all
      the rest, the seed and its regeneration are MUTUALLY EXCLUSIVE (a cycle). Hence `SNOLHallSeedRegenerates`
      holds only VACUOUSLY (seed-empty), while the REAL arithmetic content MIGRATES into the very
      `hdrop` — the existence of a strictly monotone co-height on `6m±1` (= acyclicity/EPMI), NOT exhibited.
  This is NOT a closure of Step00, and the remainder HONESTLY splits into at least: (a) `SNOLHallSeedRegenerates`; (b) `hdrop`
  (co-height/acyclicity on the real graph — the true carrier of the arithmetic); (c) the four components
  of injectivity (under `Engine:=False` they are not free); (d) instantiation. One must not compress it to "only the
  SNOL wall remains":
    • `hAll : ∀x, Legal x` — FALSE on the concrete graph `6m±1` (legality there is a real restriction);
      the abstract dichotomy does not instantiate directly without a legality-restricted König (not done);
    • `[Finite Lbl]` — this is counting/fan-in content in the guise of a typeclass (plausible for fixed A);
    • the four exact components + `hKindEq` — declared as instantiation arithmetic, but NOT proven
      (no instantiation);
    • MAIN POINT: the machine is ABSTRACT and not connected — `EuclideanEngine` is a free `Prop`, `σ`/`RealStep`/
      `edgeSig` are not bound to `TwinCenterZ`/`CoreSig`/`6m±1`, and no file outside this module
      consumes its theorems. Therefore closing `SNOLHallSeedRegenerates` on its own would NOT close
      `twin_prime_conjecture` — an instantiation to the real graph is still needed.
  Step00.twin_prime_conjecture remains `sorry`. The progress is real (the König input became a theorem), but
  the node is not closed — it is reduced to a single SNOL lemma PLUS the instantiation of the abstract machine.

  HISTORY: v1→v2 (audit by 8 agents): the false `∀ s` premise removed; `descend` renamed; a genuine
  `localLabelDeterminism`; a real conjunction `ComponentDeterminism`. v2→v3: the König branch PROVEN
  (state-level backward König); `hComp` localized to the SNOL hall-seed wall. v3→v4: the SNOL wall reduced
  to `SNOLHallSeedRegenerates` (regeneration ⟹ cycle ⟹ ⊥) + a machine-checked no-go for the bare seed.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.BoundaryDecomp

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.LabelledFanIn

/-! ### §2–3. The abstract real-step graph and path-absorbed

We work in an abstract model: a type of states `σ`, a real-step relation `RealStep`,
an old-absorber predicate `OldAbsorber`. The concrete instantiation (ActiveDelete/OldPeel/BoundaryExit/
SNOL/OldCorridor) is given in the prose; here we fix only the PROPERTIES needed for the dichotomy.

`Absorbed` is a PATH property (terminal), NOT a local step constructor: a start is absorbed
if there is a finite real-step path from it into an absorber. This is the key architectural point of §1: remove
the primitive `AbsorberStep`, which allowed an arbitrary many-to-one collapse. -/

variable {σ : Type*}

/-- Reflexive-transitive closure of `RealStep`: a finite path `s → … → O`. -/
def Path (RealStep : σ → σ → Prop) : σ → σ → Prop := Relation.ReflTransGen RealStep

/-- `Absorbed s` — from `s` there is a finite real-step path into an old absorber. A path property, not a step. -/
def Absorbed (RealStep : σ → σ → Prop) (OldAbsorber : σ → Prop) (s : σ) : Prop :=
  ∃ O, OldAbsorber O ∧ Path RealStep s O

/-- **`GlobalOldAbsorption`** — the reduction goal (§3): infinitely many distinct legal fresh
    starts, each of which is absorbed (there is a finite real-step path into an absorber). This is the abstract
    form of `BoundaryDecomp.GlobalOldTwinAbsorption`; the premise of the König branch. -/
def GlobalOldAbsorption (RealStep : σ → σ → Prop) (OldAbsorber : σ → Prop) (Fresh : σ → Prop) : Prop :=
  { s : σ | Fresh s ∧ Absorbed RealStep OldAbsorber s }.Infinite

/-! ### §6. InfiniteLegalDescent -/

/-- Infinite real-step descent: `X (n+1) → X n` for all `n`. (Strictness/distinctness is NOT built in —
    the definition allows cycles/self-loops; strictness is realized EXTERNALLY by the height hypothesis, see
    `no_infiniteLegalDescent_of_height`. As a lemma about strict decrease it is used nowhere.) -/
def InfiniteLegalDescent (RealStep : σ → σ → Prop) : Prop :=
  ∃ X : ℕ → σ, ∀ n, RealStep (X (n + 1)) (X n)

/-! ### §5. LabelledFanIn -/

/-- `LabelledFanIn`: two DISTINCT legal predecessors `U₁ ≠ U₂` of a single `V` with the SAME edge
    label. This is what should generate the engine (via label determinism). -/
def LabelledFanIn {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) : Prop :=
  ∃ U₁ U₂ V, U₁ ≠ U₂ ∧ Legal U₁ ∧ Legal U₂ ∧ Legal V ∧
    RealStep U₁ V ∧ RealStep U₂ V ∧ edgeSig U₁ V = edgeSig U₂ V

/-! ### §14. LocalLabelDeterminism -/

/-- `LocalLabelDeterminism`: coincidence of the edge label of two predecessors of a single `V` entails
    their equality ∨ engine. This is a SUBSTANTIVE input (boundary/SNOL/active normal forms). -/
def LocalLabelDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (EuclideanEngine : Prop) : Prop :=
  ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
    RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V →
    U₁ = U₂ ∨ EuclideanEngine

/-! ### §15. LabelledFanIn ⟹ Engine (PROVEN — pure logic) -/

/--
  **Theorem 15.1 (`labelledFanIn_to_engine`) — PROVEN.** If `LocalLabelDeterminism` holds,
  then `LabelledFanIn ⟹ EuclideanEngine`. Proof: from the fan-in we take `U₁ ≠ U₂` with equal label;
  determinism gives `U₁ = U₂ ∨ engine`; the first contradicts `U₁ ≠ U₂`, hence engine. -/
theorem labelledFanIn_to_engine {Lbl : Type*} {RealStep : σ → σ → Prop} {Legal : σ → Prop}
    {edgeSig : σ → σ → Lbl} {EuclideanEngine : Prop}
    (hDet : LocalLabelDeterminism RealStep Legal edgeSig EuclideanEngine)
    (hFan : LabelledFanIn RealStep Legal edgeSig) : EuclideanEngine := by
  obtain ⟨U₁, U₂, V, hne, hL1, hL2, hLV, hs1, hs2, hsig⟩ := hFan
  rcases hDet U₁ U₂ V hL1 hL2 hLV hs1 hs2 hsig with heq | heng
  · exact absurd heq hne
  · exact heng

/-! ### §7. The dichotomy — NOW PROVEN (state-level backward König)

Statement §7.1: from `GlobalOldAbsorption` (∞ absorbed starts) + finiteness of the absorbers + finiteness
of `EdgeSig` it follows that `LabelledFanIn ∨ InfiniteLegalDescent`. In version v2 this was the input `KonigBranchInput`;
here (v3, brick `step00_hkonig_label_tree_closure...`) the König branch is **proven** without the false premise
"every state has a predecessor".

METHOD. Instead of a label-prefix-tree + `stateAtPrefix` reconstruction (fragile), we run König directly on
the states, via the invariant `ManyRoute V` := "infinitely many fresh sources have a path into `V`".
The key — that under `¬LabelledFanIn` **the predecessors of any `V` are finite** (the edge label is injective on
predecessors, `preds_finite`), so from `ManyRoute V` by pigeonhole we obtain a predecessor `U`
(`RealStep U V`) with `ManyRoute U` (`manyRoute_pred`). Iteration (dependent choice) gives an infinite
descent. The initial `ManyRoute O` — by pigeonhole over the finite absorbers (`manyRoute_absorber`).
No mathlib König is needed: all the combinatorics is two infinite-fiber pigeonholes + recursion. -/

/-- `PathR` — the reflexive-transitive closure (the same `Path`, a local synonym for the König lemmas). -/
abbrev PathR (RealStep : σ → σ → Prop) : σ → σ → Prop := Path RealStep

/-- `ManyRoute V` — infinitely many fresh sources have a real-step path into `V`. The König invariant. -/
def ManyRoute (RealStep : σ → σ → Prop) (Fresh : σ → Prop) (V : σ) : Prop :=
  {s | Fresh s ∧ Path RealStep s V}.Infinite

/--
  **`preds_finite` — PROVEN.** Under `¬LabelledFanIn` (uniqueness of the predecessor by label) and
  a finite alphabet of labels, the predecessors of any `V` form a finite set: the map
  `U ↦ edgeSig U V` is injective on `{U | RealStep U V}`, and the image is finite. -/
theorem preds_finite {Lbl : Type*} [Finite Lbl] {RealStep : σ → σ → Prop} {edgeSig : σ → σ → Lbl}
    {V : σ}
    (huniq : ∀ U₁ U₂, RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂) :
    {U | RealStep U V}.Finite := by
  have hinj : Set.InjOn (fun U => edgeSig U V) {U | RealStep U V} := fun a ha b hb hab =>
    huniq a b ha hb hab
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

/-- Uniqueness of the predecessor by label — a direct rewriting of `¬LabelledFanIn`. -/
theorem unique_predecessor_of_no_labelledFanIn {Lbl : Type*} {RealStep : σ → σ → Prop}
    {Legal : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hNoFan : ¬ LabelledFanIn RealStep Legal edgeSig)
    (hAll : ∀ x, Legal x) {U₁ U₂ V : σ}
    (hs1 : RealStep U₁ V) (hs2 : RealStep U₂ V) (hsig : edgeSig U₁ V = edgeSig U₂ V) : U₁ = U₂ := by
  by_contra hne
  exact hNoFan ⟨U₁, U₂, V, hne, hAll U₁, hAll U₂, hAll V, hs1, hs2, hsig⟩

/--
  **`manyRoute_pred` — PROVEN (the key König descent step).** If infinitely many sources
  reach `V` (`ManyRoute V`), then (given uniqueness of the predecessor by label and a finite alphabet)
  there exists a predecessor `U` (`RealStep U V`) reached by infinitely many as well (`ManyRoute U`).
  Proof: sources `≠ V` factor through the predecessors of `V` (`ReflTransGen.cases_tail`);
  there are finitely many predecessors (`preds_finite`); pigeonhole over the finite set of predecessors. -/
theorem manyRoute_pred {Lbl : Type*} [Finite Lbl] {RealStep : σ → σ → Prop} {Fresh : σ → Prop}
    {edgeSig : σ → σ → Lbl}
    (huniq : ∀ V U₁ U₂, RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂)
    {V : σ} (hV : ManyRoute RealStep Fresh V) :
    ∃ U, RealStep U V ∧ ManyRoute RealStep Fresh U := by
  set S := {s | Fresh s ∧ Path RealStep s V} with hS
  have hpick : ∀ s ∈ S, s ≠ V → ∃ U, RealStep U V ∧ Path RealStep s U := by
    intro s hs hne
    rcases (Relation.ReflTransGen.cases_tail hs.2) with h | ⟨U, hsU, hUV⟩
    · exact absurd h.symm hne
    · exact ⟨U, hUV, hsU⟩
  have hS'inf : {s ∈ S | s ≠ V}.Infinite := by
    have hEq : {s ∈ S | s ≠ V} = S \ {V} := by
      ext s; constructor <;> intro h <;> simp_all
    rw [hEq]; exact hV.diff (Set.finite_singleton V)
  choose! pick hpick1 hpick2 using hpick
  have hpredfin : {U | RealStep U V}.Finite := preds_finite (huniq V)
  have hfiber : ∃ U ∈ {U | RealStep U V}, {s ∈ {s ∈ S | s ≠ V} | pick s = U}.Infinite := by
    by_contra h
    push_neg at h
    have hcov : {s ∈ S | s ≠ V} ⊆ ⋃ U ∈ {U | RealStep U V}, {s ∈ {s ∈ S | s ≠ V} | pick s = U} := by
      intro s hs
      simp only [Set.mem_iUnion]
      exact ⟨pick s, hpick1 s hs.1 hs.2, hs, rfl⟩
    exact hS'inf ((hpredfin.biUnion (fun U hU => h U hU)).subset hcov)
  obtain ⟨U, hUV, hUinf⟩ := hfiber
  refine ⟨U, hUV, hUinf.mono ?_⟩
  intro s hs
  refine ⟨hs.1.1.1, ?_⟩
  have hp := hpick2 s hs.1.1 hs.1.2
  rw [hs.2] at hp; exact hp

/--
  **`manyRoute_absorber` — PROVEN (the König starting node).** From `GlobalOldAbsorption` (∞ absorbed
  fresh sources) and finiteness of the absorbers, pigeonhole gives ONE absorber `O` reached by
  infinitely many sources (`ManyRoute O`). -/
theorem manyRoute_absorber {RealStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite) :
    ∃ O, OldAbsorber O ∧ ManyRoute RealStep Fresh O := by
  set G := {s | Fresh s ∧ Absorbed RealStep OldAbsorber s} with hG
  have hpick : ∀ s ∈ G, ∃ O, OldAbsorber O ∧ Path RealStep s O := fun s hs => hs.2
  choose! Ω hΩ1 hΩ2 using hpick
  have hfiber : ∃ O ∈ {O | OldAbsorber O}, {s ∈ G | Ω s = O}.Infinite := by
    by_contra h
    push_neg at h
    have hcov : G ⊆ ⋃ O ∈ {O | OldAbsorber O}, {s ∈ G | Ω s = O} := by
      intro s hs; simp only [Set.mem_iUnion]; exact ⟨Ω s, hΩ1 s hs, hs, rfl⟩
    exact hGlobal ((hOldFin.biUnion (fun O hO => h O hO)).subset hcov)
  obtain ⟨O, hO, hOinf⟩ := hfiber
  refine ⟨O, hO, hOinf.mono ?_⟩
  intro s hs
  exact ⟨hs.1.1, by have := hΩ2 s hs.1; rwa [hs.2] at this⟩

/--
  **`descent_from_manyRoute` — PROVEN (König iteration via dependent choice).** If every `V`
  with `ManyRoute V` has a predecessor `U` with `ManyRoute U`, then from `ManyRoute O` an infinite
  real-step descent is built. Recursion over `Nat` carrying the `ManyRoute` invariant. -/
theorem descent_from_manyRoute {RealStep : σ → σ → Prop} {Fresh : σ → Prop}
    (step : ∀ V, ManyRoute RealStep Fresh V → ∃ U, RealStep U V ∧ ManyRoute RealStep Fresh U)
    {O : σ} (hO : ManyRoute RealStep Fresh O) : InfiniteLegalDescent RealStep := by
  choose predOf hpred1 hpred2 using step
  let Y : ℕ → {V : σ // ManyRoute RealStep Fresh V} :=
    fun n => Nat.rec ⟨O, hO⟩ (fun _ prev => ⟨predOf prev.val prev.property,
      hpred2 prev.val prev.property⟩) n
  exact ⟨fun n => (Y n).val, fun n => hpred1 (Y n).val (Y n).property⟩

/--
  **Dichotomy (`absorption_labelled_dichotomy`) — NOW PROVEN (not an input!).** From `GlobalOldAbsorption`
  + finiteness of the absorbers + finiteness of the label alphabet + universal legality follows
  `LabelledFanIn ∨ InfiniteLegalDescent`. If fan-in holds — the left branch. If not — uniqueness of
  the predecessor by label (`unique_predecessor_of_no_labelledFanIn`) launches state-level König:
  `manyRoute_absorber → manyRoute_pred (iter.) → descent_from_manyRoute`. This is a strict closure of `hKonig`. -/
theorem absorption_labelled_dichotomy {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x) :
    LabelledFanIn RealStep Legal edgeSig ∨ InfiniteLegalDescent RealStep := by
  by_cases hfan : LabelledFanIn RealStep Legal edgeSig
  · exact Or.inl hfan
  · refine Or.inr ?_
    -- ¬fanin ⟹ uniqueness of the predecessor by label
    have huniq : ∀ V U₁ U₂, RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂ :=
      fun V U₁ U₂ hs1 hs2 hsig => unique_predecessor_of_no_labelledFanIn hfan hAll hs1 hs2 hsig
    obtain ⟨O, _, hO⟩ := manyRoute_absorber hGlobal hOldFin
    exact descent_from_manyRoute (fun V hV => manyRoute_pred huniq hV) hO

/-! ### §8. Removing the infinite-descent branch (EPMI) -/

/--
  **`globalAbsorption_to_labelledFanIn` — PROVEN (König closed).** If infinite descent is forbidden
  (EPMI, `hNoInf`), the proven dichotomy collapses to `LabelledFanIn`. The König branch is no longer an input. -/
theorem globalAbsorption_to_labelledFanIn {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hNoInf : ¬ InfiniteLegalDescent RealStep) :
    LabelledFanIn RealStep Legal edgeSig := by
  rcases absorption_labelled_dichotomy hGlobal hOldFin hAll (edgeSig := edgeSig) with hfan | hinf
  · exact hfan
  · exact absurd hinf hNoInf

/-! ### §14.2. LocalLabelDeterminism from components (PROVEN — assembly)

`localLabelDeterminism` is assembled from the determinisms of the step's subtypes. To make the assembly
GENUINE (rather than a renaming), we introduce a step classifier `kind : σ → σ → Kind` (edge tag: active/oldPeel/
boundary/snol/corridor), consistent with `edgeSig` (equal labels ⟹ equal tags — `kind_of_edgeSig`),
and FIVE separate component determinisms. The `localLabelDeterminism` assembly is then a real
case-split by tag with the mixed-case closed by tag consistency. The substantive load is in the five
components (§11–13), especially in `snol` (= the old SNOL/Hall wall); they are inputs here. -/

/-- Tag of a real-step edge: five mutually exclusive step sorts (§2). -/
inductive Kind | active | oldPeel | boundary | snol | corridor
deriving DecidableEq

/-- A single component determinism: for edges of a given tag `k` an equal label ⟹ equality ∨ engine. -/
def KindDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) (EuclideanEngine : Prop) (k : Kind) : Prop :=
  ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
    RealStep U₁ V → RealStep U₂ V → kind U₁ V = k → kind U₂ V = k →
    edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂ ∨ EuclideanEngine

/-- **`ComponentDeterminism` — a genuine conjunction of five sub-determinisms** (§11–13), and NOT an alias
    of the full statement. Each step sort is served by its own component. -/
def ComponentDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) (EuclideanEngine : Prop) : Prop :=
  (∀ k, KindDeterminism RealStep Legal edgeSig kind EuclideanEngine k)

/--
  **`localLabelDeterminism` — PROVEN (a GENUINE assembly, not an alias).** Given a classifier `kind`,
  consistent with `edgeSig` (`hKindEq`: equal labels ⟹ equal tags), and five component determinisms
  (`hComp`). Then `LocalLabelDeterminism` is derived by a case-split: for a pair `U₁,U₂ → V` with an equal
  label the tags `kind U₁ V` and `kind U₂ V` are EQUAL (from `hKindEq`), so both equal some `k`, and
  the component `hComp k` gives `U₁ = U₂ ∨ engine`. The mixed-case (distinct tags) is excluded by `hKindEq` itself.

  This is a real derivation: it is NOT syntactically equal to `hComp` — it uses `hKindEq` and a tag analysis.
  The load is in the five components (inputs), but the ASSEMBLY is proven. -/
theorem localLabelDeterminism {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind} {EuclideanEngine : Prop}
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind EuclideanEngine) :
    LocalLabelDeterminism RealStep Legal edgeSig EuclideanEngine := by
  intro U₁ U₂ V hL1 hL2 hLV hs1 hs2 hsig
  -- the tags coincide from the edgeSig↔kind consistency
  have htag : kind U₁ V = kind U₂ V := hKindEq U₁ U₂ V hsig
  -- apply the component responsible for the tag kind U₁ V
  exact hComp (kind U₁ V) U₁ U₂ V hL1 hL2 hLV hs1 hs2 rfl htag.symm hsig

/-! ### §16. Global absorption ⟹ engine (PROVEN under explicit inputs) -/

/--
  **Theorem 16.1 (`globalAbsorption_to_engine`) — PROVEN (König closed; ONE input `hComp` remains).**
  Assembly of the whole chain: the proven dichotomy + EPMI (no descent) gives `LabelledFanIn`; local label
  determinism turns it into an engine. The König branch is NO LONGER AN INPUT (proven in §7).

  The inputs now: `hGlobal` (the reduction goal), `hOldFin` (finiteness of the absorbers — plausible:
  absorbers `≤ M₀`), `[Finite Lbl]` (finiteness of the label alphabet for a fixed A), `hAll`
  (universal legality in the abstract model), `hNoInf` (EPMI — PROVABLE via
  `no_infiniteLegalDescent_of_height`), `hKindEq` (edgeSig↔kind consistency), and — the ONLY
  substantive unreduced input — `hComp : ComponentDeterminism`, whose SNOL case is EXACTLY the old
  SNOL/Hall wall (`SNOLBoundary` non-injective ⟹ engine, see §23–24 brick).

  CONCLUSION: the node narrowed to `hComp` = `SNOLBoundaryLabelDeterminism`. The König/counting part is closed. -/
theorem globalAbsorption_to_engine {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind} {EuclideanEngine : Prop}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hNoInf : ¬ InfiniteLegalDescent RealStep)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind EuclideanEngine) :
    EuclideanEngine := by
  have hfan : LabelledFanIn RealStep Legal edgeSig :=
    globalAbsorption_to_labelledFanIn hGlobal hOldFin hAll hNoInf
  exact labelledFanIn_to_engine (localLabelDeterminism hKindEq hComp) hfan

/-! ### §23–24. Localizing `hComp`: the SNOL wall as the sole substantive input

After closing König the only substantive unreduced input is the component determinism.
Four of the five components (`active`, `oldPeel`, `corridor`, `boundary`-exact) are exact determinisms:
the label stores the exact predecessor data, so equality of labels ⟹ equality of predecessors
(in the concrete instantiation — the arithmetic of separating scale / exact old-prime / exact corridor). The fifth,
`snol`, may be non-injective — and this is EXACTLY the old SNOL/Hall wall. We formalize its normal form.

`SNOLBoundaryLabelDeterminism` — what remains: for a SNOL edge an equal label ⟹ equality ∨ engine. -/

/-- §23. The remaining SNOL input in explicit form: determinism of the SNOL-edge label (or engine). -/
def SNOLBoundaryLabelDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) (EuclideanEngine : Prop) : Prop :=
  KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.snol

/--
  **§24 (`snol_kindDeterminism_of_normalForm`) — PROVEN (SNOL normal form).** SNOL determinism
  REDUCES to two sub-cases: `snolExact` (the label stores the exact predecessor ⟹ equality) and
  `snolHallSeed` (non-injectivity ⟹ engine). Given a classifier `snolMode : σ → σ → Bool`
  (`true` = exact, `false` = hall-seed) and two sub-determinisms — we assemble the full SNOL determinism.

  This is a GENUINE assembly (case split by `snolMode`), not an alias. The substantive load is in
  `hHallSeed` (hall-seed ⟹ engine): this is the unreduced SNOL/Hall wall (brick §24). -/
theorem snol_kindDeterminism_of_normalForm {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop} (snolMode : σ → σ → Bool)
    -- exact/exact with an equal label ⟹ equality of predecessors
    (hExact : ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
      RealStep U₁ V → RealStep U₂ V → kind U₁ V = Kind.snol → kind U₂ V = Kind.snol →
      snolMode U₁ V = true → snolMode U₂ V = true → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂)
    -- any hall-seed case (distinct predecessors with an equal label) ⟹ engine
    (hHallSeed : ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
      RealStep U₁ V → RealStep U₂ V → kind U₁ V = Kind.snol → kind U₂ V = Kind.snol →
      (snolMode U₁ V = false ∨ snolMode U₂ V = false) → edgeSig U₁ V = edgeSig U₂ V →
      U₁ = U₂ ∨ EuclideanEngine) :
    SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind EuclideanEngine := by
  intro U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig
  -- case split by snolMode of both
  by_cases hm1 : snolMode U₁ V = true
  · by_cases hm2 : snolMode U₂ V = true
    · exact Or.inl (hExact U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 hm1 hm2 hsig)
    · exact hHallSeed U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 (Or.inr (by simpa using hm2)) hsig
  · exact hHallSeed U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 (Or.inl (by simpa using hm1)) hsig

/--
  **§25 (`componentDeterminism_of_components`) — PROVEN (full assembly of `hComp`).** `ComponentDeterminism`
  is assembled from the determinism of each of the five tags. Four exact components (`active`/`oldPeel`/
  `boundary`/`corridor`) plus the SNOL component (§24). This is the final localization: the ONLY substantively
  unreduced piece is `hHallSeed` inside SNOL (the wall); everything else is exact arithmetic of the instantiation. -/
theorem componentDeterminism_of_components {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop}
    (hActive : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.active)
    (hOldPeel : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.oldPeel)
    (hBoundary : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.boundary)
    (hSnol : SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind EuclideanEngine)
    (hCorridor : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.corridor) :
    ComponentDeterminism RealStep Legal edgeSig kind EuclideanEngine := by
  intro k
  cases k with
  | active => exact hActive
  | oldPeel => exact hOldPeel
  | boundary => exact hBoundary
  | snol => exact hSnol
  | corridor => exact hCorridor

/-! ### §26. Strict closure of the SNOL component via regeneration (brick `snol_hallseed_strict_closure`)

Here we honestly carry the SNOL wall down to its exact unreduced core. First — a **machine-checked
no-go** (§1 brick): bare non-injectivity of the SNOL label does NOT yield an engine. Then — the minimal local
law `SNOLHallSeedRegenerates`, which suffices, and which remains the ONLY substantive
arithmetic input of the whole programme. -/

/-- A path of length `n` (number of real-step edges). `PathN 0 X Y := X = Y`. -/
def PathN (RealStep : σ → σ → Prop) : ℕ → σ → σ → Prop
  | 0,     X, Y => X = Y
  | (n+1), X, Y => ∃ Z, RealStep X Z ∧ PathN RealStep n Z Y

/-- A nonempty path `X →⁺ Y`: length `≥ 1`. -/
def NonemptyPath (RealStep : σ → σ → Prop) (X Y : σ) : Prop := ∃ n, 0 < n ∧ PathN RealStep n X Y

/-- `SNOLHallSeed`: two DISTINCT SNOL predecessors of a single `V` with the same label `c`. -/
def SNOLHallSeed {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) : Prop :=
  ∃ U₁ U₂ V, U₁ ≠ U₂ ∧ Legal U₁ ∧ Legal U₂ ∧ Legal V ∧
    RealStep U₁ V ∧ RealStep U₂ V ∧ kind U₁ V = Kind.snol ∧ kind U₂ V = Kind.snol ∧
    edgeSig U₁ V = edgeSig U₂ V

/--
  **§1 (`snolHallSeed_bare_no_go`) — NO-GO PROVEN (machine).** Bare non-injectivity of the SNOL label
  does NOT entail an engine. Formally: there exists a concrete model (three states `U₁,U₂,V`, two edges
  `U₁→V`, `U₂→V` of the same label, strictly decreasing height) in which `SNOLHallSeed` holds, yet
  `InfiniteLegalDescent` does NOT (height strictly drops ⟹ no descent). So from `SNOLHallSeed` in pure
  form one can derive neither `InfiniteLegalDescent`, nor (under `Engine := InfiniteLegalDescent`) an engine —
  additional arithmetic structure is needed (§2). -/
theorem snolHallSeed_bare_no_go :
    ∃ (τ : Type) (RealStep : τ → τ → Prop) (Legal : τ → Prop)
      (edgeSig : τ → τ → Unit) (kind : τ → τ → Kind),
      SNOLHallSeed RealStep Legal edgeSig kind ∧ ¬ InfiniteLegalDescent RealStep := by
  -- model: τ = Bool ⊕ Unit? Simpler: τ := Fin 3 (0=U₁,1=U₂,2=V), edges 0→2, 1→2, height 2↦0 otherwise 1.
  refine ⟨Fin 3, fun a b => (a = 0 ∨ a = 1) ∧ b = 2, fun _ => True,
    fun _ _ => (), fun _ _ => Kind.snol, ?_, ?_⟩
  · -- SNOLHallSeed: U₁=0, U₂=1, V=2
    exact ⟨0, 1, 2, by decide, trivial, trivial, trivial,
      ⟨Or.inl rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩, rfl, rfl, rfl⟩
  · -- no infinite descent: height h(2)=0, h(_)=1 strictly drops on each edge;
    -- an infinite descent would give height (X 1) < height (X 0) etc., but the set of heights {0,1} is finite —
    -- more directly: every real-step leads into 2, and from 2 there is no real-step, so a chain of length 2 cannot exist.
    rintro ⟨X, hX⟩
    -- hX 0 : (X 1 = 0 ∨ X 1 = 1) ∧ X 0 = 2  ;  hX 1 : (X 2 = 0 ∨ X 2 = 1) ∧ X 1 = 2
    have h0 := (hX 0).1   -- X 1 = 0 ∨ X 1 = 1
    have h1 := (hX 1).2   -- X 1 = 2
    rcases h0 with h | h <;> rw [h] at h1 <;> exact absurd h1 (by decide)

/-- `SNOLHallSeedRegenerates` (§2, form A): every non-injective SNOL seed has a return-path from
    the common target `V` back to one of the predecessors. The minimal sufficient local law. -/
def SNOLHallSeedRegenerates {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) : Prop :=
  ∀ U₁ U₂ V, U₁ ≠ U₂ → Legal U₁ → Legal U₂ → Legal V →
    RealStep U₁ V → RealStep U₂ V → kind U₁ V = Kind.snol → kind U₂ V = Kind.snol →
    edgeSig U₁ V = edgeSig U₂ V →
    NonemptyPath RealStep V U₁ ∨ NonemptyPath RealStep V U₂

/-- An edge `U→V` plus a return-path `V →⁺ U` give a nonempty cycle `U →⁺ U`. -/
theorem cons_step_to_nonempty_cycle {RealStep : σ → σ → Prop} {U V : σ}
    (hStep : RealStep U V) (hBack : NonemptyPath RealStep V U) : NonemptyPath RealStep U U := by
  obtain ⟨n, hn, hpath⟩ := hBack
  exact ⟨n + 1, Nat.succ_pos n, ⟨V, hStep, hpath⟩⟩

/-- A path of length `n` under STRICTLY INCREASING height along the edge (`RealStep u v ⟹ height u < height v`):
    `height X + n ≤ height Y`. (The same orientation as `no_infiniteLegalDescent_of_height`.) -/
theorem pathN_height_le {RealStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v) :
    ∀ n X Y, PathN RealStep n X Y → height X + n ≤ height Y := by
  intro n
  induction n with
  | zero => intro X Y h; have hxy : X = Y := h; subst hxy; simp
  | succ k ih =>
    intro X Y h
    obtain ⟨Z, hXZ, hZY⟩ := h
    have h1 := hdrop hXZ         -- height X < height Z
    have h2 := ih Z Y hZY        -- height Z + k ≤ height Y
    omega

/--
  **`no_cycle_of_height` — PROVEN.** Under strictly increasing height along the edge (the same orientation that
  forbids infinite descent) a nonempty cycle `W →⁺ W` is impossible: a path of length `n ≥ 1` would give
  `height W + n ≤ height W`. One and the same `hdrop` kills BOTH descent AND cycle. -/
theorem no_cycle_of_height {RealStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v)
    (W : σ) (hcyc : NonemptyPath RealStep W W) : False := by
  obtain ⟨n, hn, hpath⟩ := hcyc
  have := pathN_height_le height hdrop n W W hpath
  omega

/-- The bridge «cycle ⟹ engine»: a nonempty legal cycle yields `EuclideanEngine`. In the EPMI instantiation
    (`EuclideanEngine := False`) this is exactly `no_cycle_of_height` — see `cycleBridge_of_height`. -/
def CycleBridge {RealStep : σ → σ → Prop} (Legal : σ → Prop) (EuclideanEngine : Prop) : Prop :=
  (∃ W, Legal W ∧ NonemptyPath RealStep W W) → EuclideanEngine

/-- **`cycleBridge_of_height` — PROVEN.** Under strictly decreasing height the bridge «cycle ⟹ engine»
    holds for `EuclideanEngine := False` (there simply is no cycle). This makes `CycleBridge` not
    a hypothesis but a consequence of the engine in the real instantiation. -/
theorem cycleBridge_of_height {RealStep : σ → σ → Prop} {Legal : σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v) :
    CycleBridge (RealStep := RealStep) Legal False := by
  rintro ⟨W, _, hcyc⟩
  exact no_cycle_of_height height hdrop W hcyc

/--
  **§5.1 (`snolHallSeed_to_engine_of_regeneration`) — PROVEN under the regeneration law.** If
  the minimal local law `SNOLHallSeedRegenerates` and the `CycleBridge` bridge hold, then any
  `SNOLHallSeed` yields an engine. Mechanism: the seed gives two edges `Uᵢ → V`; regeneration gives a return
  `V →⁺ Uᵢ`; together — a nonempty cycle `Uᵢ →⁺ Uᵢ` (`cons_step_to_nonempty_cycle`); the bridge gives an engine. -/
theorem snolHallSeed_to_engine_of_regeneration {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop}
    (hBridge : CycleBridge (RealStep := RealStep) Legal EuclideanEngine)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind)
    (hSeed : SNOLHallSeed RealStep Legal edgeSig kind) :
    EuclideanEngine := by
  obtain ⟨U₁, U₂, V, hne, hL1, hL2, hLV, hs1, hs2, hk1, hk2, hsig⟩ := hSeed
  rcases hRegen U₁ U₂ V hne hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig with hVU1 | hVU2
  · exact hBridge ⟨U₁, hL1, cons_step_to_nonempty_cycle hs1 hVU1⟩
  · exact hBridge ⟨U₂, hL2, cons_step_to_nonempty_cycle hs2 hVU2⟩

/--
  **§6.1 (`snol_kindDeterminism_of_regeneration`) — PROVEN.** From `SNOLHallSeedRegenerates` + the bridge
  follows the full SNOL determinism (`SNOLBoundaryLabelDeterminism`): for a pair of SNOL edges with an equal label
  either the predecessors are equal, or (distinct ⟹ `SNOLHallSeed`) an engine via §5.1. -/
theorem snol_kindDeterminism_of_regeneration {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop}
    (hBridge : CycleBridge (RealStep := RealStep) Legal EuclideanEngine)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind) :
    SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind EuclideanEngine := by
  intro U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig
  by_cases hEq : U₁ = U₂
  · exact Or.inl hEq
  · exact Or.inr (snolHallSeed_to_engine_of_regeneration hBridge hRegen
      ⟨U₁, U₂, V, hEq, hL1, hL2, hLV, hs1, hs2, hk1, hk2, hsig⟩)

/--
  **§26bis (`regen_under_hdrop_kills_seed`) — PROVEN (an important honesty caveat).** Under the same `hdrop`
  (co-height increases along the edge) that closes everything else, `SNOLHallSeedRegenerates` and
  a FIRED `SNOLHallSeed` are MUTUALLY EXCLUSIVE: the seed edge `Uᵢ→V` gives `height Uᵢ < height V`, while
  the regeneration return `V →⁺ Uᵢ` gives `height V < height Uᵢ` — a contradiction (the cycle is forbidden).

  CONSEQUENCE (honest): in the final assembly `hdrop` and `hRegen` are compatible only when there are NO seeds. That
  is, under `hdrop` the law `SNOLHallSeedRegenerates` holds only VACUOUSLY (seed-emptiness), NOT as a
  nontrivial «fan-in ⟹ engine». The real arithmetic content then migrates into `hdrop` ITSELF
  — the existence of a strictly-monotone co-height on the `RealStep` of the `6m±1` graph (= acyclicity/EPMI/
  well-foundedness), which is NOT presented here. Hence «the node is reduced to ONE lemma» is a simplification:
  the load is split between `hRegen` (seed⇒return-path, strictly EASIER than the old seed⇒engine wall) and `hdrop`. -/
theorem regen_under_hdrop_kills_seed {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    (height : σ → ℕ) (hdrop : ∀ {u v}, RealStep u v → height u < height v)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind)
    (hSeed : SNOLHallSeed RealStep Legal edgeSig kind) : False := by
  obtain ⟨U₁, U₂, V, hne, hL1, hL2, hLV, hs1, hs2, hk1, hk2, hsig⟩ := hSeed
  rcases hRegen U₁ U₂ V hne hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig with hback | hback
  · exact no_cycle_of_height height hdrop U₁ (cons_step_to_nonempty_cycle hs1 hback)
  · exact no_cycle_of_height height hdrop U₂ (cons_step_to_nonempty_cycle hs2 hback)

/-! ### The EPMI bridge: `¬InfiniteLegalDescent` from height (PROVEN)

We show that the `hNoInf` branch is not a hypothesis but a consequence of the engine: if every real-step strictly
decreases the natural height, there is no infinite descent (`no_infinite_descent`). -/

/--
  **`no_infiniteLegalDescent_of_height` — PROVEN.** If `RealStep u v ⟹ height u < height v`
  (a downward step decreases the height), then `InfiniteLegalDescent` is impossible. Here `X (n+1) → X n` gives
  `height (X (n+1)) < height (X n)` — a strictly decreasing chain in ℕ, forbidden by well-foundedness.

  (A remark on direction: in `InfiniteLegalDescent` the edge goes `X (n+1) → X n`, i.e. `X (n+1)` is the
  predecessor, so its height is SMALLER; `height ∘ X` decreases.) -/
theorem no_infiniteLegalDescent_of_height {RealStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v) :
    ¬ InfiniteLegalDescent RealStep := by
  rintro ⟨X, hX⟩
  -- height (X (n+1)) < height (X n): a strictly decreasing ℕ-chain ⟹ contradiction via
  -- the impossibility of infinite descent (the same engine `no_infinite_descent`, A=1).
  refine EuclidsPath.Engine.no_infinite_descent (A := 1) (le_refl 1)
    (fun k => height (X k)) (fun n => ?_)
  -- DescentStep 1 (height (X n)) (height (X (n+1))) := 1 * height (X (n+1)) < height (X n)
  show 1 * height (X (n + 1)) < height (X n)
  have := hdrop (hX n)   -- height (X (n+1)) < height (X n)
  omega

/-! ### §17. Bridge to the live Step00 path (an honest link, NOT a closure)

The abstract machine above is by itself an island: `EuclideanEngine` is a free `Prop`, `σ` is abstract.
To make the link with the real node a type rather than a declaration, we instantiate `EuclideanEngine := False`
(EPMI: the engine is IMPOSSIBLE, `no_perpetual_engine`). Then `globalAbsorption_to_engine` gives `False`
from its inputs — that is, it REFUTES `GlobalOldAbsorption`. This is exactly the form
`BoundaryDecomp.no_global_absorption_under_epmi`: «global absorption + forbidding the engine ⟹ ⊥».

The honest status of the bridge: it LOGICALLY connects the abstract machine with the form of the Step00 node, but does NOT close
it — the input `hComp` (the SNOL wall) remains, and the binding of `σ`/`RealStep`/`edgeSig` to the concrete graph
`6m±1` (`Residuals.TwinCenterZ`, `ProductCore.CoreSig`) is NOT presented here. The bridge shows
the COMPATIBILITY of the form, not the derivability of twin. -/

/--
  **`globalAbsorption_refutes_under_epmi` — PROVEN (König closed; `hComp` remains).**
  Under `EuclideanEngine := False` (EPMI) the abstract chain refutes `GlobalOldAbsorption`. This is
  the same contraposition as `no_global_absorption_under_epmi`, but expressed through the labelled-fan-in
  machine in which the König branch is already proven. It rests on a single substantive input `hComp` (SNOL). -/
theorem globalAbsorption_refutes_under_epmi {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hNoInf : ¬ InfiniteLegalDescent RealStep)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind (EuclideanEngine := False)) :
    False :=
  globalAbsorption_to_engine hGlobal hOldFin hAll hNoInf hKindEq hComp

/-! ### §27. Final assembly: everything reduced to ONE law `SNOLHallSeedRegenerates`

We assemble the whole chain under EPMI (`EuclideanEngine := False`, height strictly drops on real-step). Then:
König is closed (§7), the EPMI bridge gives `hNoInf` and `CycleBridge`, four exact components are the arithmetic
of the instantiation, and the fifth (SNOL) is closed by `SNOLHallSeedRegenerates` (§26). Result: under strictly dropping
height the only substantive input is `SNOLHallSeedRegenerates`; it REFUTES `GlobalOldAbsorption`.

This is the final localization — but NOT «to one lemma»: see the honest caveat in the theorem docstring. -/

/--
  **§8–9 (`globalAbsorption_refutes_of_snolRegeneration`) — PROVEN (final assembly under EPMI).**
  Under strictly increasing co-height along the edge `GlobalOldAbsorption` is impossible, IF a set of inputs is given:
    • `SNOLHallSeedRegenerates` — the SNOL law (seed ⟹ return-path);
    • four components `hActive/hOldPeel/hBoundary/hCorridor` — under `Engine := False` these are GENUINE
      commitments of label injectivity on each edge sort, NOT free;
    • `hOldFin`, `[Finite Lbl]`, `hAll`, `hKindEq`, `hdrop` itself — assumptions of the graph instantiation.
  The height gives `hNoInf` (no descent) AND `CycleBridge` (no cycle) — both from a single `hdrop`.

  HONEST CAVEAT (confirmed by the v4 adversarial audit, `regen_under_hdrop_kills_seed`). One cannot
  say «the node is reduced to ONE lemma `SNOLHallSeedRegenerates`». Under the same `hdrop` that
  closes everything else, the seed and its regeneration are MUTUALLY EXCLUSIVE (edge + return = cycle, forbidden).
  So `hRegen` under `hdrop` holds only VACUOUSLY (when there are no seeds), while the real arithmetic
  content MIGRATES into `hdrop` itself — the existence of a strictly-monotone co-height on `6m±1` RealStep
  (= acyclicity/EPMI/well-foundedness), which is NOT presented here. Plus `hAll` is FALSE on the real
  graph, and the machine is abstract and not connected to `TwinCenterZ`/`CoreSig`.

  CONCLUSION: this is a reduction MODULO several accepted arithmetic facts on an ABSTRACT graph
  (`hRegen` — strictly EASIER than the old seed⇒engine wall — PLUS `hdrop`/co-height PLUS four components
  PLUS the instantiation), not «to one lemma». There is real progress; there is no closure of Step00. -/
theorem globalAbsorption_refutes_of_snolRegeneration {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v)
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hActive : KindDeterminism RealStep Legal edgeSig kind False Kind.active)
    (hOldPeel : KindDeterminism RealStep Legal edgeSig kind False Kind.oldPeel)
    (hBoundary : KindDeterminism RealStep Legal edgeSig kind False Kind.boundary)
    (hCorridor : KindDeterminism RealStep Legal edgeSig kind False Kind.corridor)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind) :
    False := by
  -- one and the same hdrop (height increases along the edge) kills BOTH infinite descent AND cycle
  have hNoInf : ¬ InfiniteLegalDescent RealStep := no_infiniteLegalDescent_of_height height hdrop
  have hBridge : CycleBridge (RealStep := RealStep) Legal False := cycleBridge_of_height height hdrop
  -- the SNOL component from regeneration
  have hSnol : SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind False :=
    snol_kindDeterminism_of_regeneration hBridge hRegen
  have hComp : ComponentDeterminism RealStep Legal edgeSig kind False :=
    componentDeterminism_of_components hActive hOldPeel hBoundary hSnol hCorridor
  exact globalAbsorption_refutes_under_epmi hGlobal hOldFin hAll hNoInf hKindEq hComp

end EuclidsPath.LabelledFanIn
