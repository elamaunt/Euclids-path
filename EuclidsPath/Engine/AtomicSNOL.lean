/-
  Atomic SNOL-free graph + SNOL demacrofication — Step00 post-audit re-architecture.
  Source: step00_post_audit_to_snol_deriv_final_residuals_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section "SNOL Atomisation").

  WHY. Audits v3/v4 showed that the abstract labelled machine (`LabelledFanIn.lean`) relies on
  `hAll : ∀x, Legal x` (false on `6m±1`), and SNOL as a macro-edge creates a heavy seed⇒engine wall. This
  module is a STRUCTURAL refactoring by brick (two honest wins, but NOT arithmetic progress):
    (1) the FALSE hypothesis `hAll` is eliminated: `dichotomy_legal` takes `Legal := fun _ => True`, and `hAll`
        discharges with the TRUE term `fun _ => trivial` (unlike the former false `∀x, Legal x`);
    (2) SNOL ceases to be an atomic edge: it becomes `SNOLDeriv` (inductive closure of atomic steps +
        composition + terminal engine/twin), and `SNOLDeriv_expand_or_closes` unfolds it into an atomic
        path OR closes.

  HONEST STATUS (refined by adversarial audit; NOT overstating):
  PROVED here (abstractly, standard axioms, no sorry):
    * `dichotomy_legal` — König dichotomy with `Legal := True` (false `hAll` soundly discharged);
    * `SNOLDeriv_expand_or_closes` (R7) — TRUE, but STRUCTURALLY TAUTOLOGICAL: the disjuncts
      (`AtomicPath ∨ Engine ∨ Twin`) are in exact bijection with the constructors of the free inductive; ZERO
      arithmetic content (composition was already free via `ReflTransGen.trans`);
    * `AtomicPath.append`, `atomicLabelledFanIn_closes`, `no_atomicInfiniteLegalDescent_of_height`,
      `macroPath_expand_or_closes` — structure/EPMI/finite graph theory.

  WHAT THIS REFACTORING DOES NOT DO (important):
    * `hAll` is eliminated as a FALSE hypothesis, but NOT as an OBLIGATION: with `Legal := True` the theorems speak about
      the FULL type `σ` without a legality filter, so any instantiation on a legal-subtype is obliged
      additionally (a) to build `AtomicStep` legality-closed and (b) to provide a legal `hGlobal`. The legal
      subtype is NOWHERE built here — the obligation is TRANSFERRED to the abstract `AtomicStep`/`hGlobal`.
    * R8 (`SNOLBoundaryToDeriv`) is NOT a hypothesis of the final theorem `twin_of_atomicDeterminism_and_absorption`.
      It is an input of a SEPARATE, NOT connected branch (`SNOLDeriv`/`macroPath`). One cannot say "everything is reduced
      to a single R8".
    * `SNOLDeriv_expand_or_closes` — bookkeeping, NOT progress: all SNOL/old-peel arithmetic remains
      entirely in R8, and R8 is definitionally interchangeable with the old input `hSNOLexpand`.

  REAL REMAINDER OF THE ASSEMBLED CHAIN (`twin_of_atomicDeterminism_and_absorption`):
    `{ hDet (AtomicLocalDeterminism — carries boundary/old-peel/SNOL-determinism, syntactically without
       the snol-case, but in substance the same wall, only the label is removed), hdrop (acyclicity/well-foundedness
       of co-height on `6m±1`), instantiation to `TwinCenterZ`/`CoreSig`/`Step00.EuclideanEngine` }`,
    plus R8 as a SEPARATE input of the unassembled SNOL-branch.

  CONCLUSION (audit): progress is LATERAL — two structural wins (false `hAll` discharged; SNOL-composition
  proved rather than assumed), but the substantive arithmetic is merely TRANSFERRED to cleaner places, not
  discharged. The red line is intact (no counting/probabilities). The machine is abstract and consumed by nothing.
  This is NOT a step toward proving twins. `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.LabelledFanIn

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.AtomicSNOL

open EuclidsPath.LabelledFanIn

variable {σ : Type*}

/-! ### §9–10. Atomic SNOL-free graph and path

`AtomicStep` — an atomic step (activeDelete/oldPeel/oldCorridor/boundaryExact/boundaryPeel + terminal
seeds). SNOL and absorber do NOT enter here as constructors. `AtomicPath` — a finite path over atomic steps. -/

/-- Atomic path `U ⇝ V` — the reflexive-transitive closure of the atomic step. -/
abbrev AtomicPath (AtomicStep : σ → σ → Prop) : σ → σ → Prop := Relation.ReflTransGen AtomicStep

/-- **`AtomicPath.append` — PROVED** (= transitivity of `ReflTransGen`). -/
theorem AtomicPath.append {AtomicStep : σ → σ → Prop} {U W V : σ}
    (h1 : AtomicPath AtomicStep U W) (h2 : AtomicPath AtomicStep W V) : AtomicPath AtomicStep U V :=
  h1.trans h2

/-! ### §16–17. SNOL as a finite derivation + unfolding (R7)

Instead of an opaque macro-edge SNOL — `SNOLDeriv`: the least closure of atomic steps under
composition with terminal engine/twin. Then "SNOL unfolds" is structural induction. -/

/-- `SNOLDeriv` (§16): finite derivation of a SNOL event from atomic steps, composition, and terminal
    engine/twin. Boundary exact/peel — atomic steps, NOT separate macro-constructors. -/
inductive SNOLDeriv (AtomicStep : σ → σ → Prop) (Engine : Prop) (Twin : Prop) : σ → σ → Prop
  | atomic {U V} : AtomicStep U V → SNOLDeriv AtomicStep Engine Twin U V
  | comp {U W V} : SNOLDeriv AtomicStep Engine Twin U W → SNOLDeriv AtomicStep Engine Twin W V →
      SNOLDeriv AtomicStep Engine Twin U V
  | engine {U V} : Engine → SNOLDeriv AtomicStep Engine Twin U V
  | twin {U V} : Twin → SNOLDeriv AtomicStep Engine Twin U V

/--
  **§17 (`SNOLDeriv_expand_or_closes`) — PROVED (R7, core of demacrofication).** Every SNOL derivation
  EITHER unfolds into a finite atomic path `U ⇝ V`, OR already closes Step00 (engine/twin).
  Induction on the derivation: atomic ⟹ path of length 1; comp ⟹ append of paths (or skip closure);
  engine/twin ⟹ the corresponding terminal. -/
theorem SNOLDeriv_expand_or_closes {AtomicStep : σ → σ → Prop} {Engine Twin : Prop} {U V : σ}
    (h : SNOLDeriv AtomicStep Engine Twin U V) :
    AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  induction h with
  | atomic hs => exact Or.inl (Relation.ReflTransGen.single hs)
  | comp _ _ ih1 ih2 =>
    rcases ih1 with p1 | e1 | t1
    · rcases ih2 with p2 | e2 | t2
      · exact Or.inl (p1.trans p2)
      · exact Or.inr (Or.inl e2)
      · exact Or.inr (Or.inr t2)
    · exact Or.inr (Or.inl e1)
    · exact Or.inr (Or.inr t1)
  | engine he => exact Or.inr (Or.inl he)
  | twin ht => exact Or.inr (Or.inr ht)

/-! ### §2–4. Legal subtype eliminates `hAll` (structurally)

Key to eliminating `hAll`: work on `σ` = legal subtype, where `Legal := fun _ => True` holds
by construction, so the universal-legality hypothesis discharges with `fun _ => trivial`. -/

/--
  **`dichotomy_legal` — PROVED (König dichotomy WITHOUT `hAll`).** On a legal graph (any `σ`,
  `Legal := True`) the König dichotomy from `LabelledFanIn.lean` holds without the universal-legality
  hypothesis: it discharges trivially. This structurally removes the audit objection about the false `hAll`
  on the real `6m±1` graph — legality is built into the state type. -/
theorem dichotomy_legal {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite) :
    LabelledFanIn RealStep (fun _ => True) edgeSig ∨ InfiniteLegalDescent RealStep :=
  absorption_labelled_dichotomy hGlobal hOldFin (fun _ => trivial)

/-! ### §12. Atomic fan-in closes Step00

`AtomicLocalDeterminism` (all atomic pairs with equal label ⟹ equality ∨ engine ∨ twin) + atomic
fan-in ⟹ engine ∨ twin. This is the atomic version of the consumer, now with two terminal outcomes. -/

/-- `AtomicLocalDeterminism`: for atomic pairs with equal label — equality ∨ engine ∨ twin. -/
def AtomicLocalDeterminism {Lbl : Type*} (AtomicStep : σ → σ → Prop) (edgeSig : σ → σ → Lbl)
    (Engine Twin : Prop) : Prop :=
  ∀ U₁ U₂ V, AtomicStep U₁ V → AtomicStep U₂ V → edgeSig U₁ V = edgeSig U₂ V →
    U₁ = U₂ ∨ Engine ∨ Twin

/-- `AtomicLabelledFanIn`: two distinct predecessors of a single `V` with equal atomic label. -/
def AtomicLabelledFanIn {Lbl : Type*} (AtomicStep : σ → σ → Prop) (edgeSig : σ → σ → Lbl) : Prop :=
  ∃ U₁ U₂ V, U₁ ≠ U₂ ∧ AtomicStep U₁ V ∧ AtomicStep U₂ V ∧ edgeSig U₁ V = edgeSig U₂ V

/--
  **§12 (`atomicLabelledFanIn_closes`) — PROVED.** Atomic fan-in + atomic local determinism ⟹
  engine ∨ twin. Equality of predecessors contradicts `U₁ ≠ U₂`, so engine/twin remains. -/
theorem atomicLabelledFanIn_closes {Lbl : Type*} {AtomicStep : σ → σ → Prop} {edgeSig : σ → σ → Lbl}
    {Engine Twin : Prop}
    (hDet : AtomicLocalDeterminism AtomicStep edgeSig Engine Twin)
    (hFan : AtomicLabelledFanIn AtomicStep edgeSig) : Engine ∨ Twin := by
  obtain ⟨U₁, U₂, V, hne, hs1, hs2, hsig⟩ := hFan
  rcases hDet U₁ U₂ V hs1 hs2 hsig with heq | hcl
  · exact absurd heq hne
  · exact hcl

/-! ### §14. No atomic infinite descent (EPMI bridge) -/

/-- Atomic infinite descent: `X (n+1) → X n` via atomic steps. -/
def AtomicInfiniteLegalDescent (AtomicStep : σ → σ → Prop) : Prop :=
  ∃ X : ℕ → σ, ∀ n, AtomicStep (X (n + 1)) (X n)

/--
  **§14 (`no_atomicInfiniteLegalDescent_of_height`) — PROVED.** When the height strictly decreases along every atomic
  step (EPMI) there is no atomic infinite descent — the same well-foundedness of ℕ as in `no_infinite_descent`. -/
theorem no_atomicInfiniteLegalDescent_of_height {AtomicStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, AtomicStep u v → height u < height v) :
    ¬ AtomicInfiniteLegalDescent AtomicStep := by
  rintro ⟨X, hX⟩
  refine EuclidsPath.Engine.no_infinite_descent (A := 1) (le_refl 1)
    (fun k => height (X k)) (fun n => ?_)
  show 1 * height (X (n + 1)) < height (X n)
  have := hdrop (hX n)
  omega

/-! ### §20–21. Unfolding of a macro-step and a macro-path

A macro-path (with SNOL macro-edges) unfolds into an atomic path OR closes, provided that
SNOL unfolds (`hSNOLexpand`). This is structural induction on the macro-path. -/

/--
  **§20 (`macroStep_expand_or_closes`) — PROVED given `hSNOLexpand`.** One macro-step (atomic OR
  SNOL-macro) unfolds into an atomic path or closes Step00. Atomic step ⟹ path of length 1;
  SNOL-macro ⟹ by `hSNOLexpand`. -/
theorem macroStep_expand_or_closes {AtomicStep : σ → σ → Prop} {SNOLMacro : σ → σ → Prop}
    {Engine Twin : Prop} {U V : σ}
    (hSNOLexpand : ∀ {a b}, SNOLMacro a b → AtomicPath AtomicStep a b ∨ Engine ∨ Twin)
    (hstep : AtomicStep U V ∨ SNOLMacro U V) :
    AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  rcases hstep with hat | hsn
  · exact Or.inl (Relation.ReflTransGen.single hat)
  · exact hSNOLexpand hsn

/--
  **§21 (`macroPath_expand_or_closes`) — PROVED given `hSNOLexpand`.** The entire macro-path (closure of
  "atomic ∨ SNOL-macro") unfolds into an atomic path or closes. Induction on `ReflTransGen` of the
  macro-step; append of atomic paths at each link, skip closure. -/
theorem macroPath_expand_or_closes {AtomicStep : σ → σ → Prop} {SNOLMacro : σ → σ → Prop}
    {Engine Twin : Prop} {U V : σ}
    (hSNOLexpand : ∀ {a b}, SNOLMacro a b → AtomicPath AtomicStep a b ∨ Engine ∨ Twin)
    (hpath : Relation.ReflTransGen (fun a b => AtomicStep a b ∨ SNOLMacro a b) U V) :
    AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  induction hpath with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail hstep hlast ih =>
    -- hstep : macro-path up to the penultimate node; hlast : last macro-step; ih : unfolding of the prefix
    rcases ih with pfx | e | t
    · rcases macroStep_expand_or_closes hSNOLexpand hlast with plast | e | t
      · exact Or.inl (pfx.trans plast)
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr t)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr t)

/-! ### §26. Input R8 (SNOL-branch) — SEPARATE, NOT connected to the final theorem

IMPORTANT: this SNOL-branch (`SNOLBoundaryToDeriv` → `snolMacro_expands_of_bridge` → `macroPath...`) is
SEPARATE. It is NOT a hypothesis of `twin_of_atomicDeterminism_and_absorption`: that theorem already operates on the
atomic graph. R8 is needed only if one builds the macro→atomic unfolding separately. By audit: `R8`
is definitionally interchangeable with the old input `hSNOLexpand`, and all SNOL/old-peel arithmetic lives in it.
Supplied as an explicit hypothesis. -/

/-- R8: old SNOL predicate ⟹ `SNOLDeriv` ∨ engine ∨ twin. Substantive input of the SNOL-BRANCH (in the real
    graph — SNOL/old-peel arithmetic); NOT dischargeable vacuously (`.engine` requires a real `Engine`,
    which is absent). Interchangeable with the old `hSNOLexpand`. -/
def SNOLBoundaryToDeriv (SNOLMacro AtomicStep : σ → σ → Prop) (Engine Twin : Prop) : Prop :=
  ∀ {U V}, SNOLMacro U V → SNOLDeriv AtomicStep Engine Twin U V ∨ Engine ∨ Twin

/--
  **`snolMacro_expands_of_bridge` — PROVED given R8.** From the red line R8 (`SNOLBoundaryToDeriv`)
  it follows that SNOL-macro unfolds into an atomic path or closes: apply the bridge, then
  `SNOLDeriv_expand_or_closes`. This makes `hSNOLexpand` (needed for §20–21) a consequence of R8. -/
theorem snolMacro_expands_of_bridge {AtomicStep SNOLMacro : σ → σ → Prop} {Engine Twin : Prop}
    (hBridge : SNOLBoundaryToDeriv SNOLMacro AtomicStep Engine Twin)
    {U V : σ} (h : SNOLMacro U V) : AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  rcases hBridge h with hderiv | e | t
  · exact SNOLDeriv_expand_or_closes hderiv
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr t)

/-! ### §23–24. Final assembly on the atomic graph (remainder = `hDet` + `hdrop` + instantiation)

We assemble the chain on the atomic graph. Under EPMI (atomic height grows along each edge ⟹ no atomic descent) and with
atomic local determinism, atomic fan-in closes (engine/twin). The dichotomy (`dichotomy_legal`) gives
fan-in or descent; descent is forbidden; fan-in closes.

HONESTLY (by audit): the real unreduced remainder of THIS chain is `hDet` (carries boundary/old-peel/SNOL-
determinism — syntactically without the snol-case, but in substance the same wall), `hdrop` (acyclicity/
well-foundedness of co-height on `6m±1`) and instantiation. The R8/SNOLDeriv branch does NOT enter here. -/

/--
  **§23 (`atomicGlobalAbsorption_closes`) — PROVED (atomic assembly under EPMI).** On the atomic graph:
  atomic global absorption + finiteness of absorbers + finite alphabet + atomic local determinism +
  strictly growing atomic height ⟹ engine ∨ twin. König dichotomy (without `hAll`) + EPMI + atomic consumer.

  This is the atomic version of the final theorem: the entire König/counting/EPMI part is closed; inputs — atomic local determinism
  (exact-components, instantiation arithmetic) and finiteness conditions. -/
theorem atomicGlobalAbsorption_closes {Lbl : Type*} [Finite Lbl]
    {AtomicStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {Engine Twin : Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, AtomicStep u v → height u < height v)
    (hGlobal : GlobalOldAbsorption AtomicStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hDet : AtomicLocalDeterminism AtomicStep edgeSig Engine Twin) :
    Engine ∨ Twin := by
  -- König dichotomy on the legal graph (without hAll)
  rcases dichotomy_legal (edgeSig := edgeSig) hGlobal hOldFin with hfan | hinf
  · -- LabelledFanIn (with Legal := True) ⟹ AtomicLabelledFanIn
    obtain ⟨U₁, U₂, V, hne, _, _, _, hs1, hs2, hsig⟩ := hfan
    exact atomicLabelledFanIn_closes hDet ⟨U₁, U₂, V, hne, hs1, hs2, hsig⟩
  · -- InfiniteLegalDescent is forbidden by EPMI
    exact absurd hinf (no_atomicInfiniteLegalDescent_of_height height hdrop)

/--
  **§24 (`twin_of_atomicDeterminism_and_absorption`) — PROVED (final form under given inputs).** Under
  `¬Twin` and `¬Engine` (EPMI), if atomic global absorption follows from `¬Twin` (`hNoNew_to_abs`),
  then `atomicGlobalAbsorption_closes` yields engine ∨ twin — a contradiction. Hence `Twin`.

  IMPORTANT (honesty, by audit): THIS theorem has NO bridge hypothesis R8 (`SNOLBoundaryToDeriv`) — therefore
  the former name `step00_final_of_bridge` was misleading and has been renamed. The real remainder of THIS
  chain is `hDet` (carries SNOL/boundary/old-peel-determinism, syntactically without the snol-case, but in
  substance the same wall), `hdrop` (acyclicity/well-foundedness of co-height on `6m±1`), and all instantiation
  (`Twin := ∃ m>M₀, TwinCenter m`, `Engine := Step00.EuclideanEngine`, binding of `σ`/`AtomicStep`/`edgeSig`
  to `TwinCenterZ`/`CoreSig`, `hNoNew_to_abs`, `hOldFin`, `[Finite Lbl]`). R8/`SNOLDeriv` — a SEPARATE,
  NOT connected to this theorem branch. This is a form of reduction, NOT closure. -/
theorem twin_of_atomicDeterminism_and_absorption {Lbl : Type*} [Finite Lbl]
    {AtomicStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {Engine Twin : Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, AtomicStep u v → height u < height v)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hDet : AtomicLocalDeterminism AtomicStep edgeSig Engine Twin)
    (hNoEngine : ¬ Engine)
    (hNoNew_to_abs : ¬ Twin → GlobalOldAbsorption AtomicStep OldAbsorber Fresh) :
    Twin := by
  by_contra hNoTwin
  have hGlobal := hNoNew_to_abs hNoTwin
  rcases atomicGlobalAbsorption_closes height hdrop hGlobal hOldFin hDet with he | ht
  · exact hNoEngine he
  · exact hNoTwin ht

end EuclidsPath.AtomicSNOL
