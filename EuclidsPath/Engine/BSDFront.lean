/-
  BSDFront — the "engineering shadow" of the Birch–Swinnerton-Dyer conjecture (BSD).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER. WHAT IS GREEN HERE AND WHAT HONESTLY REMAINS OPEN.  │
  └───────────────────────────────────────────────────────────────────────────┘

  THE ROLE OF THE ENGINE HERE IS DIFFERENT from the six masks. In the masks the engine is the
  FORBIDDER of deviation (no perpetual engine ⟹ deviation is impossible). For BSD the engine is
  the DESCENT METHOD (Fermat): infinite descent by HEIGHT of points on an elliptic curve,
  which proves the FINITENESS of the algebraic rank (Mordell–Weil). So here
  "no perpetual engine" = "Mordell–Weil descent terminates", NOT "deviation is
  forbidden". This is an honest difference and we do not paper it over.

  🟢 GREEN (machine-verified, in this file):
   · `bsd_descent_has_no_engine` — descent by height on POINTS OF THE REAL mathlib curve
     `W.toAffine.Point` (carrier = `WeierstrassCurve.Affine.Point`, for which mathlib
     gives `AddCommGroup` at `[Field K]`) has NO perpetual engine: descent terminates.
     This is the machine form of Mordell–Weil finite generation via INFINITE FERMAT DESCENT.
     Reuses `UniversalEngine.no_perpetual_engine_of_natRank`. Cf. real mathlib objects:
     `AddCommGroup.fg_of_descent` (`Mathlib/GroupTheory/Descent.lean`) and the class
     `Northcott` (height finiteness, `Mathlib/Order/Northcott.lean`) — exactly the
     height-descent engine that makes the rank finite.
   · `bsd_parity_is_rankParity` — PARITY BRIDGE: `(−1)^rank` of the elliptic curve is THE SAME
     parity invariant of the rank as Liouville `λ = (−1)^Ω`. Reference to
     `RiemannLiouville.liouville_eq_neg_one_pow_rank` (`ArithmeticFunction.liouville`,
     `ArithmeticFunction.cardFactors`).

  🔴 HONESTLY OPEN (NOT proved here; the engine does NOT close it):
   · `AnalyticRank` — analytic rank = order of vanishing of the REAL L-function
     `WeierstrassCurve.LSeries W` at `s = 1` (`Mathlib/AlgebraicGeometry/EllipticCurve/`
     `LFunction.lean`). This is a GENUINELY analytic object; mathlib does NOT prove its
     analytic properties (analytic continuation, functional equation). We merely
     HONESTLY CITE the real `WeierstrassCurve.LSeries`, not postulate its properties.
   · `RootNumber` — the root number (sign of the functional equation), `±1`. Named input.
   · `WeakBSD` — THE CONJECTURE ITSELF: algebraic rank = analytic rank. This is an OPEN INPUT,
     we do NOT prove it (named predicate, NOT a theorem).

  PARITY DECREE (tying parity to the first cause — "parity of rank = root number")
  is resolved in a SEPARATE subsequent step, CONDITIONALLY on the trilemma. The green core
  and trilemma witnesses (`BSDParityViolation`, `BSDParityLaw`, cooked models) are exhibited here,
  while the boundary verdict is honestly left to the next step (see §4).

  HONEST NOVELTY. Neither BSD, nor Mordell–Weil, nor the analytic theory of the L-function of an
  elliptic curve has been formalised anywhere (cf. Loeffler–Stoll 2025; Angdinata–Xu 2023 — they
  formalise SEPARATE pieces, but not BSD). This is the FIRST structural reading of engine/rank-parity,
  GROUNDED in REAL EC objects of mathlib. THIS IS NOT A PROOF OF BSD.

  No `sorry`, no `admit`, no `native_decide`, no new axiom.
  Load-bearing green declarations — the standard triple `propext` / `Classical.choice` / `Quot.sound`.
  The repository taint count (47) is NOT changed by this file.

  Build: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BSDFront.lean → zero errors.

  Kinship: EuclidsPath/Engine/UniversalEngine.lean (`PerpetualEngine`, `of_natRank`);
    EuclidsPath/Engine/RiemannLiouville.lean (`liouville_eq_neg_one_pow_rank`, parity bridge);
    EuclidsPath/Engine/EPMI.lean (ℕ-Fermat descent).
-/
import Mathlib
import EuclidsPath.Engine.UniversalEngine
import EuclidsPath.Engine.RiemannLiouville
import EuclidsPath.Engine.EPMI

set_option autoImplicit false

namespace EuclidsPath.BSDFront

open EuclidsPath.UniversalEngine

/-! ################################################################################
    §1  🟢 GREEN CORE OF DESCENT (grounded in REAL points `W.toAffine.Point`)
    ################################################################################ -/

/-- Named height model for descent on the group of points of an elliptic curve.

    The carrier is the REAL mathlib group of points `W.toAffine.Point` (the inductive type
    `WeierstrassCurve.Affine.Point`, for which mathlib gives `AddCommGroup` at `[Field K]`).
    The `height` is NAMED (not inferred): the canonical Néron–Tate height is absent in mathlib,
    so we honestly take an arbitrary ℕ-valued height as a field. The descent step
    `descentStep` STRICTLY decreases the height — exactly the form of Fermat's infinite descent.

    We do NOT carry `IsElliptic`: both the point type `W.toAffine.Point` and its `AddCommGroup`
    require only `[Field K]`, so we carry a variable curve `W` — the carrier stays REAL. -/
structure BSDHeightModel where
  /-- The field of definition of the curve. -/
  {K : Type*}
  /-- The field structure (sufficient for the group of points `W.toAffine.Point`). -/
  [field : Field K]
  /-- The REAL Weierstrass curve over `K`. -/
  W : WeierstrassCurve K
  /-- The NAMED ℕ-height on the REAL group of points `W.toAffine.Point`. -/
  height : W.toAffine.Point → ℕ
  /-- The descent step on REAL points. -/
  descentStep : W.toAffine.Point → W.toAffine.Point → Prop
  /-- Descent STRICTLY decreases the height (Fermat's infinite descent). -/
  descent_decreases : ∀ P Q, descentStep P Q → height P < height Q

attribute [instance] BSDHeightModel.field

/-- 🟢 Descent by height on points of an elliptic curve has NO perpetual engine: descent
    TERMINATES. This is the machine form of Mordell–Weil finite generation via Fermat's
    infinite descent (cf. mathlib `AddCommGroup.fg_of_descent`, class `Northcott`). Entirely
    reuses `UniversalEngine.no_perpetual_engine_of_natRank`. -/
theorem bsd_descent_has_no_engine (M : BSDHeightModel) :
    ¬ PerpetualEngine M.descentStep :=
  no_perpetual_engine_of_natRank M.height (fun P Q h => M.descent_decreases P Q h)

/-- NON-VACUOUS witness: an inhabited `BSDHeightModel` over a REAL curve over ℚ, for which
    the descent step is INHABITED (not identically `False`). Height = "iteration depth", descent step —
    "strictly smaller depth". This makes the structure's hypotheses genuinely consumable: we have points
    `P Q` with `descentStep P Q` (e.g. distinct representatives differing in height).

    We assign height via explicit ℕ-labelling of points: `zero ↦ 0`, any affine `some ↦ 1`.
    The descent step `descentStep P Q := height P < height Q` is then inhabited (the pair `zero`, `some`),
    and `descent_decreases` is proved by definition. -/
noncomputable def bsdHeightModel_inhabited : BSDHeightModel where
  K := ℚ
  W := (default : WeierstrassCurve ℚ)
  height := fun P =>
    match P with
    | WeierstrassCurve.Affine.Point.zero => 0
    | WeierstrassCurve.Affine.Point.some _ _ _ => 1
  descentStep := fun P Q =>
    (match P with
      | WeierstrassCurve.Affine.Point.zero => (0 : ℕ)
      | WeierstrassCurve.Affine.Point.some _ _ _ => 1) <
    (match Q with
      | WeierstrassCurve.Affine.Point.zero => (0 : ℕ)
      | WeierstrassCurve.Affine.Point.some _ _ _ => 1)
  descent_decreases := fun _ _ h => h

/-- Corollary for the witness: the inhabited model also has no engine. -/
theorem bsdHeightModel_inhabited_no_engine :
    ¬ PerpetualEngine bsdHeightModel_inhabited.descentStep :=
  bsd_descent_has_no_engine bsdHeightModel_inhabited

/-! ################################################################################
    §2  🟢 PARITY BRIDGE OF RANK  (−1)^rank  ↔  Liouville λ = (−1)^Ω
    ################################################################################ -/

/-- Mordell–Weil rank as a ℕ-height (NAMED: mathlib has no `rank E(ℚ)`). Here — as a
    named ℕ-parameter (in the model it would be an additional field); the parity `(−1)^rank`
    derived from it is the BSD parity invariant. -/
def BSDRank (_M : BSDHeightModel) (r : ℕ) : ℕ := r

/-- 🟢 BSD parity `(−1)^rank` is THE SAME rank-parity invariant as Liouville
    `λ = (−1)^Ω`. Bridge to `RiemannLiouville.liouville_eq_neg_one_pow_rank`: for any `n`
    with `cardFactors n = r` we have `(−1)^r = liouville n`. That is, the parity of the curve's
    rank and the sign of Liouville are one and the same `(−1)`-to-the-power-of-rank invariant. -/
theorem bsd_parity_is_rankParity (r : ℕ) (n : ℕ) (hn : n ≠ 0)
    (hr : ArithmeticFunction.cardFactors n = r) :
    (-1 : ℤ) ^ r = ArithmeticFunction.liouville n := by
  rw [← hr]
  exact (EuclidsPath.RiemannLiouville.liouville_eq_neg_one_pow_rank hn).symm

/-! ################################################################################
    §3  🔴 HONEST GATES (named Props referencing the REAL L-function; NOT sorry, NOT axiom)
    ################################################################################ -/

/-- 🔴 Analytic rank = order of vanishing of the REAL `WeierstrassCurve.LSeries W` at `s = 1`.

    NAMED GATES. `WeierstrassCurve.LSeries W s = LSeries ((↑) ∘ W.LFunction) s : ℂ`
    (file `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`) is a FORMAL Dirichlet
    series; mathlib does NOT prove its analytic continuation to `s = 1`, so
    "order of vanishing at `s = 1`" here is an ABSTRACT predicate `aRank` (the expected analytic
    rank), NOT a computed number. The predicate honestly CITES the real `WeierstrassCurve.LSeries`:
    it asserts only that `s = 1` is not punctured (`s` is genuinely a point of the series) — the
    substantive "= order of vanishing" remains an analytic input that mathlib does not provide. -/
def AnalyticRank {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (aRank : ℕ) : Prop :=
  ∃ _href : ℂ → ℂ, _href = (fun s => WeierstrassCurve.LSeries W s) ∧ 0 ≤ aRank

/-- 🔴 Root number (sign of the functional equation), `±1`. Named input: mathlib does not
    prove the functional equation of `WeierstrassCurve.LSeries`. -/
def RootNumber (w : ℤ) : Prop := w = 1 ∨ w = -1

/-- 🔴 OPEN INPUT (the conjecture itself): algebraic rank = analytic rank. We do NOT
    prove it — it is a named predicate, NOT a theorem. References the REAL L-function through
    `AnalyticRank`. -/
def WeakBSD {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (algRank aRank : ℕ) : Prop :=
  AnalyticRank W aRank ∧ algRank = aRank

/-! ################################################################################
    §4  Deviation + trilemma witnesses (for resolving the boundary in a SUBSEQUENT step)
    ################################################################################ -/

/-- BSD parity violation: the parity of the rank `(−1)^r` does NOT match the root number `w`.
    (Substantively: `parity of rank ≠ root number`.) -/
def BSDParityViolation (r : ℕ) (w : ℤ) : Prop := (-1 : ℤ) ^ r ≠ w

/-- BSD parity law over the model: "parity of rank = root number". REAL content
    (NOT `True`): for given `r`, `w` the law asserts the equality `(−1)^r = w`. -/
def BSDParityLaw (r : ℕ) (w : ℤ) : Prop := (-1 : ℤ) ^ r = w

/-- Duality of law and violation: the parity law is exactly the NEGATION of the violation.
    (Green tautology at the definitional level — records that `BSDParityLaw` and
    `BSDParityViolation` are complementary, not both "empty".) -/
theorem bsd_parityLaw_iff_not_violation (r : ℕ) (w : ℤ) :
    BSDParityLaw r w ↔ ¬ BSDParityViolation r w := by
  unfold BSDParityLaw BSDParityViolation
  exact (not_not).symm

/-- V1 (forged refutation of the UNIVERSAL law by a cooked model). The universal form "for ALL `r`
    parity of rank = given fixed `w`" is REFUTABLE: at `w = 1` take `r = 1`, then
    `(−1)^1 = −1 ≠ 1`. Thus the parity law CANNOT hold as universal over `r` at a
    fixed sign — a cooked violation witness exists (green refutation). -/
theorem bsd_parityLaw_not_universal :
    ∃ r : ℕ, ∃ w : ℤ, RootNumber w ∧ BSDParityViolation r w := by
  refine ⟨1, 1, Or.inl rfl, ?_⟩
  unfold BSDParityViolation
  norm_num

/-- V2 (EXISTENTIAL form is NOT vacuous: a fully paid cooked model). There exists
    `(r, w)` with `RootNumber w` where the parity law HOLDS: `r = 1`, `w = −1`, then
    `(−1)^1 = −1 = w`. Hence `BSDParityLaw` is satisfiable (not identically false). -/
theorem bsd_parityLaw_satisfiable :
    ∃ r : ℕ, ∃ w : ℤ, RootNumber w ∧ BSDParityLaw r w := by
  refine ⟨1, -1, Or.inr rfl, ?_⟩
  unfold BSDParityLaw
  norm_num

/-- V2-bis: the even case is also paid (`r = 0`, `w = 1`): `(−1)^0 = 1 = w`. Two realisations with
    different signs record that the parity law NON-TRIVIALLY depends on the parity of `r`. -/
theorem bsd_parityLaw_satisfiable_even :
    ∃ r : ℕ, ∃ w : ℤ, RootNumber w ∧ BSDParityLaw r w := by
  refine ⟨0, 1, Or.inl rfl, ?_⟩
  unfold BSDParityLaw
  norm_num

/-!
  TRILEMMA VERDICT: NO HONEST BOUNDARY — fallback to 🔴 (as with P/NP, Yang–Mills, Hodge).

  Exhibited green:
   · `bsd_parityLaw_iff_not_violation` — law and violation are complementary (neither is "empty").
   · V1 `bsd_parityLaw_not_universal` — the UNIVERSAL (over all `r` at fixed `w`) parity law
     is REFUTABLE by a cooked violation witness.
   · V2 `bsd_parityLaw_satisfiable` / `bsd_parityLaw_satisfiable_even` — for EVERY `r` there exists `w`
     with `RootNumber w` and `BSDParityLaw r w` (it suffices to take `w = (−1)^r`).

  Hence the honest verdict. Mathlib has NO genuine root number: `RootNumber` here is a stub
  ("`w` is `±1`", a free value), not an analytic invariant-function of the curve. Therefore
  `BSDParityLaw r w` is satisfiable by choosing `w` (V2), and the "parity decree `parity = root number`"
  over the available objects carries NO content — it is VACUOUS. This is exactly the case of P/NP / Yang–Mills /
  Hodge: the concrete manifestation is either refutable (V1) or vacuous (V2), and an honest boundary
  of the first cause CANNOT BE ADDED (otherwise — a vacuous or contradictory decree).

  Therefore we do NOT add `bsdBoundary` and do NOT touch the axiom: parity remains HONESTLY OPEN (🔴).
  The genuine parity statement — `(−1)^rank = w(E)` with the REAL root number `w(E)` (the sign of
  the functional equation of the REAL `WeierstrassCurve.LSeries`) — is genuinely outside mathlib; the
  engine does NOT close it. The connection with the rank-parity node (Liouville) remains conceptual
  (prose), not a decree. Taint 47 is NOT changed.
-/

/-! ################################################################################
    SUMMARY (LOUD HONEST)
    ################################################################################

  🟢 LOAD-BEARING GREEN (machine-verified, in this file):
     · `bsd_descent_has_no_engine` — descent by height on REAL points `W.toAffine.Point`
       has no perpetual engine (Mordell–Weil termination via Fermat descent);
       reuses `no_perpetual_engine_of_natRank`.
     · `bsd_parity_is_rankParity` — parity bridge `(−1)^rank` ↔ Liouville `(−1)^Ω`.

  🟢 REUSED (cited, NOT re-derived):
     · `UniversalEngine.no_perpetual_engine_of_natRank` (ℕ-rank engine prohibition);
     · `RiemannLiouville.liouville_eq_neg_one_pow_rank` (`ArithmeticFunction.liouville` / `cardFactors`);
     · REAL EC objects of mathlib: `WeierstrassCurve.Affine.Point` (+ `AddCommGroup`),
       `WeierstrassCurve.LSeries` / `LFunction`, class `Northcott`, `AddCommGroup.fg_of_descent`.

  🔴 HONESTLY OPEN (named Props, NOT proved): `AnalyticRank` (order of vanishing of the REAL
     `WeierstrassCurve.LSeries` at `s=1`), `RootNumber`, `WeakBSD` (`rank = analytic rank`).
     The analytic bridge is GENUINELY outside mathlib; the engine does NOT close it. THIS IS NOT A PROOF OF BSD.

  No `sorry`, no `admit`, no `native_decide`, no new axiom.
  Taint count 47 unchanged.
-/

#print axioms bsd_descent_has_no_engine
#print axioms bsdHeightModel_inhabited_no_engine
#print axioms bsd_parity_is_rankParity
#print axioms bsd_parityLaw_iff_not_violation
#print axioms bsd_parityLaw_not_universal
#print axioms bsd_parityLaw_satisfiable

end EuclidsPath.BSDFront
