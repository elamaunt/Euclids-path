/-
  BSDEpistemic — epistemic section of BSD: HONEST RECORDING OF AXIS DEGENERATION.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  THE SCEPTIC'S MAIN CORR IS RECORDED AS A THEOREM: BSD HAS NO NEW EPISTEMIC AXIS. │
  └───────────────────────────────────────────────────────────────────────────┘

  WHAT THIS IS. For the seven fronts the epistemic layer was built as a pair
  `ground` / `beyondOwnHorizon` (CollatzFirstCause, PNPFirstCause, TwinNodeEpistemic,
  OddPerfectEpistemic): "to resolve from within" = to carry both facts at once, and the
  contradiction is paid by a genuine green wall. For BSD the same pair was proposed:
  `ground := PerpetualEngine M.descentStep` (internal self-justification of the rank
  by exhibiting an infinite descent), `beyondOwnHorizon := strict decrease of height`.
  THIS PAIR DEGENERATES, and the degeneration is recorded here MACHINE-WISE, not in a comment:
  the second leg is literally the field `M.descent_decreases` of the model `BSDHeightModel`,
  inhabited for ANY `M` always. This yields two disclosure theorems:

   · `bsdGround_coincides_with_engine` — `InternalisedBSDGround M ↔
     PerpetualEngine M.descentStep`: the structure is equivalent to ONE of its legs;
   · `bsdCause_unknowable_iff_no_engine` — "unknowability from within" extensionally
     COINCIDES with the already-existing `bsd_descent_has_no_engine` (BSDFront): the package is
     a definitional repacking of the old theorem, not a new axis.

  WHAT IT COSTS (honestly). The payment for the contradiction IS REAL: `bsdCause_unknowable`
  dies against `UniversalEngine.no_perpetual_engine_of_natRank` — the genuine wall of
  well-foundedness of ℕ (the same family as the pigeonhole `no_fullPayment_of_unboundedSupply`
  in P/NP), consuming the green field `descent_decreases` on the REAL carrier
  `W.toAffine.Point`. But — unlike the P/NP reference case, where BOTH legs are independent
  non-trivial predicates — the second leg here is FREE BY CONSTRUCTION. Therefore
  the honesty formula is: "the payment is real, but the second leg is free by construction",
  and the entire epistemic layer of BSD reduces to the prohibition of the descent engine. This is NOT a defect,
  but a result: the very attempt to build a separate BSD epistemic axis provably
  collapses into the termination of Mordell–Weil descent.

  TWO HONESTY LEMMAS OF THE REPORT (also machine-verified):
   · `analyticRank_gate_satisfiable` + `weakBSD_reduces_to_bare_equality` —
     🔴-gate `AnalyticRank` (BSDFront §3) is FREELY SATISFIABLE by the choice
     (`⟨W.LSeries, rfl, 0 ≤ aRank⟩`): this is a citation marker for the real
     `WeierstrassCurve.LSeries`, not a constraint; `WeakBSD` provably reduces
     to the bare equality `algRank = aRank`. Vacuity of the gate is visible to the machine,
     not only in the comment.
   · `parity_bridge_inhabited_per_rank` — the parity bridge `bsd_parity_is_rankParity`
     is inhabited for EVERY rank r (witness n = 2^r,
     `ArithmeticFunction.cardFactors_apply_prime_pow`), including the classically OPEN
     mode r ≥ 2. The rank-parity node (Liouville) is not vacuous for any r.

  HONESTY. This is NOT a proof and NOT a refutation of BSD (WeakBSD remains a 🔴 named
  predicate; the analytic bridge is genuinely outside mathlib) and NOT Gödel (no
  independence — only well-foundedness of ℕ and disclosure of definitional coincidences).
  Formal links are annotated in the docstrings, with what each is paid by.
  No `sorry`, no new axiom, no `native_decide`; the quarantine
  (CausalClosureAxiom) is NOT imported; the repository taint (47) does not change.
  Load-bearing: no more than the standard triple `propext`/`Classical.choice`/`Quot.sound`.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BSDEpistemic.lean → zero errors.

  Kinship: Engine/BSDFront.lean (model, wall, bridge, gate);
    Engine/UniversalEngine.lean (`PerpetualEngine`, `no_perpetual_engine_of_natRank`);
    epistemic mirrors: Engine/PNPFirstCause.lean, Engine/TwinNodeEpistemic.lean.
-/
import Mathlib
import EuclidsPath.Engine.BSDFront

set_option autoImplicit false

namespace EuclidsPath.BSDFront.Epistemic

open EuclidsPath.UniversalEngine

/-! ################################################################################
    §1  The proposed epistemic pair and its MACHINE DEGENERATION (a)
    ################################################################################ -/

/-- **The proposed "internal self-justification of rank" for BSD** (following the template of
    `InternalisedPNPGround` / `InternalisedTwinGround`): (a) `ground` — internal
    justification of the finiteness of the rank by exhibiting an infinite descent (engine
    on `M.descentStep`), (b) `beyondOwnHorizon` — strict decrease of height per step.

    HONESTY (main CORR, mandatory): the pair IS DEGENERATE. `beyondOwnHorizon` —
    is literally the field `M.descent_decreases`, inhabited for ANY model `M`, therefore
    the structure is equivalent to one of its legs (`bsdGround_coincides_with_engine` below),
    and its impossibility is a definitional repacking of `bsd_descent_has_no_engine`.
    We keep the structure PRECISELY to record this: in P/NP both legs are independent
    non-trivial predicates; in BSD the second leg is free by construction. -/
structure InternalisedBSDGround (M : BSDHeightModel) : Prop where
  /-- Internal justification: an infinite descent chain (perpetual engine). -/
  ground : PerpetualEngine M.descentStep
  /-- "View beyond the horizon": a descent step strictly decreases the height. DEGENERATION:
      this is the field `M.descent_decreases`, always available — the leg is free. -/
  beyondOwnHorizon : ∀ P Q, M.descentStep P Q → M.height P < M.height Q

/-- "Internal knowledge of the BSD cause" = internal self-justification of the rank
    (mirror of `InternalKnowledgeOfPNPCause` / `InternalKnowledgeOfTwinCause`). -/
abbrev InternalKnowledgeOfBSDCause (M : BSDHeightModel) : Prop :=
  InternalisedBSDGround M

/-- **DISCLOSURE THEOREM (main CORR recorded machine-wise):** the proposed epistemic
    structure of BSD IS EQUIVALENT to one of its legs — the engine on the descent relation.
    The backward arrow is paid for free: the second leg is the field `M.descent_decreases`.
    Hence BSD has NO NEW epistemic link: `InternalisedBSDGround` is
    `PerpetualEngine M.descentStep` under a different name. The degeneration is recorded
    machine-wise — that is the honesty of this module. -/
theorem bsdGround_coincides_with_engine (M : BSDHeightModel) :
    InternalisedBSDGround M ↔ PerpetualEngine M.descentStep :=
  ⟨fun H => H.ground, fun h => ⟨h, M.descent_decreases⟩⟩

/-- **"UNKNOWABLE FROM WITHIN" — but WITHOUT A NEW AXIS:** the BSD epistemic layer
    coincides with the prohibition of the descent engine — BSD has no new axis, and this is a theorem.
    Formally: a consequence of the disclosure `bsdGround_coincides_with_engine`; the contradiction
    is paid NOT by the form of the structure but by the wall of well-foundedness of ℕ
    (`no_perpetual_engine_of_natRank` via `bsd_descent_has_no_engine`), consuming
    the real field `descent_decreases` on the carrier `W.toAffine.Point`. HONESTY:
    this is a definitional repacking of `bsd_descent_has_no_engine`, not an analogue
    of the independent P/NP pair — the payment is real, but the second leg is free by construction. -/
theorem bsdCause_unknowable (M : BSDHeightModel) :
    ¬ InternalKnowledgeOfBSDCause M :=
  fun H => bsd_descent_has_no_engine M H.ground

/-- **Axis coincidence, extensionally:** "unknowability from within" ⟺ "no descent engine" —
    i.e., `bsdCause_unknowable` is the ALREADY EXISTING
    `bsd_descent_has_no_engine` (BSDFront) up to renaming.
    A trivial `not_congr` from the disclosure — a formal link paid by
    the degeneration of the second leg. -/
theorem bsdCause_unknowable_iff_no_engine (M : BSDHeightModel) :
    (¬ InternalKnowledgeOfBSDCause M) ↔ (¬ PerpetualEngine M.descentStep) :=
  not_congr (bsdGround_coincides_with_engine M)

/-- Concrete instance on the NON-vacuous witness `bsdHeightModel_inhabited`
    (a curve over ℚ, inhabited descent step): the statement is not about an empty model. -/
theorem bsdCause_unknowable_inhabited :
    ¬ InternalKnowledgeOfBSDCause bsdHeightModel_inhabited :=
  bsdCause_unknowable bsdHeightModel_inhabited

/-! ################################################################################
    §2  Honesty lemma: 🔴-gate `AnalyticRank` is freely satisfiable (b)
    ################################################################################ -/

/-- **Gate `AnalyticRank` IS FREELY SATISFIABLE (honesty lemma, green):** for
    any curve and ANY `aRank` the predicate `AnalyticRank W aRank` is provable by the choice
    `⟨W.LSeries, rfl, 0 ≤ aRank⟩`. Machine recording of the fact that the 🔴-gate BSDFront §3 is
    a CITATION MARKER for the real `WeierstrassCurve.LSeries`, not a constraint:
    the substantive "order of vanishing at s = 1" is not provided by mathlib, and the predicate
    does not carry it. The same honesty as in the trilemma verdict `bsd_parityLaw_satisfiable`:
    vacuity is visible to the machine, not only in the comment. -/
theorem analyticRank_gate_satisfiable {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) (aRank : ℕ) :
    AnalyticRank W aRank :=
  ⟨fun s => WeierstrassCurve.LSeries W s, rfl, Nat.zero_le _⟩

/-- **Consequence for the hypothesis itself:** `WeakBSD` provably REDUCES to the bare equality
    `algRank = aRank` — the analytic conjunct is absorbed by the free satisfiability of
    the gate. A formal link paid by `analyticRank_gate_satisfiable`; records that
    ALL the open content of BSD in the current formalisation lives in one named
    equality, which we honestly do NOT prove. -/
theorem weakBSD_reduces_to_bare_equality {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) (algRank aRank : ℕ) :
    WeakBSD W algRank aRank ↔ algRank = aRank :=
  ⟨fun h => h.2, fun h => ⟨analyticRank_gate_satisfiable W aRank, h⟩⟩

/-! ################################################################################
    §3  The parity bridge is inhabited for EVERY rank (c)
    ################################################################################ -/

/-- **The parity bridge is not vacuous at any rank (green):** for each `r`
    the rank-parity node exhibits the witness `n = 2^r` — `n ≠ 0`, `Ω(n) = r` and
    `(−1)^r = λ(n)`. Paid by the mathlib fact
    `ArithmeticFunction.cardFactors_apply_prime_pow` and the bridge
    `bsd_parity_is_rankParity` (BSDFront §2). Both the even and odd cases are covered
    at once — including the classically OPEN mode r ≥ 2: inhabitedness of the bridge does not depend
    on whether such a rank is realised on a curve (we claim nothing about that). -/
theorem parity_bridge_inhabited_per_rank (r : ℕ) :
    ∃ n : ℕ, n ≠ 0 ∧ ArithmeticFunction.cardFactors n = r ∧
      (-1 : ℤ) ^ r = ArithmeticFunction.liouville n :=
  have hn : (2 : ℕ) ^ r ≠ 0 := pow_ne_zero r two_ne_zero
  have hr : ArithmeticFunction.cardFactors (2 ^ r) = r :=
    ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two
  ⟨2 ^ r, hn, hr, bsd_parity_is_rankParity r (2 ^ r) hn hr⟩

/-! ################################################################################
    SUMMARY (LOUD HONEST)
    ################################################################################

  🟢 MACHINE-VERIFIED, IN THIS FILE:
     · `bsdGround_coincides_with_engine` — the proposed BSD epistemic pair is
       DEGENERATE: `InternalisedBSDGround M ↔ PerpetualEngine M.descentStep`;
     · `bsdCause_unknowable` (+ `_iff_no_engine`, `_inhabited`) — unknowability
       from within exists, but it COINCIDES with `bsd_descent_has_no_engine`: no new axis,
       and this is a theorem; the payment is real (`no_perpetual_engine_of_natRank`), but the second
       leg is free by construction;
     · `analyticRank_gate_satisfiable` / `weakBSD_reduces_to_bare_equality` —
       🔴-gate is freely satisfiable; `WeakBSD` ⟺ bare `algRank = aRank`;
     · `parity_bridge_inhabited_per_rank` — the parity bridge is inhabited for every r
       (witness 2^r).

  🟢 REUSED (cited, NOT re-derived): `BSDHeightModel`,
     `bsd_descent_has_no_engine`, `bsdHeightModel_inhabited`, `AnalyticRank`,
     `WeakBSD`, `bsd_parity_is_rankParity` (BSDFront); `PerpetualEngine`,
     `no_perpetual_engine_of_natRank` (UniversalEngine);
     `ArithmeticFunction.cardFactors_apply_prime_pow` (mathlib).

  🔴 HONESTLY OPEN (and NOT touched): `WeakBSD` as the equality `algRank = aRank`,
     the genuine analytic rank (continuation of the L-series), the genuine root number.
     THIS IS NOT A PROOF OF BSD AND NOT GÖDEL.

  No `sorry`, no new axiom, no `native_decide`; quarantine not
  imported; taint 47 does not change.
-/

#print axioms bsdGround_coincides_with_engine
#print axioms bsdCause_unknowable
#print axioms bsdCause_unknowable_iff_no_engine
#print axioms bsdCause_unknowable_inhabited
#print axioms analyticRank_gate_satisfiable
#print axioms weakBSD_reduces_to_bare_equality
#print axioms parity_bridge_inhabited_per_rank

end EuclidsPath.BSDFront.Epistemic
