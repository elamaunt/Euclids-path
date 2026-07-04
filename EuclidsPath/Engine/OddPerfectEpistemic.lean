/-
  OddPerfectEpistemic — EPISTEMIC COMPLEMENT of odd perfect numbers
  (mirror of CollatzFirstCause / PNPFirstCause). Green engine of the front:
  Engine/OddPerfectManifestationFront.lean; branch: Engine/PerfectNumberBranch.lean.

  WHAT THIS IS. To "solve from within" the question of an odd perfect number = to present
  a witness INSIDE one's own verified horizon (`ground`: ∃ W, W.1 < 101),
  while carrying the machine unfolding of that very horizon (`beyondOwnHorizon`:
  all odd NUMBERS below 101 are ruled out by kernel computation). The legs are NOT
  logical complements of each other: `ground` speaks of WITNESSES
  (subtype `OddPerfectNumber`), `beyondOwnHorizon` is a raw decide-fact about numbers;
  the contradiction requires genuine mediation (unpacking the subtype + `Nat.odd_iff`),
  and the kernel payment is part of the refutation itself.

  WHAT PAYS FOR THE SUBSTANCE (honestly, point by point). (1) The second leg is GREENLY
  INHABITED: `oddPerfect_horizon_swept` — the kernel unfolding of the horizon, exactly
  the interior of the proof of `oddPerfect_ge_101` (pointwise decidability of
  `DecidablePred Nat.Perfect` in action). This is better than Collatz (where
  `InternalisedCollatzGround` is a bare law/not-law pair, paid for by the decree
  `collatzBoundary`; here there is no decree — §17-verdict — and none is needed), but
  WEAKER than the pigeonhole of P/NP: for `no_fullPayment_of_unboundedSupply` the
  contradiction is carried by a separate green theorem about the infinite vs the finite,
  here it is a finite kernel computation. The law-form ground := law / ¬law here
  DEGENERATES into a tautology (there is no identifying decree) — it is deliberately
  NOT taken. (2) The engine side (`oddPerfectWitness_carries_engine`) is
  CONDITIONAL on the manifestation law (`hLaw : OddPerfectManifestationLaw` — lives
  by definition, the field is NOT decreed) and on the balanced ledger: an unconditional
  analogue of `nonHalting_carries_perpetual_engine` for this front DOES NOT EXIST and
  cannot exist without solving the problem itself — hypotheses are left explicit throughout.

  HONESTY. This is model-internal epistemics, NOT a solution to the oldest open
  problem in mathematics and NOT Gödel (no independence and no fixed point —
  only computational filtering and the wall of the perpetual engine). The unique point
  of this front: "external verification" is literally `DecidablePred Nat.Perfect`,
  the strongest form among all fronts (every forgery dies by decide,
  cf. `not_perfect_945`); to present a GENUINE witness under the law and the ledger =
  to present a perpetual engine — therefore the witness is greenly unpresentable
  (`oddPerfectWitness_green_unpresentable`). The module is ENTIRELY GREEN:
  quarantine is NOT imported, no axiom/sorry/native_decide, taint 47 does not change.
-/

import EuclidsPath.Engine.OddPerfectManifestationFront

set_option autoImplicit false

namespace EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic

open EuclidsPath.PerfectNumberBranch

/-! ## Horizon unfolding: green inhabitedness of the second leg (🟢) -/

/-- **Unfolding of one's own verified horizon (green, kernel computation):**
    all odd numbers below 101 are machine-ruled-out by pointwise perfectness checking —
    exactly the interior of the proof of `oddPerfect_ge_101`
    (`PerfectNumberBranch`), extracted as a named fact about NUMBERS (not about
    witnesses). It is precisely this inhabitedness — like `concreteSupply_unbounded_smallScale`
    in P/NP — that pays for the substance of the conjunction below; Collatz has no analogue. -/
theorem oddPerfect_horizon_swept :
    ∀ M : ℕ, M < 101 → M % 2 = 1 → ¬ Nat.Perfect M := by decide

/-! ## Model: internal solution = witness inside one's own horizon -/

/-- **Internal self-justification of the decision about an odd perfect number.** Carries
    (a) a witness INSIDE one's own verified horizon (`ground`) and
    (b) the machine unfolding of that horizon (`beyondOwnHorizon`) — a raw
    decide-fact about numbers, greenly inhabited (`oddPerfect_horizon_swept`).
    The legs are NOT complements of each other (CORR-fix by the skeptic: the naive pair
    ∃ W, W.1 < 101 / ∀ W, 101 ≤ W.1 would collapse into the quantifier tautology
    `Nat.not_le`): the contradiction below is obtained by mediation — unpacking the
    subtype witness and translating `Odd` into `% 2 = 1`. This is "reaching with one's
    gaze" beyond one's own verified horizon while carrying its unfolding in hand. -/
structure InternalisedOddPerfectGround : Prop where
  ground : ∃ W : OddPerfectNumber, W.1 < 101
  beyondOwnHorizon : ∀ M : ℕ, M < 101 → M % 2 = 1 → ¬ Nat.Perfect M

/-- "Internal knowledge of the cause" = internal self-justification of the decision
    (mirror of `InternalKnowledgeOfCollatzCause` / `InternalKnowledgeOfPNPCause`). -/
abbrev InternalKnowledgeOfOddPerfectCause : Prop := InternalisedOddPerfectGround

/-! ## Core: self-justification self-destructs (🟢) -/

/-- Self-justification self-destructs: the witness from `ground` is unpacked
    into a number `N < 101` with `Odd N` and `Nat.Perfect N`, and `beyondOwnHorizon` —
    the horizon unfolding for the same number — kills it. The mediation is genuine (subtype +
    `Nat.odd_iff`), not a substitution of `H.beyondOwnHorizon H.ground`. GREEN. -/
theorem no_internalisedOddPerfectGround : InternalisedOddPerfectGround → False := by
  rintro ⟨⟨⟨N, hodd, hperf⟩, hlt⟩, hsweep⟩
  exact hsweep N hlt (Nat.odd_iff.mp hodd) hperf

/-- **"CANNOT BE KNOWN FROM WITHIN" — THEOREM** (mirror of `collatzCause_unknowable` /
    `pnpCause_unknowable`, twin-`cause_unknowable`): internal knowledge of the cause
    for odd perfect numbers is impossible. NOT a claim about the (non-)existence
    of an odd perfect number — only about the impossibility of self-justification
    within one's own verified horizon. GREEN. -/
theorem oddPerfectCause_unknowable : ¬ InternalKnowledgeOfOddPerfectCause :=
  no_internalisedOddPerfectGround

/-- **A witness below the horizon is unconditionally impossible (🟢):** here the sweep
    pays directly — `oddPerfect_ge_101` is an in-repo theorem, and no
    odd perfect witness fits below 101. Supplement
    CORR-3 of the skeptic: the same wall as in `no_internalisedOddPerfectGround`,
    but without the self-justification structure. -/
theorem no_oddPerfectWitness_below_horizon :
    ¬ ∃ W : OddPerfectNumber, W.1 < 101 :=
  fun ⟨W, h⟩ => absurd (oddPerfect_ge_101 W) (Nat.not_le.mpr h)

/-- SUBSTANTIVE DICHOTOMY (no ex falso in the statement): either the cause
    is unknowable from within, or there is a witness below the verified horizon.
    The left disjunct is a theorem; the right is unconditionally killed by
    `no_oddPerfectWitness_below_horizon` — both facts are green. -/
theorem unknowable_or_oddPerfect_below_horizon :
    (¬ InternalKnowledgeOfOddPerfectCause) ∨
      ∃ W : OddPerfectNumber, W.1 < 101 :=
  Or.inl oddPerfectCause_unknowable

/-- Ex-falso companion ("carries the engine", mirror of
    `internalisedPNPGround_builds_engine`): from the self-justification (already false)
    the engine itself is also derived. HONESTY: ex falso route; the load-bearing part is
    the impossibility itself (`no_internalisedOddPerfectGround`); the genuine
    engine construction is the conditional `oddPerfectWitness_carries_engine`. -/
theorem internalisedOddPerfectGround_builds_engine :
    InternalisedOddPerfectGround → SomeConcreteEuclideanEngine :=
  fun H => (no_internalisedOddPerfectGround H).elim

/-! ## Witness is greenly unpresentable: to present = to present the engine -/

/-- **"TO PRESENT A WITNESS = TO PRESENT THE ENGINE — THEREFORE UNPRESENTABLE"
    (conditional green summary):** under the manifestation law and the accepted boundary
    the type of odd perfect witnesses is empty — because any presented
    witness would present a perpetual engine (`oddPerfectWitness_carries_engine`),
    and engines are greenly absent (`no_someConcreteEuclideanEngine`).
    HONESTY: both hypotheses are EXPLICIT — the law lives by definition (the field is NOT
    decreed, §17-verdict), the boundary is supplied from outside; an unconditional form
    does not exist for this front and cannot exist without solving the problem itself. -/
theorem oddPerfectWitness_green_unpresentable
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : OddPerfectManifestationLaw) :
    ¬ Nonempty OddPerfectNumber :=
  noOddPerfect_iff_no_witness.mp
    (noOddPerfect_of_manifestation_and_boundary
      no_someConcreteEuclideanEngine hBoundary hLaw)

/-! ## Summaries: solution locked behind the engine; verification, not derivation (🟢) -/

/-- **"SOLUTION LOCKED BEHIND THE ENGINE" (green 3-way fork; mirror of
    `collatz_no_internal_decision_without_engine` / `pnp_no_internal_decision_without_engine`):**
    (1) TO PRESENT a witness under the law and the balanced ledger = to present
        the engine as an object (`oddPerfectWitness_carries_engine`; the conditionality
        of the law is disclosed — hypothesis is explicit);
    (2) TO SELF-JUSTIFY the decision from within — self-destructs
        (`no_internalisedOddPerfectGround`);
    (3) the engine-free path — EXTERNAL boundary: law + boundary + green
        absence of engines yield `NoOddPerfect`
        (`noOddPerfect_of_manifestation_and_boundary`).
    Gödelian independence is NOT asserted and the problem itself is NOT solved —
    only: both internal solutions cost a perpetual engine. -/
theorem oddPerfect_no_internal_decision_without_engine :
    (∀ (A M0 : ℕ), OddPerfectManifestationLaw →
        ∀ W : OddPerfectNumber, W.1 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) ∧
    (InternalisedOddPerfectGround → False) ∧
    (TheStrictLastStep00Obligation → OddPerfectManifestationLaw → NoOddPerfect) :=
  ⟨fun _A _M0 hLaw W hM proj hres =>
     oddPerfectWitness_carries_engine hLaw W hM proj hres,
   no_internalisedOddPerfectGround,
   fun hBoundary hLaw =>
     noOddPerfect_of_manifestation_and_boundary
       no_someConcreteEuclideanEngine hBoundary hLaw⟩

/-- **"VERIFICATION, NOT DERIVATION" (mirror of `collatz_verification_not_derivation` /
    `pnp_verification_not_derivation`) — with the unique point of this front:**
    (1) internal knowledge of the cause is impossible (`oddPerfectCause_unknowable`);
    (2) a witness below the verified horizon is unconditionally impossible —
        the sweep pays directly;
    (3) "external verification" here is LITERALLY pointwise decidability:
        every candidate is decided by computation (the third conjunct is proved from
        the instance `DecidablePred Nat.Perfect`, WITHOUT `Classical.em`) — the solution
        is findable exactly as far as the kernel can compute.
    HONESTY: conjunct (3) is classically trivial; its machine content is
    the proof route through the deciding instance, not the strength of the statement. -/
theorem oddPerfect_verification_not_derivation :
    (¬ InternalKnowledgeOfOddPerfectCause) ∧
    (¬ ∃ W : OddPerfectNumber, W.1 < 101) ∧
    (∀ M : ℕ, Nat.Perfect M ∨ ¬ Nat.Perfect M) :=
  ⟨oddPerfectCause_unknowable,
   no_oddPerfectWitness_below_horizon,
   fun M => if h : Nat.Perfect M then Or.inl h else Or.inr h⟩

/-- Final epistemic status of the odd front (mirror of
    `pnp_locked_behind_engine_status`, NOT `collatz_locked_behind_engine_status`:
    there is NO decree conjunct — the field is deliberately not added, §17-verdict):
    witness ≥ 101 (theorem, kernel-sweep) / internal knowledge impossible
    (theorem) / law + boundary ⟹ NoOddPerfect (conditional — hypotheses explicit) /
    witness + law + ledger ⟹ engine (conditional — hypotheses explicit).
    ENTIRELY GREEN; does NOT solve the open problem. -/
theorem oddPerfect_locked_behind_engine_status :
    (∀ W : OddPerfectNumber, 101 ≤ W.1) ∧
    (¬ InternalKnowledgeOfOddPerfectCause) ∧
    (TheStrictLastStep00Obligation → OddPerfectManifestationLaw → NoOddPerfect) ∧
    (∀ (A M0 : ℕ), OddPerfectManifestationLaw →
        ∀ W : OddPerfectNumber, W.1 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) :=
  ⟨oddPerfect_ge_101,
   oddPerfectCause_unknowable,
   fun hBoundary hLaw =>
     noOddPerfect_of_manifestation_and_boundary
       no_someConcreteEuclideanEngine hBoundary hLaw,
   fun _A _M0 hLaw W hM proj hres =>
     oddPerfectWitness_carries_engine hLaw W hM proj hres⟩

/-! ## Axiom audit: the entire module is green (no more than the standard triple),
    repo taint does NOT change -/
#print axioms oddPerfect_horizon_swept
#print axioms no_internalisedOddPerfectGround
#print axioms oddPerfectCause_unknowable
#print axioms no_oddPerfectWitness_below_horizon
#print axioms unknowable_or_oddPerfect_below_horizon
#print axioms internalisedOddPerfectGround_builds_engine
#print axioms oddPerfectWitness_green_unpresentable
#print axioms oddPerfect_no_internal_decision_without_engine
#print axioms oddPerfect_verification_not_derivation
#print axioms oddPerfect_locked_behind_engine_status

end EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic
