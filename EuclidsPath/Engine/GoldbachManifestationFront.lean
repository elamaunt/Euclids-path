/-
  GoldbachManifestationFront — GREEN (axiom-free) module of the Goldbach branch
  of the perpetual engine programme: "to present a violation of the binary
  Goldbach conjecture = to present a perpetual engine", carried out by the same
  manifestation architecture as Riemann (object-witness, mirror of odd perfect
  number and off-critical zero).

  The deviation here is a DATA OBJECT, like an off-critical Riemann zero and an
  odd perfect number (and unlike the Π-witness of Mersenne): a CONCRETE even
  number `V : GoldbachViolation` (subtype {E // GoldbachViolationAt E}) that
  has no decomposition into a sum of two primes. Hence the manifestation law is
  OBJECT-QUANTIFIED (∀ V, Manifests V) — no gate needed: the scale anchor
  M0 := V.1 is tied to the number itself (height of deviation = deviation
  itself), and an un-gated "explosive" form simply does not exist here.

  STRONGEST UNFORGEABILITY OF THE SERIES (pointwise decidability pushed to the
  limit): a violation at a FIXED even E is DECIDABLE end-to-end —
  `GoldbachRep E` is decidable via the bounded form `GoldbachRepBounded`
  (kernel `Nat.decidableExistsLT`, `Nat.decidablePrime`), and `Even`, `4 ≤ ·`
  and the negation of a decidable are also decidable. Every FORGED REFUTATION
  dies by `decide` on the spot (stronger than Mersenne, where the witness is a
  Π-form, and on a par with odd perfect). And to present a GENUINE witness =
  to REFUTE binary Goldbach — verified in the literature up to 4·10^18
  (Oliveira e Silva et al.). The literature boundary is NOT formalised — green
  here is only ≥ 52 (`goldbachViolation_ge_52`, from the machine check
  `goldbach_upTo_52`; all even 4..50 decompose by `decide`).

  HEURISTIC SIGN — FOR ("no violations" expected): the law's quantifier ranges
  over an expectedly EMPTY witness type — the law is expectedly VACUOUSLY TRUE,
  exact mirror of RH and odd perfect (Riemann was a bet on the expectedly-true;
  here the same orientation, unlike the inverted sign of Mersenne). At the
  boundary the law ⟺ GoldbachConjecture (G7).

  NOTHING TO FORGE: Goldbach violations have no distinguished chain of centres
  at all — no saw, no cookedLadder (YM), no cookedProfileCascade (NS); pattern
  V3 is empty by construction (as for odd perfect, stronger than Mersenne).

  BUT THE §17 FIELD IS NOT ADDED — INTENTIONALLY (quarantine verdict): serial
  expansion of the decree would devalue the quarantine — an axiom growing by
  one field per solved trilemma ceases to be an exception and becomes a
  technique. The law lives here BY DEFINITION (odd perfect precedent); the
  quarantine's consistency is NOT staked on it.

  BORROWED L1/L2 (disclosed): the supply object DeviationFlowSupply is THE
  SAME one that twin-bound builds greenly (L1 of the Riemann front,
  `deviationFlowSupply_of_twinBound`) — the form is non-empty; the Impossible
  side at resolved scales is the green theorem
  `no_deviationFlowSupply_at_resolved_scale` (reused), NOT a decree.

  VACUITY PROHIBITION: no free Prop fields, no free gates, no renamed
  conclusions — every hypothesis is named arithmetically; the vacuous reverse
  side of the law is disclosed by audit G5. The module does NOT import
  quarantine; no axiom/sorry/native_decide.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

/-#############################################################################
  BLOCK 1. Decidable Goldbach branch: the violation witness is a data object
#############################################################################-/

namespace EuclidsPath.GoldbachBranch

/-- **Goldbach decomposition for `E`**: `E` is a sum of two primes. The open
    (binary) conjecture asserts this for all even `E ≥ 4`. -/
def GoldbachRep (E : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = E

/-- The bounded decomposition form is DECIDABLE: enumeration of one prime `p < E`
    with primality check for the complement `E - p`. Kernel `Nat.decidableExistsLT`
    plus `Nat.decidablePrime` give the instance automatically. -/
def GoldbachRepBounded (E : ℕ) : Prop := ∃ p : ℕ, p < E ∧ p.Prime ∧ (E - p).Prime

instance : DecidablePred GoldbachRepBounded := fun E =>
  inferInstanceAs (Decidable (∃ p : ℕ, p < E ∧ p.Prime ∧ (E - p).Prime))

/-- The Goldbach existential ⟺ its bounded (decidable) form: forward —
    the smaller prime gives a candidate `p < E` (second summand ≥ 2); backward —
    the complement `E - p` closes the sum. -/
theorem goldbachRep_iff_bounded (E : ℕ) : GoldbachRep E ↔ GoldbachRepBounded E := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact ⟨p, by have := hq.two_le; omega, hp, by simpa using hq⟩
  · rintro ⟨p, hlt, hp, hq⟩
    exact ⟨p, E - p, hp, hq, by omega⟩

/-- Goldbach decomposability is DECIDABLE — decidability is transferred from the
    bounded form via the proved equivalence. This is precisely what makes every
    forged refutation killable by `decide`: the strongest unpresentability in the series. -/
instance : DecidablePred GoldbachRep := fun E =>
  decidable_of_iff _ (goldbachRep_iff_bounded E).symm

set_option maxRecDepth 4000 in
/-- **Machine check of small cases (pointwise decidability in action):**
    every even `E` in the range `4 ≤ E < 52` decomposes into a sum of two
    primes. `decide` works DIRECTLY on the decidable bounded form,
    then the result is transferred to `GoldbachRep` via the equivalence. -/
theorem goldbach_upTo_52 : ∀ E, E < 52 → 4 ≤ E → E % 2 = 0 → GoldbachRep E := by
  have h : ∀ E, E < 52 → 4 ≤ E → E % 2 = 0 → GoldbachRepBounded E := by decide
  intro E hE h4 hev
  exact (goldbachRep_iff_bounded E).mpr (h E hE h4 hev)

/-- **Binary Goldbach violation at even `E ≥ 4`** — a data object,
    mirror of an off-critical zero and an odd perfect number. The predicate is
    DECIDABLE (all three conjuncts are decidable, including the negation of the
    decidable `GoldbachRep`). -/
def GoldbachViolationAt (E : ℕ) : Prop :=
  4 ≤ E ∧ Even E ∧ ¬ GoldbachRep E

instance : DecidablePred GoldbachViolationAt := fun E => by
  unfold GoldbachViolationAt; infer_instance

/-- The witness type for a Goldbach refutation: a concrete even number together
    with a proof of the absence of decomposition. Expectedly EMPTY type (heuristic
    sign FOR the conjecture) — mirror of `OddPerfectNumber` and `RiemannOffCriticalZero`. -/
abbrev GoldbachViolation : Type := {E : ℕ // GoldbachViolationAt E}

/-- Binary Goldbach conjecture (open problem, named input). -/
def GoldbachConjecture : Prop := ∀ E : ℕ, 4 ≤ E → Even E → GoldbachRep E

/-- Goldbach conjecture ⟺ the violation witness type is empty (mirror of
    `noOddPerfect_iff_no_witness`). -/
theorem goldbachConjecture_iff_no_violation :
    GoldbachConjecture ↔ ¬ Nonempty GoldbachViolation := by
  constructor
  · rintro h ⟨⟨E, h4, hev, hno⟩⟩
    exact hno (h E h4 hev)
  · intro h E h4 hev
    by_contra hno
    exact h ⟨⟨E, h4, hev, hno⟩⟩

/-- **Witness domain localisation (mirror of OP8/M8/L8):** every violation
    witness is ≥ 52 — all smaller even candidates are screened out by the machine
    check `goldbach_upTo_52` (pointwise decidability in action). The literature
    boundary (verified up to 4·10^18) is NOT formalised — only this is green. -/
theorem goldbachViolation_ge_52 (V : GoldbachViolation) : 52 ≤ V.1 := by
  obtain ⟨E, h4, hev, hno⟩ := V
  show 52 ≤ E
  by_contra hlt
  exact hno (goldbach_upTo_52 E (by omega) h4 (Nat.even_iff.mp hev))

/-- **Witness anatomy: all prime shifts are non-prime.** For a hypothetical
    Goldbach violation at `E`, for ANY prime `p < E` the complement `E − p`
    is NOT prime — a direct unfolding of the negation of decomposition `¬GoldbachRep E`
    via the bounded form (`goldbachRep_iff_bounded`): if `E − p` were prime, the
    pair `(p, E − p)` would give a decomposition. HONESTY (CORR-correction):
    "composite" is NOT asserted — when the prime `p = E − 1` the complement
    `E − p = 1` is neither prime NOR composite; green is exactly `¬(E − p).Prime`
    (the series name from the report is kept; the statement is the corrected one).
    This is a property of the HYPOTHETICAL witness (type expectedly empty), not a
    solution to the 1742 problem. -/
theorem goldbachViolation_all_shifts_composite {E : ℕ}
    (hE : GoldbachViolationAt E) :
    ∀ p, p.Prime → p < E → ¬ (E - p).Prime := fun p hp hlt hq =>
  hE.2.2 ((goldbachRep_iff_bounded E).mpr ⟨p, hlt, hp, hq⟩)

end EuclidsPath.GoldbachBranch

/-#############################################################################
  BLOCK 2. Manifestation front (object-quantified; field NOT decreed)
           mirror of OddPerfectManifestationFront — witness → Goldbach violation
#############################################################################-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. Deviation witness: concrete Goldbach violation (data object)
#############################################################################-/

/-- **G8 (witness domain localisation, mirror of OP8; re-export from branch):**
    every Goldbach violation witness is ≥ 52 — all smaller even candidates are
    screened out by the machine check (pointwise decidability in action).
    The literature boundary (4·10^18) is NOT formalised — only this is green. -/
theorem goldbachViolation_ge_52
    (V : EuclidsPath.GoldbachBranch.GoldbachViolation) : 52 ≤ V.1 :=
  EuclidsPath.GoldbachBranch.goldbachViolation_ge_52 V

/-#############################################################################
  §2. Manifestation law (object-quantified; field NOT decreed)
#############################################################################-/

/-- A concrete Goldbach violation manifests arithmetically: at every ledger scale
    no lower than the number itself, wherever the projection balances the ledger
    (collisions are resolved), the witness appears as an unpayable infinite supply
    of flows. The anchor `V.1 ≤ M0` is consumed below only via `le_refl` (Riemann
    pattern: scale = height of deviation; here the height of deviation is the
    violating number itself). Causal form: "the deviation must manifest wherever
    the ledger is balanced" — NOT a statement about the (non-)existence of Goldbach
    violations. -/
def GoldbachViolationManifests
    (V : EuclidsPath.GoldbachBranch.GoldbachViolation) : Prop :=
  ∀ (A M0 : ℕ), V.1 ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **GOLDBACH MANIFESTATION LAW** — object-quantified over the witness type
    (mirror of `RiemannManifestationLaw` and odd perfect, NOT the gated form of
    Mersenne): the quantifier ranges over an expectedly EMPTY type, the law is
    expectedly vacuously true — exact mirror of RH. THE §17 FIELD IS NOT DECREED
    (verdict: seriality would devalue the quarantine). -/
def GoldbachManifestationLaw : Prop :=
  ∀ V : EuclidsPath.GoldbachBranch.GoldbachViolation, GoldbachViolationManifests V

/-#############################################################################
  §3. ESSENCE and readable form: presenting a witness presents the engine
#############################################################################-/

/-- **G3⁺ — READABLE FORM "to present a violation = to present an engine":**
    a concrete Goldbach violation + law + balanced ledger at a scale no lower
    than the number itself MANIFEST a perpetual engine — as an OBJECT, before
    being killed by lexRank. -/
theorem goldbachViolation_carries_engine
    (hLaw : GoldbachManifestationLaw)
    (V : EuclidsPath.GoldbachBranch.GoldbachViolation)
    {A M0 : ℕ} (hM : V.1 ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw V A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **G3 — ESSENCE (mirror of OP3, M3 and Riemannian L3):** no engines +
    accepted boundary + manifestation law ⟹ NO Goldbach violations (i.e. the
    Goldbach conjecture holds). All three hypotheses are consumed FOR REAL: the
    hypothetical witness V gives scale M0 := V.1, the boundary gives resolution
    exactly there (le_refl); the law supplies the family 𝓕 (not ex falso); from
    the collision an engine-WITNESS is built; it is precisely hNoEngine that kills
    it. -/
theorem noGoldbachViolation_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : GoldbachManifestationLaw) :
    ¬ Nonempty EuclidsPath.GoldbachBranch.GoldbachViolation := by
  rintro ⟨V⟩
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf V.1) :=
    strictSemanticExtended_resolves_old (hres V.1)
  exact hNoEngine ⟨A, V.1,
    goldbachViolation_carries_engine hLaw V (le_refl V.1) (projOf V.1) hResolves⟩

/-- **G3 in conjecture form (mirror): the same triple ⟹ Goldbach conjecture holds**
    — via the bridge `goldbachConjecture_iff_no_violation`. -/
theorem goldbachConjecture_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : GoldbachManifestationLaw) :
    EuclidsPath.GoldbachBranch.GoldbachConjecture :=
  EuclidsPath.GoldbachBranch.goldbachConjecture_iff_no_violation.mpr
    (noGoldbachViolation_of_manifestation_and_boundary hNoEngine hBoundary hLaw)

/-#############################################################################
  §4. Honesty audits (G5–G9)
#############################################################################-/

/-- **G5 (vacuous reverse side, mirror of OP5/M5/L5):** Goldbach conjecture
    ⟹ law — vacuously: the witness's own data V.2 contradicts the conjecture
    directly (the conjecture gives a decomposition, the witness negates it). The
    load-bearing side is G3, and it needs the boundary. -/
theorem goldbachManifestationLaw_of_conjecture
    (H : EuclidsPath.GoldbachBranch.GoldbachConjecture) :
    GoldbachManifestationLaw := fun V =>
  (V.2.2.2 (H V.1 V.2.1 V.2.2.1)).elim

/-- **G6 (exact green characterisation, mirror of OP6/M6/L6):** law ⟺
    "a Goldbach violation would freeze every resolving ledger at scales no lower
    than itself". The backward direction is ex falso from ¬resolves (disclosed);
    the substantive side is the forward one (law + resolution ⟹ supply ⟹
    contradiction with the green L2 `no_deviationFlowSupply_at_resolved_scale`). -/
theorem goldbachManifestationLaw_iff_no_resolution_above_witness :
    GoldbachManifestationLaw ↔
      ∀ (V : EuclidsPath.GoldbachBranch.GoldbachViolation) (A M0 : ℕ),
        V.1 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw V A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw V A M0 hle proj hres)
  · intro hFreeze V A M0 hle proj hres
    exact ((hFreeze V A M0 hle proj) hres).elim

/-- **G7 — MAIN PRICE AUDIT (mirror of OP7/M7/L7):** at the boundary the law ⟺
    Goldbach conjecture — the field would be exactly the strength of binary Goldbach.
    WITHOUT the boundary "law ⟹ conjecture" does not assemble greenly (G3 needs the
    boundary). The heuristic sign points FOR the right-hand side of this ⟺ (as for
    Riemann and odd perfect, unlike Mersenne) — and yet the field is not added (§17). -/
theorem goldbachManifestationLaw_iff_conjecture_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    GoldbachManifestationLaw ↔ EuclidsPath.GoldbachBranch.GoldbachConjecture :=
  ⟨goldbachConjecture_of_manifestation_and_boundary
      no_someConcreteEuclideanEngine hBoundary,
   goldbachManifestationLaw_of_conjecture⟩

/-- Law in Bridge form over the witness type — here a DIRECT repackaging
    (object-quantification is itself the Bridge; cf. gate repackaging for Mersenne). -/
theorem goldbachManifestationLaw_iff_bridge :
    GoldbachManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun V : EuclidsPath.GoldbachBranch.GoldbachViolation =>
          GoldbachViolationManifests V) :=
  ⟨fun hLaw V => hLaw V, fun hB V => hB V⟩

/-- **G9 (bundling audit, instantiation of the condemning machine):** the bundle
    Bridge∧Impossible ⟺ "no Goldbach violation witnesses" —
    only the Bridge side could be decreed; the Impossible side at
    permitted scales is green L2, never a decree. -/
theorem goldbachManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun V : EuclidsPath.GoldbachBranch.GoldbachViolation =>
          GoldbachViolationManifests V) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun V : EuclidsPath.GoldbachBranch.GoldbachViolation =>
          GoldbachViolationManifests V)) ↔
      ¬ Nonempty EuclidsPath.GoldbachBranch.GoldbachViolation :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Machine-visible purity in the build log (expected [propext, Classical.choice,
-- Quot.sound] — WITHOUT step00FirstCause):
#print axioms noGoldbachViolation_of_manifestation_and_boundary
#print axioms goldbachConjecture_of_manifestation_and_boundary
#print axioms goldbachViolation_carries_engine
#print axioms goldbachManifestationLaw_iff_conjecture_of_boundary
#print axioms EuclidsPath.GoldbachBranch.goldbach_upTo_52
#print axioms EuclidsPath.GoldbachBranch.goldbachViolation_ge_52
#print axioms EuclidsPath.GoldbachBranch.goldbachViolation_all_shifts_composite

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
