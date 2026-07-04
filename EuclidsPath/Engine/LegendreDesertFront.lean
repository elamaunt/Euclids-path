/-
  LegendreDesertFront — a GREEN (axiom-free) module of the prime-deserts branch
  of the perpetual-engine programme. TWO BLOCKS:

    BLOCK 1 (namespace EuclidsPath.PrimeDeserts) — the UNCONDITIONAL green
    content of Bertrand and the Legendre object-witness. The unique green
    strength of this front: Bertrand's postulate (mathlib, unconditional) yields
    the THEOREM "a desert cannot double" (no_desert_doubles): between n and 2n+1
    a prime ALWAYS EXISTS (n ≠ 0). This is the only manifestation front of the
    programme whose carrier arithmetic is green in its entirety, not gated by an
    open problem.

    BLOCK 2 (namespaces EuclidsPath / ConcreteStep00Graph /
    GeneratedFlowFormulation) — the manifestation front of the Legendre
    object-witness, a mirror of OddPerfectManifestationFront: the deviation is
    OBJECT-DATA `V : LegendreViolation` (subtype {n // LegendreViolationAt n}, a
    concrete violation of Legendre's conjecture: a prime desert between n² and
    (n+1)²). The law is OBJECT-QUANTIFIED (∀ V, Manifests V); the scale anchor
    M0 := V.1² is tied to the violation itself; no ungated "explosive" form
    exists.

  POINTWISE DECIDABILITY (the strongest form of unpresentability):
  LegendreViolationAt is decidable (DecidablePred via the bounded-ball form
  Nat.decidableBallLT) — every forgery dies to `decide`
  (legendre_holds_upTo_10: below 11 there are no violations, machine-checked),
  while presenting a REAL witness = REFUTING Legendre's conjecture, open since
  1808. The literary bound (checked far past 10^18) is NOT formalized — green
  here is only ≥ 11 (legendreViolation_ge_11).

  HONEST DISCLOSURE (machine-checked, legendre_interval_shorter_than_bertrand):
  the Legendre interval is SHORTER than Bertrand's — for n ≥ 3 we have
  (n+1)² < 2n², whereas Bertrand covers only [m, 2m]. Hence Bertrand does NOT
  solve Legendre: the green "a desert does not double" is powerless on the
  quadratic gap, and NoBertrandToLegendreImplicationClaimed = True explicitly
  records that NO implication Bertrand ⟹ Legendre is claimed here. The positive
  side of the same honesty (bertrand_localizes_desert, §3b): on a HYPOTHETICAL
  desert witness Bertrand still works — it pushes the next prime into the layer
  [(n+1)², 2n²+2]; this localizes the consequences of a violation, not its
  exclusion.

  HEURISTIC SIGN — FOR (no Legendre violations, as expected): the law's
  quantifier ranges over the expectedly EMPTY type LegendreViolation — the law
  is expectedly VACUOUSLY TRUE, an exact mirror of RH and odd perfects (Riemann
  was a bet on the expectedly-true; the same orientation here). Under a boundary
  the law ⟺ absence of violations ⟺ LegendreConjecture (LG7).

  FIELD NOT ADDED — INTENTIONALLY (§17 quarantine verdict): a serial expansion
  of the decree would devalue the quarantine. The law lives here by DEFINITION
  (the §16 / Mersenne precedent); the consistency of the quarantine is NOT
  staked on it.

  BORROWED L1/L2 (disclosed): the supply object DeviationFlowSupply is THE SAME
  one that twin-bound builds green (L1 of the Riemann front); the Impossible
  side at resolved scales is the green theorem
  no_deviationFlowSupply_at_resolved_scale (reused), NOT a decree.

  VACUITY BAN: no free Prop-fields, no free gates, and no renamed conclusions —
  every hypothesis is named arithmetically; the vacuous reverse side of the law
  is disclosed by the LG5 audit. The module does NOT import the quarantine;
  there is no axiom/sorry/native_decide.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

/-#############################################################################
  BLOCK 1 — namespace EuclidsPath.PrimeDeserts

  Prime deserts, UNCONDITIONAL Bertrand, the Legendre object-witness.
#############################################################################-/

namespace EuclidsPath
namespace PrimeDeserts

/-- **Prime desert between `a` and `b`:** no `p` strictly between `a` and `b`
    is prime. An open interval — the endpoints do not participate. -/
def PrimeDesertBetween (a b : ℕ) : Prop :=
  ∀ p, a < p → p < b → ¬ p.Prime

/-- Decidability of the desert via the bounded-ball reformulation:
    `∀ p, p < b → a < p → ¬ p.Prime` carries the green `Nat.decidableBallLT`,
    which REDUCES under `decide` (unlike the naive Finset-ball, whose instance
    is not synthesized). The order of hypotheses is permuted exactly so that
    the upper bound `p < b` comes first (the `Nat.decidableBallLT` form). -/
instance instDecidablePrimeDesertBetween (a b : ℕ) :
    Decidable (PrimeDesertBetween a b) :=
  decidable_of_iff (∀ p, p < b → a < p → ¬ p.Prime) <| by
    constructor
    · intro h p hlt hpb
      exact h p hpb hlt
    · intro h p hpb hlt
      exact h p hlt hpb

/-#############################################################################
  §1. UNCONDITIONAL Bertrand: a desert cannot double
#############################################################################-/

/-- **GREEN (unconditional) content of Bertrand — the MAIN THEOREM of block 1:**
    a prime desert CANNOT cover a doubling — between `n` and `2n+1` (for
    `n ≠ 0`) a prime ALWAYS exists. A direct repackaging of Bertrand's postulate
    (`Nat.exists_prime_lt_and_le_two_mul`, mathlib, unconditional). No open
    problem: this fact is a THEOREM, not a gate. -/
theorem no_desert_doubles {n : ℕ} (hn : n ≠ 0) :
    ¬ PrimeDesertBetween n (2 * n + 1) := by
  intro hdes
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  exact hdes p hlt (by omega) hp

/-- A direct positive repackaging of Bertrand: the next prime after `n`
    does not exceed `2n` (for `n ≠ 0`). A companion form of no_desert_doubles. -/
theorem nextPrime_le_two_mul {n : ℕ} (hn : n ≠ 0) :
    ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  exact ⟨p, hp, hlt, hle⟩

/-#############################################################################
  §2. The Legendre object-witness and pointwise decidability
#############################################################################-/

/-- **Violation of Legendre's conjecture at the point `n`:** `1 ≤ n` and a
    prime desert (no prime) lies between `n²` and `(n+1)²`. Presenting such an
    `n` = refuting Legendre's conjecture. -/
def LegendreViolationAt (n : ℕ) : Prop :=
  1 ≤ n ∧ PrimeDesertBetween (n ^ 2) ((n + 1) ^ 2)

/-- Pointwise decidability of the violation — directly from decidability of the desert. -/
instance instDecidablePredLegendreViolationAt :
    DecidablePred LegendreViolationAt := fun n =>
  inferInstanceAs (Decidable (1 ≤ n ∧ _))

/-- The violation witness type (subtype — for object-quantification and the
    bundling audit of block 2). An expectedly EMPTY type (heuristic sign — FOR). -/
abbrev LegendreViolation : Type := {n // LegendreViolationAt n}

/-- **Legendre's conjecture (1808):** between any consecutive squares
    (`n ≥ 1`) there is a prime. Open to this day. -/
def LegendreConjecture : Prop :=
  ∀ n, 1 ≤ n → ∃ p, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- Legendre's conjecture ⟺ there are no violations. A direct plumbing
    equivalence (push_neg over the definition of the desert). -/
theorem legendreConjecture_iff_no_violation :
    LegendreConjecture ↔ ∀ n, ¬ LegendreViolationAt n := by
  constructor
  · intro hLC n hViol
    obtain ⟨hn, hDesert⟩ := hViol
    obtain ⟨p, hp, hlo, hhi⟩ := hLC n hn
    exact hDesert p hlo hhi hp
  · intro hNo n hn
    by_contra hne
    refine hNo n ⟨hn, fun p hlo hhi hp => ?_⟩
    exact hne ⟨p, hp, hlo, hhi⟩

/-- **LG-machine (pointwise decidability in action):** below 11 there are NO
    Legendre violations — all candidates `1 ≤ n < 11` are screened out by a
    machine check (`decide`, WITHOUT native_decide). A forgery dies pointwise. -/
theorem legendre_holds_upTo_10 :
    ∀ n, n < 11 → 1 ≤ n → ¬ LegendreViolationAt n := by decide

/-- **LG8 (witness domain localization, mirror of M8/OP8):** every Legendre
    violation witness is ≥ 11 — smaller points are screened out by machine
    (`legendre_holds_upTo_10`). The literary bound is NOT formalized —
    only this is green. -/
theorem legendreViolation_ge_11 (V : LegendreViolation) : 11 ≤ V.1 := by
  by_contra h
  exact legendre_holds_upTo_10 V.1 (by omega) V.2.1 V.2

/-#############################################################################
  §3. HONEST DISCLOSURE: the Legendre interval is SHORTER than Bertrand's
#############################################################################-/

/-- **HONESTY (machine-checked):** the Legendre interval `(n², (n+1)²)` is
    SHORTER than Bertrand's doubling for `n ≥ 3`: `(n+1)² < 2n²`. Precisely why
    the green `no_desert_doubles` (a desert does not double) does NOT cover
    the quadratic gap — Bertrand does NOT solve Legendre. -/
theorem legendre_interval_shorter_than_bertrand {n : ℕ} (h : 3 ≤ n) :
    (n + 1) ^ 2 < 2 * n ^ 2 := by
  nlinarith

/-- **EXPLICIT REFUSAL OF AN OVERSTATED CLAIM:** NO implication Bertrand ⟹
    Legendre is claimed or proven in this module. The flag = True (trivially):
    the honesty of the front is that the green strength of block 1 (Bertrand)
    remains strictly weaker than the open block 2 (Legendre), see
    legendre_interval_shorter_than_bertrand. -/
abbrev NoBertrandToLegendreImplicationClaimed : Prop := True

theorem noBertrandToLegendreImplicationClaimed_holds :
    NoBertrandToLegendreImplicationClaimed := trivial

/-#############################################################################
  §3b. BERTRAND DESERT-LOCALIZATION: the front's only unconditional wall
       WORKS, for the first time, on a hypothetical Legendre witness
#############################################################################-/

/-- Green arithmetic of the layer: `(n+1)² ≤ 2n²+2` for ALL `n` (this is exactly
    `n² ≥ 2n−1`, i.e. `(n−1)² ≥ 0`). The layer `[(n+1)², 2n²+2]` of the theorem
    `bertrand_localizes_desert` is nondegenerate with no preconditions — the
    bound is accurate even at `n = 0`. -/
theorem legendre_layer_nonempty (n : ℕ) : (n + 1) ^ 2 ≤ 2 * n ^ 2 + 2 := by
  cases n with
  | zero => decide
  | succ m => nlinarith [Nat.zero_le m]

/-- **BERTRAND DESERT-LOCALIZATION (the positive side of the §3 honesty):** if
    a prime desert (a hypothetical Legendre violation) lies between `n²` and
    `(n+1)²`, then Bertrand PUSHES the next prime into the narrow layer
    `[(n+1)², 2n²+2]`. Proof: Bertrand on `n²+1` (mathlib,
    `Nat.exists_prime_lt_and_le_two_mul`; `n²+1 ≠ 0` always — no preconditions)
    yields a prime `p ∈ (n²+1, 2n²+2]`; the desert is an OPEN interval, so
    `p < (n+1)²` is forbidden and `p ≥ (n+1)²`; the layer is nondegenerate by
    green arithmetic (`legendre_layer_nonempty`). HONESTY: this is NOT an
    implication Bertrand ⟹ Legendre (the flag
    `NoBertrandToLegendreImplicationClaimed` stands — Bertrand does NOT exclude
    the desert) and NOT a solution of the 1808 problem: the theorem only
    precisely quantifies WHERE a violation is obliged to shift the next prime.
    Paid in full by unconditional mathlib-Bertrand — no open inputs. -/
theorem bertrand_localizes_desert (n : ℕ)
    (hdes : PrimeDesertBetween (n ^ 2) ((n + 1) ^ 2)) :
    ∃ p, p.Prime ∧ (n + 1) ^ 2 ≤ p ∧ p ≤ 2 * n ^ 2 + 2 := by
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n ^ 2 + 1) (Nat.succ_ne_zero _)
  refine ⟨p, hp, ?_, ?_⟩
  · by_contra hsmall
    exact hdes p (Nat.lt_of_succ_lt hlt) (Nat.not_le.mp hsmall) hp
  · calc p ≤ 2 * (n ^ 2 + 1) := hle
      _ = 2 * n ^ 2 + 2 := by ring

/-- **Corollary for the object-witness (bridge to block 2):** every hypothetical
    Legendre violation `V` pushes a prime into the layer `[(V.1+1)², 2·V.1²+2]` —
    a direct instantiation of `bertrand_localizes_desert` with the witness data
    `V.2.2`. The type `LegendreViolation` is expectedly empty (heuristic sign —
    FOR), so this is a property of a HYPOTHETICAL witness, not a presented number. -/
theorem legendreViolation_forces_prime_in_gap (V : LegendreViolation) :
    ∃ p, p.Prime ∧ (V.1 + 1) ^ 2 ≤ p ∧ p ≤ 2 * V.1 ^ 2 + 2 :=
  bertrand_localizes_desert V.1 V.2.2

-- Machine-visible purity of block 1
-- (expectedly [propext, Classical.choice, Quot.sound]):
#print axioms no_desert_doubles
#print axioms legendre_holds_upTo_10
#print axioms legendre_interval_shorter_than_bertrand
#print axioms legendre_layer_nonempty
#print axioms bertrand_localizes_desert
#print axioms legendreViolation_forces_prime_in_gap

end PrimeDeserts
end EuclidsPath

/-#############################################################################
  BLOCK 2 — namespaces EuclidsPath / ConcreteStep00Graph /
           GeneratedFlowFormulation

  Manifestation front of the Legendre object-witness (mirror of
  OddPerfectManifestationFront). The scale anchor M0 := V.1² is tied to the
  violation itself; the law is object-quantified over the type of witnesses.
#############################################################################-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §4. Manifestation law (object-quantified; field NOT decreed)
#############################################################################-/

/-- A concrete Legendre violation manifests arithmetically: on every
    ledger scale not below the square of the violation point `V.1²`, everywhere
    the projection reconciles the books (collisions are resolved), the witness
    shows itself as an unpayable infinite supply of flows. The anchor `V.1² ≤ M0`
    is consumed below only through `le_refl` (the Riemann/OP pattern: scale = height
    of the deviation; here the deviation height is the square of the violation point).
    Causal form: "a deviation must show itself where the books are reconciled" — NOT
    a statement about the (non-)existence of Legendre violations. -/
def LegendreDesertManifests (V : EuclidsPath.PrimeDeserts.LegendreViolation) :
    Prop :=
  ∀ (A M0 : ℕ), V.1 ^ 2 ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **LEGENDRE MANIFESTATION LAW** — object-quantified over the type of
    witnesses (mirror of `RiemannManifestationLaw` and OddPerfect, and NOT the gated
    Mersenne form): the quantifier ranges over an expectedly EMPTY type, the law is
    expectedly vacuously true — an exact mirror of RH. FIELD NOT DECREED (§17 verdict:
    seriality would devalue the quarantine). -/
def LegendreManifestationLaw : Prop :=
  ∀ V : EuclidsPath.PrimeDeserts.LegendreViolation, LegendreDesertManifests V

/-#############################################################################
  §5. ESSENCE and readable form: presenting the witness presents the engine
#############################################################################-/

/-- **LG3⁺ — READABLE FORM "present a violation = present an engine":**
    a concrete Legendre violation + the law + reconciled books on a scale not
    below `V.1²` MANIFEST a perpetual engine — as an OBJECT, before it is killed
    by lexRank'. -/
theorem legendreViolation_carries_engine
    (hLaw : LegendreManifestationLaw)
    (V : EuclidsPath.PrimeDeserts.LegendreViolation)
    {A M0 : ℕ} (hM : V.1 ^ 2 ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw V A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **LG3 — ESSENCE (mirror of OP3 and the Riemann L3):** no engines +
    accepted boundary + manifestation law ⟹ there are NO Legendre violations. All three
    hypotheses are consumed FOR REAL: a hypothetical witness V gives the
    scale M0 := V.1², the boundary — resolution exactly on it (le_refl); the law
    supplies the family 𝓕 (not ex falso); from the collision an
    engine-WITNESS is built; it is precisely hNoEngine that kills it. -/
theorem noLegendreViolation_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LegendreManifestationLaw) :
    ¬ Nonempty EuclidsPath.PrimeDeserts.LegendreViolation := by
  rintro ⟨V⟩
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves :
      SemanticExtendedFlowLedgerCollisionResolves (projOf (V.1 ^ 2)) :=
    strictSemanticExtended_resolves_old (hres (V.1 ^ 2))
  exact hNoEngine ⟨A, V.1 ^ 2,
    legendreViolation_carries_engine hLaw V (le_refl (V.1 ^ 2))
      (projOf (V.1 ^ 2)) hResolves⟩

/-- **LG4 — sufficiency as a THEOREM:** the same triple ⟹ the Legendre conjecture.
    The absence of violations (through
    `legendreConjecture_iff_no_violation`) is exactly the Legendre conjecture;
    ¬Nonempty unpacks into a pointwise negation. -/
theorem legendreConjecture_of_manifestation_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LegendreManifestationLaw) :
    EuclidsPath.PrimeDeserts.LegendreConjecture := by
  refine EuclidsPath.PrimeDeserts.legendreConjecture_iff_no_violation.mpr ?_
  intro n hViol
  exact noLegendreViolation_of_manifestation_and_boundary
    hNoEngine hBoundary hLaw ⟨⟨n, hViol⟩⟩

/-#############################################################################
  §6. Honesty audits (LG5–LG9)
#############################################################################-/

/-- **LG5 (vacuous reverse side, mirror of OP5/L5):** the absence of
    violations ⟹ the law — vacuously: the witness's own data V.2
    contradict the absence directly (the type of witnesses is empty). The carrying side is
    LG3, and it needs the boundary. -/
theorem legendreManifestationLaw_of_no_violation
    (H : ∀ n, ¬ EuclidsPath.PrimeDeserts.LegendreViolationAt n) :
    LegendreManifestationLaw := fun V =>
  (H V.1 V.2).elim

/-- **LG6 (exact green characterization, mirror of OP6/L6):** the law ⟺
    "a Legendre violation would freeze every resolving ledger at scales
    not below its square". The reverse direction — ex falso from ¬resolves
    (unfolded); the substantive side — the forward one (law + resolution ⟹
    supply ⟹ contradiction with the green L2). -/
theorem legendreManifestationLaw_iff_no_resolution_above_witness :
    LegendreManifestationLaw ↔
      ∀ (V : EuclidsPath.PrimeDeserts.LegendreViolation) (A M0 : ℕ),
        V.1 ^ 2 ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw V A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw V A M0 hle proj hres)
  · intro hFreeze V A M0 hle proj hres
    exact ((hFreeze V A M0 hle proj) hres).elim

/-- **LG7 — MAIN PRICE AUDIT (mirror of OP7/M7/L7):** under the boundary, the law ⟺
    the Legendre conjecture — the field would be exactly of the strength of the problem, open since 1808.
    WITHOUT the boundary "law ⟹ Legendre" does not assemble green (LG3/LG4 require
    the boundary). The heuristic sign points FOR the right-hand side of this ⟺ (as with Riemann
    and OddPerfect) — and yet the field is not added (§17). -/
theorem legendreManifestationLaw_iff_conjecture_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    LegendreManifestationLaw ↔ EuclidsPath.PrimeDeserts.LegendreConjecture := by
  constructor
  · exact legendreConjecture_of_manifestation_and_boundary
      no_someConcreteEuclideanEngine hBoundary
  · intro hLC
    exact legendreManifestationLaw_of_no_violation
      (EuclidsPath.PrimeDeserts.legendreConjecture_iff_no_violation.mp hLC)

/-- The law in Bridge form over the type of witnesses — here a DIRECT repacking
    (object-quantification is exactly the Bridge; cf. the repacking in OddPerfect). -/
theorem legendreManifestationLaw_iff_bridge :
    LegendreManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun V : EuclidsPath.PrimeDeserts.LegendreViolation =>
          LegendreDesertManifests V) :=
  ⟨fun hLaw V => hLaw V, fun hB V => hB V⟩

/-- **LG9 (bundling audit, instantiation of the condemning machine):** the bundle
    Bridge∧Impossible ⟺ "there are no Legendre violations" — decreeable could be
    ONLY the Bridge side; the Impossible side on resolved scales is
    the green L2, never a decree. -/
theorem legendreManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun V : EuclidsPath.PrimeDeserts.LegendreViolation =>
          LegendreDesertManifests V) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun V : EuclidsPath.PrimeDeserts.LegendreViolation =>
          LegendreDesertManifests V)) ↔
      ¬ Nonempty EuclidsPath.PrimeDeserts.LegendreViolation :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Machine-visible cleanliness of block 2 in the build log
-- (expectedly [propext, Classical.choice, Quot.sound] — WITHOUT step00FirstCause):
#print axioms noLegendreViolation_of_manifestation_and_boundary
#print axioms legendreConjecture_of_manifestation_and_boundary
#print axioms legendreViolation_carries_engine
#print axioms legendreManifestationLaw_iff_conjecture_of_boundary
#print axioms legendreManifestation_bundling_audit

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
