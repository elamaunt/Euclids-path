/-
  SophieGermainManifestationFront — the GREEN (axiom-free) branch module for
  Sophie Germain in the perpetual-engine programme: "refuting Sophie Germain =
  presenting a perpetual engine", carried through Riemann's manifestation
  architecture — a mirror of the Mersenne front (ch. 43) PLUS a unique
  restrict-section 3 (mod 4) feeding the anti-Mersenne corollary.

  The deviation here is NOT a data object (like an off-critical zero) but a
  Π-witness: `SGAbsenceAbove P` — the absence of Sophie Germain pairs above the
  threshold P (mirror of `MersenneTwinAbsenceAbove`). The manifestation law is
  GATED by this witness: the ungated form (∀ P, Manifests P) would blow up the
  accepted boundary — like the YM/NS manifestation candidates (disclosed below).

  Architecture (mirror of MersenneManifestationFront, M1–M9 ↦ SG1–SG9):
    * negation plumbing: absence witness ⟺ ¬unboundedness;
    * the center-DOUBLING chain (minus side: 2(6m−1)+1 = 6(2m)−1, branch
      disclosure `sg_center_doubling`) strictly grows (`sg_doubling_lt`) — AND
      THE KEY DISCLOSURE: the chain DOES NOT PEEL (`isEmpty_properCenterPeel_two_one`)
      — the coefficient 2, though prime, satisfies 2 ≢ ±1 (mod 6) and does not
      divide the odd sides 6n∓1; already the first step 2 → 1 is empty (sides
      11/13 are prime, targets 5/7). Hence a FORGED witness DOES NOT EXIST in
      this branch — unlike YM (cookedLadder) and NS (cookedProfileCascade),
      exactly as with Riemann and Mersenne;
    * the manifestation law `SGManifestationLaw` (anchor M0 := P, consumed
      via le_refl); the Impossible side is the green theorem
      `no_deviationFlowSupply_at_resolved_scale` (reused), NOT a decree;
    * ESSENCE SG3: no engines + accepted boundary + law ⟹ Sophie Germain pairs
      are unbounded (all three hypotheses genuinely consumed);
    * READABLE FORM SG3⁺ `sgRefutation_carries_engine`: absence witness
      + law + reconciled books ⟹ engine-WITNESS as an object.

  THE FOURTH-BOUNDARY TRILEMMA IS PASSED (V1: not refutable — any absence
  witness ≥ 89 (SG8) is green, and PRESENTING a witness = solving the open
  Sophie Germain tail problem; V2: not provable/not vacuous green — under the
  boundary the law ⟺ open unboundedness (SG7), gate vacuity ⟺ the same open
  problem; V3: does not blow up the boundary — nothing to forge, isEmpty is green).
  BUT THE FIELD IS NOT ADDED — DELIBERATELY: ⚠️ THE HEURISTIC SIGN IS POSITIVE —
  unlike Mersenne (sign inverted, ch. 43), Sophie Germain pairs are expected to
  be infinitely many (Hardy–Littlewood: ~ 2C₂ · x/ln²x), i.e. this would be a
  bet on the expectedly-true, like Riemann. AND STILL THERE IS NO FIELD — the
  verdict of §17: the programme does not multiply manifestation fields beyond
  Riemann; the law lives here by DEFINITION, the quarantine's consistency is
  NOT staked on it.

  ⚠️ CROSSROADS PEARL (branch, `sophieGermain_divides_mersenne`,
  Euler–Lagrange, green-proven): an SG-prime p ≡ 3 (mod 4), p > 3 ⟹
  (2p+1) ∣ M_p and M_p is COMPOSITE — a formal fragment of the very §16-heuristic
  that the quarantine set against the Mersenne boundary. The restrict-section §6
  turns this into "TWO BETS STARING AT EACH OTHER": the conclusion of THIS front
  (the essence of the restrict-law) feeds the COMPOSITE side of the quantity M_p —
  the very one whose PRIME side the Mersenne front (ch. 43) refused to bet on.

  BORROWING DISCLOSURE L1: the supply object `DeviationFlowSupply` and its
  substantiveness witness (Riemann's L1,
  `deviationFlowSupply_of_twinBound` — twin-bound builds the same object
  green at every scale) are TAKEN from the Riemann front and are not
  reproven here; the Impossible side at resolved scales is the green
  L2, never a decree.

  VACUITY PROHIBITION №3: no free Prop-fields, no free gates and no
  renamed conclusions — every hypothesis is named arithmetically.
  The module does NOT import the quarantine; there is no axiom/sorry.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.SophieGermainBranch

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. Deviation witness: absence of Sophie Germain pairs above a threshold
#############################################################################-/

/-- **Absence of Sophie Germain pairs above `P`** (Π-witness, mirror of
    `MersenneTwinAbsenceAbove`): every SG-prime (`p` and `2p+1` prime)
    sits no higher than `P`. -/
def SGAbsenceAbove (P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (2 * p + 1).Prime → p ≤ P

/-- Plumbing: from boundedness an absence witness is extracted. -/
theorem exists_sgAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.SophieGermainBranch.SophieGermainUnbounded) :
    ∃ P : ℕ, SGAbsenceAbove P := by
  unfold EuclidsPath.SophieGermainBranch.SophieGermainUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun p h1 h2 => by
    by_contra hgt
    exact hP p (by omega) ⟨h1, h2⟩⟩

/-- Plumbing: unboundedness ⟺ there are no absence witnesses. -/
theorem sophieGermainUnbounded_iff_no_absence :
    EuclidsPath.SophieGermainBranch.SophieGermainUnbounded ↔
      ∀ P : ℕ, ¬ SGAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨p, hlt, hSG⟩ := hU P
    have := hAbs p hSG.1 hSG.2
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_sgAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **SG8 (witness domain localization, mirror of M8):** every absence
    bound is ≥ 89 — the Sophie Germain pair (89, 179) green-exists
    (cf. `sg_instances` of the branch). -/
theorem sgAbsenceBound_ge_89 {P : ℕ}
    (hAbs : SGAbsenceAbove P) : 89 ≤ P := by
  have h := hAbs 89 (by norm_num) (by norm_num : (179 : ℕ).Prime)
  omega

/-#############################################################################
  §2. The center-doubling chain: strictly grows — and DOES NOT PEEL (no forging)
#############################################################################-/

/-- Docking remark with the branch disclosure: on the minus side the SG-map
    `p → 2p+1` in center coordinates is exactly the DOUBLING `m → 2m`
    (`sg_center_doubling`: `2(6m−1)+1 = 6(2m)−1`), and the center chain
    strictly goes up at each step — like `4m+1` for Mersenne and `5m+1` for
    the five-adic. Monotonicity is trivial, but it is precisely what makes the
    disclosure below substantive: the chain can grow, but PEEL — no. -/
theorem sg_doubling_lt (c : ℕ) (hc : 1 ≤ c) : c < 2 * c := by omega

/-- **KEY DISCLOSURE (contrast with the 5-adic, mirror of
    `isEmpty_properCenterPeel_five_one`): the doubling chain DOES NOT peel.**
    The 5-adic chain `c → 5c+1` has the identity `6(5x+1)−1 = 5(6x+1)` with a
    PRIME constant divisor 5 — which is why it builds flows for A ≤ 4.
    The doubling chain `c → 2c` has no such identity: the coefficient 2, though
    prime, satisfies 2 ≢ ±1 (mod 6) and does not divide the odd sides 6n∓1;
    already the FIRST step 2 → 1 carries no proper peel AT ANY scale: the sides
    11 and 13 are prime, the target sides are only 5 and 7. Consequence: the
    SG-chain does NOT build an unconditional supply of flows — a FORGED witness
    (the YM/NS V3 pattern) does not exist in this branch. -/
theorem isEmpty_properCenterPeel_two_one (A : ℕ) :
    IsEmpty (ProperCenterPeel A 2 1) := by
  constructor
  rintro ⟨inS, outS, q, _hq, _hA, hfac, _hsm, _hpos⟩
  cases inS <;> cases outS <;> simp only [sideValue] at hfac <;> omega

/-#############################################################################
  §3. Manifestation law (gated by the witness; the field is NOT decreed)
#############################################################################-/

/-- Absence above `P` manifests arithmetically: at every
    ledger-scale no lower than `P`, everywhere the projection reconciles the
    books, absence shows itself as an unpayable infinite supply of flows. The
    anchor `P ≤ M0` is consumed below only via `le_refl` (Riemann's pattern).
    The causal form: "a refutation is obliged to show itself where the books
    are reconciled" — NOT a statement about the Sophie Germain pairs themselves. -/
def SGAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **SOPHIE GERMAIN MANIFESTATION LAW** — gated by the absence witness.
    The ungated form `∀ P, SGAbsenceManifests P` at P := 0 together with
    the accepted boundary would yield a supply at a resolved scale — a
    contradiction with the green L2 (the exact failure mechanism of the YM/NS
    manifestation candidates). The gate over a green-unpresentable witness is
    what distinguishes this form. THE FIELD IS NOT DECREED — despite the
    POSITIVE heuristic sign (the verdict of §17, see the header). -/
def SGManifestationLaw : Prop :=
  ∀ P : ℕ, SGAbsenceAbove P → SGAbsenceManifests P

/-#############################################################################
  §4. ESSENCE and readable form: a refutation presents an engine
#############################################################################-/

/-- **SG3⁺ — READABLE FORM "refutation = engine":** absence witness
    + law + reconciled books at a scale no lower than P MANIFEST a perpetual
    engine — as an OBJECT, before it is killed by lexRank. -/
theorem sgRefutation_carries_engine
    (hLaw : SGManifestationLaw)
    {P : ℕ} (hAbs : SGAbsenceAbove P)
    {A M0 : ℕ} (hM : P ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw P hAbs A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **SG3 — ESSENCE (mirror of M3 and Riemann's L3):** no engines +
    accepted boundary + manifestation law ⟹ Sophie Germain pairs are unbounded.
    All three hypotheses are consumed FOR REAL: from finiteness the absence
    witness P is extracted; the boundary gives resolution exactly at scale
    M0 := P; the law supplies the family 𝓕 (not ex falso); from the collision an
    engine-WITNESS is built; and it is exactly hNoEngine that kills it. -/
theorem sophieGermainUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SGManifestationLaw) :
    EuclidsPath.SophieGermainBranch.SophieGermainUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_sgAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    sgRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-#############################################################################
  §5. Honesty audits (SG5–SG9)
#############################################################################-/

/-- **SG5 (vacuous reverse side, mirror of M5):** unboundedness ⟹
    the law holds vacuously — the absence gate is empty. The load-bearing side
    is SG3, and it needs the boundary. -/
theorem sgManifestationLaw_of_unbounded
    (H : EuclidsPath.SophieGermainBranch.SophieGermainUnbounded) :
    SGManifestationLaw := fun P hAbs =>
  ((sophieGermainUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **SG6 (exact green characterization, mirror of M6):** the law ⟺ "absence
    above P would freeze every resolving ledger at scales ≥ P".
    The reverse direction is ex falso from ¬resolves (disclosed). The gate
    hypothesis is potentially empty — which is why the characterization does NOT
    collapse into a global freeze (asymmetry with the ungated YM/NS forms). -/
theorem sgManifestationLaw_iff_no_resolution_above_absence :
    SGManifestationLaw ↔
      ∀ P : ℕ, SGAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **SG7 — THE MAIN PRICE AUDIT (mirror of M7):** under the boundary the law ⟺
    unboundedness of Sophie Germain pairs — the fourth field would be exactly of
    SG-conjecture strength. WITHOUT the boundary "law ⟹ unboundedness" does not
    assemble green (SG3 requires the boundary). ⚠️ Here the price is visible:
    unlike Mersenne, the heuristic sign is FOR the right-hand side of this ⟺
    (Hardy–Littlewood), yet the field is still not decreed — the verdict of §17. -/
theorem sgManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    SGManifestationLaw ↔
      EuclidsPath.SophieGermainBranch.SophieGermainUnbounded :=
  ⟨sophieGermainUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   sgManifestationLaw_of_unbounded⟩

/-- Witness type for the bundling audit (subtype — front_pair works with Type). -/
abbrev SGAbsenceWitness : Type := {P : ℕ // SGAbsenceAbove P}

theorem nonempty_sgAbsenceWitness_iff :
    Nonempty SGAbsenceWitness ↔
      ¬ EuclidsPath.SophieGermainBranch.SophieGermainUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (sophieGermainUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_sgAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- The law in Bridge form over the witness type. -/
theorem sgManifestationLaw_iff_bridge :
    SGManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : SGAbsenceWitness => SGAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **SG9 (bundling audit, instantiation of the condemning machine):** the pair
    Bridge∧Impossible ⟺ "there are no absence witnesses" — ONLY the Bridge side
    could be decreed; the Impossible side at resolved scales is the green L2,
    never a decree. -/
theorem sgManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : SGAbsenceWitness => SGAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : SGAbsenceWitness => SGAbsenceManifests W.1)) ↔
      ¬ Nonempty SGAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

/-#############################################################################
  §6. RESTRICT-LAW 3 (mod 4): anti-Mersenne — "two bets staring
      at each other"

  The same front, but over the subfamily of SG-primes with p ≡ 3 (mod 4) —
  exactly the one the branch pearl (`sophieGermain_divides_mersenne`) turns into
  killers of Mersenne primality. The essence of the restrict-law feeds
  `mersenneComposites_unbounded_of_sg`: the front's conclusion — infinitely many
  COMPOSITE M_p — is the composite side of the very quantity whose PRIME side the
  Mersenne front (ch. 43) did not bet on.

  ⚠️ HONEST DISCLOSURE OF THE LAWS' RELATION: the gates differ —
  `SGThreeMod4AbsenceAbove P` is WEAKER than `SGAbsenceAbove P` (it constrains
  only the class 3 mod 4), so the restrict-law is opened by a weaker witness
  and the full-family law does NOT give it directly (that would be strengthening
  the gate in the premise). No implication between the laws in either direction
  is asserted or consumed here — the corollary below is fed ONLY by the restrict-law.
#############################################################################-/

/-- **Absence of Sophie Germain pairs of class 3 (mod 4) above `P`** (Π-witness
    of the restrict-family — the very one that quenches Mersenne primality). -/
def SGThreeMod4AbsenceAbove (P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → (2 * p + 1).Prime → p ≤ P

/-- Plumbing: from boundedness of the restrict-family a witness is extracted. -/
theorem exists_sgThreeMod4Absence_of_not_unbounded
    (h : ¬ EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded) :
    ∃ P : ℕ, SGThreeMod4AbsenceAbove P := by
  unfold EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun p h1 h2 h3 => by
    by_contra hgt
    exact hP p (by omega) h1 h2 h3⟩

/-- **Restrict-domain localization:** every absence bound is ≥ 11 —
    the pair (11, 23) with 11 ≡ 3 (mod 4) green-exists (and indeed
    23 ∣ M₁₁: `mersenne_composite_examples` of the branch). -/
theorem sgThreeMod4AbsenceBound_ge_11 {P : ℕ}
    (hAbs : SGThreeMod4AbsenceAbove P) : 11 ≤ P := by
  have h := hAbs 11 (by norm_num) (by norm_num) (by norm_num : (23 : ℕ).Prime)
  omega

/-- Restrict-absence above `P` manifests arithmetically (the same causal
    form, the same supply object, the anchor via le_refl). -/
def SGThreeMod4Manifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **RESTRICT MANIFESTATION LAW 3 (mod 4)** — gated by ITS OWN absence
    witness (weaker than the full-family one — see the disclosure in the §6 header).
    THE FIELD IS NOT DECREED. -/
def SGThreeMod4ManifestationLaw : Prop :=
  ∀ P : ℕ, SGThreeMod4AbsenceAbove P → SGThreeMod4Manifests P

/-- Readable form of the restrict-front: absence witness + law + reconciled
    books ⟹ engine-WITNESS as an object. -/
theorem sgThreeMod4Refutation_carries_engine
    (hLaw : SGThreeMod4ManifestationLaw)
    {P : ℕ} (hAbs : SGThreeMod4AbsenceAbove P)
    {A M0 : ℕ} (hM : P ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw P hAbs A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **ESSENCE of the restrict-front:** no engines + accepted boundary +
    restrict-law ⟹ SG-primes of class 3 (mod 4) are unbounded. The consumption
    of hypotheses is the same genuine one as in SG3. -/
theorem sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SGThreeMod4ManifestationLaw) :
    EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_sgThreeMod4Absence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    sgThreeMod4Refutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- **ANTI-MERSENNE COROLLARY — "two bets staring at each other":**
    no engines + accepted boundary + restrict-law 3 (mod 4) ⟹ there are
    unboundedly many primes `p` with COMPOSITE `M_p`. The route: the essence of
    the restrict-front gives `SGThreeMod4Unbounded`, and the branch pearl
    (`mersenneComposites_unbounded_of_sg`, Euler–Lagrange) turns each such `p`
    into a killer of `M_p` primality. The conclusion of THIS front feeds the
    COMPOSITE side of the quantity `M_p` — the very one whose PRIME side the
    Mersenne front (ch. 43) did not bet on (the sign of its heuristic is inverted
    in part BECAUSE of this mechanism: p ≡ 3 (mod 4) with prime 2p+1 quenches
    M_p). The infinitude of composite Mersennes in general is OPEN (as is the
    infinitude of primes); here only the SG-route is honestly recorded. -/
theorem mersenneComposites_unbounded_of_noEngine_boundary_and_sgManifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SGThreeMod4ManifestationLaw) :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ¬ (mersenne p).Prime :=
  EuclidsPath.SophieGermainBranch.mersenneComposites_unbounded_of_sg
    (sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

-- Machine-visible purity in the build log
-- (expected [propext, Classical.choice, Quot.sound] — WITHOUT step00FirstCause):
#print axioms sophieGermainUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
#print axioms sgRefutation_carries_engine
#print axioms sgThreeMod4Refutation_carries_engine
#print axioms sgManifestationLaw_iff_unbounded_of_boundary
#print axioms sgAbsenceBound_ge_89
#print axioms isEmpty_properCenterPeel_two_one
#print axioms mersenneComposites_unbounded_of_noEngine_boundary_and_sgManifestation

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
