/-
  LandauEpistemic — EPISTEMIC COMPLEMENT of Landau's 4th problem (primes `n² + 1`).
  Green front: Engine/LandauFront.lean (bridge, residue fact); honesty spine:
  Engine/SideInfinitude.lean (Dirichlet). Epistemic templates: PNPFirstCause,
  TwinNodeEpistemic, LehmerEpistemic; engine template: PolignacManifestationFront.

  WHAT THIS IS. Four layers on top of LandauFront, none solving the open problem:
    (a) GATE CANONISATION: `landau4thUnbounded_iff_infinite` — unboundedness of
        primes `k² + 1` ⟺ infinitude of the set `LandauPrimes`; the red input
        stays exactly ONE, both forms interchangeable;
    (b) EVEN CHANNEL: `landauPrime_even_of_two_lt` (every prime `k² + 1 > 2`
        requires even `k`) and `landau4thUnbounded_iff_even_k` — the gate is
        localised to the even channel (direct arrow via `max N 1`: the witness
        `k = 1` at `N = 0` is odd and is honestly bypassed by an edge shift);
    (c) BRIDGE TO DIRICHLET: `landau_lives_in_dirichlet_class` — Landau primes lie
        in `{2} ∪ {p ≡ 1 mod 4}`, and the enclosing class `1 mod 4` is REALLY
        infinite (the same mathlib-Dirichlet `Nat.forall_exists_prime_gt_and_modEq`
        as in SideInfinitude); plus the divisor wall `landauFactor_mod_four` —
        every odd prime divisor of `k² + 1` is congruent to `1 mod 4` (mathlib
        quadratic reciprocity). Dirichlet gives an infinite enclosing front,
        what is open is precisely the SELECTION within it (marker
        `NoSelectionClaimed` — the same honesty genre as `NoPairingClaimed` on
        the twin sides);
    (d) EPISTEMICS: `InternalisedLandauGround` (ground = gate, beyondOwnHorizon =
        absence witness), `no_internalisedLandauGround`,
        `landauCause_unknowable`; the manifestation law `LandauManifestationLaw`
        (NOT decreed) and the engine fact `landauRefutation_carries_engine`
        of Polignac class.

  HONESTY (mandatory disclosures, CORR accounted for).
  (1) NOT a solution of Landau's 4th problem and NOT Gödel: about the open
      infinitude of primes `n² + 1` NOTHING is asserted (best known — Iwaniec
      1978: infinitely many `n² + 1` with ≤ 2 prime factors, absent here);
      no independence is claimed — only the self-destruction of internal
      self-grounding.
  (2) THE ground/beyondOwnHorizon PAIR IS TAUTOLOGICAL: it is `P ∧ ¬P` in
      witness packaging (Collatz packaging class, NOT pnp class: in
      `InternalisedPNPGround` the contradiction supplies an EXTERNAL green
      pigeonhole `no_fullPayment_of_unboundedSupply`, here — the fields against
      each other). Disclosed machine-wise:
      `internalisedLandauGround_semantically_selfNegating`.
  (3) THE PAYMENT OF SUBSTANCE IS TWO-LAYER, AND BOTH LAYERS ARE WEAKER THAN THE BENCHMARKS:
      * `landauRefutation_carries_engine` — a genuine engine construction
        (the engine-witness as an object via
        `infiniteFlows_in_stableNoEnergy_build_engine`), but GATED by the
        undecreed `LandauManifestationLaw` — Polignac class, weaker than the
        unconditional `nonHalting_carries_perpetual_engine` of Collatz and the
        unconditional pigeonhole `no_fullPayment_of_unboundedSupply` of P/NP;
      * `landau_supply_parityWalled` — an UNCONDITIONAL green wall, but it closes
        only the ODD channel; on the even channel, where the whole open essence
        lives, there is no wall and no supply green.
      Without the engine layer the bundle would degenerate into pure tautology —
      so the manifestation layer (§4) is built in here as a prerequisite of the
      epistemics (§5).
  (4) THE LAW IS NOT DECREED — under a POSITIVE sign of the heuristic
      (Hardy–Littlewood predicts infinitude): the Polignac precedent — a serial
      extension of the decree would devalue the quarantine; Landau does NOT belong
      to the four boundaries of step00FirstCause, and boundaries are NOT added here.
  (5) THERE IS NOTHING TO FORGE: `k² + 1` — values of a quadratic form on the
      WHOLE grid `k`, not a subsequence-chain (like 4c+1 for Mersenne) — a forged
      witness does not exist in this branch for lack of a forging substrate (as
      with the cousins).

  No sorry, no new axiom, no native_decide; the quarantine
  (Engine/CausalClosureAxiom) is NOT imported. The repository taint (47) does NOT change.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LandauEpistemic.lean
-/
import Mathlib
import EuclidsPath.Engine.LandauFront
import EuclidsPath.Engine.SideInfinitude
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath.LandauFront.Epistemic

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-! ## §1. Gate canonisation: unboundedness ⟺ infinitude (🟢) -/

/-- 🟢 **GATE CANONISATION (proven):** `Landau4thUnbounded` ⟺
    `LandauPrimes.Infinite`. Forward arrow — the existing bridge
    `landauPrimes_infinite_of_unbounded`; reverse — finiteness of `Set.Iic` on ℕ:
    if above `N` there are no primes `k² + 1`, the whole set fits under the cap
    `N² + 1`. The red input stays exactly ONE — both forms interchangeable,
    the gate does not split into "related" open inputs. -/
theorem landau4thUnbounded_iff_infinite :
    Landau4thUnbounded ↔ LandauPrimes.Infinite := by
  constructor
  · exact landauPrimes_infinite_of_unbounded
  · intro hInf N
    by_contra h
    push Not at h
    refine hInf ((Set.finite_Iic (N ^ 2 + 1)).subset ?_)
    rintro p ⟨k, rfl, hp⟩
    have hk : k ≤ N := by
      by_contra hgt
      push Not at hgt
      exact h k hgt hp
    have hle : k ^ 2 + 1 ≤ N ^ 2 + 1 := by nlinarith
    exact Set.mem_Iic.mpr hle

/-! ## §2. Even channel: the gate is localised to even `k` (🟢) -/

/-- 🟢 **EVEN CHANNEL (proven):** every prime `k² + 1 > 2` requires
    EVEN `k` — for odd `k` the number `k² + 1` is even and therefore equals `2`
    (reuse `oddLandauPrime_even_k`). -/
theorem landauPrime_even_of_two_lt {k : ℕ} (hp : (k ^ 2 + 1).Prime)
    (h2 : 2 < k ^ 2 + 1) : Even k := by
  rcases Nat.even_or_odd k with he | ho
  · exact he
  · exact absurd (oddLandauPrime_even_k ho hp) (ne_of_gt h2)

/-- 🟢 **GATE ⟺ EVEN GATE (proven):** unboundedness of primes `k² + 1`
    is equivalent to unboundedness over EVEN `k`. The existing residue fact
    ceases to be decoration: the gate's search domain is honestly halved, all
    witnesses above `1` are forced to be even. TECHNIQUE (CORR): the forward arrow
    applies the gate to `max N 1` — at `N = 0` the witness `k = 1` (prime `2`)
    is odd, an edge shift bypasses it without loss of unboundedness. -/
theorem landau4thUnbounded_iff_even_k :
    Landau4thUnbounded ↔
      ∀ N : ℕ, ∃ k : ℕ, N < k ∧ Even k ∧ (k ^ 2 + 1).Prime := by
  constructor
  · intro H N
    obtain ⟨k, hk, hp⟩ := H (max N 1)
    have hN : N < k := lt_of_le_of_lt (le_max_left N 1) hk
    have h1 : 1 < k := lt_of_le_of_lt (le_max_right N 1) hk
    have h2 : 2 < k ^ 2 + 1 := by nlinarith
    exact ⟨k, hN, landauPrime_even_of_two_lt hp h2, hp⟩
  · intro H N
    obtain ⟨k, hk, _, hp⟩ := H N
    exact ⟨k, hk, hp⟩

/-- 🟢 **CLASS `1 mod 4` (proven):** every prime `k² + 1 > 2` is congruent to
    `1` modulo `4` — even `k = j + j` gives `k² + 1 = 4j² + 1`. -/
theorem landauPrime_mod_four {k : ℕ} (hp : (k ^ 2 + 1).Prime)
    (h2 : 2 < k ^ 2 + 1) : (k ^ 2 + 1) % 4 = 1 := by
  obtain ⟨j, hj⟩ := landauPrime_even_of_two_lt hp h2
  have h : k ^ 2 + 1 = 4 * j ^ 2 + 1 := by subst hj; ring
  rw [h, Nat.mul_add_mod]

/-! ## §3. Bridge to SideInfinitude: enclosing Dirichlet class `1 mod 4` (🟢) -/

/-- 🟢 **ENCLOSING CLASS IS UNBOUNDED (proven, REAL Dirichlet):** above any
    `n` there is a prime `p ≡ 1 (mod 4)` — the same mathlib engine
    `Nat.forall_exists_prime_gt_and_modEq` (L-series analytics) as in
    `minusSide_primes_unbounded` in SideInfinitude, with `q := 4`, `a := 1`. -/
theorem onemodfour_primes_unbounded (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ p % 4 = 1 := by
  obtain ⟨p, hgt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (q := 4) (a := 1) (by norm_num) (by decide)
  exact ⟨p, hgt, hp, by simpa [Nat.ModEq] using hmod⟩

/-- 🟢 The same unboundedness in `Set.Infinite` form. -/
theorem onemodfour_primes_infinite :
    {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, hp, hmod⟩ := onemodfour_primes_unbounded B
  have hmem : p ∈ {p : ℕ | p.Prime ∧ p % 4 = 1} := ⟨hp, hmod⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- 🟢 **INCLUSION (proven):** Landau primes lie in `{2} ∪ {p ≡ 1 mod 4}` —
    the enclosing Dirichlet class; the only exception is `2 = 1² + 1`. -/
theorem landauPrimes_subset_onemodfour :
    LandauPrimes ⊆ {2} ∪ {p : ℕ | p.Prime ∧ p % 4 = 1} := by
  rintro p ⟨k, rfl, hp⟩
  rcases Nat.lt_or_ge 2 (k ^ 2 + 1) with h2 | h2
  · exact Set.mem_union_right _ ⟨hp, landauPrime_mod_four hp h2⟩
  · have h : k ^ 2 + 1 = 2 := le_antisymm h2 hp.two_le
    exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr h)

/-- 🟢 **DIVISOR WALL `mod 4` (proven, genuine theory of the form):** every
    ODD prime divisor `q ∣ k² + 1` is congruent to `1` modulo `4` — from
    `q ∣ k² + 1` it follows that `−1` is a square in `ZMod q`, and the mathlib
    quadratic-reciprocity criterion (`ZMod.exists_sq_eq_neg_one_iff`) forbids
    this when `q ≡ 3 (mod 4)`. The whole spectrum of divisors of the form (not
    just the Landau primes themselves) is pinned to the class `1 mod 4` — the
    arithmetic skeleton on which almost-prime results of the Iwaniec type stand. -/
theorem landauFactor_mod_four {q k : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hdvd : q ∣ k ^ 2 + 1) : q % 4 = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h0 : ((k : ZMod q) ^ 2 + 1) = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    have hcast : ((k ^ 2 + 1 : ℕ) : ZMod q) = ((q * t : ℕ) : ZMod q) := by
      rw [ht]
    push_cast at hcast
    rw [ZMod.natCast_self, zero_mul] at hcast
    exact hcast
  have hsq : IsSquare (-1 : ZMod q) := ⟨(k : ZMod q), by linear_combination -h0⟩
  have h3 : q % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  have h2 : q % 2 = 1 := Nat.odd_iff.mp hodd
  omega

/-- 🟢 **"DIRICHLET GIVES THE FILE, BUT NOT THE SELECTION" — EXACT FORM:** the
    Landau primes live in the class `1 mod 4` of the ambient Dirichlet (`⊆`), and
    this class is REALLY infinite (mathlib-Dirichlet). What is open is precisely
    the SELECTION of values `k² + 1` inside the infinite file — Dirichlet does
    not reach the quadratic form (see `NoSelectionClaimed` below). -/
theorem landau_lives_in_dirichlet_class :
    LandauPrimes ⊆ {2} ∪ {p : ℕ | p.Prime ∧ p % 4 = 1} ∧
      {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite :=
  ⟨landauPrimes_subset_onemodfour, onemodfour_primes_infinite⟩

/-- **HONESTY (coverage):** the infinitude of the AMBIENT class `1 mod 4` is
    green (Dirichlet), but it does NOT give infinitude of the SELECTION — the
    primes landing on the quadratic form `k² + 1`. The selection is the whole
    open essence of Landau's 4th problem, and here it is NOT asserted, NOT proven
    and derived from nowhere. The same genre of honesty as `NoPairingClaimed` for
    the twin sides (SideInfinitude) — the marker is intentionally paid for by the
    same truism. -/
abbrev NoSelectionClaimed : Prop := True

theorem noSelectionClaimed : NoSelectionClaimed :=
  EuclidsPath.SideInfinitude.noPairingClaimed

/-! ## §4. Absence witness, manifestation law, engine (🟢-plumbing,
    the law is a gate; a mirror of the cousin family PolignacManifestationFront)

    ⚠️ A chain section (an analogue of Mersenne forging) is intentionally ABSENT
    here: `k² + 1` are values of the form on the whole grid, not a subsequence-
    chain; no forged witness exists for lack of a forging substrate (as with the
    cousins). -/

/-- **Absence of Landau primes above `P`** (Π-witness, mirror of
    `CousinAbsenceAbove`): every `k` with prime `k² + 1` sits no higher than `P`. -/
def LandauAbsenceAbove (P : ℕ) : Prop :=
  ∀ k : ℕ, (k ^ 2 + 1).Prime → k ≤ P

/-- 🟢 Plumbing: from boundedness an absence witness is extracted. -/
theorem exists_landauAbsence_of_not_unbounded (h : ¬ Landau4thUnbounded) :
    ∃ P : ℕ, LandauAbsenceAbove P := by
  unfold Landau4thUnbounded at h
  push Not at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun k hk => by
    by_contra hgt
    exact hP k (by omega) hk⟩

/-- 🟢 Plumbing: gate ⟺ there are no absence witnesses (a witness form of
    negation — it is what pays for the field `beyondOwnHorizon` below). -/
theorem landau4thUnbounded_iff_no_absence :
    Landau4thUnbounded ↔ ∀ P : ℕ, ¬ LandauAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨k, hlt, hp⟩ := hU P
    exact absurd (hAbs k hp) (by omega)
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_landauAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- 🟢 **M8 (localization of the witness domain):** every absence bound ≥ 26 —
    `26² + 1 = 677` is prime (norm_num). The absence witness is green-unpresentable
    in the initial segment. -/
theorem landauAbsenceBound_ge_26 {P : ℕ}
    (hAbs : LandauAbsenceAbove P) : 26 ≤ P :=
  hAbs 26 (by norm_num)

/-- Absence above `P` manifests arithmetically: at every ledger scale no lower
    than `P`, everywhere the projection reconciles the books, absence shows itself
    as an unpayable infinite supply of flows (the object is borrowed from the
    Riemann front — `DeviationFlowSupply`; the L1 substance witness lives THERE
    TOO, `deviationFlowSupply_of_twinBound`, and is NOT re-proven here). -/
def LandauAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **LANDAU MANIFESTATION LAW** — gated by an absence witness (mirror of
    `CousinManifestationLaw`). The ungated form `∀ P, LandauAbsenceManifests P`
    at `P := 0`, together with the accepted boundary, would give a supply at the
    resolved scale — a contradiction with the green
    `no_deviationFlowSupply_at_resolved_scale` (the exact mechanism by which the
    YM/NS manifestation candidates fail). ⚠️ THE FIELD IS NOT DECREED — under a
    POSITIVE sign of Hardy–Littlewood: the Polignac precedent — a serial extension
    of the decree would devalue the quarantine; the uniqueness of the accepted
    boundary is precisely its content. -/
def LandauManifestationLaw : Prop :=
  ∀ P : ℕ, LandauAbsenceAbove P → LandauAbsenceManifests P

/-- 🟢 **"A REFUTATION PRESENTS AN ENGINE" (M3⁺, Polignac-class):**
    absence witness + law + reconciled books at a scale no lower than `P`
    manifest a perpetual engine — as an OBJECT
    (`ConcreteEuclideanEngineWitness`), before being killed by lexRank.
    HONESTY: the construction is genuine (via
    `infiniteFlows_in_stableNoEnergy_build_engine`), but it is GATED by the
    undecreed `LandauManifestationLaw` — a POLIGNAC-CLASS engine fact, weaker than
    the unconditional `nonHalting_carries_perpetual_engine` of Collatz and the
    unconditional pigeonhole `no_fullPayment_of_unboundedSupply` of P/NP. -/
theorem landauRefutation_carries_engine
    (hLaw : LandauManifestationLaw)
    {P : ℕ} (hAbs : LandauAbsenceAbove P)
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

/-- 🟢 **M3 — ESSENCE (mirror of the cousins):** no engines + accepted boundary +
    manifestation law ⟹ Landau gate. All three hypotheses are consumed FOR REAL:
    from boundedness a witness `P` is extracted; the boundary gives resolution
    exactly at the scale `M0 := P`; the law supplies a family (not ex falso); from
    the collision an engine-WITNESS is built; `hNoEngine` kills it. -/
theorem landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LandauManifestationLaw) :
    Landau4thUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_landauAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    landauRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- 🟢 Green carry-through to the programme's goal: the same triple ⟹ the set of
    Landau primes is infinite (composed with the bridge
    `landauPrimes_infinite_of_unbounded`). -/
theorem landauPrimesInfinite_of_noEngine_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LandauManifestationLaw) :
    LandauPrimes.Infinite :=
  landauPrimes_infinite_of_unbounded
    (landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-! ## §5. Epistemics: an internal solution = self-grounding beyond the horizon -/

/-- **Internal self-grounding of the Landau solution.** The field `ground` is the
    gate itself (`Landau4thUnbounded` — the red law of the form; Landau has NO
    boundary in step00FirstCause, and ground is not a decree-projection, as with
    Collatz); the field `beyondOwnHorizon` is an absence witness (a witness form of
    negation via `landau4thUnbounded_iff_no_absence`; both fields are consumed in
    `no_internalisedLandauGround`, the vacuity ban №3 is respected).

    ⚠️ HONEST CAVEAT (mandatory): the pair is TAUTOLOGICAL — it is `P ∧ ¬P` in
    witness packaging (Collatz-class, NOT pnp-class: there the contradiction was
    supplied by an external green pigeonhole). Exposed machine-wise below
    (`internalisedLandauGround_semantically_selfNegating`). The substance is paid
    for NOT by the form of the structure, but by two external layers — the engine
    construction `landauRefutation_carries_engine` (gated by the law, Polignac-
    class) and the unconditional odd-channel wall `landau_supply_parityWalled`;
    both layers are weaker than the reference standards (see the file header). -/
structure InternalisedLandauGround : Prop where
  ground : Landau4thUnbounded
  beyondOwnHorizon : ∃ P : ℕ, LandauAbsenceAbove P

/-- "Internal knowledge of the Landau cause" = internal self-grounding of the solution. -/
abbrev InternalKnowledgeOfLandauCause : Prop := InternalisedLandauGround

/-- 🟢 Self-grounding self-destructs — one line via the plumbing
    `landau4thUnbounded_iff_no_absence` (mirror of `no_internalisedPNPGround`;
    honestly: here the contradiction is supplied by the fields THEMSELVES, see the
    structure caveat). -/
theorem no_internalisedLandauGround : InternalisedLandauGround → False :=
  fun H => by
    obtain ⟨P, hAbs⟩ := H.beyondOwnHorizon
    exact landau4thUnbounded_iff_no_absence.mp H.ground P hAbs

/-- 🟢 **"CANNOT BE KNOWN FROM INSIDE" — THEOREM** (mirror of `collatzCause_unknowable`,
    `pnpCause_unknowable`, `lehmerCause_unknowable`): internal self-grounding of the
    Landau solution is impossible. NOT a statement about the 4th problem itself: the
    gate remains an open red input. -/
theorem landauCause_unknowable : ¬ InternalKnowledgeOfLandauCause :=
  no_internalisedLandauGround

/-- 🟢 **MACHINE HONESTY (tautology exposed):** the structure
    `InternalisedLandauGround` is provably equivalent to the contradictory pair
    "gate ∧ ¬gate" (the reverse arrow is ex falso, honestly). This is WEAKER than
    the pnp-analogue `internalisedPNPGround_semantically_selfNegating`: there the
    equivalence is paid for by an external exact payment law, here — by a direct
    repackaging of the negation. The module's substance lives in §3–§4, not here. -/
theorem internalisedLandauGround_semantically_selfNegating :
    InternalisedLandauGround ↔ (Landau4thUnbounded ∧ ¬ Landau4thUnbounded) := by
  constructor
  · intro H
    refine ⟨H.ground, fun hU => ?_⟩
    obtain ⟨P, hAbs⟩ := H.beyondOwnHorizon
    exact landau4thUnbounded_iff_no_absence.mp hU P hAbs
  · rintro ⟨hU, hnU⟩
    exact (hnU hU).elim

/-- 🟢 **ODD-CHANNEL WALL (unconditional):** an internal inference blind to the
    parity rail — "odd `k` supply primes `k² + 1` unboundedly" — is refuted FOR
    FREE (reuse `oddLandauPrime_even_k`).
    HONESTY: this is an analogue of the P/NP pigeonhole only by GENRE — the wall
    closes ONLY the odd channel; on the even channel, where the whole open essence
    lives, there is no green wall and there cannot be one without solving the
    problem itself. -/
theorem landau_supply_parityWalled :
    (∀ N : ℕ, ∃ k : ℕ, N < k ∧ Odd k ∧ (k ^ 2 + 1).Prime) → False := by
  intro h
  obtain ⟨k, hgt, hodd, hp⟩ := h 1
  have h2 : k ^ 2 + 1 = 2 := oddLandauPrime_even_k hodd hp
  have h3 : 2 < k ^ 2 + 1 := by nlinarith
  exact absurd h2 (ne_of_gt h3)

/-- 🟢 **"THE SOLUTION IS LOCKED BEHIND THE ENGINE" — 3-PRONGED (mirror of
    `twin_no_internal_decision_without_engine`,
    `pnp_no_internal_decision_without_engine`):**
    (1) to REFUTE under the law = to present an engine-witness
        (`landauRefutation_carries_engine`; the price is honestly visible: the law
        `LandauManifestationLaw` is NOT decreed — Polignac-class);
    (2) to SELF-GROUND the solution from inside — self-destructs
        (`no_internalisedLandauGround`);
    (3) the only engine-free path — EXTERNAL ACCEPTANCE of the gate: it entails
        infinitude of Landau primes (`landauPrimes_infinite_of_unbounded`;
        the gate itself is NOT asserted here).
    Neither Gödelian independence NOR a solution of the 4th problem is asserted —
    only: both internal solutions cost a perpetual engine. -/
theorem landau_no_internal_decision_without_engine :
    (∀ P : ℕ, LandauAbsenceAbove P → LandauManifestationLaw →
      ∀ (A M0 : ℕ), P ≤ M0 →
      ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj →
          ConcreteEuclideanEngineWitness A M0) ∧
    (InternalisedLandauGround → False) ∧
    (Landau4thUnbounded → LandauPrimes.Infinite) :=
  ⟨fun _P hAbs hLaw _A _M0 hM proj hres =>
      landauRefutation_carries_engine hLaw hAbs hM proj hres,
   no_internalisedLandauGround,
   landauPrimes_infinite_of_unbounded⟩

/-- 🟢 Final epistemic status of Landau (mirror of
    `pnp_locked_behind_engine_status` — WITHOUT the decree conjunct: the gate is
    NOT accepted, Landau has no boundary and none is added):
    (1) it cannot be decided from inside (theorem);
    (2) the odd channel is walled unconditionally (theorem);
    (3) the engine is forbidden (`no_someConcreteEuclideanEngine`, lexRank);
    (4) law + boundary ⟹ gate (the law is NOT decreed — the whole price is visible);
    (5) the gate is canonized: unboundedness ⟺ infinitude (theorem).
    ENTIRELY GREEN: conjuncts 1–3, 5 are unconditional; 4 is a conditional arrow. -/
theorem landau_locked_behind_engine_status :
    (¬ InternalKnowledgeOfLandauCause) ∧
    ((∀ N : ℕ, ∃ k : ℕ, N < k ∧ Odd k ∧ (k ^ 2 + 1).Prime) → False) ∧
    (¬ SomeConcreteEuclideanEngine) ∧
    (LandauManifestationLaw → TheStrictLastStep00Obligation → Landau4thUnbounded) ∧
    (Landau4thUnbounded ↔ LandauPrimes.Infinite) :=
  ⟨landauCause_unknowable,
   landau_supply_parityWalled,
   no_someConcreteEuclideanEngine,
   fun hLaw hBoundary =>
     landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
       no_someConcreteEuclideanEngine hBoundary hLaw,
   landau4thUnbounded_iff_infinite⟩

/-! ## Axiom audit: the whole module is green (at most the standard triple),
    the quarantine is not imported, the repo taint (47) does NOT change -/
#print axioms landau4thUnbounded_iff_infinite
#print axioms landauPrime_even_of_two_lt
#print axioms landau4thUnbounded_iff_even_k
#print axioms landauPrime_mod_four
#print axioms onemodfour_primes_unbounded
#print axioms onemodfour_primes_infinite
#print axioms landauPrimes_subset_onemodfour
#print axioms landauFactor_mod_four
#print axioms landau_lives_in_dirichlet_class
#print axioms noSelectionClaimed
#print axioms exists_landauAbsence_of_not_unbounded
#print axioms landau4thUnbounded_iff_no_absence
#print axioms landauAbsenceBound_ge_26
#print axioms landauRefutation_carries_engine
#print axioms landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms landauPrimesInfinite_of_noEngine_boundary_and_manifestation
#print axioms no_internalisedLandauGround
#print axioms landauCause_unknowable
#print axioms internalisedLandauGround_semantically_selfNegating
#print axioms landau_supply_parityWalled
#print axioms landau_no_internal_decision_without_engine
#print axioms landau_locked_behind_engine_status

end EuclidsPath.LandauFront.Epistemic
