/-
  YangMillsEpistemic — the EPISTEMIC COMPLEMENT of Yang–Mills (mirror of
  CollatzFirstCause and PNPFirstCause). The branch's green machine:
  Engine/YangMillsFront.lean; the front is discussed in prose/40_YangMills.md.

  WHAT THIS IS. An abstract spectral model (`SpectralModel`) with a question about
  the mass gap (`MassGap`). Refuting the gap is NOT passive: from it an
  engine object is BUILT — a halving ladder (`gaplessLadder_of_not_massGap`,
  exact characterization `gapless_iff_nonempty_ladder`), and this is a genuine
  perpetual engine on ℝ (`not_massGap_carries_real_engine`). On the continuum
  the engine is legal (`perpetualEngine_on_real`) — there is no wall. The wall arises
  when the per-model QUANTIZATION LAW (`QuantizationLaw`) maps energy into
  an ℕ-rank: the ladder becomes an infinite ℕ-descent and burns against
  well-foundedness (`no_quantizedLadder`, EPMI) — the same wall as in
  Collatz ("the non-falling tail") and P/NP ("payment of an unbounded supply").

  HONESTY (mandatory caveats).
  1) This is model-internal epistemics, NOT a solution of the Clay problem and NOT Gödel
     (no incompleteness/fixed point — only well-foundedness):
     neither the existence of a quantum YM theory nor its spectrum is here;
     what is missing is a data anchor (a built spectral model of a genuine
     non-abelian QFT, which mathlib does not have), NOT a Prop that can be
     decreed or proven (audit L9 `quantizationLaw_iff_massGap`).
  2) There is NO decree YM boundary in the repository — intentionally: the trilemma of §7 of the front
     machine-rejected all three forms of the law (`ymLawUniversal_refuted` /
     `ymLawExistential_green` — vacuous / `ymManifestationLaw_refutes_boundary`).
     By the first-cause numbering the fourth slot is taken by collatzBoundary; the YM slot
     (the fifth) is empty forever. That is why the module is ENTIRELY green: the quarantine
     (CausalClosureAxiom) is not imported, the repository taint does not change.
  3) THE MAIN DIFFERENCE FROM BOTH REFERENCE POINTS: the green collapse L9
     (`quantizationLaw_iff_massGap`) together with `not_massGap_iff_nonempty_ladder`
     semantically fold the conjunction ground + beyondOwnHorizon into
     `MassGap S ∧ ¬ MassGap S`. For Collatz/P-NP the sides were NOT green
     equivalent to the goal and its negation — for YM they are equivalent. The payment is genuine
     (an engine, not an unfolding of the negation), but the semantic
     tautologization via L9 is the signature feature of YM, and it is also the reason
     why the only exit of conjunct (3) of the fork is an external data anchor,
     not a decree.
  4) The quantitative "hero" massGap_lower_bound (claim: rank boundedness
     by B at energies ≤ E₀ would give Δ ≥ E₀/2^(B+1)) is NOT added here: the lemma
     is FALSE, the skeptic refuted it with a counterexample (Energy = {0, E₀/8, E₀}, B = 1,
     every valid Δ ≤ E₀/8 < E₀/4). The honest replacement is CHAIN-BOUND (the last
     section): every halving chain in the spectrum has length ≤ the rank of the start, and
     with rank bounded by B at energies ≤ E₀ — length ≤ B. This is a direct
     consequence of the strict rank descent; a lower bound on Δ does NOT follow from it —
     for that one needs levels at EVERY intermediate scale (halving density),
     which a bounded rank does not supply.
-/

import EuclidsPath.Engine.YangMillsFront
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.YangMills.Epistemic

open EuclidsPath.UniversalEngine

/-! ## Carriers: refuting the gap BUILDS an engine (🟢, genuine constructions) -/

/-- **The ladder is a genuine perpetual engine on ℝ (without a single hypothesis beyond
    the ladder itself).** The witness is `D.seq` itself: halving + positivity give
    strict descent. The antecedent is GREEN-inhabited (`cookedLadder`), `False.elim`
    is not used — this is a carrier in the exact sense of `PerpetualEngine`. On ℝ
    there is NO contradiction (`perpetualEngine_on_real`): the engine forbids not
    the continuum, but quantization. -/
theorem ladder_carries_real_engine {S : SpectralModel} (D : GaplessLadder S) :
    PerpetualEngine (· < · : ℝ → ℝ → Prop) :=
  ⟨D.seq, fun n => by
    have h := D.halving n
    have hp := D.pos (n + 1)
    show D.seq (n + 1) < D.seq n
    linarith⟩

/-- **"Refuting the gap builds an engine" (genuine carrier):** ¬gap →
    ladder (`gaplessLadder_of_not_massGap`, the choice is honestly visible) → perpetual
    ℝ-engine. Mirror of the zero extraction `offCriticalZero_of_not_RH`: for YM
    refuting the goal PRESENTS an object, rather than merely negating. -/
theorem not_massGap_carries_real_engine {S : SpectralModel}
    (h : ¬ MassGap S) : PerpetualEngine (· < · : ℝ → ℝ → Prop) :=
  ladder_carries_real_engine (gaplessLadder_of_not_massGap h)

/-- **Exact characterization of the carrier:** refuting the gap ⟺ existence of
    a ladder (composition of L1 `not_massGap_iff_gapless` and L4
    `gapless_iff_nonempty_ladder`). It is exactly this equivalence (together with L9)
    that pays for and exposes the semantic tautologization of the conjunction below. -/
theorem not_massGap_iff_nonempty_ladder (S : SpectralModel) :
    ¬ MassGap S ↔ Nonempty (GaplessLadder S) :=
  (not_massGap_iff_gapless S).trans (gapless_iff_nonempty_ladder S)

/-! ## The quantization law turns the ℝ-engine into a forbidden ℕ-engine (🟢) -/

/-- **Engine carrier under the law (term-genuine, antecedent jointly
    refuted).** The witness is built WITHOUT `False.elim`: `f t := rank(ladder t)`,
    strict rank descent is the law on a halving pair. HONESTY (mandatory,
    the standard `internalisedPNPGround_builds_engine` from PNPFirstCause): the pair of
    hypotheses (law + ladder) is JOINTLY refuted in the repository
    (`no_quantizedLadder`), so LOGICALLY the lemma is a repackaging of the killer;
    "genuineness" is a property of the TERM (the witness rank∘ladder), not of the logical
    content. This is a term-genuine analogue under a refuted antecedent — NOT an
    exact analogue of Collatz's `nonHalting_carries_perpetual_engine`, where the
    antecedent is open. -/
theorem quantizedLadder_carries_perpetual_engine {S : SpectralModel}
    (hQ : QuantizationLaw S) (D : GaplessLadder S) :
    PerpetualEngine (· < · : ℕ → ℕ → Prop) := by
  obtain ⟨rank, hrank⟩ := hQ
  exact ⟨fun t => rank ⟨D.seq t, D.mem t, D.pos t⟩,
    fun t => hrank ⟨D.seq t, D.mem t, D.pos t⟩
      ⟨D.seq (t + 1), D.mem (t + 1), D.pos (t + 1)⟩ (D.halving t)⟩

/-- **Ladder + law ⟹ contradiction — the SECOND route (through the universal
    engine lattice):** the carrier above burns against
    `no_perpetual_engine_on_nat`. The first route is `no_quantizedLadder`
    (directly through EPMI `no_infinite_descent`); the content is the same, what is new is
    the `PerpetualEngine` language, shared with Collatz and P/NP. -/
theorem quantizedLadder_impossible_via_engine {S : SpectralModel}
    (hQ : QuantizationLaw S) (D : GaplessLadder S) : False :=
  no_perpetual_engine_on_nat (quantizedLadder_carries_perpetual_engine hQ D)

/-! ## Model: an internal decision = self-grounding beyond one's own horizon -/

/-- **Internal self-grounding of the YM decision**: carries the per-model quantization
    law (`ground`; per-model — because the universal form is machine-
    refuted, `ymLawUniversal_refuted`) AND the refutation of the gap
    (`beyondOwnHorizon`) — "to reach with one's gaze" past the horizon of one's own
    law. MANDATORY DISCLOSURE (the difference from both reference points): through L9
    `quantizationLaw_iff_massGap` and `not_massGap_iff_nonempty_ladder` the conjunction
    is semantically ⟺ `MassGap S ∧ ¬ MassGap S` — for Collatz/P-NP the sides were not
    green equivalent to the goal and its negation, for YM they are equivalent. The payment
    is genuine (an engine, not an unfolding of the negation): the contradiction
    is supplied by the descent construction (the ladder from `beyondOwnHorizon` + the rank
    ℕ-descent from `ground`), but the semantic tautologization via L9 is
    the signature feature of YM, and it is also the reason why the only exit is
    an external data anchor, not a decree. -/
structure InternalisedYMGround (S : SpectralModel) : Prop where
  ground : QuantizationLaw S
  beyondOwnHorizon : ¬ MassGap S

/-- "Internal knowledge of the YM cause" = internal self-grounding of the decision. -/
abbrev InternalKnowledgeOfYMCause (S : SpectralModel) : Prop :=
  InternalisedYMGround S

/-! ## Core: self-grounding self-destructs = the perpetual-engine wall (🟢) -/

/-- Self-grounding self-destructs: `beyondOwnHorizon` builds the ladder
    (genuine carrier), `ground` quantizes it into a forbidden ℕ-engine —
    it burns against `no_perpetual_engine_on_nat`. The payment is an engine construction,
    the same wall as `no_fullPayment_of_unboundedSupply` in P/NP. -/
theorem no_internalisedYMGround {S : SpectralModel} :
    InternalisedYMGround S → False :=
  fun H => quantizedLadder_impossible_via_engine H.ground
    (gaplessLadder_of_not_massGap H.beyondOwnHorizon)

/-- **"CANNOT BE KNOWN FROM INSIDE" — THEOREM** (mirror of `collatzCause_unknowable`,
    `pnpCause_unknowable`, twin-`cause_unknowable`): internal self-grounding of the
    YM decision is impossible in any spectral model. NOT a statement about
    a genuine YM theory (see the header): the frame layer is abstract. -/
theorem ymCause_unknowable {S : SpectralModel} :
    ¬ InternalKnowledgeOfYMCause S :=
  no_internalisedYMGround

/-- **Ground cannot be supplied universally** (that is why it is per-model): the universal
    quantization law is machine-refuted — witness `cookedGapless` +
    `cookedLadder` (verbatim `ymLawUniversal_refuted`, mirror of
    Collatz's `ropeLaw_universal_refuted`). The decree door for ground is closed
    by a forged refutation, not by agreement. -/
theorem ymGround_universal_refuted :
    ¬ ∀ S : SpectralModel, QuantizationLaw S :=
  ymLawUniversal_refuted

/-- SUBSTANTIVE DICHOTOMY (without ex falso in the statement, mirror of
    `unknowable_or_collatz_fails`): either the cause is unknowable from inside, or
    there is no gap in the model. The left disjunct is a theorem. -/
theorem unknowable_or_no_massGap (S : SpectralModel) :
    (¬ InternalKnowledgeOfYMCause S) ∨ ¬ MassGap S :=
  Or.inl ymCause_unknowable

/-! ## Summaries: the decision is locked behind the engine (🟢) -/

/-- **"THE DECISION IS LOCKED BEHIND THE ENGINE" — 3-fork (mirror of
    `collatz_no_internal_decision_without_engine` /
    `pnp_no_internal_decision_without_engine`):**
    (1) REFUTING the gap under the law = presenting an ℕ-engine (the ladder from
        the refutation + rank descent) — but it is forbidden
        (`no_perpetual_engine_on_nat`); without the law the carrier lives only on ℝ,
        where the engine is legal;
    (2) SELF-GROUNDING the decision from inside — self-destructs
        (`no_internalisedYMGround`);
    (3) the per-model law DECIDES the question ⟺ it IS the question:
        `quantizationLaw_iff_massGap` is green and WITHOUT any boundary — that is why
        the decree door is impossible honestly, the only entrance of the conjunct is
        an external data anchor (the real YM spectrum outside mathlib).
    Neither Gödelian independence nor a Clay solution is asserted — only:
    both internal decisions cost a perpetual engine. -/
theorem ym_no_internal_decision_without_engine (S : SpectralModel) :
    (QuantizationLaw S → ¬ MassGap S → PerpetualEngine (· < · : ℕ → ℕ → Prop)) ∧
    (InternalisedYMGround S → False) ∧
    (QuantizationLaw S ↔ MassGap S) :=
  ⟨fun hQ hNo =>
      quantizedLadder_carries_perpetual_engine hQ (gaplessLadder_of_not_massGap hNo),
   no_internalisedYMGround,
   quantizationLaw_iff_massGap S⟩

/-- The final epistemic status of the YM horizon (mirror of
    `pnp_locked_behind_engine_status` — WITHOUT the decree conjunct: the YM decree slot
    is empty by the trilemma; and mirror of `collatz_open_status` — with the conjunct of
    the refuted universal law): the universal ground is REFUTED /
    internal knowledge is impossible / the per-model law entails the gap (hero, conditionally)
    / the forged witnesses of both sides are alive / the ℕ-engine is forbidden. ENTIRELY
    green; the Clay problem remains open 🔴 — here only the epistemics of its
    horizon. -/
theorem ym_locked_behind_engine_status (S : SpectralModel) :
    (¬ ∀ S' : SpectralModel, QuantizationLaw S') ∧
    (¬ InternalKnowledgeOfYMCause S) ∧
    (QuantizationLaw S → MassGap S) ∧
    Gapless cookedGapless ∧
    MassGap cookedGapped ∧
    ¬ PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  ⟨ymGround_universal_refuted,
   ymCause_unknowable,
   massGap_of_quantizationLaw S,
   cookedGapless_gapless,
   cookedGapped_massGap,
   no_perpetual_engine_on_nat⟩

/-! ## An honest quantitative bound: chain-bound instead of the false massGap_lower_bound (🟢)

    The skeptic refuted the claim "rank boundedness ⟹ Δ ≥ E₀/2^(B+1)"
    with the counterexample Energy = {0, E₀/8, E₀} (rank(E₀) = 1, rank(E₀/8) = 0 —
    the law holds, the rank is bounded by B = 1, but a valid Δ ≤ E₀/8 < E₀/4).
    The error in the claim: a halving chain from E₀ downward requires levels at EVERY
    intermediate scale (this is Gapless), and a bounded rank does not supply them.
    The HONEST content of the strict rank descent is a bound on CHAIN LENGTH, and only
    it: finite halving chains in a quantized spectrum are no longer than the rank of the
    start. Nothing is asserted here about the magnitude of Δ. -/

/-- **A finite halving chain in the spectrum**: `L` steps over positive
    states, each step at least a halving of the energy
    (`2·c(i+1) ≤ c(i)`; the same relation as in `GaplessLadder.halving` and in
    the antecedent of `QuantizationLaw`). The tail of `c` beyond `L` is free —
    only the first `L` steps form the chain. -/
def IsHalvingChain {S : SpectralModel} (L : ℕ) (c : ℕ → PositiveState S) : Prop :=
  ∀ i < L, 2 * ((c (i + 1) : ℝ)) ≤ ((c i : ℝ))

/-- **CHAIN-BOUND (general form): length ≤ rank of the start.** Every rank
    function with strict descent on halving pairs (exactly the field `QuantizationLaw`)
    drops by at least 1 at each step of the chain, so `L` steps require
    a start rank ≥ `L`. A direct consequence of the well-foundedness of ℕ — the same
    wall as `no_quantizedLadder`, but in a finite, quantitative form.
    For the canonical rank of a gapped model (`quantizationLaw_of_massGap`,
    rank = `Nat.log 2 ⌊E/Δ⌋₊`) this gives "length ≤ log₂ of the start in units of Δ" —
    but the canonical rank is circular in Δ, so the abstract
    form is exported. -/
theorem halvingChain_length_le_rank {S : SpectralModel}
    {rank : PositiveState S → ℕ}
    (hrank : ∀ x y : PositiveState S, 2 * (y : ℝ) ≤ (x : ℝ) → rank y < rank x)
    {L : ℕ} {c : ℕ → PositiveState S} (hc : IsHalvingChain L c) :
    L ≤ rank (c 0) := by
  have key : ∀ i, i ≤ L → rank (c i) + i ≤ rank (c 0) := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ n ih =>
        intro hn
        have hdrop : rank (c (n + 1)) < rank (c n) :=
          hrank (c n) (c (n + 1)) (hc n (Nat.lt_of_succ_le hn))
        have hprev := ih (Nat.le_of_succ_le hn)
        omega
  have := key L le_rfl
  omega

/-- **CHAIN-BOUND (CORR-replacement form): start ≤ E₀ and rank ≤ B at energies ≤ E₀
    ⟹ length ≤ B.** Exactly the honest replacement of the false `massGap_lower_bound`
    that the skeptic's verdict demanded: "every halving chain in the spectrum
    starting at energy ≤ E₀ has length ≤ B". NOT a lower bound on Δ (it is
    refuted — see the section header): a bounded rank cuts the LENGTH of the descent,
    not the depth of the spectrum. -/
theorem halvingChain_length_le_of_rank_bound {S : SpectralModel}
    {rank : PositiveState S → ℕ}
    (hrank : ∀ x y : PositiveState S, 2 * (y : ℝ) ≤ (x : ℝ) → rank y < rank x)
    {E₀ : ℝ} {B : ℕ}
    (hB : ∀ x : PositiveState S, (x : ℝ) ≤ E₀ → rank x ≤ B)
    {L : ℕ} {c : ℕ → PositiveState S} (hc : IsHalvingChain L c)
    (h0 : ((c 0 : ℝ)) ≤ E₀) : L ≤ B :=
  le_trans (halvingChain_length_le_rank hrank hc) (hB (c 0) h0)

/-- **Chain-bound in the language of the red input:** the quantization law (D5, per-model
    🔴 input) supplies a rank function bounding the LENGTH of every finite
    halving chain by its value at the start. A finite mirror of
    `no_quantizedLadder`: an infinite ladder yields chains of every length and
    therefore burns; a finite chain does not burn, but receives an honest ceiling. -/
theorem quantizationLaw_chain_bound {S : SpectralModel}
    (hQ : QuantizationLaw S) :
    ∃ rank : PositiveState S → ℕ,
      ∀ (L : ℕ) (c : ℕ → PositiveState S), IsHalvingChain L c → L ≤ rank (c 0) := by
  obtain ⟨rank, hrank⟩ := hQ
  exact ⟨rank, fun _ _ hc => halvingChain_length_le_rank hrank hc⟩

/-! ## Axiom audit: the whole module is green (the standard triple), the repo taint does NOT change -/
#print axioms ladder_carries_real_engine
#print axioms not_massGap_carries_real_engine
#print axioms not_massGap_iff_nonempty_ladder
#print axioms quantizedLadder_carries_perpetual_engine
#print axioms quantizedLadder_impossible_via_engine
#print axioms no_internalisedYMGround
#print axioms ymCause_unknowable
#print axioms ymGround_universal_refuted
#print axioms unknowable_or_no_massGap
#print axioms ym_no_internal_decision_without_engine
#print axioms ym_locked_behind_engine_status
#print axioms IsHalvingChain
#print axioms halvingChain_length_le_rank
#print axioms halvingChain_length_le_of_rank_bound
#print axioms quantizationLaw_chain_bound

end EuclidsPath.YangMills.Epistemic
