/-
  Root module `Euclids-path`. Imports go IN THE ORDER OF THE PROOF'S PATH
  (Euclid's engine → its laws → reduction to twins → attack lines → final node SNOL).

  Path map: prose/00_ProofPath.md. Paired prose for each module — prose/NN_*.md.

  Status legend:
    * proven modules — without `sorry` (standard axioms);
    * the single open goal — `Step00.twin_prime_conjecture` (= the final node SNOL);
    * the single explicit input to closure — `SNOL.SNOLInput` (also `ToTwins`-`H`).
  `sorry` cannot be forged: a "green" file = the genuinely verified part.
-/

-- 00. Foundations: goal and base definitions (TwinLowers, IsTwinCenter)
import EuclidsPath.Step00_Overview

-- I. Euclid's engine and its laws (atomic, proven)
import EuclidsPath.Engine.EPMI              -- impossibility of a perpetual engine
import EuclidsPath.Engine.Carrier           -- shared gcd ∣ 2 (carrier of two)
import EuclidsPath.Engine.TwoGap            -- XY−ZW=2 (conservation of the two, 1st law)
import EuclidsPath.Engine.Descent           -- strict descent + boundary-law
import EuclidsPath.Engine.Irreversibility   -- will not turn back / asymmetry / turn⇒halt (2nd law)
import EuclidsPath.Engine.NoBackward        -- the diagonal vanishes (exclusivity)
import EuclidsPath.Engine.Squeeze           -- cubic squeeze (short train)
import EuclidsPath.Engine.BK                -- bounded additive cycle
import EuclidsPath.Engine.Cycle             -- factor-repeat rigidity, cross-side fuel

-- II. Reduction of the twin conjecture to the block core
import EuclidsPath.Engine.NonCover          -- survivor ⇒ twin; infinite_of_unbounded_centers
import EuclidsPath.Engine.TwoTransport      -- twin_prime_conjecture_of_blocks

-- III. Attack lines on the estimate (studied along the way; hit the parity wall)
import EuclidsPath.Engine.FourCorner        -- N₃₃<N₀₀ from four-corner + side-corner
import EuclidsPath.Engine.ModelFourCorner   -- 20·C(n,6) ≤/< C(n,3)² (model, strict)
import EuclidsPath.Engine.RealFourCorner    -- exact decomposition of the remainder
import EuclidsPath.Engine.ToTwins           -- twin_primes_of_four_corner (conditional on H)
import EuclidsPath.Engine.FiniteContradiction -- finite ∧ H ⇒ False (3 routes by contradiction)
import EuclidsPath.Engine.PaymentLedger     -- channel/tax/shifted-primorial/Y_A (payment law)

-- IV. Final node: the single open lemma
import EuclidsPath.Engine.SNOL              -- rank descent → rank-1 → shifted-neighbour (SNOL)
import EuclidsPath.Engine.OldPeel           -- SNOL unfolds into old-peel ⇒ EPMI contradiction
import EuclidsPath.Engine.NOPSL             -- NOPSL: no old-peel sink ⇒ twin sink (closure)
import EuclidsPath.Engine.Regeneration      -- Old-Peel Regeneration: dichotomy Ω_A (cases 1–3)
import EuclidsPath.Engine.Residuals         -- Step00 residuals: start (primorial), sink⇒twin, height
import EuclidsPath.Engine.RigidClose        -- rigid-closure: reaches_twin without a cycle + cofactor_is_center
import EuclidsPath.Engine.CleanGraph        -- clean/boundary split: clean-sink ⟹ twin above M₀ (correction)
import EuclidsPath.Engine.BoundaryDecomp    -- BoundaryExit decomposition + global absorber node
import EuclidsPath.Engine.PumpFinal         -- pump (conditional) + EPMI break on a self-loop
import EuclidsPath.Engine.PumpStanding      -- pump v2 (two-token standing cycle) + EPMI break remains
import EuclidsPath.Engine.RiemannBranch     -- side branch: RH by contradiction through the engine (conditional)
import EuclidsPath.Engine.RiemannLiouville  -- RH via Liouville-equivalence (λ=(−1)^rank)
import EuclidsPath.Engine.ProductHall       -- ProductHall/Steering pump (4-case logic, without circular payment)
import EuclidsPath.Engine.SeparatingScale   -- separating scale: ¬ProductHall by pure arithmetic (node closed)
import EuclidsPath.Engine.RankDescent       -- energy-defect trichotomy + finite product-rank descent
import EuclidsPath.Engine.ProductCore       -- corrected product-core: 3 defects closed by theorems
import EuclidsPath.Engine.CarrierBridge     -- the last link: carrier is infinite; input = FactorizationData
import EuclidsPath.Engine.MkNode            -- mkNode: RankNode from a composite side (arithmetic, proven)
import EuclidsPath.Engine.LabelledFanIn     -- labelled fan-in: König PROVEN, SNOL reduced (v2→v4)
import EuclidsPath.Engine.AtomicSNOL         -- post-audit: legal subtype (no hAll) + SNOL-free atomic + SNOLDeriv (R8 = red line)
import EuclidsPath.Engine.ConcreteComponents -- discharge active/old-peel components from separating scale; localization of the counting wall
import EuclidsPath.Engine.BadCoverDescent    -- bypass of the counting wall: bad-cover finite descent (conditional reduction, R3 = new red line)
import EuclidsPath.Engine.ObstructionClosure -- abstract well-founded obstruction-engine; inputs are NOT instantiable (SNOL.bad — counting)
import EuclidsPath.Engine.ManyUnresolved     -- many-unresolved collision route: combinatorics proven, U4-terminal is circular
import EuclidsPath.Engine.HigherEnergy       -- weighted debt energy: a real well-founded engine; input = step00_promotion_is_weightedDebtReplacement
import EuclidsPath.Engine.HigherTower        -- Euclidean Tower: fixed-center BadTower is VACUOUS; moving tower = orientation wall
import EuclidsPath.Engine.EngineTower        -- EngineTower without traversal: the recurrence branch is ALSO vacuous; escape/collision = counting wall
import EuclidsPath.Engine.ParityBarrier       -- the parity wall as a THEOREM: a finite-sieve does not certify twin; intersection requires cofinal
import EuclidsPath.Engine.ReverseTower        -- reverse engine: ancestor tree + barrier (abstract no-go); Step00-bridges = wall
import EuclidsPath.Engine.AboveConflict       -- conflict in "Above": order-logic is trivial; step00_forces_above_conflict is trapped (machine-wise)
import EuclidsPath.Engine.JumpBarrier          -- jump/cut-barrier: paid jump + cofinal cut-pigeonhole (proven); force-ray/barrier = inputs (wall)
import EuclidsPath.Engine.PaidDynamics         -- paid dynamics: no free inertia/acceleration/cloning (proven); regeneration-to-close = SNOL wall
import EuclidsPath.Engine.ClosedUniverse       -- the engine does not leave the universe: universe-preservation + closed-paid no-run (proven); promotion_paid_or_closes = wall
import EuclidsPath.Engine.BoundaryDefectPayment -- boundary-defect: extraction of SmallPrimeDefect + impossibility of no-tax payment (proven); input = dichotomy cycle∨payment
import EuclidsPath.Engine.BoundaryLedgerCollision -- ledger-collision: pigeonhole + burning the payment ⟹ cycle (proven); input = collision-resolve
import EuclidsPath.Engine.ConcreteStep00Graph  -- CONCRETE graph 6m±1 (not the abstract σ); lexRank height PROVEN (drops on absorb); remainder = ledger/family/resolve
import EuclidsPath.Engine.TwinNodeEpistemic -- 🟢 epistemic complement of the NODE: refuting twins = an unconditional supply (twinBound_carries_unbounded_supply) ⟹ an engine in a stable universe; strict narrowing of the node to A ≥ 5; twinNode_unknowable; taint does not grow
import EuclidsPath.Engine.TwinScaleAdvances -- 🟢 scale advances of the node: small scale A ≤ 4 is dead for ALL bases M0 ≥ 1 (no_projection_resolves_at_smallScale_allM0, 5-adics+pigeonhole); a growing separating scale (exists_growing_separating_scale, Bertrand+primorial, step (1) of the plan §29.6); the §29.5 barrier is machine-visible (fixedWindow_factorization_impossible_at_separating_scale); skeleton bridge BoundaryDecomp↔CarrierBridge; taint does not grow
import EuclidsPath.Engine.RiemannEngine        -- RH→OffCriticalZero→Engine (pure form); bridges = inputs; RH is not proven
import EuclidsPath.Engine.RiemannImpossibleEngine -- RH via an impossible closed-paid engine: no_riemannEngineFactory is UNCONDITIONAL; input = strip-bridge
import EuclidsPath.Engine.RiemannImpossibleEngineOff -- OffCritical version: removes TrivialBelowZeroClassification; the SINGLE input = OffCriticalRiemannEngineBridge
import EuclidsPath.Engine.RankJumpBridge        -- rank/parity bridge (Liouville λ=(−1)^Ω ↔ factory): everything AROUND the node is proven; §4 ban on cheating; input = RankJumpLocalization
import EuclidsPath.Engine.DichotomyEngine       -- UNIFICATION: Close∨paid-step ⟹ Close is inevitable (close_forced); all cheating regimes absorbed; input = the local dichotomy
import EuclidsPath.Engine.DissipativeCascade    -- cascade-certificate (Step00/RH/NS-analogy): capacity/overflow decomposition of the Liouville node; ℝ vs ℕ warning
import EuclidsPath.Engine.NavierStokes          -- the NS equation ITSELF (PDE-predicate, mathlib fderiv/gradient/∫): momentum+incompressible; zero-solution; cascade-linkage
import EuclidsPath.Engine.RiemannRankProjection -- live node No. 8 of the RH-branch: strict+gradual decomposition unpaired_gives_jump (first-crossing PROVEN); junction with TwinCarrierPairing
import EuclidsPath.Engine.RiemannTrivialZeros -- INPUT No. 1 CLOSED: classification of zeros Re≤0 PROVEN (functional equation); RH is now conditional ONLY on EngineBridge
import EuclidsPath.Engine.RiemannRankProjectionAudit -- ⚠️ vacuity No. 2: the goal of route No. 8 is not anchored; the honest wall = ¬LiouvilleViolation; window-bookkeeping closed
import EuclidsPath.Engine.RiemannTwoTransportFront -- input No. 1 in two-transport form: split+realization+builder; HONESTY: coherent bridge ⟺ RH (circularity is inherited)
import EuclidsPath.Engine.RiemannArithmeticTwoTransport -- NON-engine goal: qrs = abv + 2 (gap 2 proven); HONESTY: with a free anchor both inputs = a single question AdmissibleAtomExists
import EuclidsPath.Engine.RiemannSpectralAnchorAudit -- collapse audit formalized; Prop-non-vacuity — the wrong criterion (proven); the corrected front = a data-anchor with a spectral invariant
import EuclidsPath.Engine.MersenneBranch -- Mersenne: embedding 2^p−1 = 6m_p+1 + twin-criterion; HONESTLY: Mersenne-twins ⟹ twins (NOT the other way around!)
import EuclidsPath.Engine.MersennePaymentConflict -- payment route: sound-ledger + pressure ⟹ ∞ Mersenne-twins ⟹ TwinLowers.Infinite; HONESTY: for the canonical ledger pressure = a consequence
import EuclidsPath.Engine.MersennePeelPressure -- pressure splitting: coverage+payment-law, then debt+realization; chains up to TwinLowers.Infinite; canonical collapse = honesty
-- COLLATZ (grounded on the same first cause; boundary = the FOURTH field of step00FirstCause, §18):
import EuclidsPath.Engine.CollatzEngine     -- Collatz: the strict law is VIOLATED (the odd step raises the height, no Lyapunov); even_marginal/odd_accel_ascends/not_descent_on_odd 🟢
import EuclidsPath.Engine.CollatzFuel       -- Collatz: fuel is finite ON AVERAGE (drift ×0.864), but there is NO monotone height (k=1 at n≡1 mod 4 grows it); no_monotone_height 🟢
import EuclidsPath.Engine.CollatzTugOfWar   -- Collatz: rope vs engine, window_budget ⟹ descent when it prevails; HERO reaches_one_of_countingLaw (per-n, conditional); the universal rope law is REFUTED 🟢 (not_ropeCountingLaw_27, ropeLaw_universal_refuted — witness n=27); refuting the conjecture = a perpetual engine 🟢
import EuclidsPath.Engine.CollatzFirstCause -- 🟢 POST-MORTEM of the decree: the fourth boundary WAS TAKEN AND REMOVED (the tripwire fired — the law is false, the decree overpaid into falsehood); the trilemma closed by a forged refutation (as with YM); epistemics survived (collatzCause_unknowable, collatz_open_status); the Collatz conjecture 🔴 open
import EuclidsPath.Engine.LocalPNPNode -- strict local P/NP-node + a concrete instantiation (at A≤4 incompressibility is UNCONDITIONAL); scope guard: NOT the classical P/NP
import EuclidsPath.Engine.ClassicalPNPBridge -- bridge to the classical P/NP: the carrier field = extraction of a local resolver from a P-decider; HONESTY: the frame is abstract (trivialFrame separates for free)
import EuclidsPath.Engine.CanonicalSelfReduction -- fuel-protocol self-reduction: run/run_done closed GENERICALLY (termination proven); FaithfulPFrame cuts off trivialFrame
import EuclidsPath.Engine.RiemannLayerBoxFront -- layerbox-series (25): residue-tables/move-algebra/blocker-cores; HONESTLY: mod-6 arithmetic + generic assemblies are proven, the rest — scaffolds
import EuclidsPath.Engine.RiemannTerminalRankFront -- terminal/rank-flow (18); HONESTLY: target_of_noZeros — a consequence as an INPUT; inert firewalls are flagged
import EuclidsPath.Engine.MersenneForwardFront -- Mersenne-forward (34); ATTENTION: the late noEngine-packages are UNINHABITED (a free witness) — the headline-theorems are vacuous, disclosed
import EuclidsPath.Engine.ClassicalFrontierRoutes -- P/NP-front (42); the false falseDecider removed; ~30 slogans = True; input-repackagings are flagged
import EuclidsPath.Engine.RankClosureFront -- rank-closure (6); the separation is entirely conditional on an unbuilt witness
import EuclidsPath.Engine.FiniteKnowledgeBarrier -- STRICTLY: a finite system knows almost nothing about twins (purity of classes, propext-only); the two walls — one nature
import EuclidsPath.Engine.RiemannDualEngineFront -- dual route (3): synchronization of payments phantom/genuine, meeting⟺rank change, counting bridge twins↔meetings↔zeros; HONESTLY: all laws — field-inputs, the bridge counts NON-trivial (not off-critical) zeros
import EuclidsPath.Engine.RiemannManifestationFront -- GREEN Riemann chain of the first cause: the manifestation law of deviations + impossibility at resolved scales (L2) + essence-lemma (L3) + audits (law⟺RH UNDER the boundary, L7)
import EuclidsPath.Engine.RiemannLawEpistemic -- 🟢 epistemics of the manifestation law: self-grounding self-destructs (riemannCause_unknowable); a deviation with the books reconciled builds an engine (deviation_carries_engine_at_resolved_scale); the boundary is alive — epistemics about the impossibility of INTERNAL grounding
import EuclidsPath.Engine.RiemannSpectralAnchor -- Hilbert–Pólya anchor in two layers: 🟢 SpectralRealisation ⟹ RH (a verbatim bridge to mathlib-RH) + AUDIT: realization ⟺ RH for free (spectralRealisation_iff — the renaming is disclosed) ⟹ the substantive layer must carry an OPERATOR — 🔴 OperatorSpectralAnchor (self-adjointness+spectrum, mathlib-structures); taint does not grow
import EuclidsPath.Engine.PNPRankPaymentFront -- GREEN P/NP-chain: NP = full payment of rank certificates, P = rank-fast passage; SEPARATION AT A ≤ 4 UNCONDITIONAL; the trilemma of candidates for the third decree field proven (two refutable, the third vacuous); VACUITY No. 4: decider-gated extraction-fronts are classically empty
import EuclidsPath.Engine.PNPFirstCause -- 🟢 EPISTEMIC COMPLEMENT of P/NP (mirror of CollatzFirstCause): the P/NP solution is unknowable FROM WITHIN a finite-fuel strictly-correct machine (pnpCause_unknowable); paying an unbounded supply from within = a perpetual engine (no_internalisedPNPGround, reuse of no_fullPayment_of_unboundedSupply + no_perpetual_engine_on_nat); WITHOUT a decree (P/NP has no honest boundary — trilemma); NOT the classical P≠NP, NOT Gödel; taint does not grow
import EuclidsPath.Engine.PNPDataAnchor -- 🔴 data-anchor of the machine model: TM2CompositionLaw exactly where mathlib proof_wanted comp; TM2FrameBridge with a FIXED encoding (the ∃-form is machine-exposed as a renaming of True — tm2DecidesWithSomeEncoding_free); 🟢 the model is inhabited (id); anchors_do_not_decide_pnp; taint does not grow
import EuclidsPath.Engine.YangMillsFront -- GREEN Yang–Mills branch: gapless-spectrum = a perpetual engine (halving-ladder = ℝ-warning of the cascade); the quantization law ⟹ the mass-gap (EPMI-killer); trilemma of the fourth boundary: universal refutable, existential vacuous, manifestation incompatible with the boundary; per-model law ⟺ gap GREEN — there is NO fourth field; Clay not declared
import EuclidsPath.Engine.YangMillsEpistemic -- 🟢 epistemics of YM: the ladder = a genuine engine (ladder_carries_real_engine, quantizedLadder_carries_perpetual_engine); ymCause_unknowable; the L9-collapse disclosed honestly
import EuclidsPath.Engine.NavierStokesFront -- GREEN NS-branch of smoothness: a singular cascade = a perpetual engine (killed by the budget under energy balance); the energy identity and the integral form of the solution BY TAKING THE INTEGRAL (FTC, E3-valued); trilemma of the fifth boundary: universal refutable (cookedFlow), existential vacuous (zero), manifestation incompatible with the boundary; surrogate ≠ C^∞ — disclosed; Clay not declared
import EuclidsPath.Engine.NavierStokesR3Assembly -- TRANSITION TO ℝ³: the NS integral assembled on a box — R1 the energy derivative under the integral (dominance), R2 the divergence theorem REALLY employed (faces vanish by support), the energy balance DERIVED green for the box-class ⟹ cascade smoothness WITHOUT a decree; pressure gated for the first time (the Forging-B channel closed); the box→ℝ³ limit is absent in mathlib — an external gap; the three E3-killers — named inputs
import EuclidsPath.Engine.NavierStokesClayReduction -- REDUCTION TO A SINGLE THEOREM: the exact Clay-(A) statement encoded; a green logical reduction "known theory (Kato+BKM) + GlobalVorticityControl ⟹ Clay-(A)"; the open CORE isolated and named (vorticity control, supercriticality barrier); NS is NOT solved — an honest map of tiers, taint unchanged
import EuclidsPath.Engine.CascadeBudget -- T2: an abstract budget-lemma (a finite budget cannot withstand eternal UNIFORM dissipation) + a CONCRETE finite shell-model (a real ODE) + the honest boundary budget_misses_nonuniform (a non-uniform cascade slips away); the first formalization of a fluid shell-model
import EuclidsPath.Engine.DyadicBlowup -- T1: a rigorous core of super-linear blowup (y'≥Cy² ⟹ finite time) + the Katz–Pavlović model (energy telescope) → dyadic_blowup; A→B: the drive DERIVED from the raw λⁿ-relations — for the exact self-similar solution (§2bis: ssMode, ssLead_drive) and for the CLASS via the front invariant (§2ter: FrontDomination, frontDrive_of_invariant), the monolithic superlinearDrive-hypothesis narrowed; infinite-mode conservation (the front) is honestly open; §2quater: the source n=0 is unknowable from within (🟢); the cascade = a REALIZED engine
import EuclidsPath.Engine.ContinuousEngine -- CONTINUOUS-TIME engine H(t)=r^t over ℝ (M1, the first formal one) — ℝ-analogue of the falsity of EPMI on the continuum; convergence≠contradiction (M2), supertask scale→0 up to T (M3), the Clay linkage as Iff.rfl (M4), an honest endpoint (M5); M6 — WHERE the engine is IMPOSSIBLE: uniform drain on finite fuel forces the endpoint (T≤H0/β), r^t survives only by non-uniformity (dividing_line); NOT a solution of NS, the Tao barrier, taint unchanged
import EuclidsPath.Engine.DyadicFirstCause -- 🟡 the source of the cascade = the first cause (manifestation): the dyadic blowup attaches to the masks through its source; the green derivation of the drive (STEP A/B) does NOT depend on this; taint grows
import EuclidsPath.Engine.DyadicFrontWindow -- 🟢 T-relative window of the front invariant: FrontPreservedUntil + the bridge "forever ⟺ up to any T" (pure quantifier logic); inhabitedness of ssMode on the whole [0,T) with a FIXED m₀=β_{J+1}/T (monotonicity of g) and an inhabited gap with Forever; the finite-window MVT-step §2ter closed (mathlib segment-estimate; gap velocity bounds = a named local input) + a stationary witness; the red input FrontPreservedForever is NOT closed, taint does not grow
import EuclidsPath.Engine.UniversalEngine -- UNIVERSAL TRANSFER of the engine: PerpetualEngine over ANY relation; impossibility from an INTERNAL cause (definition = infinite descent ⟂ WellFounded), perpetualEngine_iff_not_wellFounded; transfer by rank (no_perpetual_engine_of_rank/natRank — all fronts are consequences of a SINGLE theorem; EPMI shown as an instance); CONTROLLER — over ℝ the engine WORKS (perpetualEngine_on_real, reuse), universal_engine_dividing_line (M6); the core — mathlib-well-foundedness, the contribution is formalization-unifying; green, taint unchanged
import EuclidsPath.Engine.BSDFront -- THE EIGHTH MASK: the shadow of Birch–Swinnerton-Dyer. The engine's role is DIFFERENT — it is itself the method of DESCENT proving the algebraic rank: bsd_descent_has_no_engine (descent by height on the REAL points W.toAffine.Point has no engine = Mordell–Weil termination, reuse of UniversalEngine; references to the real Height/Northcott/fg_of_descent/LSeries); parity-bridge bsd_parity_is_rankParity to Liouville (rank-parity node). 🔴 honestly open: AnalyticRank (order of the zero of the REAL WeierstrassCurve.LSeries at s=1), WeakBSD (rank=ord L) — analysis outside mathlib, the engine does NOT close it. Trilemma: there is NO honest boundary (the parity decree is vacuous over a stub of the root number) — fallback 🔴, the axiom untouched, taint does not grow. NOT a proof of BSD
import EuclidsPath.Engine.BSDEpistemic -- 🟢 epistemics of BSD: THE DEGENERACY IS FIXED MACHINE-WISE (bsdGround_coincides_with_engine — BSD has no epistemic axis of its own, its linkage coincides with the ban on the descent engine, and this is a theorem); the AnalyticRank gate is freely satisfiable (an honesty lemma); taint does not grow
import EuclidsPath.Engine.BSDAnalyticAnchor -- 🔴 data-anchor of the analytic rank: ContinuedLFunction (Λ + reconciliation with the LSeriesSummable-domain + AnalyticAt at 1 — mathlib does NOT provide the continuation) ⟹ 🟢 analyticRankOf := analyticOrderAt Λ 1 (the genuine order of the zero) + WeakBSDContentful; the contrast with the free old gate disclosed; taint does not grow
import EuclidsPath.Engine.ChowlaFront -- NEIGHBOUR (chapter 54): the shadow of Chowla/Sarnak — a rank-parity node. 🟢 the real Liouville λ=(−1)^Ω: λ²=1, the correlation diagonal = x (perfect self-correlation of parity), the parity flip (reuse of RiemannLiouville), liouvilleSum_eq_L; "deviation = collapse of parity into a single parity". 🔴 ChowlaConjecture (correlations o(x)), SarnakConjecture — open (Tao: only the log/odd case). NOT a proof; taint does not grow
import EuclidsPath.Engine.ChowlaEpistemic -- 🟢 epistemics of Chowla (P/NP-type, no decree): collapse of parity = tail-constancy of λ — self-destructs against the flip-wall (no_parityCollapse_of_flip CONSUMES the flip-supply, CORR); the correlation ≡ x (mod 2) — zero is unreachable on odd slices; λ(2^k)=(−1)^k — both signs cofinally; chowlaCause_unknowable; summary chowla_locked_behind_flip_wall (Chowla has no engine-fact — honestly a flip-wall); NOT a solution of Chowla/Sarnak, NOT Gödel; taint does not grow
import EuclidsPath.Engine.AbcFront -- NEIGHBOUR (chapter 54): the shadow of abc. 🟢 the REAL Polynomial.abc (Mason–Stothers PROVEN) — polynomial abc = a power bound via the radical = "no infinite escape" (finiteness); the real Nat/Int.radical. 🔴 AbcConjecture (integral) is open (Mochizuki's claim is not accepted by the community). NOT a proof; taint does not grow
import EuclidsPath.Engine.AbcEpistemic -- 🟢 epistemics of abc: the radical toolkit (natRad_pow/mul); the naive law ε=0 is REFUTED (1+8=9, rad=6<9) + an unbounded supply of quality (the LTE-family 3^(2^k)); linkage on LinearAbcLaw with pigeonhole; abcCause_unknowable — honestly about the NAIVE form, the real abc-gate is untouched; taint does not grow
import EuclidsPath.Engine.BealFront -- NEIGHBOUR (chapter 54): the shadow of Beal/Fermat–Catalan — pure Fermat-descent = engine. 🟢 the REAL Polynomial.flt_catalan (PROVEN, descent over char p) + fermatLastTheoremFour/Three (descent) + descent-without-engine (reuse of EPMI/UniversalEngine). 🔴 BealConjecture, FermatCatalanConjecture (canonical form: triples of VALUES) open (Darmon–Granville: only fixed exponents); the tuple form of the gate is GREEN-REFUTED (fermatCatalan_tupleForm_refuted — a formalization lesson). NOT a proof; taint does not grow
import EuclidsPath.Engine.LehmerFront -- NEIGHBOUR (chapter 54): the shadow of Lehmer/Mahler measure — height-finiteness as in BSD. 🟢 the REAL finite_mahlerMeasure_le (Northcott: bounded degree+measure ⟹ finite = no infinite height descent) + pow_eq_one_of_mahlerMeasure_eq_one (Kronecker: measure 1 ⟺ roots of unity) + descent-without-engine. 🔴 LehmerConjecture (the sharp constant c>1) is open. NOT a proof; taint does not grow
import EuclidsPath.Engine.LehmerEpistemic -- 🟢 epistemics of Lehmer (P/NP-type): the Northcott horizon is finite green (mahlerBox), internal payment of an infinite family = a pigeonhole-engine; lehmerCause_unknowable
import EuclidsPath.Engine.LehmerBoundedDegree -- 🟢 Lehmer AT BOUNDED DEGREE is proven (lehmer_at_bounded_degree: for each n there is c>1 with no measures in (1,c) — a Northcott-minimum of the window); 🔴 UniformLehmerGap (a single c for all n) = the conjecture itself, the iff-audit disclosed; taint does not grow
import EuclidsPath.Engine.LandauFront -- NEIGHBOUR (chapter 54): the shadow of Landau n²+1 (the zoo, mirror of SideInfinitude). 🟢 the bridge unboundedness⟹infinitude + the fact oddLandauPrime_even_k (odd k ⟹ k²+1 even ⟹ the only prime = 2). 🔴 Landau4thUnbounded (Hardy–Littlewood) is open (Iwaniec: ≤2 factors). NOT a proof; taint does not grow
import EuclidsPath.Engine.LandauEpistemic -- 🟢 epistemics of Landau: canonization of the gate (iff-infinitude, the even channel via max N 1), the bridge to Dirichlet 1 mod 4 (the real Nat.forall_exists_prime_gt_and_modEq + the divisor wall landauFactor_mod_four), the manifestation law is NOT decreed (the Polignac-class landauRefutation_carries_engine), landauCause_unknowable; the ground/beyondOwnHorizon pair is tautological — disclosed machine-wise; taint does not grow
import EuclidsPath.Engine.HodgeFront -- GREEN Hodge branch: quantized charge = ℕ-height; the engine (descent chain) is dead UNCONDITIONALLY (EPMI); the descent law ⟹ the model conjecture (strong induction on height); collapse law ⟺ conjecture green — there is NO sixth field; trilemma: V1 refutable, V2 vacuous, the chain-form degenerated into a green one, V3 incompatible with the boundary; mathlib does not contain Hodge — Clay not declared
import EuclidsPath.Engine.HodgeEpistemic -- 🟢 epistemics of Hodge: per-model DescentLaw (universal FORGED — hodgeUniversal_forged_refutation); an unpaid class = a chain-engine; hodgeCause_unknowable
import EuclidsPath.Engine.MersenneManifestationFront -- GREEN Mersenne-manifestation: absence witness (Π, ≥ 29), a gated law, M3⁺ "a refutation presents an engine"; the chain 4c+1 does NOT peel (no forging); the trilemma passed, BUT the field is deferred — the heuristic sign is AGAINST (the §16-comment of the quarantine)
import EuclidsPath.Engine.FermatMersenneEpistemic -- 🟢 epistemics of Fermat+Mersenne: both bets deferred (§16/§17) AND there are no internal paths — a refutation under the law/books = an engine; fermatCause_unknowable, mersenneCause_unknowable
import EuclidsPath.Engine.SideInfinitude              -- Dirichlet: the sides 6m±1 are each separately infinite (🟢); reconciling the sides in one centre = the whole open essence
import EuclidsPath.Engine.PolignacBranch              -- Polignac in the grid: cousins (p,p+4) and sexy (p,p+6) on neighbouring centres; classification, instances, bridges (🟢)
import EuclidsPath.Engine.SophieGermainBranch         -- Sophie Germain: the minus side, doubling the centre m→2m; PEARL: SG-primes at p≡3 (mod 4) kill Mersenne (🟢, 23∣M₁₁)
import EuclidsPath.Engine.FermatBranch                -- Fermat branch: F_k ≡ 5 (mod 6) — the minus side; quadratic chain c'+4c=6c²+1; twin-instances k=1,2,4 (up to 65537/65539)
import EuclidsPath.Engine.FermatMersenneLadder -- 🟢 Fermat↔Mersenne ladder: 7∣F_k+2 (odd k — half the indices drop out), 5∣2^p−3 at p≡3 (mod 4) — the §16 heuristic is now green; the bridge mersenne(2^n)=∏F_k + Goldbach uniqueness of the layer; NOT a solution of the infinitudes, taint does not grow
import EuclidsPath.Engine.PerfectNumberBranch         -- Perfect numbers: Euclid–Euler BOTH directions green (Archive); Mersenne primes ⟺ even perfect numbers unbounded (🟢-iff)
import EuclidsPath.Engine.PolignacManifestationFront    -- Polignac-fronts (cousins p+4, sexy p+6): absence witness Π, law, essence M3; there is NO field (§17, sign FOR)
import EuclidsPath.Engine.PolignacEpistemic -- 🟢 epistemics of Polignac: cousinCause_unknowable/sexyCause_unknowable; a refutation with the books reconciled = an engine (reuse of *Refutation_carries_engine)
import EuclidsPath.Engine.BoundedGapsAnchor -- 🔴 anchor of bounded gaps BoundedGaps B (Zhang 70M / Maynard–Tao 246 — NOT formalized, names only) + 🟢 bridges: monotonicity upward in B, the MAIN AUDIT boundedGaps_two_iff_twins (B=2 ⟺ TwinLowers.Infinite — the goal renaming disclosed by an iff), disjunctions of thresholds 4/6 on the Polignac grid; descent 246→2 is NOT asserted (NoDescentFrom246To2Claimed); taint does not grow
import EuclidsPath.Engine.SophieGermainManifestationFront -- Sophie Germain front + anti-Mersenne restriction: SG-manifestation feeds the composite side of Mersenne ("two bets")
import EuclidsPath.Engine.SophieGermainEpistemic -- 🟢 epistemics of Sophie Germain: sgCause_unknowable (+3 mod 4); a refutation = an engine (sgRefutation_carries_engine); the pearl 23∣M₁₁ is unconditional
import EuclidsPath.Engine.GoldbachManifestationFront    -- Goldbach-front (object-witness, decide-decidable): an unpaid even number manifests an engine
import EuclidsPath.Engine.LegendreDesertFront           -- Prime deserts: GREEN Bertrand (a desert does not double) + Legendre-front (the interval is shorter — Bertrand does not decide it)
import EuclidsPath.Engine.GoldbachLegendreEpistemic -- 🟢 epistemics of Goldbach+Legendre: a violation with the books reconciled = an engine; goldbachCause_unknowable/legendreCause_unknowable; the witness is decide-decidable — "verification, not derivation"
import EuclidsPath.Engine.GoldbachLegendreEpistemic     -- 🟢 EPISTEMIC COMPLEMENT of Goldbach+Legendre (mirror of PNPFirstCause): goldbachCause_unknowable / legendreCause_unknowable; self-grounding = an engine-object (builds_engine, paid by no_deviationFlowSupply_at_resolved_scale, NOT P∧¬P); summary goldbachLegendre_locked_behind_engine_status WITHOUT a decree-conjunct (§17); NOT a solution of problems 1742/1808, NOT Gödel; taint does not grow
import EuclidsPath.Engine.OddPerfectManifestationFront  -- Odd perfect numbers (object-witness): the even side is green-constructible, the deviation lives on the odd one
import EuclidsPath.Engine.OddPerfectThreePrimes -- 🟢 an odd perfect number has ≥ 3 distinct prime divisors (classic via abundance: σ(n)/n < p/(p−1)·q/(q−1) ≤ 15/8 < 2); steps: not a prime power, not two primes; taint does not grow
import EuclidsPath.Engine.OddPerfectEulerForm -- 🟢 FLAGSHIP: Euler's theorem — an odd perfect number n = q^α·m², q prime, q ≡ α ≡ 1 (mod 4), q ∤ m; steps: the unique odd exponent, residues of q and α, packing the square; taint does not grow
import EuclidsPath.Engine.OddPerfectEpistemic -- 🟢 epistemics of odd perfect numbers: presenting a witness = presenting an engine (conditional on the law); oddPerfectCause_unknowable; variant (b) — non-degenerate
import EuclidsPath.Engine.FermatManifestationFront      -- Fermat-front: localization ≥ 65537; the sign is INVERTED more strongly than Mersenne (only F₀–F₄) — §16 verbatim

-- ⚠️ QUARANTINE: the SINGLE axiom of the repository — the first cause with TWO boundaries:
-- the twin-node (causalBoundary) and the Riemann manifestation law (riemannBoundary, §10).
-- Everything depending on it — CONDITIONALLY, machine-flagged by the verifier as AXIOM-TAINTED.
-- twin_prime_conjecture is NOT closed through this module and remains sorry;
-- riemannHypothesis_from_firstCause — a reduction closed by decree, NOT a proof of RH.
import EuclidsPath.Engine.CausalClosureAxiom
import EuclidsPath.Engine.GeometryFront -- GEOMETRY OF THE PATH: the arrow of time (lexRank ↓), curvature κ=1−outdeg COMPUTED (spectrum −8…+1, χ(cone3)=−5), flatness everywhere ⟹ an engine; lines are finite — Euclid's SECOND postulate falls, there are no parallels; a web through the grave of zero; the intersection of lines 🟡 from the same first cause, but it cannot be known from within 🟢 (exactly 2 tainted-declarations)
