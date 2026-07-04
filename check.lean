/-
  check.lean — a standing spot-check of the flagship theorems and their axioms.

  Run from the repository root:

      lake env lean check.lean

  How to read `#print axioms X`:
    * GREEN  (🟢): the list contains only the standard axioms
                   [propext, Classical.choice, Quot.sound] (or none) —
                   `step00FirstCause` is ABSENT ⇒ proved without the decree.
    * YELLOW (🟡): the list contains
                   `…GeneratedFlowFormulation.step00FirstCause` ⇒ conditional on the first cause.
    * The single `sorry`: `twin_prime_conjecture` reports `sorryAx`.

  For the exhaustive, repo-wide invariant check (one axiom, one sorry, taint count)
  use instead:  lake env lean scripts/VerifyAll.lean
-/
import EuclidsPath
open EuclidsPath

/-! ## Euclid's engine — the bare core (🟢, axiom-free) -/
#check @Engine.no_infinite_descent
#print axioms Engine.no_infinite_descent
#check @Engine.no_perpetual_engine
#print axioms Engine.no_perpetual_engine
#check @Engine.engine_never_returns
#print axioms Engine.engine_never_returns
#check @Engine.turned_engine_halts
#print axioms Engine.turned_engine_halts
#check @UniversalEngine.no_perpetual_engine_of_rank
#print axioms UniversalEngine.no_perpetual_engine_of_rank
#check @UniversalEngine.perpetualEngine_on_real   -- the engine WORKS on ℝ (🟢)
#print axioms UniversalEngine.perpetualEngine_on_real

/-! ## The first cause and the main theorem -/
#check @ConcreteStep00Graph.GeneratedFlowFormulation.step00FirstCause   -- THE single axiom
#print axioms ConcreteStep00Graph.GeneratedFlowFormulation.step00FirstCause
#check @ConcreteStep00Graph.GeneratedFlowFormulation.cause_unknowable    -- 🟢 (theorem)
#print axioms ConcreteStep00Graph.GeneratedFlowFormulation.cause_unknowable
#check @FiniteKnowledgeBarrier.higherEnergyIncompatibility_main          -- ★ MASTER, 🟢
#print axioms FiniteKnowledgeBarrier.higherEnergyIncompatibility_main
#check @FiniteKnowledgeBarrier.higherEnergyIncompatibility_twins         -- 🟡 (from the decree)
#print axioms FiniteKnowledgeBarrier.higherEnergyIncompatibility_twins
#check @ConcreteStep00Graph.GeneratedFlowFormulation.twins_infinite_of_noEngine_and_boundary
#print axioms ConcreteStep00Graph.GeneratedFlowFormulation.twins_infinite_of_noEngine_and_boundary

/-! ## The single open node — the one `sorry` -/
#check @twin_prime_conjecture
#print axioms twin_prime_conjecture   -- reports sorryAx

/-! ## Riemann hypothesis -/
#check @RiemannBranch.not_RH_gives_engine                                                  -- 🟢
#print axioms RiemannBranch.not_RH_gives_engine
#check @ConcreteStep00Graph.GeneratedFlowFormulation.riemannHypothesis_of_manifestation_and_boundary
#print axioms ConcreteStep00Graph.GeneratedFlowFormulation.riemannHypothesis_of_manifestation_and_boundary
#check @ConcreteStep00Graph.GeneratedFlowFormulation.riemannHypothesis_from_firstCause      -- 🟡
#print axioms ConcreteStep00Graph.GeneratedFlowFormulation.riemannHypothesis_from_firstCause
#check @ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic.no_internalisedRiemannGround -- 🟢
#print axioms ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic.no_internalisedRiemannGround

/-! ## P versus NP (🟢, no decree) -/
#check @PNPRankPayment.no_fullPayment_of_unboundedSupply
#print axioms PNPRankPayment.no_fullPayment_of_unboundedSupply
#check @PNPRankPayment.pnp_rank_separation_smallScale
#print axioms PNPRankPayment.pnp_rank_separation_smallScale
#check @PNPRankPayment.FirstCause.pnpCause_unknowable
#print axioms PNPRankPayment.FirstCause.pnpCause_unknowable

/-! ## Yang–Mills and Hodge (🟢 conditional theorems) -/
#check @YangMills.quantizationLaw_iff_massGap
#print axioms YangMills.quantizationLaw_iff_massGap
#check @YangMills.massGap_of_quantizationLaw
#print axioms YangMills.massGap_of_quantizationLaw
#check @Hodge.descentLaw_of_hodgeProperty
#print axioms Hodge.descentLaw_of_hodgeProperty

/-! ## Navier–Stokes -/
#check @NavierStokesR3.noSingularCascade_of_r3Assembly                          -- 🟢 box class
#print axioms NavierStokesR3.noSingularCascade_of_r3Assembly
#check @NavierStokesClay.clayA_of_regularityTransfer_and_vorticityControl       -- 🟢 the Clay reduction
#print axioms NavierStokesClay.clayA_of_regularityTransfer_and_vorticityControl
#check @NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl      -- 🟢 engine surrogate is weaker
#print axioms NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl
#check @DyadicBlowup.dyadic_blowup                                              -- 🟢 blow-up (engine realised)
#print axioms DyadicBlowup.dyadic_blowup
#check @DyadicFirstCause.dyadicOrigin_from_firstCause                           -- 🟡 (nsBoundary)
#print axioms DyadicFirstCause.dyadicOrigin_from_firstCause

/-! ## Collatz — the decree taken and withdrawn (forged refutation) -/
#check @Collatz.TugOfWar.ropeLaw_universal_refuted            -- 🟢 the rope law is FALSE (witness n = 27)
#print axioms Collatz.TugOfWar.ropeLaw_universal_refuted
#check @Collatz.TugOfWar.nonHalting_carries_perpetual_engine  -- 🟢 refuting Collatz = a perpetual engine
#print axioms Collatz.TugOfWar.nonHalting_carries_perpetual_engine
#check @Collatz.FirstCause.collatz_decree_postmortem          -- 🟢 post-mortem summary
#print axioms Collatz.FirstCause.collatz_decree_postmortem
#check @Collatz.FirstCause.collatzCause_unknowable            -- 🟢
#print axioms Collatz.FirstCause.collatzCause_unknowable

/-! ## The arithmetic zoo (🟢, no field taken) -/
#check @SophieGermainBranch.sophieGermain_divides_mersenne    -- 🟢 Euler–Lagrange classic (23 ∣ M₁₁)
#print axioms SophieGermainBranch.sophieGermain_divides_mersenne
#check @PerfectNumberBranch.perfect_of_mersennePrime          -- 🟢 Euclid (Elements IX.36)
#print axioms PerfectNumberBranch.perfect_of_mersennePrime
#check @PerfectNumberBranch.evenPerfect_eq                    -- 🟢 Euler (converse)
#print axioms PerfectNumberBranch.evenPerfect_eq
#check @PerfectNumberBranch.oddPerfect_ge_101
#print axioms PerfectNumberBranch.oddPerfect_ge_101
#check @GoldbachBranch.goldbach_upTo_52
#print axioms GoldbachBranch.goldbach_upTo_52
#check @PrimeDeserts.no_desert_doubles                        -- 🟢 Bertrand
#print axioms PrimeDeserts.no_desert_doubles

/-! ## Geometry of the path and the open neighbours -/
#check @GeometryFront.twin_vertices_beyond_every_horizon      -- 🟡 (via the twin boundary)
#print axioms GeometryFront.twin_vertices_beyond_every_horizon
#check @GeometryFront.lines_meet_but_unknowable_from_inside   -- 🟡
#print axioms GeometryFront.lines_meet_but_unknowable_from_inside
#check @ChowlaFront.chowlaCorrelation_zero_eq_card            -- 🟢 real mathlib anchor
#print axioms ChowlaFront.chowlaCorrelation_zero_eq_card
#check @LandauFront.landauPrimes_infinite_of_unbounded        -- 🟢
#print axioms LandauFront.landauPrimes_infinite_of_unbounded
