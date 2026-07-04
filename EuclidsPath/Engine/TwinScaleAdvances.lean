/-
  TwinScaleAdvances — two scale-level advances of the main node (twins) + skeleton bridge.
  Report section: "Twin Primes Conjecture", candidates #4 (allM0) and #5 (growing separating
  scale, CORR-route) + #6 (bridge BoundaryDecomp ↔ CarrierBridge).
  Prose: prose/29_CarrierBridge.md §29.5–29.6 (scale barrier and closing plan),
  prose/30 (SeparatingScale). Green machines: Engine/ConcreteStep00Graph.lean,
  Engine/ProductCore.lean, Engine/CarrierBridge.lean, Engine/BoundaryDecomp.lean.

  WHAT IS HERE.
  (a) `no_projection_resolves_at_smallScale_allM0`: the small-scale band of the node (A ≤ 4)
      is dead for ANY base M0 ≥ 1, not only for M0 = 1. The payment is the same as for
      `no_projection_resolves_at_smallScale`: the 5-adic chain (injective supply
      via `fiveAdicChain_strictMono`) + pigeonhole `Finite.exists_ne_map_eq_of_infinite`;
      the chain start is taken above any M0 (the chain is unbounded: `fiveAdicChain_ge`),
      the terminal `center 1` remains old for 1 ≤ M0.
  (b) `exists_growing_separating_scale`: step (1) of the closing plan §29.6 — for each
      window m ≥ 1 there exists a scale A (with an explicit upper bound 12m+2) at which
      the side 6m+1 fits in the window (X_A := m) AND the separating scale holds:
      6m+1 < oldPrimorial A. Payment: Bertrand's postulate
      (`Nat.exists_prime_lt_and_le_two_mul`, mathlib) + primorial divisibility
      (`prime_dvd_oldPrimorial` + `Nat.le_of_dvd`). CORR correction accounted for:
      oldPrimorial does NOT contain 2 and 3, so the move "2·p > 6m+1" is unavailable — instead
      ONE Bertrand on n = 6m+1 gives a prime p > 6m+1, p ≥ 5, A := p.
  (c) `factorization_collision_as_absorber_instance`: the CarrierBridge pump-chain
      (`engine_of_factorization`) is machine-fed through the pigeonhole skeleton
      `BoundaryDecomp.global_absorber_forces_engine` (key := coreSigOf ∘ node,
      pump := PROVED descent machine ProductCore). This is an identification of TWO
      SKELETONS, NOT "one wall instead of two": both red inputs (FactorizationData
      for CarrierBridge; pump/GlobalOldAbsorption for the genuine genealogies) remain.

  HONESTY. Nothing here PROVES the twin primes conjecture or IS Godel.
  (a) — strengthening of the already-refuted branch A ≤ 4 (the node survives only at A ≥ 5,
  where Dirichlet-class arithmetic is needed, which is absent from the repo). (b) — green finite
  arithmetic: it closes exactly step (1) of plan §29.6 (existence of the scale)
  and does NOT touch the irreducible core GlobalOldAbsorption (step (2): scale-consistent
  absorption). Moreover, the barrier §29.5 is machine-visible here:
  `fixedWindow_factorization_impossible_at_separating_scale` — at a FIXED
  window and separating scale the input `FactorizationData` is altogether empty, i.e. the missing
  maps must live on the GROWING scale, as the prose says. (c) — the "perpetual engine"
  is supplied by a pump-contradiction (ex falso from rank-1 arithmetic) — this is the accepted
  form of `engine_of_factorization` itself, here merely fed through the second skeleton.

  The file is ENTIRELY GREEN: it does not import Engine/CausalClosureAxiom (quarantine),
  adds no axioms or sorry, and the taint list of 47 declarations does not change.
-/

import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.SeparatingScale
import EuclidsPath.Engine.CarrierBridge
import EuclidsPath.Engine.BoundaryDecomp

set_option autoImplicit false

namespace EuclidsPath.TwinScaleAdvances

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.Residuals
open EuclidsPath.ProductCore

/-! ## (a) Small scale is dead for ALL bases M0 ≥ 1

The existing `no_projection_resolves_at_smallScale` is hard-fixed to M0 = 1
(`fiveAdicChainFlow : ExtendedProperGeneratedFlow A 1`). We generalise: the 5-adic chain
itself and its peels do not depend on M0 (in `ProperRealStep` the base enters only the
constructor `absorb`, monotonically), the terminal `center 1` is old for any M0 ≥ 1,
and the start is taken above M0 because the chain grows faster than the index. -/

/-- **Monotonicity of the proper step in the base.** `ProperRealStep A M0 ⊆ ProperRealStep A M1`
    when `M0 ≤ M1`: constructors `clean`/`boundary`/`peel` do not depend on the base, `absorb`
    requires `n ≤ M0 ≤ M1`. Pure structural lemma (case analysis). -/
theorem properRealStep_mono_basepoint {A M0 M1 : ℕ} (hM : M0 ≤ M1) {U V : State}
    (h : ProperRealStep A M0 U V) : ProperRealStep A M1 U V := by
  cases h with
  | clean hmClean hnClean hPeel => exact ProperRealStep.clean hmClean hnClean hPeel
  | boundary hmClean hBoundary => exact ProperRealStep.boundary hmClean hBoundary
  | peel hcert => exact ProperRealStep.peel hcert
  | absorb hOld => exact ProperRealStep.absorb (le_trans hOld hM)

/-- The 5-adic chain does not fall behind the index: `k ≤ c(k)`. Together with strict
    monotonicity this gives unboundedness of the chain — the start can be taken above any M0. -/
theorem fiveAdicChain_ge : ∀ k : ℕ, k ≤ fiveAdicChain k
  | 0 => Nat.zero_le _
  | k + 1 => by
      have ih := fiveAdicChain_ge k
      show k + 1 ≤ 5 * fiveAdicChain k + 1
      omega

/-- **Admissible genealogy at an arbitrary base `M0 ≥ 1`** (generalisation of
    `fiveAdicChainFlow` with M0 = 1). Start — `c(M0+k+1) > M0` (freshness via
    `fiveAdicChain_ge`), path — the same 5-adic (`fiveAdicChainPath`, lifted in
    the base via `properRealStep_mono_basepoint`), terminal — the old clean-center 1
    (`extendedLedgerTerminal_oldCleanCenter`, common across M0). WITHOUT any twin hypothesis. -/
def fiveAdicChainFlowAt {A M0 : ℕ} (hA : A ≤ 4) (hM0 : 1 ≤ M0) (k : ℕ) :
    ExtendedProperGeneratedFlow A M0 :=
  { start := fiveAdicChain (M0 + k + 1)
    terminal := State.center 1
    steps := M0 + k + 1
    nonempty := Nat.succ_pos _
    properPath := pathN_mono (R := ProperRealStep A 1) (S := ProperRealStep A M0)
      (fun hStep => properRealStep_mono_basepoint hM0 hStep)
      (fiveAdicChainPath hA (M0 + k + 1))
    startClean := clean_of_scale_le_four hA (fiveAdicChain_pos _)
    startFresh := by
      have h := fiveAdicChain_ge (M0 + k + 1)
      omega
    terminalLegal := clean_of_scale_le_four hA le_rfl
    ledgerTerminal := extendedLedgerTerminal_oldCleanCenter hM0
      (clean_of_scale_le_four hA le_rfl) }

/-- The family is injective in k — via strict monotonicity of the starts
    (`fiveAdicChain_strictMono`), just like the original at M0 = 1. -/
theorem fiveAdicChainFlowAt_injective {A M0 : ℕ} (hA : A ≤ 4) (hM0 : 1 ≤ M0) :
    Function.Injective (fiveAdicChainFlowAt hA hM0) := by
  intro k₁ k₂ h
  have hstart : fiveAdicChain (M0 + k₁ + 1) = fiveAdicChain (M0 + k₂ + 1) :=
    congrArg ExtendedProperGeneratedFlow.start h
  have := fiveAdicChain_strictMono.injective hstart
  omega

/-- **SMALL SCALE IS DEAD FOR ALL BASES (candidate #4).** For `A ≤ 4` and ANY
    `M0 ≥ 1` no finite-key projection resolves: the injective 5-adic
    supply above M0 + pigeonhole `Finite.exists_ne_map_eq_of_infinite` yield a same-key
    pair, and both resolution alternatives are burned (`no_extendedFlowResolutionAlternative`).
    The existing `no_projection_resolves_at_smallScale` is the special case M0 = 1.
    HONESTY: at A ≥ 5 the same technique requires clean starts with peel-target control —
    Dirichlet-class arithmetic that is absent from the repo; the node is genuinely open there. -/
theorem no_projection_resolves_at_smallScale_allM0 {A M0 : ℕ} (hA : A ≤ 4) (hM0 : 1 ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  intro hRes
  letI : Finite proj.Key := proj.finiteKey
  obtain ⟨k₁, k₂, hne, hkey⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun k => proj.keyFlow (fiveAdicChainFlowAt hA hM0 k))
  have hFne : fiveAdicChainFlowAt hA hM0 k₁ ≠ fiveAdicChainFlowAt hA hM0 k₂ :=
    fun h => hne (fiveAdicChainFlowAt_injective hA hM0 h)
  exact no_extendedFlowResolutionAlternative A M0
    (hRes _ _ hFne (extendedFlow_admissible _) (extendedFlow_admissible _) hkey)

/-- **Uniform refutation of the A ≤ 4 branch**: the node falls not "for all M0 at once
    via M0 = 1" (as in `smallScale_branch_of_lastStep00Obligation_refuted`),
    but AT EACH individual base M0 ≥ 1 — no resolving projection exists for any of them. -/
theorem smallScale_branch_refuted_at_every_basepoint {A M0 : ℕ}
    (hA : A ≤ 4) (hM0 : 1 ≤ M0) :
    ¬ ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj := by
  rintro ⟨proj, hRes⟩
  exact no_projection_resolves_at_smallScale_allM0 hA hM0 proj hRes

/-! ## (b) Growing separating scale (step (1) of plan §29.6, CORR-route)

The closing plan §29.6 begins with a scale-function: for each window m a scale A is needed
at which the side 6m+1 fits in the window (X_A := m — trivially, by equality) and
the separating scale `6·X_A+1 < P_A` holds (hypothesis `hsep` of the entire pump machine
ProductCore/CarrierBridge and `SeparatingScale.no_productHall`). CORR: the primorial
`oldPrimorial A = ∏_{5≤p≤A} p` does NOT contain 2 and 3, so the route is one Bertrand
on n = 6m+1: a prime p with 6m+1 < p ≤ 12m+2 is automatically ≥ 5, and p itself divides
oldPrimorial p. -/

/-- **GROWING SEPARATING SCALE (candidate #5, CORR-route).** For each window
    `m ≥ 1` there exists a scale `A` with an explicit bound `A ≤ 12m+2`, at which
    `6m+1 < oldPrimorial A` — i.e. the separating-scale hypothesis `hsep` is satisfiable
    with margin at every window, and the scale-function from step (1) of plan §29.6 exists.
    PAID: Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`: prime
    `6m+1 < p ≤ 12m+2`), `p ≥ 5` (since `p > 6m+1 ≥ 7`), `p ∣ oldPrimorial p`
    (`prime_dvd_oldPrimorial`) and `Nat.le_of_dvd` + `oldPrimorial_pos`.
    HONESTY: this is finite green arithmetic; the irreducible step (2) of the plan —
    scale-consistent absorption (GlobalOldAbsorption) — is NOT touched. -/
theorem exists_growing_separating_scale (m : ℕ) (hm : 1 ≤ m) :
    ∃ A : ℕ, 5 ≤ A ∧ A ≤ 12 * m + 2 ∧ 6 * m + 1 < oldPrimorial A := by
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (6 * m + 1) (by omega)
  have hp5 : 5 ≤ p := by omega
  have hdvd : p ∣ oldPrimorial p := prime_dvd_oldPrimorial hp hp5 le_rfl
  have hlep : p ≤ oldPrimorial p := Nat.le_of_dvd (oldPrimorial_pos p) hdvd
  exact ⟨p, hp5, by omega, by omega⟩

/-- **The scale grows with the window**: the separating scale for window `m` is achievable
    ABOVE any given threshold `B` — Bertrand on `max (6m+1) B`. This is
    the "consistent growth of A and X_A together with m" from §29.6 in existential form. -/
theorem exists_growing_separating_scale_above (m B : ℕ) (hm : 1 ≤ m) :
    ∃ A : ℕ, B ≤ A ∧ 5 ≤ A ∧ 6 * m + 1 < oldPrimorial A := by
  obtain ⟨p, hp, hlt, _⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (max (6 * m + 1) B) (by omega)
  have hp5 : 5 ≤ p := by omega
  have hdvd : p ∣ oldPrimorial p := prime_dvd_oldPrimorial hp hp5 le_rfl
  have hlep : p ≤ oldPrimorial p := Nat.le_of_dvd (oldPrimorial_pos p) hdvd
  exact ⟨p, by omega, hp5, by omega⟩

/-- **ProductHall is dead on the growing window** (interface with chapter 30): for each
    window `m ≥ 1` there exists a scale `A` at which a legal ProductHall with
    `X_A := m`, `P_A := oldPrimorial A` is impossible — pure arithmetic
    `SeparatingScale.no_productHall`, whose hypothesis `hsep` is paid by
    `exists_growing_separating_scale`. -/
theorem no_legalProductHall_on_growing_window (m : ℕ) (hm : 1 ≤ m) :
    ∃ A : ℕ, 5 ≤ A ∧
      (SeparatingScale.LegalProductHall m (oldPrimorial A) → False) := by
  obtain ⟨A, h5, _, hsep⟩ := exists_growing_separating_scale m hm
  exact ⟨A, h5, fun PH => SeparatingScale.no_productHall hsep PH⟩

/-- **Barrier §29.5 is machine-visible.** At a FIXED window `X_A` and separating
    scale the input `FactorizationData A X_A` is EMPTY: an infinite injective
    AmbientLegal family on a single window is destroyed by the pump machine (pigeonhole over
    finite `CoreSig` + proved descent + rank-1 arithmetic) — this is
    `engine_of_factorization` with `Engine := False`. HONEST corollary: the missing
    maps `rankOf`/`mkNode`/`hinj`/`hamb` MUST live on the growing scale
    (step (2) of plan §29.6, GlobalOldAbsorption), the fixed window is excluded. -/
theorem fixedWindow_factorization_impossible_at_separating_scale
    {A X_A P_A : ℕ} [NeZero P_A] (hsep : 6 * X_A + 1 < P_A)
    (F : CarrierBridge.FactorizationData A X_A) : False :=
  CarrierBridge.engine_of_factorization (P_A := P_A) hsep F

/-! ## (c) Skeleton bridge: CarrierBridge via BoundaryDecomp pigeonhole

`BoundaryDecomp.global_absorber_forces_engine` — the pigeonhole skeleton of the Hall node
(infinite starts → finite key → collision → pump). Below, the CarrierBridge data are
fed through THIS skeleton: key := coreSigOf ∘ node (finite codomain by
`coreSig_fintype`), pump := PROVED machine ProductCore
(`product_core_pump_closed` = descent `core_step_proved` + rank-1 base). -/

/-- **SKELETON BRIDGE (candidate #6).** `FactorizationData` + separating scale yield
    `EuclideanEngine` EXACTLY VIA the pigeonhole skeleton `global_absorber_forces_engine`:
    starts — subtype of infinite `F.S`, key — `coreSigOf ∘ F.node` into finite
    `CoreSig P_A F.r` (a fixed `P_A` with `[NeZero P_A]` and `hsep` is required; `hamb`
    is mandatory for the pump direction), pump — the proved descent machine ProductCore.
    HONESTY (CORR): this is a machine IDENTIFICATION OF TWO SKELETONS (the Hall-pump node of
    BoundaryDecomp and the chain `engine_of_factorization`), NOT "one wall instead of two":
    both red inputs remain — `FactorizationData` is still a hypothesis here
    (at the separating scale it is moreover empty, see the barrier above, so the
    identification concerns the PROOF ROUTE, not new inhabitants),
    and the pump hypothesis for genuine genealogies (GlobalOldTwinAbsorption) is not closed. -/
theorem factorization_collision_as_absorber_instance
    {A X_A P_A : ℕ} {EuclideanEngine : Prop} [NeZero P_A]
    (hsep : 6 * X_A + 1 < P_A)
    (F : CarrierBridge.FactorizationData A X_A) : EuclideanEngine := by
  haveI : Infinite F.S := F.hS.to_subtype
  refine BoundaryDecomp.global_absorber_forces_engine
    (α := F.S) (Codom := CoreSig P_A F.r)
    Set.univ Set.infinite_univ
    (fun γ => coreSigOf (F.node γ.1))
    (fun γ₁ γ₂ hne hkey => ?_)
  refine product_core_pump_closed hsep ⟨F.r, F.hr.1, F.hr.2, ?_⟩
  exact ⟨F.node γ₁.1, F.node γ₂.1,
    fun h => hne (Subtype.ext (F.hinj γ₁.2 γ₂.2 h)),
    F.hamb γ₁.1 γ₁.2, F.hamb γ₂.1 γ₂.2, hkey⟩

/-! ## Axiom audit: the whole module is green (standard triple), the repo taint does NOT change -/
#print axioms properRealStep_mono_basepoint
#print axioms fiveAdicChain_ge
#print axioms fiveAdicChainFlowAt
#print axioms fiveAdicChainFlowAt_injective
#print axioms no_projection_resolves_at_smallScale_allM0
#print axioms smallScale_branch_refuted_at_every_basepoint
#print axioms exists_growing_separating_scale
#print axioms exists_growing_separating_scale_above
#print axioms no_legalProductHall_on_growing_window
#print axioms fixedWindow_factorization_impossible_at_separating_scale
#print axioms factorization_collision_as_absorber_instance

end EuclidsPath.TwinScaleAdvances
