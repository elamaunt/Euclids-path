import EuclidsPath.Engine.Step00TwoEngineOscillation
import EuclidsPath.Engine.Step00RelativeCurvatureInstance

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Graded killed-boundary route — the named hypotheses and the genuine bridge

This file states the two named research inputs of the ordered-exponent route as STRUCTURES
(hypotheses, never axioms), proves green that together they build the certificate family
`RelativeCurvatureRealizationProblem` demanded by the ornament route, and DISCLOSES by a
machine-checked iff that possessing the route is exactly the twin conjecture — the parity
barrier relocated into a finite matching + signed-window form, not a shortcut.

## The two named inputs

* `GradedKilledBoundaryMatching SafeAt sign` — a discrete-Morse style matching: for every
  horizon `M0 ≥ 5` a finite window above `M0`, a killed subsector, and a sign-flipping
  fixed-point-free involution pairing the killed states; unkilled window states are survivors.
  The fields mirror `Finset.sum_involution` one-to-one.
* `SignedBlockProductModulusEstimate GKB` — the signed window sums do not vanish.  This is the
  analytic half (the parity-barrier strength input); ordered prime blocks
  (`orderedPrimeBlock`, file `Step00OrderedExponentGeometry`) are its INTENDED realization
  shape for the windows/moduli, not forced by the structure — disclosed here.

## Green consequences (proved below, no hypotheses)

* `killed_sum_zero` — the killed sector cancels ("the killed-boundary exact sector carries zero
  signed mass"): `Finset.sum_involution` consumes the matching fields verbatim.
* `survivor_exists` — matching + estimate force a safe hole above every horizon: the literal
  form of "graded survivor sector ⊥ killed exact sector".
* `relativeCurvatureRealization_of_orderedExponentRoute` — the route BUILDS the certificates
  (`relIndex := -5`, collapse field discharged by the forced survivor), reaching
  `TwinLowers.Infinite` through the existing adapter — conditional ONLY on the two named inputs.

## Honesty interlocks

* `toyMatching`/`toyEstimate` — a non-trivial model instance (nonempty killed sector, genuine
  cancellation): the machinery does real work — contentfulness witness.
* `trivialMatching` + `no_estimate_over_trivialMatching` — the matching alone is free, and the
  estimate cannot ride the trivial matching: the content lives only in the PAIR.
* `nonempty_orderedExponentRoute_iff_unboundedTwinCenters` — the disclosure iff: a route
  inhabitant exists iff twin centers are unbounded.  The backward direction consumes the new
  green lemmas `twinCenterZ_activeSieveSafe` and `wingSign_of_twin`, so the iff is contentful;
  the forward direction is the route.  Nobody can mistake this layer for progress: it RELOCATES
  the barrier to where the graded data (which exchanges move, unlike the parity sign —
  `neg_one_pow_cardFactors_exchange`) is available to a future matching construction.
-/

namespace EuclidsPath
namespace GradedKilledBoundary

open EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament
open EuclidsPath.OrderedExponent
open EuclidsPath.GenealogicalOrnament.RelativeCurvature
open EuclidsPath.GenealogicalOrnament.RelativeCurvature.RealInstance

/-! ### The two named hypothesis structures -/

/-- **Named input 1 (data): a graded killed-boundary matching.**  For each horizon `M0 ≥ 5` it
    fixes a finite window above `M0`, a killed subsector, and a sign-flipping fixed-point-free
    involution pairing the killed states; unkilled window states are survivors of the sieve.
    The seven laws are shaped one-to-one for `Finset.sum_involution`.  A HYPOTHESIS-SHAPED
    structure, never an axiom; its real inhabitant for `(ActiveSieveSafe, wingSign)` is the
    relocated parity barrier (see the disclosure iff below). -/
structure GradedKilledBoundaryMatching (SafeAt : ℕ → Prop) (sign : ℕ → ℤ) where
  window : ℕ → Finset ℕ
  killed : ℕ → Finset ℕ
  pair : ℕ → ℕ → ℕ
  window_above : ∀ M0, 5 ≤ M0 → ∀ m ∈ window M0, M0 < m
  killed_subset : ∀ M0, 5 ≤ M0 → killed M0 ⊆ window M0
  survivor_of_unkilled : ∀ M0, 5 ≤ M0 → ∀ m ∈ window M0, m ∉ killed M0 → SafeAt m
  pair_mem : ∀ M0, 5 ≤ M0 → ∀ m ∈ killed M0, pair M0 m ∈ killed M0
  pair_involutive : ∀ M0, 5 ≤ M0 → ∀ m ∈ killed M0, pair M0 (pair M0 m) = m
  pair_sign_anti : ∀ M0, 5 ≤ M0 → ∀ m ∈ killed M0, sign m + sign (pair M0 m) = 0
  pair_ne : ∀ M0, 5 ≤ M0 → ∀ m ∈ killed M0, sign m ≠ 0 → pair M0 m ≠ m

/-- **Named input 2 (Prop): the signed window estimate.**  The signed sums over the SAME
    windows do not vanish.  This is the analytic (parity-barrier strength) half; the ordered
    prime blocks of the geometry file are its intended modulus realization, not forced by the
    structure — disclosed. -/
structure SignedBlockProductModulusEstimate {SafeAt : ℕ → Prop} {sign : ℕ → ℤ}
    (GKB : GradedKilledBoundaryMatching SafeAt sign) : Prop where
  window_sum_ne_zero : ∀ M0, 5 ≤ M0 → ∑ m ∈ GKB.window M0, sign m ≠ 0

/-! ### Green consequences -/

/-- **The killed sector cancels** — the matching data feeds `Finset.sum_involution` verbatim. -/
theorem killed_sum_zero {SafeAt : ℕ → Prop} {sign : ℕ → ℤ}
    (GKB : GradedKilledBoundaryMatching SafeAt sign)
    {M0 : ℕ} (h5 : 5 ≤ M0) : ∑ m ∈ GKB.killed M0, sign m = 0 :=
  Finset.sum_involution (fun m _ => GKB.pair M0 m)
    (fun m hm => GKB.pair_sign_anti M0 h5 m hm)
    (fun m hm h => GKB.pair_ne M0 h5 m hm h)
    (fun m hm => GKB.pair_mem M0 h5 m hm)
    (fun m hm => GKB.pair_involutive M0 h5 m hm)

/-- **Matching + estimate force a survivor above every horizon** — the literal form of
    "graded survivor sector ⊥ killed-boundary exact sector". -/
theorem survivor_exists {SafeAt : ℕ → Prop} {sign : ℕ → ℤ}
    (GKB : GradedKilledBoundaryMatching SafeAt sign)
    (EST : SignedBlockProductModulusEstimate GKB) :
    ∀ M0 : ℕ, 5 ≤ M0 → ∃ m : ℕ, M0 < m ∧ SafeAt m := by
  intro M0 h5
  have hsplit : ∑ m ∈ GKB.window M0 \ GKB.killed M0, sign m
      + ∑ m ∈ GKB.killed M0, sign m = ∑ m ∈ GKB.window M0, sign m :=
    Finset.sum_sdiff (GKB.killed_subset M0 h5)
  have hkz := killed_sum_zero GKB h5
  rw [hkz, add_zero] at hsplit
  have hsdiff : ∑ m ∈ GKB.window M0 \ GKB.killed M0, sign m ≠ 0 := by
    rw [hsplit]
    exact EST.window_sum_ne_zero M0 h5
  have hne : (GKB.window M0 \ GKB.killed M0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsdiff
    exact hsdiff rfl
  obtain ⟨m, hm⟩ := hne
  obtain ⟨hmw, hmk⟩ := Finset.mem_sdiff.mp hm
  exact ⟨m, GKB.window_above M0 h5 m hmw, GKB.survivor_of_unkilled M0 h5 m hmw hmk⟩

/-! ### The real pair and the genuine bridge to the certificate family -/

/-- The route's real instantiation: the project's sieve predicate and the Liouville wing sign. -/
abbrev RealMatching := GradedKilledBoundaryMatching ActiveSieveSafe wingSign

/-- The packaged route (Type: carries the matching data and the estimate over it). -/
structure OrderedExponentRoute where
  gkb : RealMatching
  est : SignedBlockProductModulusEstimate gkb

/-- **THE BRIDGE (green, genuine construction)**: the route literally builds the certificate
    family demanded by `RelativeCurvatureRealizationProblem` — `relIndex := -5` with the
    collapse field discharged by the forced survivor.  Nothing here proves the route itself. -/
def relativeCurvatureRealization_of_orderedExponentRoute (R : OrderedExponentRoute) :
    RelativeCurvatureRealizationProblem := fun M0 h5 =>
  { relIndex := -5
    noSafeHole_relIndex_zero := fun hNo => by
      obtain ⟨m, hm, hsafe⟩ := survivor_exists R.gkb R.est M0 h5
      exact absurd hsafe (hNo m hm)
    relIndex_computed := rfl }

/-- **Green conditional**: the route reaches the twin goal through the EXISTING adapter of the
    ornament route.  Conditional only on the two named inputs packaged in `R`. -/
theorem twinLowersInfinite_of_orderedExponentRoute (R : OrderedExponentRoute) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_relativeCurvatureRealization
    (relativeCurvatureRealization_of_orderedExponentRoute R)

/-! ### Contentfulness witness: a toy model where the machinery does real work -/

private theorem neg_one_pow_succ_cancel (n : ℕ) :
    (-1 : ℤ) ^ n + (-1 : ℤ) ^ (n + 1) = 0 := by
  rw [pow_succ]
  ring

/-- Toy model: `SafeAt := (5 < ·)`, `sign := (−1)^·`, window `(M0, M0+3]`, killed
    `{M0+1, M0+2}` paired by swap.  The killed sector is NONEMPTY and the pairing genuinely
    flips signs — the cancellation machinery is consumed contentfully. -/
def toyMatching : GradedKilledBoundaryMatching (fun m => 5 < m) (fun m => (-1) ^ m) where
  window M0 := Finset.Ioc M0 (M0 + 3)
  killed M0 := {M0 + 1, M0 + 2}
  pair M0 m := if m = M0 + 1 then M0 + 2 else M0 + 1
  window_above M0 _ m hm := (Finset.mem_Ioc.mp hm).1
  killed_subset M0 _ := by
    intro m hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rw [Finset.mem_Ioc]
    omega
  survivor_of_unkilled M0 h5 m hm hk := by
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  pair_mem M0 _ m hm := by
    rw [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    split_ifs <;> omega
  pair_involutive M0 _ m hm := by
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    split_ifs <;> omega
  pair_sign_anti M0 _ m hm := by
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · rw [if_pos rfl]
      exact neg_one_pow_succ_cancel (M0 + 1)
    · rw [if_neg (by omega)]
      rw [add_comm]
      exact neg_one_pow_succ_cancel (M0 + 1)
  pair_ne M0 _ m hm _ := by
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    split_ifs <;> omega

/-- The toy estimate: the three-term window sum is `−(−1)^{M0} ≠ 0`. -/
theorem toyEstimate : SignedBlockProductModulusEstimate toyMatching := by
  constructor
  intro M0 h5
  show ∑ m ∈ Finset.Ioc M0 (M0 + 3), (-1 : ℤ) ^ m ≠ 0
  have hset : Finset.Ioc M0 (M0 + 3) = {M0 + 1, M0 + 2, M0 + 3} := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hset,
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
    Finset.sum_singleton]
  have h1 : ((-1 : ℤ)) ^ (M0 + 1) = (-1) ^ M0 * (-1) := by rw [pow_succ]
  have h2 : ((-1 : ℤ)) ^ (M0 + 2) = (-1) ^ M0 := by
    rw [pow_add]
    norm_num
  have h3 : ((-1 : ℤ)) ^ (M0 + 3) = (-1) ^ M0 * (-1) := by
    rw [pow_add]
    norm_num
  rw [h1, h2, h3]
  have hx : ((-1 : ℤ)) ^ M0 ≠ 0 := pow_ne_zero _ (by norm_num)
  intro h
  apply hx
  linarith

/-- Non-vacuity summary: in the toy model the route machinery forces a survivor above every
    horizon — the SHAPE is inhabited where it does real work. -/
theorem toy_route_survivor : ∀ M0 : ℕ, 5 ≤ M0 → ∃ m : ℕ, M0 < m ∧ 5 < m :=
  survivor_exists toyMatching toyEstimate

/-! ### Anti-cheat interlocks -/

/-- ANTI-CHEAT 1: the matching ALONE is free — the all-empty instance exists for ANY pair.
    No theorem may consume only the matching and claim content. -/
def trivialMatching (SafeAt : ℕ → Prop) (sign : ℕ → ℤ) :
    GradedKilledBoundaryMatching SafeAt sign where
  window _ := ∅
  killed _ := ∅
  pair _ m := m
  window_above _ _ m hm := absurd hm (Finset.notMem_empty m)
  killed_subset _ _ := Finset.empty_subset _
  survivor_of_unkilled _ _ m hm _ := absurd hm (Finset.notMem_empty m)
  pair_mem _ _ m hm := absurd hm (Finset.notMem_empty m)
  pair_involutive _ _ m hm := absurd hm (Finset.notMem_empty m)
  pair_sign_anti _ _ m hm := absurd hm (Finset.notMem_empty m)
  pair_ne _ _ m hm := absurd hm (Finset.notMem_empty m)

/-- ANTI-CHEAT 2: the estimate cannot ride the trivial matching — empty windows sum to zero.
    The content lives ONLY in the interlock of the two structures. -/
theorem no_estimate_over_trivialMatching (SafeAt : ℕ → Prop) (sign : ℕ → ℤ) :
    ¬ SignedBlockProductModulusEstimate (trivialMatching SafeAt sign) := fun EST =>
  EST.window_sum_ne_zero 5 le_rfl (by
    show ∑ m ∈ (∅ : Finset ℕ), sign m = 0
    exact Finset.sum_empty)

/-! ### The disclosure iff: possessing the route ⟺ the twin conjecture -/

/-- **DISCLOSURE (house convention): a route inhabitant exists iff twin centers are unbounded.**
    Forward: the route forces safe holes, which are twins (`safeHole_implies_twin`).  Backward:
    a twin above each horizon builds a singleton-window route — this direction consumes the NEW
    green lemmas `twinCenterZ_activeSieveSafe` (the wing-primality collapse of divisors) and
    `wingSign_of_twin`, so the equivalence is contentful.  The route is exactly the parity
    barrier in graded matching + signed-window form; it is NOT a shortcut. -/
theorem nonempty_orderedExponentRoute_iff_unboundedTwinCenters :
    Nonempty OrderedExponentRoute ↔ (∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m) := by
  constructor
  · rintro ⟨R⟩ M0
    obtain ⟨m, hm, hsafe⟩ := survivor_exists R.gkb R.est (max M0 5) (le_max_right _ _)
    have h1 : 1 ≤ m := by omega
    exact ⟨m, lt_of_le_of_lt (le_max_left _ _) hm, safeHole_implies_twin h1 hsafe⟩
  · intro H
    choose t ht htwin using H
    refine ⟨⟨
      { window := fun M0 => {t M0}
        killed := fun _ => ∅
        pair := fun _ m => m
        window_above := fun M0 _ m hm => by
          rw [Finset.mem_singleton] at hm
          exact hm ▸ ht M0
        killed_subset := fun _ _ => Finset.empty_subset _
        survivor_of_unkilled := fun M0 _ m hm _ => by
          rw [Finset.mem_singleton] at hm
          subst hm
          exact twinCenterZ_activeSieveSafe (by have := ht M0; omega) (htwin M0)
        pair_mem := fun _ _ m hm => absurd hm (Finset.notMem_empty m)
        pair_involutive := fun _ _ m hm => absurd hm (Finset.notMem_empty m)
        pair_sign_anti := fun _ _ m hm => absurd hm (Finset.notMem_empty m)
        pair_ne := fun _ _ m hm => absurd hm (Finset.notMem_empty m) }, ?_⟩⟩
    constructor
    intro M0 _
    show ∑ m ∈ ({t M0} : Finset ℕ), wingSign m ≠ 0
    rw [Finset.sum_singleton, wingSign_of_twin (htwin M0)]
    norm_num

end GradedKilledBoundary
end EuclidsPath
