/-
Step00RelativeOrnamentCurvatureCorrections.lean

Purpose
=======

This file is the corrected relative-curvature scaffold for the twin-ornament
route.

It implements the following audit conclusions.

1. The relative value `relIndex = -5` is Not proved here.  It is a named
   local certificate field, Not a global assumption and Not a proof placeholder.
2. The absolute computation for a fixed cone graph must Not be used as the
   relative sieve index for arbitrary boundaries.
3. The green logic is only this:

      relIndex = -5
      no safe hole -> relIndex = 0
      ----------------------------
      Not no safe hole
      ----------------------------
      safe hole
      ----------------------------
      twin witness

4. The infinite theorem is therefore conditional on a family of such relative
   curvature certificates on the tail `M0 >= 5`.

This file is intentionally generic.  In the integrated project, instantiate
`SafeAt` with the real active-sieve safe-hole predicate and `TwinCenterZ` with
the real residual twin-center predicate.

No proof placeholders or new primitive declarations are used.
-/

import Mathlib

namespace EuclidsPath
namespace GenealogicalOrnament
namespace RelativeCurvature

/-!
Pointwise safe-hole scaffold
============================

`SafeAt m` means that the center `m` is an actual survivor/safe-hole candidate
above the current boundary.  The real project should instantiate it with the
active triangular sieve safe predicate.
-/

/-- No pointwise safe hole above a boundary. -/
def PointwiseNoSafeHoleAbove (SafeAt : Nat -> Prop) (M0 : Nat) : Prop :=
  ∀ m : Nat, M0 < m -> ¬ (SafeAt m)

/-- The elementary fact that every witness strictly above a natural boundary is
positive.  This is useful when the real `safeHole_implies_twin` lemma asks for
`1 <= m`. -/
theorem one_le_of_boundary_lt {M0 m : Nat} (hm : M0 < m) : 1 <= m := by
  have h0m : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le M0) hm
  exact Nat.succ_le_of_lt h0m

/-- Negating `PointwiseNoSafeHoleAbove` produces an explicit safe-hole witness.
This is kept as a separate lemma so the main curvature theorem does Not rely on
an inline `push_neg`. -/
theorem exists_safeHole_of_not_pointwiseNoSafeHoleAbove
    {SafeAt : Nat -> Prop} {M0 : Nat}
    (h : ¬ (PointwiseNoSafeHoleAbove SafeAt M0)) :
    ∃ m : Nat, M0 < m ∧ SafeAt m := by
  classical
  unfold PointwiseNoSafeHoleAbove at h
  push_neg at h
  exact h

/-!
Relative curvature certificate
==============================

This is the honest hard input.  The field `relIndex_computed` is the named
relative-curvature computation.  It is Not derived here.
-/

/-- A pointwise relative-curvature certificate at one boundary.

The intended interpretation of `relIndex` is the relative Euler/curvature index
`chi(Ornament, KilledBoundary)` after the killed/boundary subcomplex has been
factored out.  This file does not construct that quotient; it only records the
certificate shape.  It is Not the absolute Euler characteristic of a fixed toy
graph.

The field `relIndex_computed` is the hard parity-barrier certificate.  Any
result using this structure is conditional on having this certificate.
-/
structure RelativeCurvatureCertificate
    (SafeAt : Nat -> Prop) (M0 : Nat) where
  relIndex : Int
  /-- If no safe hole ∃ above `M0`, the relative survivor quotient
  collapses to zero index. -/
  noSafeHole_relIndex_zero :
    PointwiseNoSafeHoleAbove SafeAt M0 -> relIndex = 0
  /-- Hard relative-curvature input.  This is a local certificate field, Not a
  global assumption.  It must eventually be proved by an explicit relative matching
  or an equivalent exact killed-boundary computation. -/
  relIndex_computed :
    relIndex = -5

/-- Audit projection: the only numerical hard input carried by a relative
curvature certificate is exactly `relIndex = -5`. -/
theorem relativeCurvature_hard_input_is_relIndex
    {SafeAt : Nat -> Prop} {M0 : Nat}
    (C : RelativeCurvatureCertificate SafeAt M0) :
    C.relIndex = -5 :=
  C.relIndex_computed

/-- Relative curvature excludes the no-safe-hole state. -/
theorem not_noSafeHole_of_relativeCurvature
    {SafeAt : Nat -> Prop} {M0 : Nat}
    (C : RelativeCurvatureCertificate SafeAt M0) :
    ¬ (PointwiseNoSafeHoleAbove SafeAt M0) := by
  intro hNo
  have h0 : C.relIndex = 0 := C.noSafeHole_relIndex_zero hNo
  have hm5 : C.relIndex = -5 := C.relIndex_computed
  have hbad : (0 : Int) = -5 := by
    calc
      (0 : Int) = C.relIndex := h0.symm
      _ = -5 := hm5
  have hneq : (0 : Int) ≠ -5 := by norm_num
  exact hneq hbad

/-- A relative-curvature certificate forces a pointwise safe hole above the
boundary. -/
theorem safeHole_exists_of_relativeCurvature
    {SafeAt : Nat -> Prop} {M0 : Nat}
    (C : RelativeCurvatureCertificate SafeAt M0) :
    ∃ m : Nat, M0 < m ∧ SafeAt m := by
  exact exists_safeHole_of_not_pointwiseNoSafeHoleAbove
    (not_noSafeHole_of_relativeCurvature C)

/-- The safe-hole-to-twin form with an explicit positivity side condition. -/
def PointwiseSafeHoleImpliesTwin
    (SafeAt TwinCenterZ : Nat -> Prop) (M0 : Nat) : Prop :=
  ∀ m : Nat, M0 < m -> 1 <= m -> SafeAt m -> TwinCenterZ m

/-- A relative-curvature certificate plus the real sieve lemma
`safe hole -> twin` gives a twin witness above the boundary. -/
theorem twin_exists_above_of_relativeCurvature
    {SafeAt TwinCenterZ : Nat -> Prop} {M0 : Nat}
    (C : RelativeCurvatureCertificate SafeAt M0)
    (safe_to_twin : PointwiseSafeHoleImpliesTwin SafeAt TwinCenterZ M0) :
    ∃ m : Nat, M0 < m ∧ TwinCenterZ m := by
  rcases safeHole_exists_of_relativeCurvature C with ⟨m, hm, hsafe⟩
  exact ⟨m, hm, safe_to_twin m hm (one_le_of_boundary_lt hm) hsafe⟩

/-- Variant for projects whose `safeHole_implies_twin` lemma does Not require
an explicit `1 <= m` side condition. -/
def PointwiseSafeHoleImpliesTwinNoBase
    (SafeAt TwinCenterZ : Nat -> Prop) (M0 : Nat) : Prop :=
  ∀ m : Nat, M0 < m -> SafeAt m -> TwinCenterZ m

/-- Same as `twin_exists_above_of_relativeCurvature`, without the positivity
side condition on the safe-hole-to-twin lemma. -/
theorem twin_exists_above_of_relativeCurvature_noBase
    {SafeAt TwinCenterZ : Nat -> Prop} {M0 : Nat}
    (C : RelativeCurvatureCertificate SafeAt M0)
    (safe_to_twin : PointwiseSafeHoleImpliesTwinNoBase SafeAt TwinCenterZ M0) :
    ∃ m : Nat, M0 < m ∧ TwinCenterZ m := by
  rcases safeHole_exists_of_relativeCurvature C with ⟨m, hm, hsafe⟩
  exact ⟨m, hm, safe_to_twin m hm hsafe⟩

/-!
Tail family from center 5
=========================

The finite anomaly at center `4` should be handled by explicit computation.
The infinite relative-curvature route only has to start from the tail
`M0 >= 5`.
-/

/-- Cofinality of the twin-center predicate. -/
def TwinCenterZCofinal (TwinCenterZ : Nat -> Prop) : Prop :=
  ∀ M0 : Nat, ∃ m : Nat, M0 < m ∧ TwinCenterZ m

/-- Tail cofinality from the boundary `5`. -/
def TwinCenterZCofinalFromFive (TwinCenterZ : Nat -> Prop) : Prop :=
  ∀ M0 : Nat, 5 <= M0 -> ∃ m : Nat, M0 < m ∧ TwinCenterZ m

/-- Tail cofinality plus the seed at center `5` gives full cofinality. -/
theorem twinCenterZCofinal_of_fromFive
    {TwinCenterZ : Nat -> Prop}
    (seed_five : TwinCenterZ 5)
    (H : TwinCenterZCofinalFromFive TwinCenterZ) :
    TwinCenterZCofinal TwinCenterZ := by
  intro M0
  by_cases hsmall : M0 < 5
  · exact ⟨5, hsmall, seed_five⟩
  · have htail : 5 <= M0 := Nat.le_of_not_gt hsmall
    exact H M0 htail

/-- A family of relative-curvature certificates on the tail `M0 >= 5`. -/
structure RelativeCurvatureFamilyFromFive
    (SafeAt TwinCenterZ : Nat -> Prop) where
  seed_five : TwinCenterZ 5
  certificateAt :
    ∀ M0 : Nat, 5 <= M0 -> RelativeCurvatureCertificate SafeAt M0
  safe_to_twin_tail :
    ∀ M0 : Nat, 5 <= M0 ->
      PointwiseSafeHoleImpliesTwin SafeAt TwinCenterZ M0

/-- A tail family of relative-curvature certificates gives cofinal twin centers. -/
theorem twinCofinal_of_relativeCurvatureFamilyFromFive
    {SafeAt TwinCenterZ : Nat -> Prop}
    (F : RelativeCurvatureFamilyFromFive SafeAt TwinCenterZ) :
    TwinCenterZCofinal TwinCenterZ := by
  apply twinCenterZCofinal_of_fromFive F.seed_five
  intro M0 h5
  exact twin_exists_above_of_relativeCurvature
    (F.certificateAt M0 h5)
    (F.safe_to_twin_tail M0 h5)

/-- Tail family variant without an explicit positivity side condition in the
safe-hole-to-twin lemma. -/
structure RelativeCurvatureFamilyFromFiveNoBase
    (SafeAt TwinCenterZ : Nat -> Prop) where
  seed_five : TwinCenterZ 5
  certificateAt :
    ∀ M0 : Nat, 5 <= M0 -> RelativeCurvatureCertificate SafeAt M0
  safe_to_twin_tail :
    ∀ M0 : Nat, 5 <= M0 ->
      PointwiseSafeHoleImpliesTwinNoBase SafeAt TwinCenterZ M0

/-- Cofinality from a tail relative-curvature family, no-base variant. -/
theorem twinCofinal_of_relativeCurvatureFamilyFromFive_noBase
    {SafeAt TwinCenterZ : Nat -> Prop}
    (F : RelativeCurvatureFamilyFromFiveNoBase SafeAt TwinCenterZ) :
    TwinCenterZCofinal TwinCenterZ := by
  apply twinCenterZCofinal_of_fromFive F.seed_five
  intro M0 h5
  exact twin_exists_above_of_relativeCurvature_noBase
    (F.certificateAt M0 h5)
    (F.safe_to_twin_tail M0 h5)

/-!
Aggregate compatibility layer
=============================

Some earlier bridge files package `SafeHoleAbove M0` as an aggregate existence
predicate instead of a pointwise predicate `SafeAt m`.  The following minimal
layer records the same corrected relative-curvature logic for that style.
-/

/-- Aggregate no-safe-hole predicate, compatible with previous bridge files. -/
def AggregateNoSafeHoleAbove (SafeHoleAbove : Nat -> Prop) (M0 : Nat) : Prop :=
  ¬ (SafeHoleAbove M0)

/-- Relative-curvature certificate for aggregate safe-hole predicates. -/
structure AggregateRelativeCurvatureCertificate
    (SafeHoleAbove : Nat -> Prop) (M0 : Nat) where
  relIndex : Int
  noSafeHole_relIndex_zero :
    AggregateNoSafeHoleAbove SafeHoleAbove M0 -> relIndex = 0
  relIndex_computed :
    relIndex = -5

/-- Aggregate audit projection. -/
theorem aggregate_relativeCurvature_hard_input_is_relIndex
    {SafeHoleAbove : Nat -> Prop} {M0 : Nat}
    (C : AggregateRelativeCurvatureCertificate SafeHoleAbove M0) :
    C.relIndex = -5 :=
  C.relIndex_computed

/-- Aggregate relative curvature excludes aggregate no-safe-hole. -/
theorem aggregate_not_noSafeHole_of_relativeCurvature
    {SafeHoleAbove : Nat -> Prop} {M0 : Nat}
    (C : AggregateRelativeCurvatureCertificate SafeHoleAbove M0) :
    ¬ (AggregateNoSafeHoleAbove SafeHoleAbove M0) := by
  intro hNo
  have h0 : C.relIndex = 0 := C.noSafeHole_relIndex_zero hNo
  have hm5 : C.relIndex = -5 := C.relIndex_computed
  have hbad : (0 : Int) = -5 := by
    calc
      (0 : Int) = C.relIndex := h0.symm
      _ = -5 := hm5
  have hneq : (0 : Int) ≠ -5 := by norm_num
  exact hneq hbad

/-- Aggregate relative curvature forces aggregate safe hole. -/
theorem aggregate_safeHole_of_relativeCurvature
    {SafeHoleAbove : Nat -> Prop} {M0 : Nat}
    (C : AggregateRelativeCurvatureCertificate SafeHoleAbove M0) :
    SafeHoleAbove M0 := by
  classical
  by_contra hNo
  exact aggregate_not_noSafeHole_of_relativeCurvature C hNo

/-- Aggregate safe-hole-to-twin condition. -/
def AggregateSafeHoleImpliesTwin
    (SafeHoleAbove TwinCenterZ : Nat -> Prop) (M0 : Nat) : Prop :=
  SafeHoleAbove M0 -> ∃ m : Nat, M0 < m ∧ TwinCenterZ m

/-- Aggregate relative curvature plus aggregate safe-hole-to-twin gives a twin
witness above the boundary. -/
theorem aggregate_twin_exists_above_of_relativeCurvature
    {SafeHoleAbove TwinCenterZ : Nat -> Prop} {M0 : Nat}
    (C : AggregateRelativeCurvatureCertificate SafeHoleAbove M0)
    (safe_to_twin : AggregateSafeHoleImpliesTwin SafeHoleAbove TwinCenterZ M0) :
    ∃ m : Nat, M0 < m ∧ TwinCenterZ m := by
  exact safe_to_twin (aggregate_safeHole_of_relativeCurvature C)

/-!
Audit notes encoded as theorem names
====================================

The following names are intentionally explicit.  They make it hard to treat the
relative scaffold as an unconditional proof.
-/

/-- Any pointwise cofinal theorem from this file is conditional on a family of
relative curvature certificates. -/
def pointwise_family_required_for_tail_cofinality
    {SafeAt TwinCenterZ : Nat -> Prop}
    (F : RelativeCurvatureFamilyFromFive SafeAt TwinCenterZ) :
    ∀ M0 : Nat, 5 <= M0 -> RelativeCurvatureCertificate SafeAt M0 :=
  F.certificateAt

/-- The `-5` value required at each tail boundary is exactly the hard field of
the corresponding certificate. -/
theorem relIndex_minus_five_required_at_tail
    {SafeAt TwinCenterZ : Nat -> Prop}
    (F : RelativeCurvatureFamilyFromFive SafeAt TwinCenterZ)
    (M0 : Nat) (h5 : 5 <= M0) :
    (F.certificateAt M0 h5).relIndex = -5 :=
  (F.certificateAt M0 h5).relIndex_computed

end RelativeCurvature
end GenealogicalOrnament
end EuclidsPath
