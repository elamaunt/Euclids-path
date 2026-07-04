/-
  RiemannSpectralAnchor — the Hilbert–Pólya anchor in two layers: the data form and the operator.

  The classical dream (Hilbert–Pólya): the nontrivial zeros of zeta are `1/2 + t·I`,
  where `t` ranges over the SPECTRUM of a self-adjoint operator; self-adjointness gives
  reality of `t` — and the zeros themselves land on the critical line. Here this dream
  is decomposed into two honest layers:

  (a) DATA LAYER — `SpectralRealisation`: there exists a set `E ⊆ ℝ`,
      realising all nontrivial zeros in the form `1/2 + t·I`, `t ∈ E`.
      Green: realisation ⟹ critical line ⟹ mathlib-`RiemannHypothesis`
      (the bridge is literal: mathlib-RH is exactly "all nontrivial zeros on the line",
      the routes `riemannHypothesis_of_*` from RiemannBranch are not needed — they are costlier,
      requiring the named inputs `EngineBridge`/`TrivialBelowZeroClassification`).

  (b) MANDATORY GOAL-RENAMING AUDIT — the converse is built FOR FREE: under RH we take
      `E := Set.univ` and `t := ρ.im`. Result: `spectralRealisation_iff_critical` and
      `spectralRealisation_iff_RH` — the data layer is EQUIVALENT to the goal literally,
      a mirror of `offCriticalBridge_iff_RH`. Audit conclusion: a substantive anchor
      must carry an OPERATOR, not a bare set of real numbers.

  (c) OPERATOR LAYER — `OperatorSpectralAnchor`: a self-adjoint bounded
      operator `T` on a complex Hilbert space whose spectrum
      realises the zeros. Green bridge `operatorAnchor_implies_realisation`:
      the spectrum of a self-adjoint operator is real (mathlib
      `IsSelfAdjoint.mem_spectrum_eq_re`, C*-algebra `H →L[ℂ] H` — mathlib
      instance from Analysis/CStarAlgebra/ContinuousLinearMap). The converse audit
      of layer (c) does NOT pass for free — and that is good: the green negative theorem
      `no_operatorAnchor_of_unbounded_ordinates` shows that when
      the ordinates of zeros are unbounded (classical fact, ABSENT in mathlib v4.31)
      a BOUNDED anchor is impossible altogether: the spectrum of a bounded operator
      lies in the ball of radius ‖T‖ (`spectrum.norm_le_norm_of_mem`). An honest
      Hilbert–Pólya operator must be UNBOUNDED; in mathlib v4.31
      there is `LinearPMap.adjoint` and `IsSelfAdjoint` for `E →ₗ.[𝕜] E`
      (Analysis/InnerProductSpace/LinearPMap), but there is NO spectral theory
      of unbounded operators (no `spectrum` for `LinearPMap`, no
      spectral theorem) — this is the exact missing piece of the anchor.

  CONNECTION with RiemannSpectralAnchorAudit (without duplicating its abstract audit):
  `zeroOrdinateLaw` — a concrete `DataAnchoredLaw` (Zero := nontrivial zeros,
  Atom := ℝ), `zeroOrdinateInvariantAnchor` — a genuine `SpectralInvariantAnchor`
  (invariant = imaginary part; respects IS PROVED), `zeroOrdinateBridge_iff_RH` —
  the Prop-shadow of this data-law is again literally RH. What is missing for
  `NonVacuousDataAnchor.separates` — TWO nontrivial zeros with distinct
  ordinates; in mathlib v4.31 there is NOT A SINGLE concrete nontrivial zero.

  HONESTY: this is NOT a solution to RH and NOT Gödel. Red def-named inputs — named
  data that mathematics MUST supply; green theorems — that the front
  closes GIVEN the anchor. Quarantine (CausalClosureAxiom) is NOT imported;
  axiom/sorry/native_decide are absent; taint 47 does not change.
-/
import Mathlib
import EuclidsPath.Engine.RiemannBranch
import EuclidsPath.Engine.RiemannSpectralAnchorAudit

set_option autoImplicit false

namespace EuclidsPath.RiemannSpectralAnchor

open Complex EuclidsPath.RiemannBranch

/-! ## §0. Arithmetic of the form `1/2 + t·I` -/

/-- The real part of the form `1/2 + t·I` equals `1/2`. -/
lemma half_add_mul_I_re (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).re = 1 / 2 := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
  ring

/-- The imaginary part of the form `1/2 + t·I` equals `t`. -/
lemma half_add_mul_I_im (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).im = t := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
  ring

/-- A point on the critical line HAS the form `1/2 + t·I` with `t := ρ.im` —
    the technical core of the goal-renaming audit (the converse is built for free). -/
lemma eq_half_add_of_re_eq_half {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ρ = 1 / 2 + (ρ.im : ℂ) * Complex.I := by
  have h := (Complex.re_add_im ρ).symm
  rw [hre] at h
  rw [h]
  norm_num

/-! ## §1. Layer (a): the data form -/

/--
  **`SpectralRealisation` — RED named input of the data layer (Hilbert–Pólya anchor without
  an operator).** There exists a set `E ⊆ ℝ` such that every nontrivial
  zero `ρ` (in the sense of mathlib-RH, predicate `NontrivialZeroM` from RiemannBranch)
  has the form `1/2 + t·I` with `t ∈ E`: the zeros are realised by a real "spectrum".

  ⚠️ The audit in §2 will show: this named input is a GOAL RENAMING of RH (`spectralRealisation_iff_RH`),
  because the set `E` is bare data with no carrier. A substantive anchor
  must carry an OPERATOR (§3). -/
def SpectralRealisation : Prop :=
  ∃ E : Set ℝ, ∀ ρ : ℂ, NontrivialZeroM ρ → ∃ t ∈ E, ρ = 1 / 2 + (t : ℂ) * Complex.I

/-- **GREEN: realisation ⟹ critical line.** From the form `1/2 + t·I`
    we immediately get `Re ρ = 1/2` for every nontrivial zero. -/
theorem spectralRealisation_implies_critical
    (h : SpectralRealisation) {ρ : ℂ} (hρ : NontrivialZeroM ρ) : ρ.re = 1 / 2 := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨t, _, hform⟩ := hE ρ hρ
  rw [hform]
  exact half_add_mul_I_re t

/-- **GREEN: realisation ⟹ mathlib-`RiemannHypothesis`.** The bridge is literal:
    mathlib-RH is exactly "every nontrivial zero has `Re = 1/2`", so
    the costly routes from RiemannBranch (`riemannHypothesis_of_engine_bridge` with
    named inputs) are not needed here. -/
theorem riemannHypothesis_of_spectralRealisation
    (h : SpectralRealisation) : RiemannHypothesis := by
  intro ρ hz htriv hne1
  exact spectralRealisation_implies_critical h ⟨hz, htriv, hne1⟩

/-! ## §2. Mandatory goal-renaming audit (mirror of `offCriticalBridge_iff_RH`) -/

/-- **AUDIT (the converse is built FOR FREE).** Under RH the realisation is assembled from nothing:
    `E := Set.univ`, `t := ρ.im` — a zero on the line reports its own ordinate.
    No operator, no spectrum: the bare data set is free. -/
theorem spectralRealisation_of_RH (hRH : RiemannHypothesis) : SpectralRealisation := by
  refine ⟨Set.univ, fun ρ hρ => ⟨ρ.im, Set.mem_univ _, ?_⟩⟩
  exact eq_half_add_of_re_eq_half (hRH ρ hρ.1 hρ.2.1 hρ.2.2)

/-- **AUDIT CONCLUSION (critical line).** The data layer ⟺ "all nontrivial zeros
    on the line" — a literal renaming of the statement about the line. -/
theorem spectralRealisation_iff_critical :
    SpectralRealisation ↔ ∀ ρ : ℂ, NontrivialZeroM ρ → ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ
    exact spectralRealisation_implies_critical h hρ
  · intro h
    refine ⟨Set.univ, fun ρ hρ => ⟨ρ.im, Set.mem_univ _, ?_⟩⟩
    exact eq_half_add_of_re_eq_half (h ρ hρ)

/--
  **`spectralRealisation_iff_RH` — MAIN AUDIT of the data layer (honesty,
  mirror of `offCriticalBridge_iff_RH`).** The named input `SpectralRealisation` is EQUIVALENT
  to mathlib-`RiemannHypothesis` — machine-verified and assumption-free. "Spectral
  realisation by a set" is not a reduction but a goal renaming: the set `E`
  carries no carrier from which the zeros are EXTRACTED.

  AUDIT CONCLUSION: a substantive Hilbert–Pólya anchor must carry an OPERATOR —
  a structure whose spectrum is real BY REASON (self-adjointness), not by
  decree. That is §3. -/
theorem spectralRealisation_iff_RH : SpectralRealisation ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_spectralRealisation, spectralRealisation_of_RH⟩

/-! ## §3. Layer (c): the operator -/

/--
  **`OperatorSpectralAnchor` — RED named input of the next layer (the genuine
  Hilbert–Pólya, bounded form).** Data: a complex Hilbert
  space `H` (mathlib structures: `NormedAddCommGroup` +
  `InnerProductSpace ℂ` + `CompleteSpace`) and a bounded operator
  `T : H →L[ℂ] H`, for which:
    * `T` is self-adjoint (`IsSelfAdjoint T`, star = mathlib adjoint);
    * every nontrivial zero has the form `1/2 + z·I` with `z ∈ spectrum ℂ T`.

  What mathematics MUST supply: the operator itself. In mathlib v4.31 there is no
  candidate, nor (for the honest unbounded form — see audit §4) even the
  spectral theory of unbounded operators. The bounded form is not canonical
  (the classical Hilbert–Pólya is an unbounded operator); here the
  BOUNDED form is honestly named — and §4 will show what it is worth. -/
def OperatorSpectralAnchor (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint T ∧
    ∀ ρ : ℂ, NontrivialZeroM ρ →
      ∃ z ∈ spectrum ℂ T, ρ = 1 / 2 + z * Complex.I

/-- **GREEN BRIDGE: operator ⟹ realisation.** The spectrum of a self-adjoint operator
    is real — mathlib `IsSelfAdjoint.mem_spectrum_eq_re` (C*-algebra
    `H →L[ℂ] H` — a ready mathlib instance). `E` := the real points of the spectrum;
    here self-adjointness is CONSUMED genuinely: without it `z` from the
    spectrum need not be real and `E ⊆ ℝ` cannot be assembled. -/
theorem operatorAnchor_implies_realisation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hA : OperatorSpectralAnchor H T) : SpectralRealisation := by
  obtain ⟨hsa, hreal⟩ := hA
  refine ⟨{t : ℝ | (t : ℂ) ∈ spectrum ℂ T}, fun ρ hρ => ?_⟩
  obtain ⟨z, hz, hform⟩ := hreal ρ hρ
  have hzre : z = (z.re : ℂ) := hsa.mem_spectrum_eq_re hz
  refine ⟨z.re, ?_, ?_⟩
  · show ((z.re : ℝ) : ℂ) ∈ spectrum ℂ T
    rw [← hzre]; exact hz
  · rw [hform, hzre, Complex.ofReal_re]

/-- **GREEN COMPOSITION: operator ⟹ mathlib-RH.** The full anchor ladder:
    self-adjoint operator realises zeros ⟹ zeros on the line ⟹ RH. -/
theorem riemannHypothesis_of_operatorAnchor
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hA : OperatorSpectralAnchor H T) : RiemannHypothesis :=
  riemannHypothesis_of_spectralRealisation (operatorAnchor_implies_realisation hA)

/-! ## §4. Audit of the operator layer: the bounded form is NOT a goal renaming — it is STRONGER than the goal -/

/--
  **Analytic named input `UnboundedZeroOrdinates`.** The ordinates of nontrivial zeros are
  unbounded: above any threshold there is a zero. Classical fact (Hardy: infinitely many
  zeros ON the line; von Mangoldt: `N(T) ~ (T/2π)log(T/2π)`), but in mathlib v4.31
  there is NOT a single concrete nontrivial zero and there is no Hardy theorem — hence
  an explicit named input rather than a theorem. -/
def UnboundedZeroOrdinates : Prop :=
  ∀ B : ℝ, ∃ ρ : ℂ, NontrivialZeroM ρ ∧ B < |ρ.im|

/--
  **GREEN NEGATIVE (audit of the operator layer).** With unbounded ordinates a
  BOUNDED anchor is impossible FOR ANY `T`: the spectrum of a bounded
  operator lies in the ball of radius `‖T‖` (`spectrum.norm_le_norm_of_mem`), and a zero
  with `|Im ρ| > ‖T‖` requires a spectral point `z = Im ρ` outside the ball.

  The meaning of the audit — asymmetry with the data layer: layer (a) collapses INTO the goal
  (`spectralRealisation_iff_RH` — a goal renaming), layer (c) in the bounded
  form falls BEYOND the goal (under classical analysis it is false, not equivalent to
  RH). An honest Hilbert–Pólya = an UNBOUNDED self-adjoint operator;
  in mathlib v4.31 there is `LinearPMap.adjoint` / `IsSelfAdjoint` for `E →ₗ.[𝕜] E`,
  but there is NO `spectrum` for `LinearPMap` and NO spectral theorem for unbounded
  operators — the exact missing piece that mathematics must supply. -/
theorem no_operatorAnchor_of_unbounded_ordinates
    (hUnb : UnboundedZeroOrdinates)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (T : H →L[ℂ] H) : ¬ OperatorSpectralAnchor H T := by
  rintro ⟨hsa, hreal⟩
  obtain ⟨ρ, hρ, hgt⟩ := hUnb ‖T‖
  obtain ⟨z, hz, hform⟩ := hreal ρ hρ
  have hzre : z = (z.re : ℂ) := hsa.mem_spectrum_eq_re hz
  have hform' : ρ = 1 / 2 + (z.re : ℂ) * Complex.I := by rw [← hzre]; exact hform
  have him : ρ.im = z.re := by rw [hform']; exact half_add_mul_I_im z.re
  have habs : |ρ.im| ≤ ‖T‖ := by
    rw [him]
    exact le_trans (Complex.abs_re_le_norm z) (spectrum.norm_le_norm_of_mem hz)
  exact absurd habs (not_le.mpr hgt)

/-! ## §5. Connection with SpectralAnchorAudit: the data level of a concrete anchor -/

open EuclidsPath.Riemann.ArithmeticTwoTransport.SpectralAnchorData

/--
  **`zeroOrdinateLaw` — a concrete data-law of the anchor (connection with the audit).**
  Zero := nontrivial zeros (subtype `NontrivialZeroM`), Atom := ℝ (ordinates),
  Anchor Z t := "Z has the form `1/2 + t·I`". This is the CANONICAL instantiation
  of `DataAnchoredLaw` from RiemannSpectralAnchorAudit for the Hilbert–Pólya anchor. -/
def zeroOrdinateLaw : DataAnchoredLaw {ρ : ℂ // NontrivialZeroM ρ} ℝ where
  Admissible := fun _ => True
  Anchor := fun Z t => (Z : ℂ) = 1 / 2 + (t : ℂ) * Complex.I

/--
  **`zeroOrdinateInvariantAnchor` — a GENUINE spectral invariant (PROVED).**
  Invariant = imaginary part: the atom `t` anchored to zero `Z` must equal
  `Im Z` — the `respects` condition from the audit holds genuinely, so a single
  atom CANNOT serve two zeros with distinct ordinates
  (`no_single_atom_anchors_two_distinct_invariants` is applicable). What is MISSING:
  `NonVacuousDataAnchor.separates` requires TWO zeros with distinct ordinates,
  while in mathlib v4.31 there is not a single concrete nontrivial zero of zeta. -/
def zeroOrdinateInvariantAnchor : SpectralInvariantAnchor zeroOrdinateLaw where
  Inv := ℝ
  zeroInv := fun Z => (Z : ℂ).im
  atomInv := id
  respects := fun Z t h => by
    show t = (Z : ℂ).im
    rw [h]
    exact (half_add_mul_I_im t).symm

/--
  **AUDIT of the Prop-shadow of the data-law: again literally RH.** The bridge
  `DataAnchoredLaw.Bridge zeroOrdinateLaw` ⟺ mathlib-`RiemannHypothesis` —
  the same fate as layer (a): the Prop-shadow of a data-law without an operator-supplier
  of atoms is a goal renaming. The lesson of the audit (SpectralAnchorAudit §2)
  is reproduced on the concrete anchor: non-vacuity must live at the level of
  DATA (extractor + invariant), and the data supplier is the operator of §3. -/
theorem zeroOrdinateBridge_iff_RH :
    DataAnchoredLaw.Bridge zeroOrdinateLaw ↔ RiemannHypothesis := by
  constructor
  · intro hB ρ hz htriv hne1
    obtain ⟨t, _, hform⟩ := hB ⟨ρ, hz, htriv, hne1⟩
    have hρform : ρ = 1 / 2 + (t : ℂ) * Complex.I := hform
    rw [hρform]
    exact half_add_mul_I_re t
  · intro hRH Z
    exact ⟨(Z : ℂ).im, trivial,
      eq_half_add_of_re_eq_half (hRH Z.val Z.prop.1 Z.prop.2.1 Z.prop.2.2)⟩

end EuclidsPath.RiemannSpectralAnchor

/-! Axiom check: only a subset of [propext, Classical.choice, Quot.sound] is admissible. -/
#print axioms EuclidsPath.RiemannSpectralAnchor.half_add_mul_I_re
#print axioms EuclidsPath.RiemannSpectralAnchor.half_add_mul_I_im
#print axioms EuclidsPath.RiemannSpectralAnchor.eq_half_add_of_re_eq_half
#print axioms EuclidsPath.RiemannSpectralAnchor.SpectralRealisation
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_implies_critical
#print axioms EuclidsPath.RiemannSpectralAnchor.riemannHypothesis_of_spectralRealisation
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_of_RH
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_iff_critical
#print axioms EuclidsPath.RiemannSpectralAnchor.spectralRealisation_iff_RH
#print axioms EuclidsPath.RiemannSpectralAnchor.OperatorSpectralAnchor
#print axioms EuclidsPath.RiemannSpectralAnchor.operatorAnchor_implies_realisation
#print axioms EuclidsPath.RiemannSpectralAnchor.riemannHypothesis_of_operatorAnchor
#print axioms EuclidsPath.RiemannSpectralAnchor.UnboundedZeroOrdinates
#print axioms EuclidsPath.RiemannSpectralAnchor.no_operatorAnchor_of_unbounded_ordinates
#print axioms EuclidsPath.RiemannSpectralAnchor.zeroOrdinateLaw
#print axioms EuclidsPath.RiemannSpectralAnchor.zeroOrdinateInvariantAnchor
#print axioms EuclidsPath.RiemannSpectralAnchor.zeroOrdinateBridge_iff_RH
