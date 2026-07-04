# 37. Riemann fronts of the session

<!--navtop-->
[← 36. Navier–Stokes: the equation](36_NavierStokes.md) · [Table of contents](00_Overview.md) · [38. Riemann through the first cause →](38_RiemannFirstCause.md)
<!--/navtop-->



> Lean: `Engine/RiemannTrivialZeros.lean` (input No. 1 closed — 🟢), `Engine/RiemannRankProjection.lean` +
> `Engine/RiemannRankProjectionAudit.lean` (vacuity episode No. 2), `Engine/RiemannTwoTransportFront.lean`,
> `Engine/RiemannArithmeticTwoTransport.lean`, `Engine/RiemannSpectralAnchorAudit.lean`,
> `Engine/RiemannLayerBoxFront.lean` (25 bricks), `Engine/RiemannTerminalRankFront.lean` (18 bricks).
> Prose context: [30. The Riemann hypothesis](30_RiemannBranch.md), [24](24_BoundaryDecomp.md) (the dissipative cascade). All theorems cited here are
> 🟢 under the standard axioms, without `step00FirstCause`; RH itself is 🔴 open, and nothing below softens that.

The repository's Riemann branch is contraposition through the engine: a nontrivial zero off the critical line
would have to feed a perpetual paid dynamics, which does not exist (`no_riemannEngineFactoryOff`). All
the analysis, meanwhile, lived in two inputs — recall that an input (a gate) is an honestly named red
statement still missing on the way to the goal (see the [glossary](GLOSSARY.md)): the classification of zeros in the left half-plane
(input No. 1) and the bridge "zero ⟹ engine" (`EngineBridge`, input No. 2 with its retinue).

This chapter is the chronicle of a single session: one input
genuinely closed, one wrapper exposed as empty, one route provably circular, one
honesty criterion provably wrong — and, in the remainder, two live inputs.

## Input No. 1 closed: the trivial zeros

**`trivialBelowZeroClassification`** 🟢: every zero of $\zeta$ with $\mathrm{Re}\,s \le 0$ equals $-2(n+1)$.
The route comes entirely from mathlib: $s=0$ is excluded (`riemannZeta_zero` $= -1/2$); for $s \ne 0$ the functional
equation `riemannZeta_one_sub` at the point $w = 1-s$ (where $\mathrm{Re}\,w \ge 1$), the nontrivial factors
are nonzero (`riemannZeta_ne_zero_of_one_le_re`, `Gamma_ne_zero_of_re_pos`, `cpow_ne_zero`), so it is
the cosine that vanished: $\cos(\pi(1-s)/2)=0 \Rightarrow s = -2k$, $k \ge 1$.

The former "analytic input"
turned out to be derivable: mathlib supplied the values of the trivial zeros, and the reverse classification
follows from that same source.

The adapters `trivialBelowZeroClassification_proved` / `_branch_proved` plug the theorem into the exact
Props of `RiemannEngine`/`RiemannBranch`; the unconditional consequences: `nontrivialZero_in_strip_unconditional`
(localization to the strip $0<\mathrm{Re}\,\rho<1$ — now a theorem) and the pair
`riemannHypothesis_of_engineBridge_only` / `riemannHypothesis_of_twoTransportBridge_only` — RH is conditional
*only* on the bridge.

**Conclusion.** This is an honest closure: the input is removed, and the load did not move elsewhere — it vanished.

## Vacuity No. 2: the rank-jump target is unanchored

Symmetric in genre, opposite in sign, comes a vacuity episode: this is our name for
the situation where a candidate goal holds for free, by a stub witness (see the [glossary](GLOSSARY.md)).
Route No. 8 decomposed the bridge through
Liouville: a violation of the RH bound $|L(X)| \le C\,X^{1/2+\varepsilon}$ ⟹ overflow of the relevant part
⟹ an unpaired carrier ⟹ a rank-jump.

The `RiemannRankProjection` bricks are proven honestly:
`rankProjectionSoundness`, the discrete first-crossing lemma `exists_firstOverflowCrossing` (Nat.find),
the assembly `gradualOverflow_forces_rankJump`. Piece (A) is honest too:
`relevantViolation_gives_window` — a concrete ledger (mass $=|L_{\mathrm{relevant}}|$, capacity
$=\lceil X^{1/2+\varepsilon}\rceil$) with a genuine overflow window.

But an adversarial probe (`RiemannRankProjectionAudit`) cracked the target open. `TwinCarrierEnergyJump` is a bare
`Nonempty (RankEnergyJump …)` with no tie to the violation: for the natural system (rank $=\Omega$,
sign $=\lambda$) it is an *unconditional theorem* `liouvilleRankSystem_has_jump` (states 1 and 2 already
jump), whence `localizationTarget_trivial_for_natural_system` — the central node is trivial.

Worse:
`fullLocalization_noInput` — the full package `LiouvilleToTwinLocalization` is inhabited with **zero
analytic input** (the partition "everything is relevant", `irrelevantCancellation_trivial`,
`paired := False`); the field `paired` is inert (`unpaired_gives_jump` never mentions it), and rank-visibility
is discharged for free (`trivialVisibility`: the pair $\langle 0,1\rangle$ for any carrier). The decomposition
"cancellation + pairing" was false: the pairing side carried no weight.

The honest remainder is
**`wall_relevant`** / **`wall_global`** 🟢: for any system usable downstream (jump-free),
pairing is exactly $\lnot$`LiouvilleViolation`, i.e. the wall of route No. 8 is the RH-strength bound on $L$ itself.
Nothing is lost except an illusion: RH is not proven, the wrapper is cracked open, and the target demands a reformulation
tied to the violation.

## Two-transport: circularity is inherited

Live input No. 1 (the bridge) is decomposed into `TwoTransportLaw` — a non-opaque replacement for `EngineBridge` in which all
paid-dynamics obligations are exposed as fields. The machine honesty of the concrete layer is merciless:
**`no_coherent_twoTransportLaw`** 🟢 — a coherent law (`CoherentLaw`: the law's universe coincides
with the universe of its paid dynamics) for a real zero is empty, since it would build a factory, and a factory
is unconditionally empty (the engine-killer).

And the main point, **`coherentTwoTransportBridge_iff_RH`** 🟢 — a coherent
two-transport bridge ⟺ RH *verbatim*. The decomposition is a map of obligations, not a non-circular path;
the audit gates `zero_anchored`/`non_circular` are free (`regateTrivially` regates them into `True`) —
markers, not checks.

## The arithmetic atom and the polar collapse

The answer to the collapse is a non-engine target: `ArithmeticTransportAtom`, six positive parameters with
the twin-layer identity $qrs = abv + 2$ (`natGap_eq_two`: the gap is exactly 2).

But the integration audit
showed that here too the tie to the zero is not yet load-bearing: `trivialAtom` ($3 = 1 + 2$) exists for free, and
**`law_iff_admissibleAtom`** 🟢 — the inhabitedness of the law at a given $Z$ ⟺ the Z-*independent* question
`AdmissibleAtomExists`.

Both inputs of the front — `bridge_iff` and `impossible_iff` — are one and the same
arithmetic question, split by polarity under the zero hypothesis, and
**`front_pair_iff_no_zero`** 🟢: the pair of inputs is jointly satisfiable ⟺ there are no zeros. The circularity
persists as long as the anchor is free. The assembly with genuine extraction from the repository
(`RH_of_concreteArithmeticFront`) is ready — but there is nothing to feed it yet.

## The corrected front: non-vacuity lives at the level of data

The next layer (`RiemannSpectralAnchorAudit`) formalizes the exposed collapse itself (`FreeLawCollapse`;
the splice `concrete_freeLawCollapse`: my `law_iff_admissibleAtom` is precisely the free collapse of the concrete
route) and proves a subtle negative result:
**`propLevel_nonvacuity_incompatible_with_bridge`** 🟢 — a Prop-level criterion "the law never
collapses into a Z-independent statement" is incompatible with the bridge itself (a proven bridge collapses
the law into `True`).

The honesty criterion must live at the level of *data* — that is, be a data anchor, an anchor in data:
a real object tying the propositional law to the genuine problem
(see the [glossary](GLOSSARY.md)).

Hence `DataAnchoredLaw`
(Admissible + Anchor), an extractor of atoms from zeros, `SpectralInvariantAnchor` with the field `respects`
(the invariant of an anchored atom = the invariant of the zero) and `NonVacuousDataAnchor` (two zeros with distinct
invariants) — then `nonVacuousDataAnchor_forbids_freeOriginSupply` and
`extractor_not_constant_under_nonVacuousDataAnchor` 🟢 forbid free-origin supply and constant
extractors. The corrected obligation is packaged into `SpectralAnchorStrictFront`.

## The layerbox/terminal batch: what is really proven in 43 bricks

The series `RiemannLayerBoxFront` (25 bricks) and `RiemannTerminalRankFront` (18) are the session's most
massive delivery, and here the assembly-audit flags matter more than the volume.

The arithmetic actually proven consists of
mod-6 residue facts: **`no_identity_with_residues_555_111_plus_two`** 🟢 (the polarity
$q,r,s \equiv 5$, $a,b,v \equiv 1 \pmod 6$ is incompatible with $qrs = abv+2$: residue 5 on the left, 3 on the right),
`tuple555_111_unbalanced_mod6`, `tuple511_511_balanced_mod6` (kernel-checked `decide`;
`native_decide` has been thrown out of the bricks — trust in `ofReduceBool` is not introduced), plus generic
well-founded descent / finite-cover assemblies.

The rest are skeletons of obligations, and honesty requires
saying so plainly: *every* closure certificate of the terminal series carries the field
`target_of_noZeros : (there are no zeros) → Target` — the RH-shaped conclusion is an *input*, while the
no-zeros part itself comes from assumption fields (`contradiction : False` in
`LayerPressure`/`DeterminantPressure` — uninstantiable slots, not proofs); gates like
`NonEngineCoherenceFirewall` and the Prop ledgers are inert.

**Section takeaway.** The batch delivered a language and tables, not bridges.

## Summary: two live inputs

The session's dichotomy, fixed by the terminal layer: the engine-coherent routes are empty or
circular (⟺ RH); free-origin arithmetic is not a bridge but an external $0\to 1$ supply (a supply being what
a deviation pays with; see the [glossary](GLOSSARY.md)); the Liouville route is
an equivalence of target strength ($\lnot$`LiouvilleViolation`).

Two inputs remain alive: (1) a **load-bearing
spectral anchoring** — a data anchor with a spectral invariant and a zero-indexed extractor
(`SpectralAnchorStrictFront`, a finite LayerBox transcript as the last nontrivial form), and
(2) **`AdmissibleAtomExists`** as a free-standing arithmetic question — interesting in its own right,
but so far its resolution in either direction is not unmoored from the polar collapse.

RH is 🔴; only input No. 1 has been closed honestly,
and that is exactly why this chapter has something to show: the negative and exposing theorems
here are just as machine-checked as the positive ones.

## Postscript (chapter 38)

After this chapter Riemann is taken through the first cause: the law of manifestation of deviations became **the second
boundary of the single decree**, and `riemannHypothesis_from_firstCause` 🟡 derives RH from the
extended axiom by the same rank machine as the twins — with a machine-disclosed price
(`riemannManifestation_asserts_RH`: under the boundary, the law ⟺ RH).

Both live inputs of this chapter remain
🔴 and untouched: the fronts are maps of obligations for the axiom-free path, the decree is a deliberate detour at a
price declared out loud.

See [38_RiemannFirstCause.md](38_RiemannFirstCause.md).

<!--navbot-->

---

[← 36. Navier–Stokes: the equation](36_NavierStokes.md) · [Table of contents](00_Overview.md) · [38. Riemann through the first cause →](38_RiemannFirstCause.md)
<!--/navbot-->
