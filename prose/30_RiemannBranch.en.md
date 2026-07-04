# 30. The Riemann Hypothesis: contraposition through the engine

<!--navtop-->
[← 29. The last link](29_CarrierBridge.md) · [Table of contents](00_Overview.md) · [31. Riemann via Liouville →](31_RiemannLiouville.md)
<!--/navtop-->



> Lean: `Engine/RiemannBranch.lean` (`NontrivialZeroM`, `no_zero_of_one_le_re`,
> `TrivialBelowZeroClassification`, `nontrivialZero_in_strip`, `EngineBridge`,
> `riemannHypothesis_of_engine_bridge`, `not_RH_gives_engine`, `TwoTransportLaw`, `twoTransportLaw_holds`,
> `TwoTransportBridge`, `riemannHypothesis_of_two_transport`). Core: `Engine/EPMI.lean`
> (`no_infinite_descent`), `Engine/TwoGap.lean` (`det_law_rank33`).
> **`RiemannHypothesis` is from mathlib** (the official formulation via the zeros of `riemannZeta`, all
> nontrivial zeros), *not* a home-made def. The location of zeros `Re ≥ 1` is from mathlib
> (`riemannZeta_ne_zero_of_one_le_re`); the classification `Re ≤ 0 ⟹ trivial` is an explicit analytic
> input, `TrivialBelowZeroClassification`.

Having completed part V, we possess a fully closed mechanism of the perpetual engine's impossibility:
the abstract theorem `no_infinite_descent` is proven without axioms, and the two-transport law `det_law_rank33`
is machine-checked. It is natural to ask what else this mechanism can close *by the same argument by
contradiction* with which we closed the twins. In the present chapter we work through a side branch — the Riemann
Hypothesis (RH) — and we do it honestly: we show exactly where the border of the proven runs, and why RH
remains here conditional on one explicitly singled-out node.

## An honest frame: what we do *not* claim

First of all, let us pin down what would be easy to pass off as more than it is.

> **Note.** RH does **not** follow logically from the infinitude of twins. These are two independent
> arithmetic statements, and we do **not** record the implication `twin ⟹ RH` as a theorem — it would be
> false. All this branch does is reuse *the same proven EPMI mechanism* and *the same
> contraposition scheme*, not transfer the truth of one hypothesis onto the other.

The logical form of the branch is exactly the same as for the twins. We have already seen it in the pair "no engine ⟹ there are
twins"; here it takes the form

$$\bigl(\neg P \Rightarrow \text{Engine}\bigr)\ \wedge\ \neg\,\text{Engine}\ \Longrightarrow\ P,
\qquad P := \text{RH}.$$

Substantively, we build the chain

$$\neg\text{RH}\ \Longrightarrow\ \exists\,\text{zero }\rho,\ \mathrm{Re}\,\rho \ne \tfrac12
\ \overset{H_{RH}}{\Longrightarrow}\ \text{perpetual engine}\ \Longrightarrow\ \bot,$$

where the last step is the already-proven `no_infinite_descent`, and the transition marked $H_{RH}$ is
the branch's **only open node**. We pass no reduction off as a proof: below, RH is
formalized as a *conditional* theorem whose premise is explicitly written out and explicitly marked open.

## Definitions: nontrivial zero and RH

We introduce the object in question. We work with the Riemann zeta function `riemannZeta` from mathlib and
are interested in its zeros inside the critical strip.

**The Riemann Hypothesis — from mathlib (not home-made).** Following the principle "everything external comes from mathlib", the goal is
precisely `RiemannHypothesis` from mathlib: a quantifier over *all* zeros of `riemannZeta`, excluding the trivial ones
(`-2(n+1)`) and `s = 1`. This is strictly more general than "zeros only in the strip", and we are obliged to deliver `Re = 1/2` for
every such zero.

**Definition 30.1** (`NontrivialZeroM`, nontrivial zero). $\mathrm{NontrivialZeroM}(\rho) :\Longleftrightarrow \zeta(\rho)=0 \wedge (\neg\exists n,\ \rho = -2(n{+}1)) \wedge \rho \ne 1$ — exactly the premise of mathlib-RH, gathered into a single object.

**Localizing the zero (proven + one input).** An input here is meant in the house sense: a named open
statement still missing on the way to the goal (see the [glossary](GLOSSARY.md)). To apply the engine, we must drive a nontrivial zero
into the strip $0 < \mathrm{Re}\,\rho < 1$:

- **The top ($\mathrm{Re}\,\rho < 1$) — closed by mathlib analysis (not by the engine core).**
  `no_zero_of_one_le_re` from `riemannZeta_ne_zero_of_one_le_re` (zeta has no zeros for $\mathrm{Re}\ge 1$).
  ⚠️ An honest caveat: this non-vanishing of zeta on $\mathrm{Re}\ge 1$ is a *PNT-level analytic
  result*, proven in mathlib and *not* by us. "Proven" here = "derivable from mathlib", not from the core.
  It merely bounds the strip; it does not place the zero on $\tfrac12$ and does not close any bridge.
- **The bottom ($\mathrm{Re}\,\rho > 0$) — an explicit analytic input.** `TrivialBelowZeroClassification`: every
  zero with $\mathrm{Re}\,\rho \le 0$ is trivial. This is classical (the functional equation); mathlib gives only the
  *values* of the trivial zeros (`riemannZeta_neg_two_mul_nat_add_one`), not the converse classification, —
  so we take it as an explicit flagged hypothesis, and *not* as a home-made RH.

`nontrivialZero_in_strip` assembles both facts: a nontrivial zero lies strictly in the strip. The negation of RH
that we exploit is the existence of a nontrivial zero $\rho$ with $\mathrm{Re}\,\rho \ne \tfrac12$.

## The `EngineBridge` bridge: where all the analysis lives

All the substantive difficulty of the branch is gathered into one proposition, which we call the **engine bridge**.
Note that the object described below is not an axiom in the narrow sense: it is an explicit premise of a conditional
theorem, and we honestly keep it open.

**Definition 30.2** (`EngineBridge`, engine bridge).

$$\mathrm{EngineBridge}\ :\Longleftrightarrow\ \forall\,\rho,\
\zeta(\rho)=0\ \wedge\ 0<\mathrm{Re}\,\rho\ \wedge\ \mathrm{Re}\,\rho<1\ \wedge\ \mathrm{Re}\,\rho \ne \tfrac12\ \Longrightarrow\
\exists\,A\ge 1,\ \exists\,H:\mathbb N\to\mathbb N,\ \forall t,\ \mathrm{DescentStep}\,A\,(H\,t)\,(H(t{+}1)).$$

In Lean (the premise is a zero strictly in the strip with $\mathrm{Re}\ne\tfrac12$; localization into the strip is done by
mathlib + the input `TrivialBelowZeroClassification`):

```
def EngineBridge : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (A : ℕ) (H : ℕ → ℕ), 1 ≤ A ∧ ∀ t, DescentStep A (H t) (H (t + 1))
```

Recall from part I that `DescentStep A h h' : Prop := A * h' < h` — one successful clean descent, in
which the height drops by a factor of at least $A$. A witness — in the house sense, a concrete object
certifying a statement (see the [glossary](GLOSSARY.md)): here $H:\mathbb N\to\mathbb N$ with
$\mathrm{DescentStep}\,A\,(H\,t)\,(H(t{+}1))$ for all $t$ — is exactly an infinite clean chain of strictly
decreasing height, that is, a **perpetual engine**.

Substantively, the bridge says the following. The asymmetry $\mathrm{Re}\,\rho \ne \tfrac12$ corresponds to an imbalance
between the "left" and "right" halves of the critical strip. From the intuition of the carrier of two: balance
at $\tfrac12$ is exactly the condition under which the gain and loss of mass along the descent compensate each other,
and the chain is forced either to exit onto the boundary or to hit the bottom.

A zero off $\tfrac12$ removes this
compensation and yields a "free" directed pumping of mass: every descent step strictly
lowers the height without exiting onto the boundary, which cannot happen in the balanced regime. This very
pumping is the engine forbidden by `no_infinite_descent`.

> **Note.** `EngineBridge` is **not proven**, and in any foreseeable form is, by all appearances, comparable in difficulty
> to RH itself — exactly as, for the twins, the final distributional node ([18 SNOL])
> turned out comparable to the twin conjecture itself. We do not mask this: the branch is honest only because
> all its unprovenness is localized in one explicit premise, not smeared across the chain of reasoning.

## RH by contradiction: a conditional theorem

Now let us assemble the chain. We claim that if the bridge is true, RH follows.

**Theorem 30.3** (`riemannHypothesis_of_engine_bridge`). If `TrivialBelowZeroClassification` and
`EngineBridge`, then (mathlib-)`RiemannHypothesis`.

Let us prove it. Take an arbitrary zero $\rho$, nontrivial and $\ne 1$ (this is exactly the premise of mathlib-RH).
First we localize it into the strip $0<\mathrm{Re}\,\rho<1$ via `nontrivialZero_in_strip` (the top from
mathlib, the bottom from the classification input). Suppose, for contradiction, that $\mathrm{Re}\,\rho \ne \tfrac12$.
The bridge yields $A\ge 1$ and a chain of heights $H$ with $\mathrm{DescentStep}\,A\,(H\,t)\,(H(t{+}1))$ — a perpetual engine.
But it does not exist: `no_infinite_descent`, delivering $\bot$. Whence $\mathrm{Re}\,\rho = \tfrac12$:

```
theorem riemannHypothesis_of_engine_bridge
    (hClass : TrivialBelowZeroClassification) (H_RH : EngineBridge) :
    RiemannHypothesis := by
  intro ρ hz htriv hne1
  have hρ : NontrivialZeroM ρ := ⟨hz, htriv, hne1⟩
  obtain ⟨hpos, hlt⟩ := nontrivialZero_in_strip hClass hρ
  by_contra hne
  obtain ⟨A, Hgt, hA, hchain⟩ := H_RH ρ hz hpos hlt hne
  exact no_infinite_descent hA Hgt hchain
```

Why this works, and what it means. It works because all the analysis has been moved into the premise `H_RH`,
while the tail of the chain (engine ⟹ $\bot$) is an already machine-checked fact.

**Conclusion.** What it means is exactly this: the
contraposition of RH is **reduced** to the analytic bridge `EngineBridge`, and not one iota more: the truth of
RH is obtained here *conditionally*, under the assumption of the bridge.

It is useful to write out the contraposition in direct form as well — as "$\neg$RH begets an engine", without `by_contra`:

**Theorem 30.4** (`not_RH_gives_engine`). If `EngineBridge` and $\neg\text{RH}$, then there exist $A\ge 1$ and
$H:\mathbb N\to\mathbb N$ with $\mathrm{DescentStep}\,A\,(H\,t)\,(H(t{+}1))$ for all $t$.

Here we unfold $\neg\text{RH}$ via `not_forall`, extract a witness zero $\rho$ off
$\tfrac12$, and feed it into the bridge. This form makes the mechanism explicit: the negation of RH is a concrete
asymmetric zero, and the bridge turns it into a concrete infinite descent chain. The contradiction with
`no_infinite_descent` is then literally the same one that closes the twins — a shared finale, not two different
ones.

## The link with the twins: one shared node instead of two

We want to place the branch next to the twins not declaratively but structurally: to show that the open
node of RH is not new independent analysis, but the same carrier of two already proven in the core. For this
we introduce an abstract form of the transport law.

**Definition 30.5** (`TwoTransportLaw`, the two-transport law abstractly).

$$\mathrm{TwoTransportLaw}\ :\Longleftrightarrow\ \forall\,m,a,b,v,q,r,s\ge \text{(with }1\le m\text{)},\
6m-1 = a b v\ \wedge\ 6m+1 = q r s\ \Longrightarrow\ q r s = a b v + 2.$$

This is exactly the identity "the right companion exceeds the left by two" at the level of factorizations. And it is **already
proven** — by the concrete identity `det_law_rank33` from `Engine/TwoGap.lean`:

**Theorem 30.6** (`twoTransportLaw_holds`). `TwoTransportLaw` holds.

```
theorem twoTransportLaw_holds : TwoTransportLaw :=
  fun _ _ _ _ _ _ _ hm h1 h2 => det_law_rank33 hm h1 h2
```

Note: this is neither an axiom nor a hypothesis, but a witnessed proposition — any identity of the family
`det_law_*` (`det_law_rank33`, `det_law_CD`, `det_collapse`, …) will do as a witness.

Now we single out the *only* implication one would have to prove in order to connect the carrier of
two with the engine bridge.

**Definition 30.7** (`TwoTransportBridge`, the linking node).

$$\mathrm{TwoTransportBridge}\ :\Longleftrightarrow\ \bigl(\mathrm{TwoTransportLaw}\ \Rightarrow\
\mathrm{EngineBridge}\bigr).$$

Let us stress: this is an **implication**, not an equivalence of hypotheses. We do not identify RH with the twins and
do not transfer truth; we merely ask whether the very bridge RH needs follows from the already-proven core of the
carrier of two. If `TwoTransportBridge` is proven, RH follows from what is already at hand:

**Theorem 30.8** (`riemannHypothesis_of_two_transport`). If `TrivialBelowZeroClassification` and
`TwoTransportBridge`, then (mathlib-)`RiemannHypothesis`.

```
theorem riemannHypothesis_of_two_transport
    (hClass : TrivialBelowZeroClassification) (bridge : TwoTransportBridge) :
    RiemannHypothesis :=
  riemannHypothesis_of_engine_bridge hClass (bridge twoTransportLaw_holds)
```

The proof is transparent: we plug the already-proven `twoTransportLaw_holds` (Theorem 30.6) into the link, obtain
`EngineBridge`, and apply Theorem 30.3 (`riemannHypothesis_of_engine_bridge`).

**Section takeaway.** The value of the formulation is that it
names **precisely** the price of the branches' "simultaneity": what remains open is exactly `TwoTransportBridge` —
one implication "carrier of two ⟹ bridge" — and the analytic input `TrivialBelowZeroClassification`, not
separate zeta analysis and not an equivalence of the two hypotheses.

## The status, honestly, and an open conjecture

Let us draw the border of the proven, shifting it in neither direction.

- **Proven.** The conditional theorem `riemannHypothesis_of_engine_bridge`
  (`TrivialBelowZeroClassification ∧ EngineBridge ⟹` mathlib-`RH`), its contraposition
  `not_RH_gives_engine`, and also `riemannHypothesis_of_two_transport` — all via the *machine-checked*
  `no_infinite_descent`, `twoTransportLaw_holds` and mathlib `riemannZeta_ne_zero_of_one_le_re`
  (`no_zero_of_one_le_re`, `nontrivialZero_in_strip`). The goal is the official mathlib `RiemannHypothesis`
  (all nontrivial zeros), not a home-made one. The tail "engine ⟹ $\bot$" is shared with the twins.
- **Open.** `EngineBridge` (equivalently: `TwoTransportBridge`) — the link "a zero in the strip off $\tfrac12$
  ⟹ perpetual engine" — and the analytic input `TrivialBelowZeroClassification` (zeros with $\mathrm{Re}\le 0$
  are trivial; the functional equation, mathlib gives only the values of the trivial zeros). RH here is
  *conditional* on these two nodes and is **NOT proven**.
- **⚠️ Circularity of the impossible-engine routes (machine-checked, `RiemannImpossibleEngineOff` §7bis).**
  `offCriticalBridge_iff_RH`: since the factory is unconditionally impossible, the input `OffCriticalRiemannEngineBridge`
  is **equivalent to RH verbatim** (the bridge is satisfiable only vacuously — that is, for free, without a substantive
  witness; on vacuity and goal renaming see the [glossary](GLOSSARY.md)). Likewise
  `criticalStripBridge_iff_no_stripZero` (the strip variant) and `spectralBridge_forces_no_violation`
  (the rank-jump bridge covertly carries `¬LiouvilleViolation` = RH content). These routes are exact
  *reformulations* of RH, not reductions of difficulty; their value is the form (an engine), not a reduction.

> **Conjecture (the node to be closed).** The asymmetry $\mathrm{Re}\,\rho \ne \tfrac12$ of a nontrivial
> zero entails a violation of the two-transport balance strong enough to beget an infinite clean chain
> $\mathrm{DescentStep}\,A\,(H\,t)\,(H(t{+}1))$ — that is, `TwoTransportLaw ⟹ EngineBridge`.

**Closure plan.** We sketch it in terms of the apparatus already built, without passing the sketch off as a
proof.

1. Translate the asymmetry $\mathrm{Re}\,\rho \ne \tfrac12$ into a quantitative imbalance of the left and right
   companions along the descent — using the explicit form $qrs = abv + 2$ from `twoTransportLaw_holds` as the
   point of balance, the deviation from which is estimated through the position of the zero.
2. Show that this imbalance is not absorbed by a boundary exit (see the boundary decomposition from
   [24](24_BoundaryDecomp.md)), that is, the chain stays clean at every step.
3. Assemble from the steps an explicit witness $H$ and a constant $A\ge 1$, closing `EngineBridge`; from there all the
   work is done by the available `no_infinite_descent`.

Each of the three items is an analytic problem in its own right, and we do not claim they are small.
The honest assessment stands: this bridge is, by all appearances, comparable in difficulty to RH itself.

## Bridge to the next chapter

So the Riemann branch rests on exactly one arithmetic imbalance — the deviation of the carrier of two from the
exact value $+2$.

The same question, "how large is the deviation and does it tear on the boundary",
arises outside zeta as well — in the purely multiplicative statistics of divisor signs. In [31 Liouville] we
take the Liouville function $\lambda(n)=(-1)^{\Omega(n)}$ and its summatory function — and show how the same
descent mechanism and the same dichotomy "balance or engine" carry over to the parity defect of $\Omega$,
yielding one more contrapositional branch on the shared EPMI core.

<!--navbot-->

---

[← 29. The last link](29_CarrierBridge.md) · [Table of contents](00_Overview.md) · [31. Riemann via Liouville →](31_RiemannLiouville.md)
<!--/navbot-->
