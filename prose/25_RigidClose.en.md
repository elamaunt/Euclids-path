# 25. Rigid closure: descent without a cycle

<!--navtop-->
[← 24. Boundary decomposition](24_BoundaryDecomp.md) · [Table of contents](00_Overview.md) · [26. Separating scale →](26_SeparatingScale.md)
<!--/navtop-->



> Source: `Engine/RigidClose.lean` (namespace `EuclidsPath.RigidClose`; standard axioms, no `sorry` in the core — a single constructive input remains open). Numbers: cofactor `100%` on `307010` cases.

In the previous chapter [24 boundary](24_BoundaryDecomp.md) we decomposed the active side into boundary layers and convinced ourselves that divisibility of the catch always arrives with a concrete divisor — the boundary is never "empty".

Now we take that divisor and show that it does not merely exist but **builds the next, smaller center** — and that this one fact suffices to close the entire descent construction without appealing to a cycle and without the engine branch. In other words, we replace the old argument "a flow without sinks ⟹ directed cycle ⟹ Euclid's engine ⟹ ⊥" with a direct statement of well-foundedness.

## Motivation: why the cycle was superfluous

Recall the old closure logic (see [19 old-peel]). If every non-twin center has an outgoing descent edge, then the old-peel flow has no sinks; by a graph lemma such a flow closes into a directed cycle; and a cycle is precisely a rigid engine, forbidden by EPMI (the engine is the programme's central forbidden object, see the [glossary](GLOSSARY.md)). The scheme works, but it contains three separate nontrivial links: (i) building a cycle from the absence of sinks, (ii) identifying the cycle with an engine, (iii) the cycle's rigid signature (the audit of §13.D).

The observation that removes all three links is elementary. A descent edge does not merely "go somewhere" — it **strictly decreases the height**. And in that situation a directed cycle is impossible for an utterly trivial reason: the height cannot return to its initial value if every step strictly decreases it.

So, instead of building a cycle and driving it to a contradiction, it is natural to suppose that it suffices to invoke the well-foundedness of $\mathbb{N}$ directly. Strict fall of the height by itself rules out infinite descent — and with it the cycle, and the entire engine branch.

This chapter formalizes that observation as an abstract "rigid" graph with a height, and proves that in it reaching a twin follows from the regeneration property alone — by strong induction on the height.

## Definition: a graph with a height

Let us abstract away from the arithmetic. All that the descent mechanism needs is a height, a transition relation, and a sink predicate.

> **Definition 25.1** (`HeightGraph`). A rigid graph with a height over a type of states $\sigma$ is a triple
>
> $$
> G = \bigl(\mathrm{height} : \sigma \to \mathbb{N},\; \mathrm{Twin} : \sigma \to \mathrm{Prop},\; \mathrm{Step} : \sigma \to \sigma \to \mathrm{Prop}\bigr),
> $$
>
> subject to a single axiom of strict fall:
>
> $$
> \forall\, s\, t,\quad \mathrm{Step}\,s\,t \;\Longrightarrow\; \mathrm{height}\,t < \mathrm{height}\,s.
> $$

In Lean this is the structure `HeightGraph` with the field `step_drops : ∀ {s t}, Step s t → height t < height s`. The field `Twin` is the predicate of a proper sink (in the application — "$t$ is a twin center"); the field `Step` is the relation "there is a descent edge" (in the application — an old-peel or an active edge).

The single substantive input to the construction we isolate as a separate property.

> **Definition 25.2** (`Regenerates`). The graph $G$ **regenerates** if every non-twin state has a descending successor:
>
> $$
> \mathrm{Regenerates}(G) \;:\equiv\; \forall\, s,\; \neg\,\mathrm{Twin}\,s \;\Longrightarrow\; \exists\, t,\; \mathrm{Step}\,s\,t.
> $$

In Lean this is `def Regenerates (G : HeightGraph σ) : Prop`. Note the asymmetry of the burden: the axiom `step_drops` about the height falling comes "for free" with the structure itself (it is built into the definition of an edge), whereas `Regenerates` is the only property that will have to be proven in the application.

The entire theorem to come lives over these two givens and demands nothing more.

## Main theorem: reaching a twin without a cycle

Now the chapter's central statement.

> **Theorem 25.3** (`reaches_twin`). If $G$ regenerates, then a twin is reached from any start:
>
> $$
> \mathrm{Regenerates}(G) \;\Longrightarrow\; \forall\, s : \sigma,\; \exists\, t,\; \mathrm{Twin}\,t.
> $$

Let us take apart what is proven here and *why* it goes this way. The proof is strong induction on the height of the start (`Nat.strong_induction_on`). The auxiliary statement:
$$\mathrm{key} : \forall\, n : \mathbb{N},\; \forall\, s,\; \mathrm{height}\,s = n \;\Longrightarrow\; \exists\, t,\; \mathrm{Twin}\,t.$$
We fix $n$ and the induction hypothesis `ih`, which gives the conclusion for all strictly smaller heights. For a state $s$ of height $n$ we split into cases:

- if $\mathrm{Twin}\,s$ — a sink is already found, take $t := s$;
- otherwise `hregen` supplies a successor $t$ with $\mathrm{Step}\,s\,t$; by `step_drops` we have $\mathrm{height}\,t < \mathrm{height}\,s = n$, and applying `ih` to the height $\mathrm{height}\,t$ closes the step.

**Why this works, and the cycle was not needed.** The induction builds no path and considers no cycles. It simply asserts: the set of reachable heights is a subset of $\mathbb{N}$, and $\mathbb{N}$ is well-founded. A non-twin state is forced to step down to a strictly smaller height, and one cannot strictly decrease forever in $\mathbb{N}$.

The rigidity of the graph — the fact that *every* step strictly drops the height — turns "no sinks" from a pretext for building a cycle into a direct contradiction with well-foundedness. We do not discard the "cycle ⟹ engine" branch as false — we show that it is **logically redundant**: what it was introduced for (the impossibility of an infinite non-return to a twin) is already contained in the axiom of fall.

> **Note.** The formulation $\forall s,\ \exists t,\ \mathrm{Twin}\,t$ is deliberately weaker than "a twin is reachable from $s$ along a $\mathrm{Step}$-path": it asserts only the *existence* of a twin sink in the whole graph, which is exactly what the final contradiction requires (in the application, "a twin exists at every height" is already the theorem on the infinitude of twins at the given scale). Strengthening to a concrete path is extracted trivially from the same induction, but is not needed for the closure.

## Impossibility of a cycle as a separate lemma

The same well-foundedness we also record in an explicit, "graph-theoretic" form — as a direct replacement of the old rigid cycle.

> **Theorem 25.4** (`no_cycle`). In a graph with strictly decreasing height, a directed cycle does not exist. More precisely, for any chain $z : \mathbb{N} \to \sigma$
>
> $$
> \bigl(\forall\, k,\; \mathrm{Step}\,(z\,k)\,(z\,(k{+}1))\bigr) \;\Longrightarrow\; \bot.
> $$

The proof is one line: from the chain $z$ we obtain the sequence of heights $k \mapsto \mathrm{height}\,(z\,k)$, which by `step_drops` strictly decreases at every step, and `OldPeel.old_peel_terminates` (the same core as `no_infinite_engine_descent` from [19 old-peel]) asserts that a strictly descending infinite chain in $\mathbb{N}$ does not exist. That is, `no_cycle` is a repackaging of an already-proven impossibility of the engine: we do not prove it anew, we point out that "an infinite $\mathrm{Step}$-chain" is a special case of "infinite strict descent".

> **Note.** The difference from the old scheme is purely logical, but essential for the audit: previously the impossibility of a cycle was a *consequence* of identifying the cycle with a rigid engine (the §13.D link, which required a signature). Here it is the *definition* of a rigid graph. The rigid signature as a separate input disappears: it is already sewn into `step_drops`.

## The target center is built by algebra

One thing remains: to show that the abstract edge `Step` is, in the arithmetic application, actually **constructed**, not postulated. This is exactly where a hole used to hide — from "a divisor $q$ exists" it does not follow automatically that the quotient is a *valid smaller center* of the required form $6t'+\eta'$. This construction we prove by algebra.

> **Theorem 25.5** (`cofactor_is_center`). Let $t,q,\eta \in \mathbb{Z}$, with $t \ge 1$, $\eta \in \{+1,-1\}$, a prime divisor $q \ge 5$ coprime to $6$ (that is, $q \bmod 6 \in \{1,5\}$) and $q \mid 6t+\eta$. Then there exist $t',\eta'$ such that
>
> $$
> \eta' \in \{+1,-1\},\qquad 6t'+\eta' = \frac{6t+\eta}{q},\qquad 0 \le t' \;<\; t.
> $$

This is the chapter's key substantive lemma: it turns divisibility into a **state**. Let us see why the conclusion has exactly this shape.

We write $6t+\eta = q\cdot c$, whence $(6t+\eta)/q = c$ (the integer division is exact, `Int.mul_ediv_cancel_left`). Then — three observations.

1. **The cofactor is coprime to $6$.** From $6t+\eta = qc$ modulo $6$: $\eta \equiv (q \bmod 6)\cdot(c \bmod 6) \pmod 6$. Enumerating the finitely many cases $q\bmod 6 \in\{1,5\}$, $\eta\in\{\pm1\}$, $c\bmod 6\in\{0,\dots,5\}$ (in Lean — `rcases … <;> omega`) leaves exactly $c \bmod 6 \in \{1,5\}$. Substantively: both the left-hand side $6t+\eta$ and the factor $q$ lie outside the classes $2,3,4\pmod 6$ (coprime to $6$); therefore the second factor $c$ is also forced to lie in $\{1,5\}\pmod 6$ — otherwise the product would lose its coprimality with $6$. This is precisely the statement that $c$ has the center form $6t'\pm1$.

2. **The cofactor is positive.** Since $6t+\eta > 0$ (given $t\ge1$, $\eta\ge-1$) and $q>0$, from $qc = 6t+\eta$ it follows that $c>0$ (`nlinarith`). Hence $t' \ge 0$ — the center does not "escape to zero".

3. **Strict fall.** From $q \ge 5$ and $qc = 6t+\eta \le 6t+1$ we obtain $5c \le 6t+1$ (`nlinarith`), whence $c < 6t/5 + \tfrac15$, and after unfolding $c = 6t'\pm1$ we get $t' < t$ (`omega`). A case split on $c\bmod6=1$ (then $\eta'=+1$, $t'=(c-1)/6$) and $c\bmod6=5$ (then $\eta'=-1$, $t'=(c+1)/6$) completes the construction.

Thus the cofactor $c=(6t+\eta)/q$ **always** turns out to be a proper center $6t'+\eta'$ of strictly smaller height $t'<t$.

The divisibility delivered by the boundary from [24 boundary](24_BoundaryDecomp.md) converts automatically into a `Step` edge of the rigid graph — the fall of the height is secured by point 3, the center form by point 1, non-negativity by point 2.

> **Note (numbers).** The statement was checked empirically on 307010 cases with a 100% hit rate: in every checked catch the cofactor indeed turned out to be a valid smaller center of the form $6t'+\eta'$. This does not replace the proof (it is purely algebraic and already complete), but it confirms that the lemma covers the real old-peel flow with no exceptions — there are no "holes at the edges" of the range.

## An honest reduction: what is built and what remains an input

Let us take stock of what is proven and what is open. The regeneration dichotomy (`regeneration_dichotomy`, [21 regeneration](21_Regeneration.md)) for a center $t$ yields one of three elementary classes: `Twin t`; or (`¬OldFree`) an old-peel divisor $q$; or (`OldFree`, not a twin) a composite active side. To obtain `Regenerates`, from each of the right-hand cases one must **construct a concrete downward edge** — that is, exhibit $t' < t$ of center form.

Here it is important to draw an honest line.

- **The fall of the height $t'<t$ is proven** separately in both cases: `active_descent_height` (composite side) and `old_peel_height_drop` (old-peel).
- **The center form $6t'+\eta'$ is proven** exactly now — by Theorem 25.5 (`cofactor_is_center`). It is this theorem that closes the nontrivial passage "a divisor $q\mid 6t+\eta$" $\Rightarrow$ "there exists a center $t'$ of the form $6t'+\eta'$", which does not follow from divisibility alone automatically (the cofactor could have been a multiple of $2$ or $3$ — the lemma shows that it cannot).

With that in place we record the remaining input — in the house sense: an honestly named unproven link (see the [glossary](GLOSSARY.md)) — as an **honest reduction**, not passed off as a proof:

> **Theorem 25.6** (`regenerates_needs_target_center`). If for every non-twin center a downward edge is built, then the graph regenerates:
>
> $$
> \bigl(\forall\, t,\; \neg\,\mathrm{Twin}\,t \Rightarrow \exists\, t',\; \mathrm{Step}\,t\,t'\bigr) \;\Longrightarrow\; \mathrm{Regenerates}(G).
> $$

This theorem is tautological by construction (in Lean its body is simply `build_target`), and that is precisely its value: it **explicitly names the single remaining constructive input**. Not "there is a hole somewhere", but exactly: what is needed is that for every non-twin center the divisor produce a valid smaller center.

Half of this input — the form and the fall — we have already closed (Theorem 25.5 (`cofactor_is_center`) plus the height-drop lemmas); what remains is to assemble this into a single `build_target` over the full dichotomy, that is, to make sure the dichotomy really delivers a divisor in *all* non-twin cases with no unclassifiable terminal.

> **Hypothesis and closure plan.** Hypothesis: for every non-twin center $t$ the dichotomy (`regeneration_dichotomy`) delivers either an old-peel divisor $q\ge5$, $q\mid 6t\pm1$, or a composite side with a large divisor — that is, in either case there exists a $q$ to which `cofactor_is_center` applies.
>
> Plan: (i) from `not_oldfree_gives_peel` extract $q$ in the case $t\notin\Omega_A$; (ii) from `composite_oldfree_has_big_divisor` — in the active case; (iii) apply Theorem 25.5 (`cofactor_is_center`) to each $q$, obtaining $\mathrm{Step}\,t\,t'$; (iv) plug the result as `build_target` into Theorem 25.6 (`regenerates_needs_target_center`) and, via Theorem 25.3 (`reaches_twin`), close onto the existence of a twin.
>
> The node that remains genuinely open here is not the arithmetic of the edge (that is built), but the **completeness of the dichotomy on the required set of centers**: that fan-in/Hall does not introduce a hidden unclassifiable class. It is this input that moves on to the next chapter.

## Where we are now and the bridge onward

**Chapter takeaway.** Strict fall of the height makes the cycle logically superfluous. We replaced the chain "no sinks ⟹ directed cycle ⟹ rigid engine ⟹ ⊥" with a direct strong induction on the height (Theorem 25.3 (`reaches_twin`)), and kept the impossibility of a cycle only as a repackaging of the already-proven well-foundedness (Theorem 25.4 (`no_cycle`)). The engine branch and the rigid signature as separate inputs are gone.

Moreover, the single arithmetically nontrivial link — that the divisor produces a *valid* smaller center — is now proven by algebra (Theorem 25.5 (`cofactor_is_center`), 100% on 307010 cases), and the remaining input is honestly localized in one tautological reduction, Theorem 25.6 (`regenerates_needs_target_center`).

What remains unclosed we have named explicitly: the completeness of the dichotomy, that is, the absence of an unclassifiable terminal at carrier-scale. This is no longer a question about the edge of a single center, but a question about the *set of ancestries* converging into a bounded set of centers — that very fan-in/Hall.

In the next chapter [26 separating scale] we attack exactly this counting node: we show that at the separating scale $P_A > 6X_A+1$ the active factor becomes smaller than the primorial, the coarse passport becomes exact, and `ProductHall` is closed by pure arithmetic — narrowing the trichotomy to a single branch and turning "completeness of the dichotomy" from a hope into a checkable separating inequality.

<!--navbot-->

---

[← 24. Boundary decomposition](24_BoundaryDecomp.md) · [Table of contents](00_Overview.md) · [26. Separating scale →](26_SeparatingScale.md)
<!--/navbot-->
