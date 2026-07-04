# 23. Clean-boundary split

<!--navtop-->
[← 22. Residuals](22_Residuals.md) · [Table of contents](00_Overview.md) · [24. Boundary decomposition →](24_BoundaryDecomp.md)
<!--/navtop-->



In [22 Residuals] we closed the residual Lean lemmas of the engine without appealing to density: a constructive clean start above any $N$ (`carrier_nonempty_above`), the elementary `sink_is_twin` (an old-free side below $A^2$ is prime), and the anchoring `clean_twin_above` (when $6N+1 < A$, the twin centre automatically lies above $N$).

These three facts gave us tools, but not architecture: they tell us *what a halt of the descent turns out to be*, not *where exactly* the descent is allowed to halt.

In this chapter we bring order to the notion of a halt — and discover a hidden gap that had, until now, been quietly breaking the reduction.

## The "sink-is-clean" gap

Let us begin with an observation about a concrete failure. The descent audit (`RESULTS_descent_gap`) revealed that a Euclidean descent from a clean start can slip through to a small twin centre that is itself *not* clean. The canonical example:
$$
m = 18 \;\longrightarrow\; (6\cdot18-1,\;6\cdot18+1) = (107,\,109).
$$
The pair $(107,109)$ consists of genuine twin primes, but the centre $m=18$ is divisible by the primes $2,3$, which are certainly $\le A$, and hence $18 \notin \Omega_A$ (not old-free).

To such a centre the theorem `clean_twin_above` is **inapplicable**: its premise demands cleanliness of the sides with respect to all $q \le A$, whereas here $6m\pm1$, though prime, sit on a "contaminated" centre. The formally proven anchoring "the sink lies above $M_0$" collapses precisely because we allowed the descent to finish at an unclean centre and still called that a sink.

Intuitively, the gap is eliminated by a single restriction: **a sink is defined only in the clean graph**. A descent to a centre $n \notin \Omega_A$ is not a halt but a special transition, which we call a *boundary exit* and dispatch to the defect/old-peel ledger — the bookkeeping of descent loads (on ledgers, see the [glossary](GLOSSARY.md); chapters [19](19_OldPeel.md)–[21](21_Regeneration.md)).

A small unclean twin such as $18$ is then honestly classified as boundary, not as sink, and `clean_twin_above` is applied only where its premises hold. The present chapter formalises the provable clean part of this construction.

> **Note.** The gap was *semantic*, not arithmetic: both sides of $(107,109)$ really are prime. The mistake lay in silently identifying the notion of "sink" with "halt of the descent", whereas a correct halt must occur inside the graph on which the invariants are proven. The clean/boundary split is precisely the repair of that silent identification.

## Definitions of the graph

Fix a sieving threshold $A$ and work with centres $m \in \mathbb{N}$ (sides $6m-1$, $6m+1$). The basic property is inherited from [22](22_Residuals.md), but here we take its natural-number form.

**Definition (clean centre).** A centre $m$ is called *clean* with respect to $A$ if no prime $q \le A$ divides either side:
$$
\mathrm{Clean}\,A\,m \;:\equiv\; \forall q\ \text{prime},\ q \le A \;\Rightarrow\; \neg\bigl(q \mid (6m-1)\ \lor\ q \mid (6m+1)\bigr).
$$
In Lean this is `Clean` (the ℕ-version; its ℤ-twin is `CleanZ` from `Residuals`, and we shall exhibit the bridge between them below).

**Definition (active edge).** An edge $m \to n$ is *active* if $n$ is a smaller target centre of the descent:
$$
\mathrm{ActiveEdge}\,A\,m\,n \;:\equiv\; \top \ \land\ n < m .
$$
In `ActiveEdge` the carrier is abstract: the concrete mechanism (a composite side $6m+\sigma = a\,(6n+\varepsilon)$ with $a > A$) is delegated to `OldPeel`/cofactor and to `active_descent_height` from [22](22_Residuals.md); all that matters here is that an active edge carries a strict drop in height, $n < m$.

The distinction within active edges is the subject of this chapter:

**Definition (clean edge).** $\mathrm{CleanActiveEdge}\,A\,m\,n :\equiv \mathrm{Clean}\,A\,m \land \mathrm{Clean}\,A\,n \land \mathrm{ActiveEdge}\,A\,m\,n$ — both endpoints clean.

**Definition (boundary exit).** $\mathrm{BoundaryExit}\,A\,m\,n :\equiv \mathrm{Clean}\,A\,m \land \mathrm{ActiveEdge}\,A\,m\,n \land \neg\,\mathrm{Clean}\,A\,n$ — the source is clean, the target is *not*.

A boundary exit is an edge leaving the clean graph. It is *not* a sink: it is an entry into the defect ledger, where old-peel and regeneration take over. This is exactly where the transition $18 \to \dots$ from the gap above is sent.

## The active-edge dichotomy

The first theorem is a complete and unconditional classification of every active edge leaving a clean centre.

**Theorem** (`active_edge_clean_or_boundary`)**.** If $m$ is clean and there is an active edge $m \to n$, then this edge is either clean or a boundary exit:
$$
\mathrm{Clean}\,A\,m \ \land\ \mathrm{ActiveEdge}\,A\,m\,n \;\Longrightarrow\; \mathrm{CleanActiveEdge}\,A\,m\,n \ \lor\ \mathrm{BoundaryExit}\,A\,m\,n .
$$

The proof is trivial by the law of excluded middle applied to the predicate $\mathrm{Clean}\,A\,n$: if $n$ is clean — the left branch; otherwise — the right.

What is substantive is not the difficulty but the *completeness*: an active edge from a clean centre admits no third outcome. This means that the boundary of the clean graph is sealed — every arrow leaving a clean centre does exactly one of two things: it stays inside (clean edge) or it pierces the boundary (boundary).

It is this dichotomy that lets us rigorously separate the "interior work" of the descent from the "exit to the boundary", where a different apparatus takes over.

> **Note.** Observe that the dichotomy is stated from the *source* $m$ (which must be clean), yet the outcome is decided by a property of the *target* $n$. The asymmetry is no accident: the clean graph is the region where we know how to prove invariants; on leaving it we lose all guarantees about $n$ and must hand control over to the ledger.

## A clean sink is a twin

Now for the correct notion of a halt.

**Definition (clean sink).** $m$ is a *clean sink* if $m$ is clean and has no active edge at all:
$$
\mathrm{CleanSink}\,A\,m \;:\equiv\; \mathrm{Clean}\,A\,m \ \land\ \neg\,\exists n,\ \mathrm{ActiveEdge}\,A\,m\,n .
$$
The key phrase is "no edge at all": an unclean target reached by a boundary edge does *not* count as a sink. A descent that runs into $18 \to (107,109)$ *does* have an active edge (the transition exists), so it is not a clean sink but a boundary exit. Thus the "sink-is-clean" gap is eliminated at the level of the definition.

**Theorem** (`clean_sink_is_twin`, the corrected Lemma 3.1)**.** If $m$ is clean, both sides $6m-1,\,6m+1 \ge 2$ and both $< A^2$, and $m$ is a clean sink, then $m$ is a twin centre:
$$
2 \le 6m-1,\ \ 2 \le 6m+1,\ \ 6m-1 < A^2,\ \ 6m+1 < A^2,\ \ \mathrm{CleanSink}\,A\,m \;\Longrightarrow\; \mathrm{TwinCenterZ}\,m .
$$

The proof rests on `sink_is_twin` from [22](22_Residuals.md): a clean side below $A^2$ must be prime, because its least prime divisor is either $\le A$ (forbidden by cleanliness) or $> A$, in which case the cofactor is also $> A$, whence $6m\pm1 > A^2$ — a contradiction.

Note a subtlety of the implementation: the premise $\mathrm{CleanSink}$ contains "no active edge", yet the proof directly uses only the cleanliness ($\mathrm{hsink}.1$). The absence of an edge works here not as an arithmetic fact but as a *semantic guarantee*: since the halt is legal (inside the clean graph) and neither side is composite with respect to $q \le A$, both sides are prime — and that is a twin.

Old-free below $A^2 \Rightarrow$ prime; parity and divisibility by $3$ are elementary and already absorbed by `oldfree_below_sq_prime`.

## The complete outcome of a clean centre

Let us merge the edge dichotomy and the notion of sink into a single classification.

**Theorem** (`clean_center_outcome`, §5)**.** For every clean centre $m$, exactly one of four holds:
$$
\mathrm{TwinCenterZ}\,m
\ \lor\ (\exists n,\ \mathrm{CleanActiveEdge}\,A\,m\,n)
\ \lor\ (\exists n,\ \mathrm{BoundaryExit}\,A\,m\,n)
\ \lor\ \mathrm{CleanSink}\,A\,m .
$$

The proof is a nested case analysis: if $m$ is already a twin, we are done; otherwise we look at whether $m$ has any active edge at all. If it does, we apply `active_edge_clean_or_boundary` and land in a clean edge or a boundary. If there is no active edge whatsoever, then by definition $m$ is a clean sink.

The theorem's significance is that it *correctly excludes* the unclean small twin from the sink case: the centre $18$, being the source of a boundary-exit edge, settles in the third branch (boundary), not the first (twin) and not the fourth (sink). Previously it fell erroneously into "sink", breaking the height anchoring; now the classification does not let it in there.

> **Note.** The four branches are not a choice but an exhaustion: twin (terminal success), clean edge (the descent continues inside the graph), boundary (control is handed to the defect ledger), clean sink (we halted cleanly $\Rightarrow$ twin by the previous theorem). The first and fourth branches are "upward exits" to the result; the second is the internal dynamics; the third is the only channel carrying the load away out of the clean graph.

## A clean sink lies above $M_0$

It remains to tie the correct halt to height — the very thing for which the restriction "sink only in the clean graph" was introduced.

**Theorem** (`clean_sink_above`, §4)**.** If $6M_0+1 < A$, $m \ge 1$, $m$ is clean and a twin, then $m > M_0$:
$$
6M_0+1 < A,\ \ 1 \le m,\ \ \mathrm{Clean}\,A\,m,\ \ \mathrm{TwinCenterZ}\,m \;\Longrightarrow\; M_0 < m .
$$

This is a bridge to the already-proven `Residuals.clean_twin_above`. The only work here is transporting ℕ-divisibility of the sides to ℤ-divisibility: the equalities
$$
\bigl((6m-1 : \mathbb{N}) : \mathbb{Z}\bigr) = 6m-1, \qquad \bigl((6m+1 : \mathbb{N}) : \mathbb{Z}\bigr) = 6m+1
$$
(the first requires $1 \le 6m$ for a correct `Nat.cast_sub`) allow us to rewrite the premise `hcl` from natural-number cleanliness into integer cleanliness, after which `clean_twin_above` fires.

Substantively it says: the prime $6m-1$ must be $> A$ (otherwise an old prime would divide its own side, violating cleanliness), and $A > 6M_0+1$, whence $6m-1 > 6M_0+1$ and $m > M_0$. This implication is now *safe* precisely because we have guaranteed the cleanliness of $m$: at the unclean centre $18$ it would not apply — and we no longer try to apply it there.

## The honest boundary: the clean graph is not self-sufficient

Here we must be precise and not pass the reduction off as a proof. The formalised clean part — `active_edge_clean_or_boundary`, `clean_sink_is_twin`, `clean_center_outcome`, `clean_sink_above` — is fully proven, under the standard axioms, without `sorry`. But it describes only the *interior and the boundary* of the clean graph, not its closedness. And the measurements show that the graph is far from closed.

The numbers from `RESULTS_clean_graph`: **59% of clean centres have all their active edges in the boundary** — that is, for the majority of clean centres every exit from the graph pierces the boundary, leading to an unclean target.

This means the clean graph is *not self-sufficient*: a descent that starts clean is almost always forced to leave the clean region, and almost the entire load of the reduction goes into the `BoundaryExit` branch of `clean_center_outcome`.

**Conclusion.** The whole remainder of the programme concentrates in a single open input — a named 🔴 statement still missing on the way to the goal (see the [glossary](GLOSSARY.md)): a boundary state must *regenerate* — produce a correct successor (a clean return or a defect-ledger step) — rather than be a dangling terminal.

In the engine this is the hypothesis

$$
\textbf{(H)}\quad \mathrm{boundary\_exit\_regenerates}:\quad \mathrm{BoundaryExit}\,A\,m\,n \ \Longrightarrow\ (\text{boundary state yields an engine / regenerates}).
$$

Let us stress it plainly: **(H) is NOT proven.** It is an explicit hypothesis, not a lemma.

The clean part has honestly localised the difficulty — it has narrowed the entire open node down to one structural statement about boundary exits — but it has not closed it.

> **Note.** The "sink-is-clean" gap and the number $59\%$ are two sides of the same fact. While we were mistakenly counting unclean twins as sinks, the graph *appeared* almost closed: the descent "halted" everywhere. As soon as halting is restricted to clean centres, it turns out that $59\%$ of the apparent halts were in fact boundary exits. The repair did not create the load on the boundary — it *made it visible*.

**Closure plan.** (H) is neither a counting nor a distributional hypothesis; it is in the spirit of `regenerate` from [20 NOPSL] and of Lemma 6.1 on regeneration from [21 Regeneration].

It is natural to conjecture that a boundary exit $m \to n$ with $n \notin \Omega_A$ yields, by the definition of $\Omega_A$, a prime divisor $q \le A$, $q \ge 5$ of one of the sides of $n$ — that is, an old-peel edge — and that the old-peel ledger of [19](19_OldPeel.md)–[21](21_Regeneration.md) closes on this divisor with a drop in height.

Then (H) would reduce to the already-studied `regenerate`, and the whole programme would close on a single structural fact of boundary regeneration. Exhibiting this closure rigorously is the task of the next step.

**Section takeaway.** So: we have split the graph into a clean interior (proven) and a boundary (open), and localised the whole remainder in `boundary_exit_regenerates`.

But there are infinitely many boundary exits, at all scales $A$; isolated local regenerations give no global conclusion until we gather them into a single invariant acting on the entire genealogy tree at once.

How to glue the local clean/boundary dichotomy into a global statement about the unboundedness of twin centres is the subject of [24 Global node], to which we now turn.

<!--navbot-->

---

[← 22. Residuals](22_Residuals.md) · [Table of contents](00_Overview.md) · [24. Boundary decomposition →](24_BoundaryDecomp.md)
<!--/navbot-->
