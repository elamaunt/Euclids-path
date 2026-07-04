# P/NP: full payment versus fast traversal

<!--navtop-->
[← 38. Riemann through the first cause](38_RiemannFirstCause.md) · [Table of contents](00_Overview.md) · [40. Yang–Mills →](40_YangMills.md)
<!--/navtop-->



> Lean source: `Engine/PNPRankPaymentFront.lean` — a green chain, all of it 🟢;
> `Engine/CausalClosureAxiom.lean` §11 — the P/NP language of the decree.
> Status legend: 🟢 — proven under the
> standard axioms; 🟡 — proven conditionally on the axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

The twins and Riemann arrived at the same dénouement: the green machine carried us to a node, and the node we accepted by decree —
recall that a decree is the intentional acceptance of a law by axiom, under an honestly disclosed price (see the [glossary](GLOSSARY.md)).
Here the machine behaves differently — and this is, perhaps, the most pleasant surprise of the entire programme.
**The reading of the P/NP problem turns out to be a green theorem; no decree is needed at all.**

The reading is simple and physical. **An NP problem is the full payment of all rank certificates**: to solve
the search is to account for *every* witness individually. **P is a fast traversal of the rank**: the motion of
an engine that flies past the rank without visiting all the states. And the inequality between them comes from the fact that
a fast traversal physically cannot pay for an unbounded family of certificates. All of this we shall now
prove, machine-checked and without any axiom.

## The two sides in the language of rank

Let us translate the metaphor into exact definitions — directly over the structures we already have.

**The P side.** Fast traversal is `RankFastTraversal`: every legal path `PathN` is shorter than its
starting rank, `n ≤ lexRank x`. The engine does not visit all the states — it is bounded by the rank
it started from. And this is not a hypothesis but a law of the machine itself:

**Theorem 39.1** (`rankFastTraversal_holds`, 🟢). *Every ranked graph traverses the rank fast:* for any ranked graph $G$, every legal path `PathN` of length $n$ from $x$ satisfies $n \le \operatorname{lexRank}(x)$.
A direct consequence of the fact that the length of a path does not exceed the starting rank (`len_le_lexRank`, [chapter 01](01_EPMI.md)).
The P side is a gift of the construction itself.

**The NP side.** Full payment is `FullRankCertificatePayment`: the existence of an injective
finite-key compression of the *entire* family of genealogies, where every certificate is accounted for individually. Checking
a single witness is cheap (`verificationEasy_always` 🟢 — verifying a certificate is always easy); what is expensive is
accounting for all of them.

Between them sits the notion of an unbounded supply (a supply is a family of certificates with which a
deviation "pays", see the [glossary](GLOSSARY.md)): `UnboundedCertificateSupply` — the family
of certificates is infinite.

## The heart of the inequality: pigeonhole

Now the key green theorem that makes everything work.

**Theorem 39.2** (`no_fullPayment_of_unboundedSupply`, 🟢). *A fast finite-key engine cannot
fully pay for an unbounded family of certificates:* if a genealogy family $F$ satisfies `UnboundedCertificateSupply` (is infinite), then `FullRankCertificatePayment` for $F$ fails, i.e. no injective finite-key compression of $F$ exists.

**Why this is true.** It is pure pigeonhole. A finite key trying to compress an infinite supply
is forced to collide two distinct witnesses into one — otherwise it would be distinguishing infinitely many objects
with a finite number of labels. And a collision is double bookkeeping, an impossible payment. It is cheap
to traverse the rank, expensive to touch every state; and the second is incompatible with the first under an infinite supply.

It remains to exhibit a scale where the supply really is infinite. There is one — and without a single hypothesis about
the twins:

**Theorem 39.3** (`concreteSupply_unbounded_smallScale`, 🟢). *For $A \le 4$ the concrete family of certificates
is infinite:* the type `concreteFamily A 1`.Index is infinite, witnessed by the injection of the pentadic chain `fiveAdicChainFlow` (the very one that refuted the branch $A \le 4$ in [chapter 24](24_BoundaryDecomp.md)).

**Corollary 39.4** (`concrete_noFullPayment_smallScale`, 🟢). *For $A \le 4$ full payment of the concrete family is impossible:* `FullRankCertificatePayment (concreteFamily A 1)` fails. Directly from Theorem 39.2 (`no_fullPayment_of_unboundedSupply`) applied to the infinite supply of Theorem 39.3.

## "NP = full payment" — a theorem, not a metaphor

It remains to tie "full payment" to local P-success, so that the phrase in the title stops being
an image. And it does tie together — at *every* scale:

**Theorem 39.5** (`concrete_localPSuccess_iff_fullPayment`, 🟢). *Local P-success is equivalent to the full
payment of certificates:* for all $A, M_0$, `LocalPSuccess (concreteProblem A M0)` $\iff$ `FullRankCertificatePayment (concreteFamily A M0)`.

This works because both alternatives for resolving a collision (a legal cycle and an impossible payment)
have already been burnt green (`no_extendedFlowResolutionAlternative`): the resolver cannot cheat, and
the only way to resolve collisions is to honestly account for each one. Now the inequality can be assembled
in its entirety, in a single theorem.

**Theorem 39.6** (`pnp_rank_separation_smallScale`, 🟢 — the inequality itself). *For $A \le 4$ five statements hold simultaneously:* `RankFastTraversal (concreteGraph A 1)` (the engine traverses the rank fast), `VerificationEasy` for every certificate `(concreteFamily A 1).cert i` (checking is easy), `UnboundedCertificateSupply (concreteFamily A 1)` (the supply is unbounded), $\lnot$ `FullRankCertificatePayment (concreteFamily A 1)` (full payment is impossible), *and* `LocalSearchIncompressible (concreteProblem A 1)` (local search is incompressible).

**Section takeaway.** The five facets of the metaphor have converged in one green statement: fast traversal, easy verification,
infinite supply, impossibility of full payment, incompressibility. This is "P ≠ NP" in the rank
model — proven, without axioms.

## The split across scales

A legitimate question arises here: if incompressibility is proven, does it not contradict the twins decree,
which on its own scale precisely *resolves* collisions? No — and they are kept apart by the simple observation that
local P-success and incompressibility are strict negations of each other, while they live on *different
scales*.

The twins decree works for `A ≥ 5` (the small branch we refuted), and there it gives local
P-success at every threshold — that is, **on its own scale the first cause fully pays the
certificates** (`decreedScale_fullPayment` 🟡). Incompressibility, meanwhile, lives at `A ≤ 4`, where the supply is
infinite and payment impossible, — unconditionally, green, owing nothing to the decree. One and the same language
describes both worlds; they are simply separated by scale.

Let us also note a handsome asymmetry with Riemann. There the boundary was *needed* for the carrying lemma — it supplied
the resolving projection. Here, for the separation, the boundary is **not needed**: the killer is green, the decree has nothing to do with it.
We did not insert an unused hypothesis for the sake of symmetry — it is more honest to leave the asymmetry visible.

## Why there is no third boundary of the decree

For the twins and Riemann the decree was an honest second boundary. It is natural to ask: should we not add
a third — a P/NP boundary? The answer is **no, and this is proven machine-wise**. We checked all three conceivable forms
of such a field, and every verdict turned out to be a green theorem:

- the **universal form** (in every good-faith frame a P-solver extracts a resolver)
  is *refutable* (`pnpLawUniversal_refuted`): for the frame `allPFrame` it would make the quarantine
  contradictory immediately;
- the **decider form** (reconstructing a resolver from a bare decider) is likewise *refutable*
  (`pnpLawDeciderGated_refuted`): a bare `PDecider` exists classically for any language, and
  the resolver extracted from it crashes against incompressibility at `A ≤ 4`;
- the **existential form** is *already proven* (`pnpLawExistential_green`, witness `constantsFrame`) —
  and decreeing a green theorem is pointless: the decree would be empty.

The cost mirror here collapses on its own: `pnpLaw_asserts_separation` 🟢 shows that the law
is equivalent to the separation **without any boundary**, and both sides are already theorems.

**Conclusion.** No honest third field exists. The genuinely missing object is not a proposition over abstract frames but a
data-anchored real machine model (mathlib has `Turing.TM2ComputableInPolyTime`, but
even the composition of machines there is still `proof_wanted`). This is the same lesson the spectral audit of Riemann taught:
"non-vacuity at the level of propositions" is the wrong criterion — a data anchor is needed.

> **Note (the machine-model anchor).** This missing object is now named — `Engine/PNPDataAnchor.lean`
> places two red inputs over *real* TM2 structures. The first, `TM2CompositionLaw`, names
> the input exactly where mathlib itself has a `proof_wanted` (`TM2ComputableInPolyTime.comp` — composition
> of polytime machines): `proof_wanted` creates no declaration, there is nothing to reference, the input is honestly red.
>
> And right here — a fine catch of honesty: the tempting `∃`-form "the language is TM2-decidable *with some*
> encoding" is machine-refuted as a renaming of `True` (`tm2DecidesWithSomeEncoding_free`) — the cheating
> encoding `enc x := encodeBool (run x)` smuggles the answer into the input, and the identity machine
> "computes" it. This is exactly why the real bridge `TM2FrameBridge` must live over the *fixed*
> canonical encoding `encodeNat`, not over the existential one; it is the same lesson about encodings that
> the spectral audit of Riemann taught at the level of propositions.

## Plasticity of frames and vacuity no. 4

From here comes an important honest caveat about what we have **not** proven. The abstract layer of "complexity
classes" is plastic: it can be tailored so that the classes coincide for free (`allPFrame`), and so that they separate
for free (`constantsFrame`, with the language `boolLanguage` as witness). Hence no statement about the *genuine*
classical P and NP follows from the abstract layer, and we make none.

Along the way, the adversarial audit uncovered in already-written code a **fourth episode of vacuity**
(vacuity is when a statement holds for free, by a stub witness; see the [glossary](GLOSSARY.md)): a bare
`PDecider` carries no complexity content and is built classically for any language (`classicalPDecider`);
therefore over the incompressible node there exists neither a `CanonicalResolverReconstruction` nor a
`DeciderGuidedSelfReduction` (both types are provably empty).

As a consequence, the decider fronts
`FaithfulSelfReductionFront` and `CurrentExtractionFront` are classically empty — their separation conclusions
are vacuous. Only this decider channel is affected; the InP bridge `Step00ToClassicalBridge` remains an honest
conditional form (`InP` is abstract). The vacuity is exposed and put on record, not hidden.

## Philosophical digression: the thermodynamics of computation

P/NP has a physical underside, and it fits the engine image more precisely than one might think. Landauer
showed that erasing one bit of information costs no less than `kT·ln 2` of energy — computation is physical, and
information has a thermodynamic price.

In our reading this comes to the foreground. *An NP problem is
the full payment of all certificates*, accounting for every witness individually; *P is a fast
traversal of the rank*, a motion that flies past without touching all the states. A fast engine
is cheap in "energy" — the number of steps is bounded by the starting rank — and precisely for that reason it *cannot*
pay for an unbounded supply: a finite key compressing an infinite family is forced to collide
two distinct witnesses into one.

The analogy is direct: with finite energy one cannot enumerate infinitely many distinguishable states without
confusing some of them. Fast traversal saves fuel exactly at the price of driving past; full
payment requires touching every one. The gap between "traversing the rank" and "paying all the certificates" is
precisely the gap between P and NP in physical dress: between cheap motion and expensive full accounting.

And only here, the single time in seven branches, did the inequality turn out to be **a green theorem without any
decree**: in the rank model the fast engine provably does not pay for the unbounded supply.
The thermodynamic intuition — "full accounting costs more than fast motion" — is proven in the rank world; its
transfer to the world of Turing machines remains that very missing data anchor, like the real Hamiltonian for
Yang–Mills and the real `(p,p)`-classes for Hodge.

## Place in the greater arc

The three great questions now stand in one architecture, but with three different honest outcomes: the twins —
a boundary of the decree (a node, 🟡), Riemann — a second boundary of the decree (a manifestation law, 🟡), and P/NP — **a green
theorem in the rank model, without any decree** (🟢), with a machine proof that the decree
path for it is either contradictory or empty. Classical P ≠ NP is neither proven nor claimed.

There is also an epistemic twin of this prohibition:
an internal, finite-fuel resolution of P/NP would be a perpetual engine — unreachable from inside, "beyond the same
horizon" as the cause of Collatz ([chapter 56](56_CollatzFirstCause.md), `Engine/PNPFirstCause`);
green, without a decree, the taint — the axiom's trace in the dependency list (see the [glossary](GLOSSARY.md)) — does not grow.

Next comes
Yang–Mills ([chapter 40](40_YangMills.md)), where the engine meets the spectrum, and a gapless spectrum turns out to be a perpetual
engine in its purest form.

<!--navbot-->

---

[← 38. Riemann through the first cause](38_RiemannFirstCause.md) · [Table of contents](00_Overview.md) · [40. Yang–Mills →](40_YangMills.md)
<!--/navbot-->
