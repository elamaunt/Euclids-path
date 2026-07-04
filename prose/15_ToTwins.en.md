# 15. The chain to the twins from four-corner (conditional)

<!--navtop-->
[← 14. Decomposition of the remainder](14_RealFourCorner.md) · [Table of contents](00_Overview.md) · [16. By contradiction →](16_FiniteContradiction.md)
<!--/navtop-->



> Lean source: `EuclidsPath/Engine/ToTwins.lean` (`twin_primes_of_four_corner`).
> Builds on: `EuclidsPath/Engine/FourCorner.lean`, `EuclidsPath/Engine/TwoTransport.lean`,
> `EuclidsPath/Engine/NonCover.lean`, `EuclidsPath/Step00_Overview.lean`.

In the previous chapter we obtained an exact decomposition of the remainder: the real rank counts
split into a model (CRT) part plus a correction $e_{ij}$, and the whole question of the
model→reality transfer reduced to whether the remainder flips the sign of the model four-corner.
Now we take the next, purely assembly step: we show that *if* the real strict four-corner really
does hold at all scales, then the infinitude of twin primes follows from it mechanically.

In other words, here we close the entire verified part of the programme into a single
machine-checked chain and exhibit the sole remaining open input — an honestly named statement,
neither proven nor hidden (see the [glossary](GLOSSARY.md)) — in explicit, typed form.

## 15.1. The setting: what exactly we are assembling

Recall the working definitions fixed in the overview module `Step00_Overview.lean`.

**Definition 15.1** (`IsTwinCenter`)**.** A centre $m$ determines a twin pair if both sides of the
six-fold window are prime:
$$
\mathrm{IsTwinCenter}(m) \;:\Longleftrightarrow\; (6m-1)\ \text{prime}\ \wedge\ (6m+1)\ \text{prime}.
$$

**Definition 15.2** (`TwinLowers`)**.** The set of lower members of twin pairs is
$$
\mathrm{TwinLowers} \;=\; \{\,p \mid p\ \text{prime}\ \wedge\ (p+2)\ \text{prime}\,\},
$$
and the final goal of the whole chain is the statement `TwinLowers.Infinite`, that is, the
infinitude of this set.

Our task in this chapter is to exhibit a theorem of the form
$$
(\text{real four-corner at all scales}) \;\Longrightarrow\; \mathrm{TwinLowers}.\mathrm{Infinite},
$$
in which the premise is the single hypothesis, and the implication is machine-checked in its
entirety, without `sorry`. All the intermediate links have by this point already been proven in
separate modules; here they are joined into one derivation.

## 15.2. The four verified links

The chain is assembled from four previously proven statements. Let us list them with their exact
Lean names and explain what each one does.

**Link 1 — the four-corner passage (strict).**

**Lemma 15.3** (`N33_lt_N00_of_four_corner`)**.** Given $N_{00}>0$, the strict four-corner
$N_{00}\cdot N_{33} < N_{03}\cdot N_{30}$ and the side-corner $N_{03}\cdot N_{30} \le N_{00}^2$,
it follows that
$$
N_{33} < N_{00}. \tag{15.1}
$$
The proof is elementary and purely arithmetical: from $N_{00}N_{33} < N_{03}N_{30} \le N_{00}^2$
we get $N_{00}N_{33} < N_{00}N_{00}$, and cancelling the positive factor $N_{00}$ (the lemma
`lt_of_mul_lt_mul_left`) yields $N_{33}<N_{00}$.

> **Note.** The role of the side-corner here is a single one: to convert an inequality about the
> *product* of the diagonals $N_{03}N_{30}$ into an inequality about the *square* of the base rank
> $N_{00}^2$. It is precisely then that the strict four-corner becomes a comparison of
> $N_{00}N_{33}$ with $N_{00}^2$, from which $N_{33}<N_{00}$ drops out. Without the side-corner,
> the four-corner by itself does not control $N_{33}$ relative to $N_{00}$. This is why the
> side-corner appears in the hypothesis `H` as a separate, "light" conjunct.

**Link 2 — non-cover yields a survivor.**

**Lemma 15.4** (`survivor_of_not_covered`)**.** If for finite sets $\Omega$ (the carrier) and
$\mathrm{bad}$ we have $|\mathrm{bad}| < |\Omega|$, then there exists $m\in\Omega$ with
$m\notin\mathrm{bad}$. This is
pure Finset combinatorics: were $\Omega\subseteq\mathrm{bad}$, we would have
$|\Omega|\le|\mathrm{bad}|$ — a contradiction. Substantively: the "bad" centres are too few to
cover the whole carrier, so at least one centre survives.

**Link 3 — the block core.**

**Theorem 15.5** (`twin_prime_conjecture_of_blocks`)**.** From the premise
$$
\forall N,\ \exists\,\text{carrier},\ \text{bad}:\quad
(\forall m\in\text{carrier},\ N<m)\ \wedge\ |\text{bad}|<|\text{carrier}|\ \wedge\
(\forall m\in\text{carrier},\ m\notin\text{bad}\Rightarrow\mathrm{IsTwinCenter}(m)) \tag{15.2}
$$
it follows that `TwinLowers.Infinite`. Via the auxiliary `twin_center_of_block` it extracts the
survivor (link 2, Lemma 15.4), places it above $N$, and by the condition "survivor $\Rightarrow$
twin" recognizes it as a twin centre.

**Link 4 — unboundedness yields infinitude.**

**Theorem 15.6** (`infinite_of_unbounded_centers`)**.** If for every $N$ there is a twin centre
$m>N$, then `TwinLowers.Infinite`. Formally it uses `Set.infinite_of_not_bddAbove` — from a
centre $m>N$ one
builds the pair member $6m-1$, which exceeds $N$, so the set of lower twins is not bounded above,
and hence is infinite.

## 15.3. The main theorem

Joining the four links, we obtain the conditional theorem `twin_primes_of_four_corner`. Let us
state its hypothesis $H$ explicitly.

> **Hypothesis `H` (real four-corner at all scales).** For every $N\in\mathbb{N}$
> there exist finite rank sets $R_{00}, R_{03}, R_{30}, R_{33}$ and sets
> $\mathrm{carrier}, \mathrm{bad}$ such that
> $$
> 0 < |R_{00}|,\qquad
> |R_{00}|\cdot|R_{33}| \;<\; |R_{03}|\cdot|R_{30}| \quad(\text{strict four-corner}),
> $$
> $$
> |R_{03}|\cdot|R_{30}| \;\le\; |R_{00}|^2 \quad(\text{side-corner, light}),
> $$
> $$
> |\mathrm{carrier}| = |R_{00}|,\qquad |\mathrm{bad}| = |R_{33}|,
> $$
> $$
> (\forall m\in\mathrm{carrier},\ N<m),\qquad
> (\forall m\in\mathrm{carrier},\ m\notin\mathrm{bad}\Rightarrow\mathrm{IsTwinCenter}(m)).
> $$

Substantively, $H$ says: at an arbitrarily large scale $N$ there is a block in which the carrier
is identified with the rank-$(0,0)$ set, the bad set with the rank-$(3,3)$ set, the real rank
counts give the strict four-corner (plus the light side-corner), the whole carrier lies above
$N$, and every surviving carrier centre is a twin.

**Theorem 15.7** (`twin_primes_of_four_corner`)**.** 🟡 (conditional)
$$
H \;\Longrightarrow\; \mathrm{TwinLowers}.\mathrm{Infinite}. \tag{15.3}
$$

A walk through the proof. We apply Theorem 15.5 (`twin_prime_conjecture_of_blocks`) — it remains,
for every $N$, to exhibit a block with $|\mathrm{bad}| < |\mathrm{carrier}|$. We unfold $H\,N$,
obtaining the ranks, the carrier, the bad set and all seven conjuncts.

The key step is link 1 (Lemma 15.3):
$$
|R_{33}| < |R_{00}| \quad\text{via}\quad `N33\_lt\_N00\_of\_four\_corner`\ (h_{\text{pos}}, h_{\text{fc}}, h_{\text{sc}}).
$$
Then, by the identities $|\mathrm{carrier}|=|R_{00}|$ and $|\mathrm{bad}|=|R_{33}|$, we rewrite
this inequality as $|\mathrm{bad}| < |\mathrm{carrier}|$ — exactly the premise of the block core.

The conditions "the carrier lies above $N$" and "survivor $\Rightarrow$ twin" are passed on from
$H$ unchanged. At this point the machine chain closes: Theorem 15.5
(`twin_prime_conjecture_of_blocks`) returns `TwinLowers.Infinite`.

> **Note.** There is no `sorry` in the file. This is an honest *conditional* theorem: the
> conclusion (the twin conjecture) follows from the explicit input $H$. We never pass this
> reduction off as a proof of the twin conjecture — what is proven is exactly what the signature
> says: the implication $H\Rightarrow$ `TwinLowers.Infinite`. All the nontrivial content is
> carried by the premise $H$.

## 15.4. Why the boundary runs exactly here

It is natural to ask: why is it exactly $H$ that remains open, and not something else? The
observation is that each of the four links is distribution-free — they appeal neither to
analysis nor to the distribution of primes:

- link 1 — natural-number arithmetic (cancelling an inequality by a positive factor);
- link 2 — the pigeonhole principle in the form `Finset.card_le_card`;
- link 3 — the combinatorial assembly of the survivor;
- link 4 — "unbounded above $\Rightarrow$ infinite" for sets.

None of them "knows" anything about primes beyond the definition of `IsTwinCenter`. Everything
analytically hard — the distributional part — turns out to be concentrated inside $H$, namely in
two of its conjuncts:

1. **the strict real four-corner** $|R_{00}|\,|R_{33}| < |R_{03}|\,|R_{30}|$ at all scales —
   this is the transfer of the model (CRT) four-corner to the real rank counts, that is, the
   control of the remainder $e_{ij}$ from chapter 14; by its nature this is a problem of parity
   and the sieve remainder term;
2. **the carrier conditions** — that the carrier lies above $N$ and that every survivor is a
   twin (a density lower bound plus the elementary "sieve-to-the-root $\Rightarrow$ primality",
   cf. `isTwinCenter_of_root_sieve` in `TwoTransport.lean`).

> **Note.** The Lean source's comment states the status directly: the model four-corner is
> already proven (`ModelFourCorner`); what is open is exactly the model→reality transfer. The
> empirical data from `tools/RESULTS_remainder.md` (chapter 14) show that the remainder $e_{ij}$
> exceeds the model roughly fourfold while the model four-corner's margin melts away — that is,
> the model inequality does *not* transfer distribution-free. Here the line runs into the parity
> problem, and this is not a defect of the assembly but the precise localization of the single
> unresolved node.

**Section takeaway.** This chapter thus performs a double function. First, it gives the first
exact formulation of the programme's single distributional input: everything needed for the twin
conjecture beyond what is already verified is packed into one typed predicate $H$. Second, it
turns the scattered links into a single artifact — an implication which the machine checks in
its entirety.

> **Note.** The hypothesis $H$ in this formulation is the direct predecessor of the later,
> non-counting reformulation of the node (the line of [18](18_SNOL.md); SNOL:
> `twin_primes_of_SNOL` in `SNOL.lean` uses the same bridge `twin_prime_conjecture_of_blocks`).
> There the open core is lifted out of the counting language of ranks into a structural
> predicate; but the logical skeleton — "block $\Rightarrow$ survivor $\Rightarrow$ twin
> $\Rightarrow$ infinitude" — remains the same one assembled here.

## 15.5. The plan for closing

To close $H$ means to establish its two analytic conjuncts on the real intervals: to exhibit the
strict real four-corner at arbitrarily large scales (the transfer of the model via control of
the remainder $e_{ij}$, chapter 14) and to secure the carrier bound together with the
recognition of the survivor as a twin. The first conjunct is a problem of parity and the sieve
remainder term; the second is a lower bound on the carrier's density. Neither of them, on the
available numerical evidence, follows distribution-free from the current ideas.

The explicit, isolated form of $H$ is needed precisely so that further work strikes at one
sharply outlined target rather than at a blurred assortment of lemmas.

Having assembled the direct implication $H\Rightarrow$ `TwinLowers.Infinite`, it is natural to
look at it from the other side — by contradiction. In the next chapter we take the
contraposition of the whole programme: we assume that the twins are *finite* and show that,
together with the same input $H$, this leads to a contradiction (`twin_finite_contradiction`).

We shall see that the proof by contradiction gives no new leverage — it re-encodes the very same
four-corner/carrier/parity wall — but it does give a clean verified verdict: the finiteness of
the twins is contradictory modulo $H$, and $H$ is the single, precisely localized open input.

<!--navbot-->

---

[← 14. Decomposition of the remainder](14_RealFourCorner.md) · [Table of contents](00_Overview.md) · [16. By contradiction →](16_FiniteContradiction.md)
<!--/navbot-->
