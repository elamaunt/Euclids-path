# 28. Factorisation: a RankNode from the composite side

<!--navtop-->
[← 27. Product-core](27_ProductCore.md) · [Table of contents](00_Overview.md) · [29. The last link →](29_CarrierBridge.md)
<!--/navtop-->



> Lean source: `Engine/MkNode.lean` (namespace `EuclidsPath.MkNode`, `open EuclidsPath.ProductCore`).
> All the arithmetic of this chapter is proven without axioms and without `sorry`.

In the previous chapter, on the product-core, we fixed the finite stage of the engine: a node of rank `r`
as the extensional object `RankNode r`, consisting of a sign `sign` and a role-indexed
family of factors `factors : Fin r → ℕ`, together with the certificate `AmbientLegal`, guaranteeing
that all factors divide a single top-side `N₀ ≤ 6X_A+1`. But the stage remained empty: we described *what*
a node should be, and proved that a ProductHall is impossible on such nodes — yet we exhibited not a
single node.

The present chapter fills this gap. We shall show how, from the pure arithmetic of the composite
side of a centre `m`, to build a concrete `RankNode r` with `2 ≤ r ≤ 4`, factors `> A`, and the certificate
`AmbientLegal`. This is the brick from which the next chapter will assemble an infinite stream of nodes.

## 28.1. The setting: from a centre to a decomposition

Let us recall the geometry of the carrier space. Every candidate for a twin centre is a number `m`, and its two
sides are

$$
6m - 1 \quad\text{and}\quad 6m + 1 .
$$

The centre is a twin centre exactly when both sides are prime. If at least one side is
composite, the centre "misses", and it is precisely this miss that we want to turn into structure. The composite
side `N` decomposes into a product of primes, and this decomposition is nothing other than the list of factors
of the future `RankNode`. The task of the chapter: to prove that this list has length between `2` and `4`, that all its
elements exceed `A`, and that it carries the certificate `AmbientLegal`.

> **Note.** The parameter `A` is the upper bound on the "small" primes filtered out by the sieve. The condition
> `Clean A m` (see §28.5) means that no prime `q ≤ A` divides either side of the centre
> `m`. It is precisely the cleanness of the centre that forces all prime factors of the composite side to be large,
> `> A` — and this, in turn, bounds the *number* of factors from above.

## 28.2. The lower bound on the product: `(A+1)^len ≤ prod`

The first and most elementary fact is a lower bound on the product of the list of factors in terms of its length.

> **Definition 28.1** (list of large factors). Let `L : List ℕ` be a list of natural numbers. We say
> that `L` consists of factors greater than `A` if
> $$ \forall a \in L,\quad A < a . $$

**Theorem 28.2** (`prod_ge_of_factors_gt`). If every element of the list `L` is strictly greater than `A`, then

$$
(A+1)^{\lvert L\rvert} \le \prod L , \tag{28.1}
$$

where `|L|` is the length of the list, and `∏ L = L.prod` is the product of its elements.

*What is proven and why.* The proof goes by induction on the list. For the empty list both sides equal
`1` (`(A+1)^0 = 1 = ∏ []`). At the step `cons x xs` we use the fact that every element, being `> A`,
satisfies `A + 1 ≤ x` (in the natural numbers the strict inequality `A < x` is equivalent to
`A + 1 ≤ x`), while by the induction hypothesis `(A+1)^{|xs|} ≤ ∏ xs`. Multiplying these two inequalities
by the monotonicity of multiplication (`Nat.mul_le_mul`), we get

$$
(A+1)^{|xs|}\cdot(A+1) \;\le\; \bigl(\textstyle\prod xs\bigr)\cdot x ,
$$

and the left-hand side is exactly `(A+1)^{|xs|+1} = (A+1)^{|L|}`, while the right-hand side, after rearranging the factors
(`ring`), equals `∏ L`. Here the substitution `x * ∏ xs = (∏ xs) * x` matters, to match the order with
`List.prod_cons`.

*What this means.* The bound translates a statement about the *number* of factors into a statement about the *size* of the
product. Each factor weighs at least `A+1`, so a long list of large factors yields
an exponentially large product. It is precisely this that will allow us to bound the length from above, knowing that
the product cannot be too large.

## 28.3. The rank does not exceed four: `factor_rank_le_four`

Now we join the lower bound of §28.2 with the scale constraint. The key observation: the composite
side `N` of a legal centre does not exceed `6X_A + 1`, and the sieve is tuned so that this threshold is itself
smaller than `A^5`. From the intuition of decomposition it is clear that "too many" large factors do not fit under
such a ceiling.

**Theorem 28.3** (`factor_rank_le_four`). Let `1 ≤ A`, let the list `L` consist of factors `> A`, let its
product satisfy `∏ L ≤ 6X_A + 1`, and let the scale inequality `6X_A + 1 < A^5` hold.
Then

$$
\lvert L\rvert \le 4 .
$$

*What is proven and why.* We argue by contradiction. Suppose `|L| ≥ 5` (in Lean this is written as
`4 < |L|` after `not_le`). Then, combining the monotonicity of the power in the exponent
(`Nat.pow_le_pow_right`) with the lower bound Theorem 28.2 (`prod_ge_of_factors_gt`), we obtain the chain

$$
(A+1)^5 \;\le\; (A+1)^{\lvert L\rvert} \;\le\; \prod L \;\le\; 6X_A + 1 \;<\; A^5 . \tag{28.2}
$$

On the other hand, since `A ≥ 1`, the power is strictly increasing in the base:

$$
A^5 \;<\; (A+1)^5
$$

(the lemma `Nat.pow_lt_pow_left` with `A < A+1`). All told, we simultaneously have `(A+1)^5 ≤ 6X_A+1 < A^5` and
`A^5 < (A+1)^5`, which yields `(A+1)^5 < (A+1)^5` — a contradiction, closed by `omega`.

*What this means.* This is the very source of the magic number `4` in the whole engine construction. The rank of a node
— the number of prime factors of the composite side — is bounded above by four not by definition and not by
convention, but as an arithmetic consequence of the sieve scale `6X_A + 1 < A^5`. Five large factors
would give a product of at least `(A+1)^5 > A^5`, which does not fit under the ceiling `6X_A + 1`.

**Conclusion.** Hence the finiteness of the rank space `{2,3,4}`, on which the subsequent
pigeonhole — the boxes principle (see the [glossary](GLOSSARY.md)) — rests.

> **Note.** The scale inequality `6X_A + 1 < A^5` is not a hypothesis but a checkable property of the
> sieve's tuning; here it enters as an explicit hypothesis `hscale`, so that the theorem remains pure
> arithmetic, untied to any concrete `X_A`. The exponent `5` is `4 + 1`: it is exactly one
> greater than the sought rank bound, and that is what makes the step "five factors ⟹ product `≥ (A+1)^5 > A^5`"
> decisive.

## 28.4. The rank is at least two: `composite_rank_ge_two`

An upper bound on the rank is useless without a lower one: a node of rank `0` or `1` would not be a decomposition of a composite
number. The lower bound is supplied by the very definition of compositeness.

**Theorem 28.4** (`composite_rank_ge_two`). If `1 < N` and `N` is not prime (`¬ N.Prime`), then the list of prime
factors has length at least two:

$$
2 \le \bigl\lvert \mathrm{primeFactorsList} N\bigr\rvert .
$$

*What is proven and why.* The starting point is the identity `Nat.prod_primeFactorsList`: for `N ≠ 0`
the product of the canonical list of prime factors equals `N` itself. Then comes a case analysis by contradiction
on the length of the list (`interval_cases` under `|L| < 2`):

- Length `0` would mean `L = []`, whence `∏ L = 1`, that is `N = 1`, contradicting `1 < N`.
- Length `1` would mean `L = [p]` with a single prime `p` (by `List.length_eq_one_iff`). Then
  `∏ L = p = N`, and since `p` is prime (by `Nat.prime_of_mem_primeFactorsList`), `N` itself
  would turn out to be prime, contradicting `¬ N.Prime`.

Both cases lead to a contradiction, so the length is at least `2`.

*What this means.* Compositeness is exactly the presence of at least two prime factors (counted with
multiplicity). Formally, this fact, trivial on paper, requires carefully tying together three mathlib
lemmas about `primeFactorsList`, and here it is proven clean. Together with §28.3 we get the pinched fork
$2 \le r \le 4$ — the finite range of node ranks.

## 28.5. A clean centre forces the factors to be large: `prime_factor_gt_A_*`

It remains to explain *where* the condition "all factors `> A`", which we have used everywhere as
a hypothesis, comes from. It follows from the cleanness of the centre.

> **Definition 28.5** (`Clean A m`). The centre `m` is clean with respect to `A` if no prime `q ≤ A`
> divides either of its sides:
> $$ \forall q\ \text{prime},\ q \le A \;\Rightarrow\; \neg\bigl(q \mid (6m-1)\ \lor\ q \mid (6m+1)\bigr). $$

**Theorem 28.6** (`prime_factor_gt_A_plus`, `prime_factor_gt_A_minus`). Let the centre `m` be clean
(`Clean A m`), and let `p` be prime. If `p ∣ (6m + 1)` (respectively `p ∣ (6m - 1)`), then

$$
A < p .
$$

*What is proven and why.* The proof of both versions is a direct contraposition. Suppose
`p ≤ A`. Then `p` is a prime not exceeding `A` that divides one of the sides, which exactly negates
the cleanness condition `Clean A m` (in the `plus` case via `Or.inr hdvd`, in the `minus` case via
`Or.inl hdvd`). Contradiction; hence `A < p`.

*What this means.* This is the bridge lemma between the sieve and the decomposition. The sieve guarantees that the surviving centres
have no small prime divisors on their sides; consequently, any prime factor of the composite side
is automatically large, `> A`. It is precisely this property that feeds the hypothesis `hgt` into all the preceding theorems — and
closes the fork `2 ≤ r ≤ 4` on a *concrete* decomposition of a concrete side.

## 28.6. Choosing the composite side: `composite_side_of_not_twin`

Before building a node, we must choose *which* side to decompose. For a centre that missed,
at least one of the two sides is composite — and that one we shall take.

**Theorem 28.7** (`composite_side_of_not_twin`). Let both sides be nontrivial, `1 < 6m - 1` and
`1 < 6m + 1`, and let the centre *not* be twin, that is, it is false that both sides are prime
(`¬ ((6m-1).Prime ∧ (6m+1).Prime)`). Then there exists a composite nontrivial side:

$$
\bigl(1 < 6m-1\ \land\ \neg(6m-1)\ \text{prime}\bigr)\ \lor\ \bigl(1 < 6m+1\ \land\ \neg(6m+1)\ \text{prime}\bigr).
$$

*What is proven and why.* A case analysis on the primality of the lower side. If `6m - 1` is not prime —
we take it (the left disjunct). If, however, `6m - 1` is prime, then the negation of the twin condition implies that
`6m + 1` cannot be prime, and we take the upper side (the right disjunct). The case where both
sides are prime is impossible — it directly contradicts `¬ (…∧…)` via `absurd`.

*What this means.* The negation of a twin centre — the purely logical statement "not both prime" — constructively
turns into the presentation of a *concrete* composite side. This is the transition from "the centre missed" to
"here is the number we shall decompose". The requirement `1 < side` cuts off the degenerate small centres, where
a side equals `1` and there is no decomposition.

## 28.7. Assembling the node: `mkNode_of_composite`

All the ingredients are ready. The composite side `N` yields a list of prime factors; §28.4 guarantees
length `≥ 2`, §28.3 — length `≤ 4`, §28.5 — that all factors are `> A`. It remains to pack this into a
`RankNode` with the certificate `AmbientLegal`.

> **Definition 28.8** (`AmbientLegal`, a reminder from chapter 27). The family `factors : Fin r → ℕ`
> is legal in the ambient `X_A` if there exists a common top-side `N₀` which they all divide and which
> does not exceed the sieve's ceiling:
> $$ \exists N_0,\ 0 < N_0\ \land\ N_0 \le 6X_A + 1\ \land\ \forall i,\ \mathtt{factors}\,i \mid N_0 . $$

**Theorem 28.9** (`mkNode_of_composite`). Let `1 ≤ A`, `1 < N`, let the number `N` be composite, not exceeding
the ceiling `N ≤ 6X_A + 1`, let the scale inequality `6X_A + 1 < A^5` hold, and let every prime divisor
of `N` be greater than `A` (`∀ p, p.Prime → p ∣ N → A < p`). Then for any sign `sgn : Sign` there exists a rank
`r` with `2 ≤ r ≤ 4` and a node `X : RankNode r` such that

$$
\mathtt{AmbientLegal}\ X_A\ X.\mathtt{factors}\qquad\text{and}\qquad \prod \bigl(\mathrm{ofFn} X.\mathtt{factors}\bigr) = N . \tag{28.3}
$$

*What is proven and why.* We build the node explicitly. Let `L = primeFactorsList N`. Then:

- `hr2 : 2 ≤ |L|` — from Theorem 28.4 (`composite_rank_ge_two`, §28.4);
- `hgt : ∀ a ∈ L, A < a` — every element of the list is a prime divisor of `N`
  (`Nat.prime_of_mem_primeFactorsList`, `Nat.dvd_of_mem_primeFactorsList`), and the hypothesis `hbig`
  makes it `> A` (this is §28.5, supplied as an input);
- `hprodN : ∏ L = N` — the identity `Nat.prod_primeFactorsList`;
- `hr4 : |L| ≤ 4` — from Theorem 28.3 (`factor_rank_le_four`, §28.3), where the premise `∏ L ≤ 6X_A+1` is obtained
  by substituting `∏ L = N ≤ 6X_A+1`.

As the rank we take `r = |L|`, and the node itself is `⟨sgn, fun i => L.get i⟩`: the sign is fixed from outside,
the factors are the elements of the list, indexed by `Fin |L|`. Two obligations remain to be checked:

1. `AmbientLegal`: we take a witness — a concrete object certifying the statement (see
   the [glossary](GLOSSARY.md)) — `N₀ = N`. It is positive (from `1 < N`), does not exceed the ceiling
   (`hNle`), and every `L.get i` divides `N`, since it divides the product `∏ L = N`
   (`List.dvd_prod` for a list element `List.get_mem`).
2. The agreement of products: `(ofFn (L.get ·)).prod = ∏ L` by `List.ofFn_get` (recovering a
   list from its components), and `∏ L = N` is already established.

*What this means.* This is the central theorem of the chapter — "Theorem 7.1" in the source's numbering. It
turns an arithmetic fact (a composite side has `2..4` large prime factors) into a
structural object of the engine's stage: a genuine `RankNode` with a certificate of legality. The sign `sgn`
is supplied from outside, because it encodes *which* of the two sides was composite — that information
comes from §28.6, not from the decomposition itself.

It is important to stress: the node is built *constructively*, not
postulated; the product of its factors is provably equal to the original side `N`, that is, the node is an
exact decomposition, not an abstract label.

> **Note (no reduction passed off as a proof).** All seven statements of this chapter —
> `prod_ge_of_factors_gt`, `factor_rank_le_four`, `composite_rank_ge_two`,
> `prime_factor_gt_A_plus`, `prime_factor_gt_A_minus`, `composite_side_of_not_twin`,
> `mkNode_of_composite` — are proven in full, without `sorry` and without axioms beyond mathlib. This is pure
> factorisation arithmetic: it assumes no property of the engine and asserts nothing about it. There
> are no open nodes here.

## 28.8. Where the boundary of the proven lies, and the bridge to chapter 29

It is worth delineating explicitly what this chapter does *not* do, so as not to pass off a partial result as the whole. We
have shown: a *given* clean centre `m` that missed the twin supplies *one* legal
`RankNode` of rank `2..4`. We have not shown here that such centres are infinitely many and that among them
infinitely many share the same rank. Precisely this is the single substantive input (a gate: an honestly named missing statement,
see the [glossary](GLOSSARY.md)) separating the local factorisation from the global launch of the engine.

> **Hypothesis carried into the next chapter.** There exists an infinite set of clean centres (this
> is an already-proven fact, `Residuals.carrier_nonempty_above`: above any `N` there is a clean centre),
> and, applying `mkNode_of_composite` to each, we obtain an infinite family of nodes. By
> pigeonhole on the finite set of ranks `{2,3,4}`, infinitely many nodes have *one* rank `r`.
> **Closure plan:** cast this as a structure `FactorizationData` — an infinite subset of
> centres of fixed rank with an injective, `AmbientLegal`-certified map
> `node : ℕ → RankNode r`.

In other words, `mkNode_of_composite` is a "node factory", and the next chapter connects an
infinite conveyor to it: the **carrier bridge** will take the proven infinitude of clean centres, run
it through this chapter's factorisation, apply the infinite-pigeonhole on rank, and present that very
`FactorizationData` from which the product-core assembles the `Engine`. To this bridge — from a single node to an
infinite stream of nodes of one rank — we now turn.

<!--navbot-->

---

[← 27. Product-core](27_ProductCore.md) · [Table of contents](00_Overview.md) · [29. The last link →](29_CarrierBridge.md)
<!--/navbot-->
