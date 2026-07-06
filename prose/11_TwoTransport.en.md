# 11. The twin conjecture from the block core

<!--navtop-->
[← 10. survivor ⇒ twin](10_NonCover.md) · [Table of contents](00_Overview.md) · [12. Four-corner →](12_FourCorner.md)
<!--/navtop-->



> Lean: `Engine/TwoTransport.lean` (`twin_prime_conjecture_of_blocks`, `twin_center_of_block`, `prime_of_no_small_prime_factor`, `isTwinCenter_of_root_sieve`).

In chapter [10 NonCover](10_NonCover.md) we built two elementary facts: from an overweight of the carrier over the "bad" set a survivor is extracted (`survivor_of_not_covered`), and a scale-unbounded supply of twin centers implies the conjecture itself (`infinite_of_unbounded_centers`). Now we assemble these bricks into a single non-circular bridge and, more importantly, delineate precisely where within it the boundary between the proven and the open runs.

The present chapter is a nodal one: it states a conditional reduction of the twin prime conjecture to a single block statement and proves that one of the three ingredients of that statement (the survivor⟹twin passage) is elementary, so that all the remaining difficulty is localized in the counting part.

## Setting: what we want to transport

Let us recall the center form of a twin pair, fixed in the foundations of the programme. A center $m$ determines a twin pair if both sides are prime.

**Definition 11.1** (twin center). For $m \in \mathbb{N}$ we set
$$\mathrm{IsTwinCenter}(m) \;:\Longleftrightarrow\; (6m-1)\ \text{prime}\ \wedge\ (6m+1)\ \text{prime}.$$
In Lean this is `IsTwinCenter m := (6 * m - 1).Prime ∧ (6 * m + 1).Prime`. The set of lower members of twin pairs is denoted `TwinLowers`, and the goal of the whole chain is `TwinLowers.Infinite`, that is, the infinitude of the set $\{p : p, p+2\ \text{prime}\}$.

Restricting to centers of the form $6m\pm 1$ does not narrow the problem: every twin pair except $(3,5)$ has the form $(6m-1, 6m+1)$, since any prime $>3$ is congruent to $\pm 1$ modulo $6$. Hence the infinitude of twin centers is equivalent to the infinitude of twin pairs — and this equivalence is exactly what `infinite_of_unbounded_centers` from the previous chapter packages.

## One block: the local transport lemma

The work proceeds block by block. At each scale $N$ we consider a finite set of candidates — the **carrier** — all of whose elements lie above $N$, and a finite set **bad** of those which are definitely not twin centers. The local step asserts: if the carrier numerically outweighs the bad and every non-bad element of the carrier is a twin center, then above $N$ a twin center is guaranteed to exist.

**Theorem 11.2** (`twin_center_of_block`). Let $N \in \mathbb{N}$, and let $\mathit{carrier}, \mathit{bad} \subseteq \mathbb{N}$ be finite sets satisfying:
$$(\mathrm{above})\ \forall m \in \mathit{carrier},\ N < m;\qquad (\mathrm{cov})\ |\mathit{bad}| < |\mathit{carrier}|;$$
$$(\mathrm{twin})\ \forall m \in \mathit{carrier},\ m \notin \mathit{bad} \Rightarrow \mathrm{IsTwinCenter}(m).$$
Then $\exists m,\ N < m\ \wedge\ \mathrm{IsTwinCenter}(m).$

The proof is direct and rests on exactly two facts. From the strict cardinality inequality $(\mathrm{cov})$, by `survivor_of_not_covered` (chapter [10](10_NonCover.md)), a survivor $m \in \mathit{carrier}$ with $m \notin \mathit{bad}$ is extracted. Condition $(\mathrm{above})$ gives $N < m$, and the implication $(\mathrm{twin})$, applied to this survivor, gives $\mathrm{IsTwinCenter}(m)$. In Lean this is literally two lines:
```
obtain ⟨m, hm, hmb⟩ := survivor_of_not_covered hcov
exact ⟨m, habove m hm, htwin m hm hmb⟩
```

> **Note.** There is no analysis here, no distribution of primes — only Finset combinatorics: if the carrier lay entirely inside the bad set, we would have $|\mathit{carrier}| \le |\mathit{bad}|$, contradicting $(\mathrm{cov})$. All the substantive work is hidden in the three hypotheses $(\mathrm{above})$, $(\mathrm{cov})$, $(\mathrm{twin})$; the lemma merely combines them honestly.

## The global bridge: reducing the conjecture to the block core

The local lemma yields a twin center above a single $N$. To obtain infinitude, the block premise must hold at *every* scale. That is the block core.

**Theorem 11.3** (`twin_prime_conjecture_of_blocks`). Suppose that
$$\forall N \in \mathbb{N},\ \exists\, \mathit{carrier}, \mathit{bad} \subseteq \mathbb{N}\ \text{finite},\quad (\mathrm{above}) \wedge (\mathrm{cov}) \wedge (\mathrm{twin}).$$
Then $\mathrm{TwinLowers.Infinite}$ — there are infinitely many twin primes.

The proof is assembled from parts already at hand. By `infinite_of_unbounded_centers` it suffices to show the unboundedness of twin centers: for an arbitrary $N$, to exhibit a center above $N$. We fix $N$, take from the premise a block $(\mathit{carrier}, \mathit{bad})$ for this $N$, and apply Theorem 11.2 (`twin_center_of_block`). Formally:
```
apply infinite_of_unbounded_centers
intro N
obtain ⟨carrier, bad, habove, hcov, htwin⟩ := h N
exact twin_center_of_block habove hcov htwin
```

The point of the theorem is that it **isolates the open core** in a form fit for further work. The implication "block core $\Rightarrow$ conjecture" is machine-verified and non-circular: nowhere does it use the conjecture itself, and it does not hide the conjecture inside the premise. What remains open is exactly the premise — that at every scale such a block exists. This premise splits into three independent nodes:

1. **the carrier lower bound** — that the carrier of candidates above $N$ is large enough (in the programme's terms this is the input `CarrierInput` — a named 🔴 statement still missing on the way to the goal, see the [glossary](GLOSSARY.md));
2. **the bad upper bound** — that the bad set is strictly smaller than the carrier (via the fan/cycle count, see [09 Cycle](09_Cycle.md));
3. **survivor⟹twin** — that every non-bad survivor really is a twin center.

> **Note.** The split into three nodes is not cosmetic. It turns "prove the conjecture" into "prove a cardinality inequality plus a survival criterion", that is, into a purely combinatorial problem about finite sets. No step of the bridge appeals to the density of primes. This is precisely why we call it non-circular: the conjecture is derived, not postulated somewhere deep inside the premise.

## The third node is elementary: sieving up to the root

The remaining part of the chapter closes node (3) completely and thereby shifts all the difficulty into the counting pair (1)–(2). The key is the classical primality criterion via trial division up to the square root.

**Theorem 11.4** (`prime_of_no_small_prime_factor`). Let $n \ge 2$ and suppose no prime $p$ with $p^2 \le n$ divides $n$:
$$\forall p\ \text{prime},\ p^2 \le n \Rightarrow p \nmid n.$$
Then $n$ is prime.

The proof is by contradiction. If $n$ is not prime, consider its minimal prime divisor $p = \mathrm{minFac}(n)$; for $n \ge 2$ it exists and is prime (`Nat.minFac_prime`), and $p \mid n$ (`Nat.minFac_dvd`). Minimality gives $p \le n / p$ (`Nat.minFac_le_div` for non-prime $n$), whence
$$p^2 = p \cdot p \le p \cdot (n / p) \le n$$
(the last step is `Nat.mul_div_le`). Thus $p$ is a prime divisor of $n$ with $p^2 \le n$, contradicting the premise. Hence $n$ is prime.

> **Note.** The observation underlying the criterion: a composite $n$ has its least prime divisor at most $\sqrt n$, for otherwise the product of two divisors, each greater than $\sqrt n$, would exceed $n$. This is an identity of the era of Eratosthenes, here cast without a sieve as such — via `minFac`. No enumeration whatsoever: one inequality and minimality.

Applying the criterion to both sides of a center, we obtain the desired survival criterion.

**Theorem 11.5** (`isTwinCenter_of_root_sieve`). Suppose that for a center $m$ both sides are at least $2$ ($2 \le 6m-1$ and $2 \le 6m+1$), and no prime up to the root of each side divides it:
$$\forall p\ \text{prime},\ p^2 \le 6m-1 \Rightarrow p \nmid (6m-1);\qquad \forall p\ \text{prime},\ p^2 \le 6m+1 \Rightarrow p \nmid (6m+1).$$
Then $\mathrm{IsTwinCenter}(m)$.

The proof is just a pair of applications of the previous theorem: Theorem 11.4 (`prime_of_no_small_prime_factor`) gives the primality of $6m-1$ and $6m+1$ separately, and their conjunction is exactly $\mathrm{IsTwinCenter}(m)$. In Lean it is one line via the constructor:
```
⟨prime_of_no_small_prime_factor h1 s1, prime_of_no_small_prime_factor h2 s2⟩
```

The substantive conclusion: node (3) contains no difficulty. The condition "$m$ is not bad", in the right encoding, means exactly "no small prime (up to the root of a side) divides either side" — and by Theorem 11.5 (`isTwinCenter_of_root_sieve`) this immediately implies twin-centrality. In other words, if the bad set is defined as the centers for which *at least one* side has a prime divisor below the root, then the implication $(\mathrm{twin})$ of the block core holds automatically, with no additional assumptions.

> **Note.** It is important here not to pass a reduction off as a proof. Theorem 11.5 (`isTwinCenter_of_root_sieve`) proves only the *direction* survivor⟹twin: a non-bad survivor is a twin center. It does not assert that a survivor exists — that is the job of nodes (1)–(2). We have closed the third of the three nodes and thereby shown where the remaining difficulty definitely is *not* hiding.

## What is proven and what remains

Let us take stock of the chapter. Machine-verified and non-circular are:

- the local transport Theorem 11.2 (`twin_center_of_block`): a block with a carrier overweight $\Rightarrow$ a twin center above $N$;
- the global reduction Theorem 11.3 (`twin_prime_conjecture_of_blocks`): the block core at all scales $\Rightarrow$ the twin conjecture;
- the elementarity of the third node: Theorem 11.4 (`prime_of_no_small_prime_factor`) and Theorem 11.5 (`isTwinCenter_of_root_sieve`) close survivor⟹twin without analysis.

**Chapter takeaway.** What remains open is the **counting core** — nodes (1) and (2): at every $N$, the carrier above $N$ strictly outweighs the bad set, $|\mathit{bad}| < |\mathit{carrier}|$.

It is natural to expect that this overweight is secured by the structural **exclusivity of two** (chapter [02 Carrier](02_Carrier.md)): a prime $p>2$ divides at most one of the sides $6m\pm 1$, since $\gcd(6m-1, 6m+1) \mid 2$. From this exclusivity the bad classes over different primes cannot "add up freely" — they partially exclude one another, and the total bad share does not cover the carrier.

The plan for closing is this: translate the overweight $|\mathit{bad}| < |\mathit{carrier}|$ into an inequality on the counts of low and high ranks and prove that inequality combinatorially, not through the density of primes.

It is exactly to this translation that we turn in the next chapter, [12 four-corner]: there the exclusivity of two is cast as negative association of the side ranks — the cross term is forbidden, the generating function factors into a product $\prod_p (c_p + a_p x + b_p y)$ with no $xy$ term — and this yields the four-corner inequality $N_{00}N_{33} \le N_{03}N_{30}$, from which the sought overweight of the carrier over the bad is extracted. Thus the open counting core of the present chapter acquires its concrete combinatorial route.

<!--navbot-->

---

[← 10. survivor ⇒ twin](10_NonCover.md) · [Table of contents](00_Overview.md) · [12. Four-corner →](12_FourCorner.md)
<!--/navbot-->
