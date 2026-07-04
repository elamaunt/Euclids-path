# 22. Discharging density and parity in existential form

<!--navtop-->
[← 21. Regeneration](21_Regeneration.md) · [Table of contents](00_Overview.md) · [23. Clean graph →](23_CleanGraph.md)
<!--/navtop-->



> Source: `step00_residuals_formal_proofs_ru_2026-06-30-1.md`. Lean: `Engine/Residuals.lean`
> (namespace `EuclidsPath.Residuals`, standard axioms, no `sorry`).

## Where we are

The dichotomy of [21](21_Regeneration.md) classified every quotient centre `t` into one of the elementary classes —
twin, old-peel edge, or a composite old-free side — and localised the nontrivial residue in
structural regeneration, not in counting.

But the dichotomy itself was left with two inputs (an input is a named missing statement,
see the [glossary](GLOSSARY.md)) which in the earlier prose looked "distributional":
(i) where to find a clean centre arbitrarily high (density of the carrier) and (ii) why a clean sink
really consists of two primes (parity/distribution of primes on the sides).

In this chapter we show that both inputs are discharged **in existential form** —
by construction and elementary divisibility, without a single density estimate or prime count.

## Working definitions

We work with the sides of a centre `m`, that is, with the pair $6m-1,\ 6m+1$. Throughout, `A` is the
boundary of the "old" primes (the old primorial is built over `5 ≤ p ≤ A`), and `N` is the scale above
which we want to find a centre.

**Definition 22.1** (clean centre). We call a centre $m$ *clean* relative to $A$ if no prime $q \le A$ divides either side:
$$\mathrm{CleanZ}\,A\,m \ :\equiv\ \forall q\ \text{prime},\ q \le A \ \Rightarrow\ \neg\big(q \mid 6m-1\ \lor\ q \mid 6m+1\big). \tag{22.1}$$
In Lean this is `CleanZ A m` (the sides are taken in `ℤ`, so that the subtraction $6m-1$ is safe).

**Definition 22.2** (twin centre). A centre $m \ge 1$ is a *twin* if both sides are prime:
$$\mathrm{TwinCenterZ}\,m \ :\equiv\ (6m-1)\ \text{prime}\ \wedge\ (6m+1)\ \text{prime}. \tag{22.2}$$
In Lean this is `TwinCenterZ m` (the sides in `ℕ`).

The distinction between the two properties is the key to the whole chapter. Clean is a negation of
divisibility by *small* primes; it is available constructively. Twin is a positive statement of
primality; naively it requires knowing the distribution of primes. We will join them so that the
second follows from the first plus a bound on the scale.

## Residue ② — a constructive clean start above any `N` (without density)

It is natural to suppose that clean centres are "rare", and hence their existence above `N` demands a
density estimate. The observation that discharges this input is the opposite: a clean centre can be
**written out by a formula**.

**Definition 22.3** (old primorial). We set
$$P_A \ :=\ \prod_{\substack{5 \le p \le A\\ p\ \text{prime}}} p, \tag{22.3}$$
in Lean — `oldPrimorial A := (Finset.range (A+1)).prod (fun p => if p.Prime ∧ 5 ≤ p then p else 1)`.
Each factor is either a prime $5 \le p \le A$ or $1$; hence `oldPrimorial_pos` gives
$P_A \ge 1$, and `prime_dvd_oldPrimorial` — that every prime $5 \le q \le A$ divides $P_A$ (it is
literally one of the factors of the product).

The central lemma is that any multiple of this primorial is already clean.

**Lemma 22.4** (`primorial_multiple_clean`). For all $A$ and $k \ge 1$ the centre $m = k \cdot P_A$
is clean: $\mathrm{CleanZ}\,A\,((k \cdot \mathrm{oldPrimorial}\,A : \mathbb{N}) : \mathbb{Z})$. The case split goes by the size of $q$:

- **$q \ge 5$.** Then $q \mid P_A \mid m$, hence $q \mid 6m$. If $q$ divided $6m-1$, then from
  $q \mid 6m$ and $q \mid 6m-1$ we would get $q \mid 1$ (the difference), that is $q \le 1$ — a contradiction;
  symmetrically for $6m+1$. Formally: $6m \equiv 0 \pmod{q} \Rightarrow 6m \pm 1 \equiv \pm 1 \not\equiv 0$.
- **$q = 2$.** Both sides are odd ($6m$ is even, $6m\pm1$ odd), so there is no divisibility.
- **$q = 3$.** $6m \equiv 0 \pmod{3} \Rightarrow 6m\pm1 \equiv \pm 1 \pmod{3} \not\equiv 0$.

The cases $q < 5$ in Lean are closed by `interval_cases q` (the values $2,3$ are handled by `omega`, the
values $0,1,4$ are discarded as non-prime).

> **Note.** This is exactly why the old primorial is taken with lower bound `5`: the factors `2` and `3`
> need not be excluded — their staying off the sides is guaranteed not by the divisibility of `m` but by
> the very shape $6m\pm1$. This makes the construction minimal: $P_A$ carries exactly those primes that
> could otherwise touch the sides.

From the lemma we obtain the existence of a clean centre above an arbitrary scale.

**Corollary 22.5** (`carrier_nonempty_above`). For any $A, N$ there exists $m > N$ with $\mathrm{CleanZ}\,A\,m$.
The witness (a concrete object certifying a statement — see the [glossary](GLOSSARY.md)) is
$m = (N+1)\cdot P_A$: it is clean by Lemma 22.4 (`primorial_multiple_clean`) (with $k = N+1 \ge 1$), and the
inequality $N < m$ follows from $P_A \ge 1$ via the chain $N < N+1 = (N+1)\cdot 1 \le (N+1)\cdot P_A$.

> **Note.** This is precisely the discharge of the "density of the carrier" input *in existential
> form*. We do not claim how many clean centres lie in a segment — we exhibit *one* concrete centre,
> above any given bound. For a programme that works through descent (it needs *at least one* high clean
> start at each scale), this is enough; the asymptotics of the carrier is never invoked at all.

## Residue ③ — a clean sink is a twin (parity is elementary)

The second input question: why is a correct sink of the engine really a twin pair, and not merely a
clean centre with a composite side. Here "parity/distribution" is discharged: positive primality is
derived from negative cleanliness plus a bound on the scale.

We begin with an observation about what can possibly "hide" in a clean composite side.

**Lemma 22.6** (`clean_side_composite_big_divisor`, the core). If a side $\mathit{side} \ge 2$ is not prime and
no prime $q \le A$ divides it, then its least prime divisor is greater than $A$:
$$\exists b\ \text{prime},\ A < b\ \wedge\ b \mid \mathit{side}.$$
The witness is `side.minFac`. It is prime (`Nat.minFac_prime`, since $\mathit{side} \ge 2$) and divides $\mathit{side}$; and if
it were $\le A$, that would contradict cleanliness. Such a large divisor is exactly the *active edge*
of the dichotomy [21](21_Regeneration.md): a composite clean side is forced to carry a new prime $> A$.

Hence — the bound that turns cleanliness into primality.

**Lemma 22.7** (`oldfree_below_sq_prime`). If $n \ge 2$, $n < A^2$ and no prime $q \le A$
divides $n$ (an *old-free* number), then $n$ is prime. Proof by contradiction: suppose $n$ is composite.
Then $p := n\text{.minFac}$ is prime, $p \mid n$ and by cleanliness $p > A$. For composite $n$ the minimality
of the prime divisor gives $p \le n/p$ (`Nat.minFac_le_div`), whence
$$p^2 \ \le\ p \cdot (n/p) \ =\ n. \tag{22.4}$$
But then $A^2 < p^2 \le n < A^2$ — a contradiction (`nlinarith`). Hence $n$ is prime.

> **Note.** The threshold `A^2` is not a heuristic but the exact "sieve of Eratosthenes" boundary: a
> number without prime divisors `\le A` and smaller than `A^2` cannot be composite, since a composite
> number always has a prime divisor `\le \sqrt{n} < A`. This makes the derivation of primality
> *elementary*: one needs neither to know the distribution of primes nor to count them — it suffices
> that the sides are clean and lie below `A^2`.

Joining the cleanliness of both sides with the threshold, we obtain the main conclusion of residue ③.

**Theorem 22.8** (`sink_is_twin`). If both sides satisfy $2 \le 6m\pm1 < A^2$ and the centre is
clean (no $q \le A$ divides either side), then $m$ is a twin: $\mathrm{TwinCenterZ}\,m$. The proof is
two copies of Lemma 22.7 (`oldfree_below_sq_prime`), one per side; the old-freeness of each side is extracted
from the shared cleanliness (`Or.inl` / `Or.inr`).

> **Note.** This is how the "parity/distribution" input is discharged *in existential form*: we do not
> estimate the density of twin centres — we show that **every** clean sink below `A^2` is *automatically*
> a twin. Nature does the work: cleanliness excludes small divisors, the threshold `A^2` excludes large
> ones. Between them, there is no room left for a composite side.

## Pinning the sink to a centre above `N`

It remains to close the loop with residue ②: to make sure the twin sink we found really lies above
the scale `N`, rather than falling below.

**Theorem 22.9** (`clean_twin_above`). If $6N+1 < A$, the centre $m \ge 1$ is clean and is a twin, then $m > N$.
The argument: the side $6m-1$ is prime (from $\mathrm{TwinCenterZ}$), and it is $> A$ — otherwise it would be an
old prime $\le A$ dividing its own side, violating cleanliness (`hcl` with the divisibility $(6m-1) \mid (6m-1)$).
Then from $A > 6N+1$ and $6m-1 > A$ it follows that $6m-1 > 6N+1$, that is $m > N$ (`omega`). In Lean
one carefully coerces $((6m-1 : \mathbb{N}) : \mathbb{Z}) = 6 \cdot m - 1$ (`Nat.cast_sub`, `push_cast`), so that
cleanliness, which lives in $\mathbb{Z}$, applies to the natural-number side.

> **Note.** The condition $6N+1 < A$ is the requirement "the old boundary $A$ overlaps the scale $N$".
> It is automatically compatible with Corollary 22.5: there we are free to take $A$ as large as we like relative to $N$, and
> the sink, being prime, is forced to lie above $A$, and hence above $N$. **Conclusion.** The pair Corollary 22.5 + Theorem 22.8 yields a
> twin centre above any $N$ with no reference to distribution.

## Residue ① — active descent strictly decreases the height

Finally, for the dichotomy to be a genuine *engine* (in the sense of the descent method —
see the [glossary](GLOSSARY.md)), and not merely a classification, the outgoing edge in the
active case must lead *downwards* in height. This is a purely algebraic fact of Euclidean descent.

**Theorem 22.10** (`active_descent_height`). Let $6m+\sigma = a\,(6n+\varepsilon)$, where $a > A \ge 5$,
$\sigma,\varepsilon \in \{\pm1\}$, and the centres $m, n \ge 1$. Then $n < m$.

The case split: the side
$6n+\varepsilon > 0$ (for both signs of $\varepsilon$, since $n \ge 1$), and from $a \ge 5$ it follows that
$$5\,(6n+\varepsilon)\ \le\ a\,(6n+\varepsilon)\ =\ 6m+\sigma. \tag{22.5}$$
Hence $6n+\varepsilon \le (6m+\sigma)/5$, and for $m \ge 1$ the fraction is strictly less than $6m-1$, which after
running through the four sign combinations is closed by `nlinarith`. Substantively: divisibility of the active side
by a large $a > A$ cannot fail to "compress" the centre — the new $n$ is strictly lower.

> **Note.** The factor `5` here is no accident: it is the smallest old prime, and `a > A \ge 5`
> only strengthens the compression. It is the same coefficient `1/5` as in the height-drop of old-peel [19](19_OldPeel.md)
> (`old_peel_height_drop`, `t < n/5`); here it appears on the active edge of the dichotomy and makes the descent
> strict. It is precisely the strict decrease of height that forbids an infinite chain and closes the flow onto the
> impossibility of the engine [20](20_NOPSL.md).

## What is proven and what it means

All seven links are checked by the compiler on the standard axioms, without `sorry`:

| Link | Lean (number) | What is discharged |
|---|---|---|
| clean start above $N$ | `carrier_nonempty_above` (Corollary 22.5, via Lemma 22.4) | **density of the carrier** — replaced by the construction $m=(N+1)P_A$ |
| old-free $< A^2$ ⟹ prime | `oldfree_below_sq_prime` (Lemma 22.7) | the sieve threshold, elementary |
| clean sink ⟹ twin | `sink_is_twin` (Theorem 22.8) | **parity/distribution** — replaced by cleanliness + the threshold |
| active edge | `clean_side_composite_big_divisor` (Lemma 22.6) | a large divisor $> A$ of a clean composite side |
| twin sink above $N$ | `clean_twin_above` (Theorem 22.9) | pinning the sink to the scale |
| strict descent | `active_descent_height` (Theorem 22.10) | $n < m$ on the active edge |

The point of the chapter is not a new "proof of twins" but the **precise localisation of the inputs**. The two nodes
that all the earlier prose carried as distributional — "is there a clean start high up" and "is a clean
sink really a twin" — are discharged *existentially*: the first by the primorial construction, the second
by the elementary sieve below `A^2`.

**Conclusion.** This is NOT passed off as a closure of the programme: the structural input remains
where the dichotomy [21](21_Regeneration.md) and NOPSL [20](20_NOPSL.md) left it — in regeneration
(closedness of the ledger over old-peel quotients, `regenerate`; the ledger is the bookkeeping of flows,
see the [glossary](GLOSSARY.md)). We have only shown that *around* this input nothing
distributional remains: the start, the threshold, and the descent are constructive and verified.

> **Conjecture and plan (what remains open).** What remains open is `regenerate` — that a quotient centre
> `t` is always classified (clean return / next-peel / fan-in/Hall / known-defect) without an
> unclassifiable terminal. The plan for closing it goes not through density but through the **clean boundary**: to show
> that the boundary of the clean region behaves rigidly, so that fan-in creates no hidden terminal.
> This, precisely, is the subject of the next chapter.

## Bridge to the next chapter

So, density and parity are discharged in existential form: a clean start is written out by a formula, and a
clean sink below `A^2` automatically yields twins. There remains a single structural question —
how **rigid the boundary of the clean region is** when several lineages converge on one centre. It is to
this boundary — the clean boundary — that we turn in [23](23_CleanGraph.md).

<!--navbot-->

---

[← 21. Regeneration](21_Regeneration.md) · [Table of contents](00_Overview.md) · [23. Clean graph →](23_CleanGraph.md)
<!--/navbot-->
