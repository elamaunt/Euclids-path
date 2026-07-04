# 13. The fractal layer and the model four-corner

<!--navtop-->
[← 12. Four-corner](12_FourCorner.md) · [Table of contents](00_Overview.md) · [14. Remainder decomposition →](14_RealFourCorner.md)
<!--/navtop-->




> Lean source: `Engine/ModelFourCorner.lean` (`four_corner_binom`, `four_corner_binom_strict`, `model_four_corner`). The file compiles; `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`.

In the previous chapter [12](12_FourCorner.md) we reduced the statement about twin centres to the **four-corner** inequality $N_{00}N_{33}\le N_{03}N_{30}$ and showed that its sign is rooted not in the density of primes but in the *exclusivity of two*: a prime $p>2$ does not divide both sides $6m\pm1$ at once (`Engine/Carrier.no_large_shared_divisor`, `shared gcd ∣ 2`).

There we worked with abstract rank counts $N_{ij}$ and left one question open: *where do these counts themselves come from, and why does the product over primes have no cross term $xy$*. The present chapter closes that question at the level of the *model*: we write out the rank generating function as a self-similar product, extract from it exact binomial counts, and prove the model four-corner — elementarily, without any distribution of primes, entirely in Lean.

![Fractal of Euclid's path — the rank field](assets/2_rank_field.png)

*Fractal of Euclid's path · **the rank field**: the rank `lexRank` of each centre, coloured by layer — the
very self-similar generating function from which the four-corner grows. The self-similarity here is
*contracting*, not diverging: the pattern repeats on ever finer scales as one moves toward the
centre, rather than branching outward (more in the [coda, chapter 50](50_Coda.md)).*

> **Generation algorithm (Figure 13.1).** Source: `tools/fractal/euclid_fractal.py::rank_field`. Parameters $A=60$, $W=900$; the prime layer is $\{p:\ A<p\le A^2\}$. For each centre index $m\in\{0,\dots,W^2-1\}$ two ranks are counted: $r_-(m)$, the number of layer primes dividing the lower side $6m-1$, and $r_+(m)$, the upper side $6m+1$. Technically, for each $p$ the congruence $6m\equiv\pm1\pmod p$ is solved: the inverse $6^{-1}\bmod p$ gives the root $r\equiv\pm 6^{-1}\pmod p$, the start offset $(r-1)\bmod p$, and a unit is added to every $p$-th position of the array $r_\mp$. The "charge" $r_-(m)-r_+(m)$ is imaged; the length-$W^2$ vector is reshaped into a $W\times W$ matrix (row $=\lfloor m/W\rfloor$, column $=m\bmod W$) and drawn as an image with the diverging *twilight-shifted* palette (negative and positive charge at opposite ends, zero at the centre), lower origin.

## The fractal generating function of rank

We begin with an observation about the structure of rank (on rank as the "height" of a state — see the [glossary](GLOSSARY.md)). By the rank of a centre $m$ we mean the pair $(r_-,r_+)$, where $r_-$ is the number of prime divisors of the lower side $6m-1$, and $r_+$ of the upper side $6m+1$ (within the layer $A$ under consideration). Each prime $p$ of the layer contributes to the rank *independently* by CRT, and its contribution obeys two structural laws that we established earlier.

**The law of $\pm$-symmetry.** A prime's weight on the lower and upper sides is the same: the probability of landing in the class where $p\mid 6m-1$ equals that of the class $p\mid 6m+1$. This is exactly the mirror symmetry provided by the substitution $m\mapsto -m$ (a swap of sides) — from the intuition of the engine (the perpetual engine — the forbidden infinitely descending chain, see the [glossary](GLOSSARY.md)), both sides stand on equal footing, neither is privileged.

**The law of exclusivity.** No $p>2$ divides both sides: the classes $p\mid 6m-1$ and $p\mid 6m+1$ are incompatible. This is `no_large_shared_divisor` from [12](12_FourCorner.md).

From this it is natural to posit that the contribution of a prime $p$ to the rank generating function is a factor
$$
G_p(x,y)\;=\;c_p + a_p\,x + b_p\,y,\qquad a_p=b_p\ (\text{$\pm$-symmetry}),\ \textbf{no } xy\ \text{term}\ (\text{exclusivity}),
$$
where $x$ marks a divisor of the lower side, $y$ of the upper, and the absence of $xy$ is the direct reflection of the fact that "both at once" is impossible. The full generating function is the product over the primes of the layer:
$$
G(x,y)\;=\;\prod_{p}\bigl(c_p + a_p x + a_p y\bigr).
$$

> **Note.** It is precisely the absence of the $xy$ term that is the heart of the whole argument. In the general (non-exclusive) model the factor would be $c+ax+by+dxy$, and the sign of the four-corner would not be forced. Exclusivity zeroes out $d$ at *every* prime, not merely on average; this is a Diophantine property, not a statistical one.

The key **self-similarity**: the factor $G_p$ depends on $x$ and $y$ only through the symmetric combination, so the product $G(x,y)$ is a function of a single variable $s=x+y$. In the equilibrium (homogeneous) model, where all $n$ primes of the layer share a common weight $w$ and a common constant term normalised to one, this gives
$$
G(x,y)\;=\;\prod_{k=1}^{n}\bigl(1 + w(x+y)\bigr)\;=\;\bigl(1+w\,s\bigr)^{n},\qquad s=x+y.\tag{13.1}
$$
The expansion in $s$ is the Maclaurin binomial:
$$
(1+ws)^n=\sum_{k\ge0}\binom{n}{k}w^k\,s^k .
$$

## From the generating function to the counts

The count $N_{ij}$ — the coefficient of $x^i y^j$ — is extracted from the coefficient $Q_k$ of $s^k$ by distributing the exponents between $x$ and $y$:
$$
N_{ij}\;=\;Q_{i+j}\cdot\binom{i+j}{i},\qquad Q_k=\binom{n}{k}w^k .
$$

The factor $\binom{i+j}{i}$ is the number of ways to scatter $i+j$ chosen primes over $i$ lower and $j$ upper positions; this is exactly the "choice-within-choice" identity that will become the core of the Lean proof below. Substituting the corners of the rectangle $\{0,3\}\times\{0,3\}$, we obtain
$$
\begin{aligned}
N_{00}&=Q_0\binom{0}{0}=1,\\
N_{03}=N_{30}&=Q_3\binom{3}{0}=\binom{n}{3}w^3,\\
N_{33}&=Q_6\binom{6}{3}=20\,\binom{n}{6}\,w^6,
\end{aligned}
$$

where $\binom{6}{3}=20$ is the very constant that in [12](12_FourCorner.md) we denoted $R_{\mathrm{CRT}}=20\,e_6/e_3^2$. The four-corner $N_{00}N_{33}\le N_{03}N_{30}$ becomes
$$
1\cdot\bigl(20\,\tbinom{n}{6}w^6\bigr)\;\le\;\bigl(\tbinom{n}{3}w^3\bigr)^2,
$$
and after cancelling $w^6$ — a purely binomial inequality:
$$
\boxed{\,20\,\binom{n}{6}\le\binom{n}{3}^2\,.}\tag{13.2}
$$

## The binomial four-corner: `four_corner_binom`

**Definition 13.1** (model four-corner). By the model four-corner we mean the inequality
$$
20\,\binom{n}{6}\le\binom{n}{3}^2\qquad\text{for all }n\in\mathbb N,
$$
understood over $\mathbb N$ (for $n<6$ the left-hand side is trivially zero).

**Theorem 13.2** (`four_corner_binom`). 🟢 For all $n\in\mathbb N$, $20\,\binom{n}{6}\le\binom{n}{3}^2$.
```
theorem four_corner_binom (n : ℕ) : 20 * n.choose 6 ≤ (n.choose 3) ^ 2
```

The proof is elementary and rests on the **"choice-within-choice" identity**. In Mathlib this is `Nat.choose_mul`:
$$
\binom{n}{6}\binom{6}{3}=\binom{n}{3}\binom{n-3}{3}.\tag{13.3}
$$
On the left we choose $6$ primes out of $n$, then $3$ of those six (for the upper side); on the right, we choose $3$ out of $n$ straight away, then $3$ more out of the remaining $n-3$. Both ways count the same thing — an ordered pair of disjoint triples — hence they are equal. Substituting $\binom{6}{3}=20$ (`decide` in Lean) and $6-3=3$, we obtain
$$
20\,\binom{n}{6}=\binom{n}{3}\binom{n-3}{3}.
$$

What remains is the **monotonicity** of the binomial coefficient in its upper argument, `Nat.choose_le_choose`:
$$
\binom{n-3}{3}\le\binom{n}{3}\quad(\text{since }n-3\le n),
$$
whence
$$
20\,\binom{n}{6}=\binom{n}{3}\binom{n-3}{3}\le\binom{n}{3}\binom{n}{3}=\binom{n}{3}^2.
$$
In Lean the step `_ ≤ _` is closed by the tactic `gcongr` (monotonicity of multiplication), the final equalities by `ring`.

> **Note.** What this inequality *means*. The corners $N_{00}$ and $N_{33}$ (both ranks minimal / both maximal) cannot together outweigh the mixed corners $N_{03},N_{30}$. This is precisely **negative association** of the ranks: high divisibility of one side repels high divisibility of the other. The cause is exclusivity: a triple of divisors "occupied" by the upper side is unavailable to the lower one, which is exactly what the transition $\binom{n}{3}\to\binom{n-3}{3}$ expresses (the second side has three fewer candidates). We assumed nothing about *how often* primes divide the sides — only that they divide them mutually exclusively.

## The model four-corner in the original coordinates: `model_four_corner`

So as not to lose contact with the rank counts (in which the weight $w$ remains), the same inequality is also proven before the cancellation of $w^6$, as `model_four_corner`.

**Theorem 13.3** (`model_four_corner`). 🟢 For all $n,w\in\mathbb N$, $1\cdot\bigl(20\,\binom{n}{6}w^6\bigr)\le\bigl(\binom{n}{3}w^3\bigr)\bigl(\binom{n}{3}w^3\bigr)$.
```
theorem model_four_corner (n w : ℕ) :
    1 * (20 * n.choose 6 * w ^ 6) ≤ (n.choose 3 * w ^ 3) * (n.choose 3 * w ^ 3)
```
Here the left-hand side is $N_{00}\cdot N_{33}$, the right-hand side $N_{03}\cdot N_{30}$, literally in the form of the model counts. The proof is a direct consequence of Theorem 13.2 (`four_corner_binom`): we multiply the inequality $20\binom{n}{6}\le\binom{n}{3}^2$ by $w^6\ge0$ (again `gcongr`) and regroup the factors (`ring`).

**Conclusion.** Substantively, this confirms that the weight $w$ is a common positive factor which does not affect the *direction* of the four-corner; the sign is carried exclusively by the binomial part.

## Strict positivity and the unreachable singularity: `four_corner_binom_strict`

The inequality $20\binom{n}{6}\le\binom{n}{3}^2$ is non-strict, and equality is indeed attained — but only in the degenerate cases $n\le6$, where the left-hand side vanishes. The substantive question is whether the inequality is strict on a *non-trivial* layer, where the ranks can genuinely reach three on both sides, that is, for $n\ge7$. The answer is yes — `four_corner_binom_strict`.

**Theorem 13.4** (`four_corner_binom_strict`). 🟢 For $7\le n$ the strict inequality $20\,\binom{n}{6}<\binom{n}{3}^2$ holds.
```
theorem four_corner_binom_strict {n : ℕ} (hn : 7 ≤ n) :
    20 * n.choose 6 < (n.choose 3) ^ 2
```

The proof strengthens the monotonicity to a *strict inequality* via Pascal's identity `Nat.choose_succ_succ`:
$$
\binom{n}{3}=\binom{n-1}{2}+\binom{n-1}{3}.
$$

For $n\ge7$ we have $\binom{n-1}{2}>0$ (`Nat.choose_pos`), so together with the monotonicity $\binom{n-3}{3}\le\binom{n-1}{3}$ we obtain
$$
\binom{n-3}{3}\le\binom{n-1}{3}<\binom{n-1}{2}+\binom{n-1}{3}=\binom{n}{3}.
$$
Since $\binom{n}{3}>0$ for $n\ge7$, multiplying the strict inequality $\binom{n-3}{3}<\binom{n}{3}$ by $\binom{n}{3}$ (`mul_lt_mul_of_pos_left`) gives
$$
20\,\binom{n}{6}=\binom{n}{3}\binom{n-3}{3}<\binom{n}{3}^2 .
$$

> **Note (the unreachable singularity).** Denote the deficit $D=\binom{n}{3}^2-20\binom{n}{6}\ge0$. Equality $D=0$ would mean exact equilibrium $N_{00}N_{33}=N_{03}N_{30}$ — rank *independence* of the sides, in engine terms an "idle run". The strictness of `four_corner_binom_strict` says: as soon as the layer is non-trivial ($n\ge7$), the system cannot settle on this singularity — $D>0$ is forced. And this is exactly the strict positivity which in [12](12_FourCorner.md) yields not merely $N_{33}\le N_{00}$ but the strict $N_{33}<N_{00}$, and hence a guaranteed survivor.

## What is proven, and what is not

Let us take honest stock. We have proven — machine-checked, elementary, distribution-free — that in the **equilibrium symmetric exclusive model** (the product of factors $1+w(x+y)$) the four-corner inequality holds always (`four_corner_binom`, `model_four_corner`) and strictly on non-trivial layers (`four_corner_binom_strict`). The sign is forced by a single structural cause — the absence of the $xy$ term, that is, the exclusivity of two; neither the density of primes, nor a sieve, nor parity entered anywhere.

> **Conjecture (model $\to$ reality).** The real CRT rank counts coincide with the model product $\prod_p(1+w_p(x+y))$ *up to a remainder that does not flip the sign of the four-corner*. The plan for closing it: write out the real factors $G_p$ by CRT, show their $\pm$-symmetry and exclusivity at each $p$ (the first from the mirror symmetry $m\mapsto-m$, the second is the already-proven `no_large_shared_divisor`), and estimate the accumulated remainder of the product. This is not a repackaging of the conjecture: the direction $R_{\mathrm{fc}}\le1$ is already observed numerically on all blocks; only the control of the remainder remains open.

The model layer is the fractal "skeleton": a self-similar product yielding the exact binomial combinatorics of the corners. Reality differs from the skeleton by a remainder $e_{ij}$, and its exact decomposition is precisely the subject of the next chapter [14 RealFourCorner]: the real counts decompose as *model plus remainder*, the four-corner for reality reduces to the remainder not flipping the sign of the model one — and it is where the remainder swells against a melting gap that the line first runs into parity.



<!--navbot-->

---

[← 12. Four-corner](12_FourCorner.md) · [Table of contents](00_Overview.md) · [14. Remainder decomposition →](14_RealFourCorner.md)
<!--/navbot-->
