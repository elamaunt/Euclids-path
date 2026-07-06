# Cubic squeeze: a short train

<!--navtop-->
[← 06. No way back](06_NoBackward.md) · [Table of contents](00_Overview.md) · [08. Bounded cycle →](08_BK.md)
<!--/navtop-->



> Lean: `EuclidsPath/Engine/Squeeze.lean` (`cubic_squeeze`, `cubic_squeeze_sq_lt`).

## Where we are

In the previous chapter we established irreversibility at two points: the diagonal $\sum_p X_p Y_p$ vanishes, one and the same prime does not sit on both sides, and Euclid's engine does not run backwards ([06 NoBackward](06_NoBackward.md)). Irreversibility forbids *going back*.

But there remains the question of *how far the forward run reaches*: when the engine, descending, produces a repeated atom and tries to lay it out along a single affine line of indices — how far does this "train" of actually reachable centres extend? In this chapter we show that, despite the infinity of the line itself, its *valid segment* is short: it is squeezed by a cubic bond between the atom's height and the active scale.

## Setting: the atom, its repetition, and the line of indices

Let us recall the engine's coordinates. We denote the active threshold by $A$: this is the scale separating the "old" small primes $p \le A$ from the "new" large factors $>A$ taking part in the rank decomposition of the sides $6m \pm 1$ ([04 Descent](04_Descent.md)); recall that the rank is the "height" of a state, strictly dropping along permitted steps (see the [glossary](GLOSSARY.md)). When a descended centre structurally reproduces the same Euclidean equation at a smaller scale, a *repeated atom* arises — the self-similar step from the catalogue of §23.

Let us introduce the **atom height** $h \in \mathbb{N}$ — an integer parameter measuring how deep the repetition of one and the same factor stretches along the affine line of indices $n \mapsto N_0 + q\,n$. The line is infinite: formally, the index $n$ ranges over all natural numbers, and the fuel $+1$ (the index step) never runs out. That is precisely why it naively seems that the train of repetitions could be arbitrarily long.

The observation we formalise says the opposite. The cost of a repetition grows not linearly but **cubically** in $h$, while the budget is bounded by the active scale $A$. Hence — a hard ceiling on $h$.

> **Note.** The word "train" here is not a railway metaphor for the sake of imagery but the exact name of the object: the sequence of actually reachable centres along a single affine line. The infinity of the line (the carrier of indices) and the finiteness of its valid segment (the train) are different things, and the entire content of the chapter is to keep them apart.

## Defining the cost of a repetition

By the catalogue of §23, the cost of repeating an atom of height $h$ at active scale $A$ is subject to the *cubic threshold*

$$
h\,(1 + 6h) < \frac{A}{12}.
$$

Expanding the brackets and passing to the honest integer form (with no root extraction, so as to stay in $\mathbb{N}$ and lose no rounding rigour), we obtain the input hypothesis

$$
12\,\bigl(h + 6h^2\bigr) < A.
\tag{7.1}
$$

The left-hand side $12h + 72h^2$ is the exact integer record of the repetition's "energy": the linear term $12h$ accounts for the step along the line, the quadratic term $72h^2$ — for the self-similar doubling of scale at each level of nesting.

It is natural to expect (and below we prove it) that the quadratic term dominates, and hence the validity of the repetition is governed by the root $\sqrt{A}$, not by $A$ itself.

## Theorem: the cubic squeeze

**Theorem 7.1** (`cubic_squeeze`). Let $A, h \in \mathbb{N}$ and suppose $(7.1)$ holds, that is, $12(h + 6h^2) < A$. Then

$$
72\,h^2 < A.
\tag{7.2}
$$

*What is proved.* From the full cost $12h + 72h^2 < A$ we discard the non-negative linear term $12h \ge 0$, and what remains is the bound on the pure quadratic contribution. In Lean this is a single line of `omega`: linear arithmetic over the atom $h^2$, taken as a variable in its own right. There is no rounding, no root is extracted — the conclusion stays an integer inequality.

*Why this is true.* The key is that $12(h + 6h^2) = 12h + 72h^2$ and both summands are non-negative. The strict inequality $(7.1)$ is only strengthened by removing one of the positive summands on the left: $72h^2 \le 12h + 72h^2 < A$. This is exactly why the proof is elementary — all the work is done by expanding the brackets, and `omega` merely closes the trivial linear arithmetic.

*What it means.* The inequality $(7.2)$ is equivalent (in the real-valued interpretation) to the bound

$$
h < \sqrt{\frac{A}{72}}.
\tag{7.3}
$$

The height of the repetition cannot exceed $\sqrt{A/72}$.

**Conclusion.** The valid segment of the train has length of order $\sqrt{A}$, not $A$ and certainly not $\infty$. The affine line of indices is infinite, but the stretch of it the engine can actually traverse is compressed to the square root of the active scale. This is the *cubic squeeze* — the cubic cost squeezes the quadratic result into a square root.

> **Note.** We deliberately work in the integers and with $(7.2)$, not with $(7.3)$. The real-valued form with the root is only an interpretation; the load-bearing statement, the one the compiler checks, is the integer one. No appeal to irrationalities and no hidden rounding enters the proof.

## Corollary: the repetition is even shorter

**Theorem 7.2** (`cubic_squeeze_sq_lt`). Under the same input $(7.1)$ we have

$$
h^2 < A, \qquad\text{and a fortiori}\qquad h < A.
\tag{7.4}
$$

*Discussion.* This is a direct weakening of the squeeze of Theorem 7.1: from $(7.2)$ and $h^2 \le 72h^2$ we get $h^2 < A$; in Lean — `have := cubic_squeeze hsq; omega`. The formulation $h^2 < A$ is more convenient for the gluings that follow, since it removes the numeric factor $72$ and gives the clean bound "the square of the height is less than the scale". Substantively it says the same thing: the atom's repetition is *extremely short* relative to $A$.

## What it means for the framework: self-similarity and scale compression

The squeeze $(7.3)$ is the quantitative form of the engine's self-similarity. Each level of repetition doubles the scale through the quadratic term $72h^2$, so the number of levels fitting into the budget $A$ is root-logarithmic, not linear. In the geometry of the fractal layer [13](13_FractalLayer.md) this manifests as the scale compression $P \to P^{1/3}$: the cubic cost of repetition turns one step along the line into a cube root in the parameter, and the repeated atom turns out to be "extremely short".

The connection with the overall picture is direct. The fuel $+1$ (the index step along the line) is indeed infinite, but this does not grant the engine an infinite run: the valid segment is squeezed. This is one more facet of the asymmetry recorded in the law of irreversibility ([05 Irreversibility](05_Irreversibility.md)): upwards the line stretches without bound, but downwards — through the actually reachable centres — the engine covers only a short stretch of $O(\sqrt{A})$. The infinity of the carrier and the finiteness of the useful run are a matched pair, just like "time is not reversible / always halts".

> **Note.** There is no reduction of the twin conjecture to anything here — this is an atomic, fully verified lemma about the geometry of repetition. Theorem 7.1 (`cubic_squeeze`) and Theorem 7.2 (`cubic_squeeze_sq_lt`) compile cleanly; `#print axioms` shows only the standard `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` and no forbidden axioms. We do not pass this squeeze off as a proof of anything larger: it merely bounds the length of a single train. There are no open nodes inside the lemma itself.

## Bridge to the next chapter

So, along *one* affine line the repetition is short: at most $\sqrt{A/72}$ centres. But the engine produces not one line but a whole fan of such lines, and it is natural to ask: what happens when the repetitions and the lines become *many* — does a nontrivial coincidence not arise from symmetric sums over this fan? The answer is given by the next chapter: pigeonhole — the boxes principle (see the [glossary](GLOSSARY.md)) — on symmetric sums forces a *bounded additive cycle* ([08 BK](08_BK.md), `exists_additive_cycle`).

The short train bounds the length of each repetition; the bounded cycle will bound their mutual coordination — and together they close off the possibility of perpetual clean-recycling.

<!--navbot-->

---

[← 06. No way back](06_NoBackward.md) · [Table of contents](00_Overview.md) · [08. Bounded cycle →](08_BK.md)
<!--/navbot-->
