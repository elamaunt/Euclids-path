# The first law: conservation of two

<!--navtop-->
[← 02. Carrier of two](02_Carrier.md) · [Table of contents](00_Overview.md) · [04. Descent and the boundary-law →](04_Descent.md)
<!--/navtop-->



> Lean source: `EuclidsPath/Engine/TwoGap.lean`. Every statement of this chapter is elementary ring algebra over `ℤ` and `ℕ` (`ring`, `linear_combination`, `omega`, `mul_left_cancel₀`); no analysis, no distribution results, no sieve.

In the previous chapter (02, the carrier) we established that two is what *separates* the sides of a twin: any common divisor of `6m−1` and `6m+1` divides their difference, hence `\gcd(6m-1,6m+1)\mid 2`. There, the two acted as a barrier of exclusivity.

Here we turn our gaze: this same two is not only the difference of two numbers at a single point, but also an *invariant carried along the descent*. We shall show that in every coordinate system in which Euclid's engine — recall, the programme's central forbidden object, an infinite strictly descending chain (see the [glossary](GLOSSARY.md)) — describes the motion of the centre, one and the same identity recurs — a determinant of the form `XY-ZW=2`. This is the programme's first law: **conservation of two**.

## The setting: what exactly is conserved

Recall the centre form. Every twin is given by a centre `m` so that the sides are `6m-1` and `6m+1`. The difference of the sides is identically two:
$$(6m+1)-(6m-1)=2.$$

As arithmetic of numbers, this is trivial. What is non-trivial is that upon passing to *multiplicative* coordinates — when one or both sides are decomposed into products of active primes of the layer `(A,A^2]` — this two does not vanish and does not blur, but emerges as the **determinant** of the linear system linking the factors. It is precisely the determinant form that makes the two rigid: a determinant cannot be "nudged slightly" — it either equals `2`, or there is no solution.

We shall call the *first law* the collection of identities of `TwoGap.lean`, each of which asserts: in its own pair of coordinates, the difference of two "diagonal products" equals a fixed constant, a multiple of two. Formally, in all forms this is `XY-ZW=2K`, where the base case `K=1` gives exactly `XY-ZW=2`.

> **Note.** The term "law" is used here in the physical sense of a conserved quantity, not in the sense of a logical axiom. The two plays the role of a charge that the engine carries without loss; the subsequent chapters (04, descent, and then the second law of irreversibility) will add to this charge the *direction* of its motion.

## The determinant law of rank-(3,3)

We begin with the most direct form — the "bad cell" `N_{33}`, where both sides of the twin are composite and each decomposes into a product of three factors.

**Definition 3.1** (rank-(3,3) centre). A centre `m` is called rank-(3,3) if there exist naturals `a\le b\le v` and `q\le r\le s` such that
$$6m-1=abv,\qquad 6m+1=qrs.\tag{3.1}$$

Here the rank `(3,3)` records that the *left* side is a product of three atoms and the *right* side of three as well. From this decomposition an exact Diophantine constraint follows immediately.

**Theorem 3.2** (`det_law_rank33`). Let `1\le m`, `6m-1=abv` and `6m+1=qrs`. Then
$$q r s = a b v + 2.\tag{3.2}$$

*What is proven.* The two multiplicative decompositions are forcibly linked additively: the product of the right side's factors exceeds the product of the left side's factors by exactly two. In Lean the proof is a single line of `omega`: the system `6m-1=abv`, `6m+1=qrs` over the naturals (with the condition `1\le m` removing the ambiguity of the subtraction `6m-1` in `ℕ`) linearly entails `qrs=abv+2`.

*Why this is true.* The difference `qrs-abv` equals the difference of the sides `(6m+1)-(6m-1)=2` — but now this two is expressed *through the factors*, not through `m`. We have "forgotten" the centre `m` and kept only the multiplicative record; the two survived and became a bond between the two products.

*What it means.* The equation `qrs=abv+2` is the first manifestation of rigidity. It means the six factors `a,b,v,q,r,s` cannot be chosen independently: once five are fixed, the sixth is determined (or absent) by the equation on the two. It is precisely this reserve of rigidity that the subsequent chapters trade for upper bounds on the number of rank-(3,3) centres.

> **Note.** The reverse passage is substantive too: every admissible solution of `qrs=abv+2` recovers the centre `m=(abv+1)/6=(qrs-1)/6`, provided congruence-admissibility holds (the right residues modulo 6, so that `abv+1` is divisible by 6). Thus the equation on the two becomes the *defining* equation of the cell `N_{33}`, not merely its consequence.

## The abstract form: `Cb − Dr = −2`

A triple product is inconvenient for linear algebra. Let us fold one factor from each side into "product variables" and obtain a bilinear form in which the two becomes a literal `2\times 2` determinant.

**Definition 3.3** (product coordinates). For a rank-(3,3) centre set `C=av`, `D=qs`. Then the sides are written as `Cb=6m-1` and `Dr=6m+1`, where `b` and `r` are the remaining "free" factors.

**Theorem 3.4** (`det_law_CD`). Over `ℤ`: if `Cb=6m-1` and `Dr=6m+1`, then
$$C b - D r = -2.\tag{3.3}$$

*What is proven.* Subtract the second equality from the first: `Cb-Dr=(6m-1)-(6m+1)=-2`. In Lean — `linear_combination h1 - h2`, exactly this linear combination of the two hypotheses.

*Why this is true, and what it means.* Write the system in matrix form. The rows `(C,\,-D)` and the vector `(b,\,r)^{\top}` give `Cb-Dr`; the sign `-2` is the oriented determinant, carried down onto the diagonal.

The key consequence is reduction modulo the modulus. When `\gcd(C,D)=1`,
$$C b - D r = -2 \;\Longrightarrow\; b \equiv -2\,\overline{C} \pmod{D},\tag{3.4}$$
where `\overline{C}` is the residue inverse to `C` modulo `D`. That is, the free factor `b` is not arbitrary: it lies in *one* residue class modulo `D=qs`.

**Conclusion.** This is exactly the "zero-one slot" on which all upper bounds for the counting part rest: if `b` is forced into an interval `(A,A^2]` of length smaller than the modulus `D`, then in a fixed box `(a,v,q,s)` *at most one* value of `b` is admissible. The two, having moved to the right-hand side of the congruence, governs the density of solutions.

> **Note.** Here the motif of the whole programme is visible: we do *not* solve `Cb-Dr=-2` explicitly and do *not* estimate the number of its solutions by a distributional argument. We merely record the *algebraic rigidity* (uniqueness of the residue class). The passage from rigidity to *counting* centres is a separate, analytically heavy step, and nowhere do we pass one off as the other.

## Determinant collapse: carrying the two along a ray

The two preceding forms describe the two at a *single* point. The first law, however, is about *conservation under motion*. Consider two points of one descent "ray" and show that the two is carried from point to point in a controlled way.

**Definition 3.5** (a ray and its step). By a ray we mean a family of points with common `v,s`, where the i-th point satisfies the rank-one equation `u_i v+2=r_i s`, and the transition between two points is given by an integer step `K`:
$$u_2-u_1=sK.$$

**Theorem 3.6** (`det_collapse`). Let `u_1 v+2=r_1 s`, `u_2 v+2=r_2 s`, the step `u_2-u_1=sK` and `s\ne 0`. Then
$$u_2 r_1 - u_1 r_2 = 2K.\tag{3.5}$$

*What is proven.* The determinant assembled from the coordinates of two points of the ray equals `2K` — that is, the two accumulated over `K` steps. For `K=1` (adjacent points) this is again `u_2r_1-u_1r_2=2`.

*Why this is true.* Multiply the target expression by `s` and substitute both rank-one equations:
$$s\,(u_2 r_1 - u_1 r_2) = u_2(r_1 s) - u_1(r_2 s) = u_2(u_1 v+2) - u_1(u_2 v+2) = 2(u_2-u_1) = 2sK.$$
The terms with `v` cancel (`u_2 u_1 v - u_1 u_2 v=0`) — this is where the two "survives": everything that depends on the scale `v` is quenched, and what remains is the pure transport of the two. Then we cancel by `s\ne 0`.

In Lean it goes exactly so: the identity `s\cdot(u_2r_1-u_1r_2)=u_2(r_1s)-u_1(r_2s)` is closed by `ring`, substituting the hypotheses reduces the right-hand side to `2\cdot(u_2-u_1)`, and `linear_combination 2*hK` yields `2sK`; the final `mul_left_cancel₀ hs` strips the factor `s`.

*What it means.* The name *collapse* is exact: the quantities `u_i,r_i` may grow along the ray, but their "cross determinant" collapses to a function strictly linear in `K` with coefficient `2`. The two is the lattice step along which the engine moves. Hence the link with the next chapter: descent is a transition of `K=1` per step, and each such step carries exactly one two.

## The exact Euclidean identity of descent: `qΔ − vΞ = 2`

The three forms above are linear and bilinear. Descent, by its nature, is *quadratic*: Euclidean division compares a side with the square of the scale. The next identity is the diagonal kernel of self-similarity, thanks to which descent reproduces itself at a smaller scale.

**Definition 3.7** (Euclidean decomposition of a step). Suppose the rank-one equation `abv+2=qP` holds. Decompose `P` and `ab` with respect to the scale `v`:
$$P=v^{2}+\Delta,\qquad ab=qv+\Xi,$$
where `\Delta` is the remainder of `P` relative to the square `v^2`, and `\Xi` is the remainder of `ab` relative to `qv`. The quantities `\Delta,\Xi` are the "Euclidean remainders" of the step.

**Theorem 3.8** (`euclid_descent_identity`). Given `abv+2=qP`, `P=v^{2}+\Delta`, `ab=qv+\Xi`:
$$q\,\Delta - v\,\Xi = 2.\tag{3.6}$$

*What is proven.* The two standing in the rank-one equation is fully expressed through the Euclidean remainders `\Delta,\Xi` and the "diagonal" coefficients `q,v`. In Lean — `linear_combination -h1 - q*h2 + v*h3`: substituting both decompositions into the rank-one equation and collecting like terms yields exactly `q\Delta-v\Xi=2`.

*Why this is true.* Expand `qP=q(v^2+\Delta)=qv^2+q\Delta` and `abv=(qv+\Xi)v=qv^2+\Xi v`. Then
$$abv+2=qP \iff (qv^{2}+\Xi v)+2 = qv^{2}+q\Delta,$$
and `qv^2` cancels on both sides — once again everything carrying the main scale is quenched, and what remains is `\Xi v+2=q\Delta`, that is `q\Delta-v\Xi=2`.

*What it means.* This identity is the **diagonal kernel of self-similar descent**. It says that after one Euclidean step the two is reproduced on the pair of remainders `(\Delta,\Xi)`, which are themselves smaller than the original data. That is, descent maps the problem "the two on `(a,b,v,q)`" into the structurally identical problem "the two on `(\ldots,\Delta,\Xi)`" of smaller size. It is precisely this reproducibility that ensures Euclid's engine loses none of its charge as the height decreases — the subject of the next chapter.

> **Note.** It is worth stressing the role of the sign and the constant. In all forms the right-hand side is a *positive* fixed two (or its multiple `2K`, `12h`). In none of them can it turn to zero non-trivially: that would rule out `\gcd\mid 2` from chapter 02 and would mean the sides coincide. The impossibility of annihilating the two is the algebraic forerunner of irreversibility (the second law): the engine does not go backwards precisely because the two does not collapse to zero.

## Small determinant collapse for a repeated atom: `B₂Q₁ − B₁Q₂ = 12h`

The last form covers a degenerate but important case: when one and the same prime atom `a` appears twice and the centres are linked through a common "bridge" `qs`. Here the two is carried not as `2` but as its rescaled shadow `12h` (twelve being `6\cdot 2`, where the six comes from the step `6` of the centre lattice).

**Definition 3.9** (the bridge equation and its shift). Let the repeated atom `a` link two points by the bridge equations
$$a\,B_1=qs\,Q_1-2,\qquad a\,B_2=qs\,Q_2-2,$$
and let the shift along the bridge be a multiple of `6qs`:
$$B_2-B_1=6\,(qs)\,h.$$

**Theorem 3.10** (`small_det_collapse`). Given `a\ne 0`, `qs\ne 0` and the equations above:
$$B_2 Q_1 - B_1 Q_2 = 12\,h.\tag{3.7}$$

*What is proven.* The cross determinant of the points `(B_i,Q_i)` is again linear in the step `h`, with coefficient `12`. The two from the bridge equations and the six from the lattice step have multiplied into `12`.

*Why this is true.* The proof proceeds through two cancellations. First, from the bridge equations and the shift one derives the conjugate shift in `Q`:
$$qs\,(Q_2-Q_1)=qs\cdot 6ah \;\Longrightarrow\; Q_2-Q_1=6ah$$
(cancelling by `qs\ne 0`; in Lean `linear_combination e1 - e2 + a*hsh`, then `mul_left_cancel₀ hqs`). Next, the target determinant, multiplied by `a`, is reduced to `a\cdot 12h`:
$$a\,(B_2 Q_1 - B_1 Q_2) = Q_1(a B_2)-Q_2(a B_1)+2(Q_2-Q_1)=\ldots=a\cdot 12h$$
(the combination `Q1*e2 - Q2*e1 + 2*hQ`), after which we cancel by `a\ne 0`.

*What it means.* Even in the degenerate regime of a repeated atom the first law does not break: the two is conserved, merely dressed up as `12h` by the arithmetic of the step `6`. The conditions `a\ne 0`, `qs\ne 0` are not a technical detail but a substantive requirement that the atom and the bridge be *active*: one may only cancel by non-zero factors, and it is precisely the non-vanishing of the atom `a>A` (from chapter 04) that legitimates the collapse.

## Summary: the unified form of the first law

Gathering the five identities, we see one and the same skeleton in different coordinates:

| Form (Lean) | Coordinates | Identity |
|---|---|---|
| `det_law_rank33` | rank-(3,3) factors | `qrs = abv + 2` |
| `det_law_CD` | product variables `C=av`, `D=qs` | `Cb - Dr = -2` |
| `det_collapse` | two points of a ray, step `K` | `u₂r₁ - u₁r₂ = 2K` |
| `euclid_descent_identity` | Euclidean remainders `Δ,Ξ` | `qΔ - vΞ = 2` |
| `small_det_collapse` | repeated atom, step `h` | `B₂Q₁ - B₁Q₂ = 12h` |

In all forms this is **`XY-ZW=2K`**: the cross determinant of two multiplicative states equals a fixed two (or its multiple along the step). The two is neither created nor destroyed by the engine — it is *carried*. This is the first law in full analogy with a conservation law: the quantity is invariant, and motion merely transfers it from one pair of coordinates to another.

> **Note (what is rigorous here and what is not).** All five theorems are machine-proven, with no `sorry`, by the means of ring arithmetic — this is *pure conservation algebra*, and we do not overrate it. The first law contains **no** counting or distributional statement whatsoever: it does not say how many rank-(3,3) centres exist, and it does not estimate the density of solutions of `Cb-Dr=-2`. It merely records the rigidity that the subsequent, analytically non-trivial chapters will *trade* for bounds. To confuse the conservation of two with the counting of centres would be to pass a reduction off as a proof; we do not do that.

The first law has given us a conserved quantity, but not its direction: the identities `XY-ZW=2K` are symmetric in the sign of `K` and by themselves permit motion both upward and downward.

In the next chapter (04, descent) we add to the conservation of two a **strict drop of height**: if one side of a centre `m\in\Omega_A` is composite and `6m+\sigma=a(6n+\varepsilon)` with an active `a>A`, then `n<m/A`, and carrying the two over to the opposite side `6n-\varepsilon=(6n+\varepsilon)-2\varepsilon` collapses the entire obstruction into a single divisibility (the boundary-law). Thus the first law will turn into a directed step of the engine — and prepare the second law, irreversibility.

<!--navbot-->

---

[← 02. Carrier of two](02_Carrier.md) · [Table of contents](00_Overview.md) · [04. Descent and the boundary-law →](04_Descent.md)
<!--/navbot-->
