# 16. By contradiction: finite and H yield False

<!--navtop-->
[← 15. The chain to the twins](15_ToTwins.md) · [Table of contents](00_Overview.md) · [17. The payment law →](17_PaymentLedger.md)
<!--/navtop-->



In chapter [15 ToTwins](15_ToTwins.md) we assembled the direct chain: from the real four-corner at all scales follows `TwinLowers.Infinite` — the infinitude of twins. Now we look at the same construction from the opposite side: assume the contrary — that the twins are *finite* — and show that together with the four-corner input this leads to `False`. This is not a new theorem but the *contraposition* of the whole programme, and its value lies in localizing, with mathematical precision, the single open node.

> Machine-checked: `Engine/FiniteContradiction.lean` (`twin_finite_contradiction`, no `sorry`, standard axioms only).

## The setup by contradiction

Let us introduce the object whose finiteness is precisely the hypothesis being denied. Let `TwinLowers` be the set of lower members of twin pairs, that is, the set of those $n$ for which both numbers $n$ and $n+2$ are prime (in the engine's terms — the centres $m$ with both sides $6m\pm 1$ prime). The twin-infinitude hypothesis is exactly the statement `TwinLowers.Infinite`. Its negation is written as

$$
\neg\,\mathtt{TwinLowers.Infinite},
$$

which for sets is equivalent to `TwinLowers.Finite`. Substantively this means: there exists a last twin centre $M_0$ beyond which *every* centre $m > M_0$ is bad — at least one of the sides $6m\pm 1$ is composite.

The second ingredient is the open input. In the file it is introduced as an abbreviation coinciding verbatim with the premise of `twin_primes_of_four_corner` from the previous chapter:

**Definition 16.1** (the open input of the programme). The abbreviation `FourCornerInput`: for every scale $N$ there exist finite sets $R_{00}, R_{03}, R_{30}, R_{33},\ \mathrm{carrier},\ \mathrm{bad}$ satisfying

$$
0 < |R_{00}|,\qquad
|R_{00}|\cdot|R_{33}| \;<\; |R_{03}|\cdot|R_{30}| \;\le\; |R_{00}|^2, \tag{16.1}
$$

$$
|\mathrm{carrier}| = |R_{00}|,\qquad |\mathrm{bad}| = |R_{33}|, \tag{16.2}
$$

$$
(\forall m\in\mathrm{carrier})\; N < m,\qquad
(\forall m\in\mathrm{carrier})\; m\notin\mathrm{bad}\ \Rightarrow\ \mathtt{IsTwinCenter}\ m. \tag{16.3}
$$

The first inequality $|R_{00}|\cdot|R_{33}| < |R_{03}|\cdot|R_{30}|$ is the strict *real* four-corner on the genuine rank counts; the second, $|R_{03}|\cdot|R_{30}| \le |R_{00}|^2$, is the easy side-corner. Together, as shown in [15 ToTwins](15_ToTwins.md) via `N33_lt_N00_of_four_corner`, they yield $|R_{33}| < |R_{00}|$ — the bad centres in the block are strictly fewer than the carrier slots — hence at least one survivor, and that survivor is a twin.

## The contradiction theorem

The contradiction proper is stated in a single line.

**Theorem 16.2** (`twin_finite_contradiction`). If $\neg\,\mathtt{TwinLowers.Infinite}$ (the twins are finite) and `FourCornerInput` `H` holds, then `False`.

The proof is transparent: from `H` the direct chain of the previous chapter (`twin_primes_of_four_corner`) produces `TwinLowers.Infinite`; applying the finiteness hypothesis `hfin` to it, we obtain `False`. In Lean this is literally `hfin (twin_primes_of_four_corner H)` — finiteness is a function "from infinitude into the void", and we feed it exactly the infinitude that the four-corner manufactures.

The same fact is restated through explicit finiteness of the set:

**Theorem 16.3** (`twin_finite_contradiction_of_finite`). If `TwinLowers.Finite` and `FourCornerInput` `H`, then `False`.

The only difference is the passage `Set.not_infinite.mpr`, which removes the gap between `Finite` and `¬ Infinite`; substantively it is the same theorem, written so as to be convenient wherever finiteness is given as `Finite` rather than as a negation.

Finally, the contraposition is extracted in pure form:

**Theorem 16.4** (`twin_infinite_of_fourCorner`). From `FourCornerInput` `H` follows `TwinLowers.Infinite`.

This is identical to `twin_primes_of_four_corner H` — we merely give the conclusion a name that underlines its logical role: `H` *refutes* finiteness. The three theorems (16.2, 16.3, 16.4) are one and the same statement in three grammatical voices (contradiction, contradiction-via-`Finite`, direct derivation), and the presence of all three in the file is not redundancy but a map of how one implication plugs into different contexts of a proof.

> **Note.** Logically, contraposition adds nothing: $(\neg P \wedge H \to \bot)$ and $(H \to P)$ are equivalent. The value of the "by contradiction" form is methodological: it makes *tangible* exactly what breaks when the thesis is denied. If the twins are finite, the engine must process the entire infinite tail $(M_0,\infty)$ so that the bad centres cover it completely, leaving not a single survivor. `H` asserts the opposite — that at every scale a survivor exists. The two cannot be reconciled, and this irreconcilability is precisely `False`.

## Why every route runs into the same wall

It is natural to ask: does reasoning by contradiction supply a new lever — perhaps denying the thesis opens a way around the open node? Independent reconnaissance through three lenses — counting, EPMI, four-corner — returned a single answer: *no route bypasses the wall*; all of them reduce to the strict real four-corner together with a lower bound on the carrier. Let us tabulate the observation.

| Route | Where the open part lives | Why this is a red line |
|---|---|---|
| **Counting** (union bound over primes) | $2\!\sum_{A<p\le\sqrt X} 1/p < \text{density}$ | By Mertens $\sum 1/p \to \infty$, so the union bound *never* beats the carrier; the fix goes only through Brun's inclusion–exclusion, and its main term $\prod(1-2/p)\cdot|\Omega|$ together with remainder control on a real interval is Bombieri–Vinogradov, i.e. the distribution of primes. |
| **EPMI** (infinite descent) | "manufacture a total descent chain $H:\mathbb N\to\mathbb N$" | Inverts the burden: to apply `no_infinite_descent` one needs a *perpetual* descent chain, and "the covering is total" is exactly what must be refuted, not assumed. An orphan branch, resting on nothing on the live line. |
| **Four-corner** (this file) | the conjunct "strict real four-corner" in `H` | The model$\to$reality transfer (`real_four_corner_of_remainder`): the harness `tools/RESULTS_remainder.md` shows the remainder is $\sim 4\times$ the model while the model's gap melts away — the model four-corner does *not* transfer distribution-free. This is parity. |

The reconnaissance verdict, verbatim: «No route escapes the four-corner/carrier/parity wall; all three reduce to it. The machine-checked links are all distribution-FREE and red-line-clean; distribution is quarantined entirely inside `H`.» Three different starting points — counting primes, infinite descent, the four-corner — converge on a single point, and that convergence is itself evidence: the wall is structural, not an artifact of one choice of route.

> **Note.** The convergence of the three routes has a geometric image. The real four-corner holds as long as the *margin* — the gap $|R_{03}|\cdot|R_{30}| - |R_{00}|\cdot|R_{33}|$, normalized by the block's scale — stays positive. Numerically the margin creeps *toward zero*: it is a knife-edge. And it melts not for an accidental reason, but because the remainder $e_{ij}$ of the real counts relative to the CRT model [14 RealFourCorner](14_RealFourCorner.md) carries the same sign structure that, in the sieve, is sensitive to the parity of the number of prime factors. In other words, margin$\to 0$ is not "almost there" but a manifestation of the parity problem: distribution-free methods are in principle blind to the sign on which the four-corner's advantage depends.

## What is honestly proven — and what is not

Let us draw the line strictly. What is proven is the **conditional theorem** (Theorem 16.2) `finite ∧ H ⟹ False` — machine-checked, without `sorry`, on the standard axioms. It is a correctly assembled contradiction, complete at the level of the model: every link of the glue (16.4)

$$
\texttt{N33_lt_N00_of_four_corner}\ \to\ \texttt{survivor\_of\_not\_covered}\ \to\ \texttt{twin\_prime\_conjecture\_of\_blocks}\ \to\ \texttt{infinite\_of\_unbounded\_centers} \tag{16.4}
$$

is verified and distribution-free. What remains open is *exactly* `H` (Definition 16.1), and inside `H` the only substantively open conjunct is the strict real four-corner (= parity + the model$\to$reality transfer) together with the lower bound on the carrier (= density). The model side (`four_corner_binom_strict`, `model_four_corner`) is already proven unconditionally; what fails to transfer is precisely the step from model to reality.

> **Conjecture** (open node). `FourCornerInput` `H` is true: at arbitrarily large scales the real rank counts yield a strict four-corner. **Closure plan:** control of the remainder $e_{ij}$ on the genuine interval, precise enough to keep the sign of the margin positive. From the ideas at hand this does *not* follow distribution-free — as confirmed numerically as well (margin$\to 0$, remainder $\sim 4\times$ the model). The honest status: `H` is a typed hypothesis, NOT a proven fact, and nowhere do we pass the reduction to it off as a proof of the thesis itself.

## Summary and a bridge to the next chapter

Reasoning by contradiction supplies no new lever: it re-encodes the same wall — "the union bound covers the interval" and "the remainder flips the four-corner" are one and the same parity/sieve-remainder obstruction. But it does supply a clean verified artifact: the finiteness of twins is *contradictory modulo `H`*, and `H` is the single, precisely localized, open input of the entire programme.

The natural next question: if the engine is nonetheless forced to halt at a bad centre — what does that cost it? Denying the thesis demands that the whole tail $(M_0,\infty)$ be covered by bad centres, that is, that the engine "pay" at the boundary infinitely often. In chapter [17 the payment law] we shall pass from the logic of the contradiction to its *algebra*: we shall show that boundary death is not free, that the payment is spread across the small primes and obeys a strict defect law — and we shall see the same parity wall show through from a new, more arithmetic angle.

<!--navbot-->

---

[← 15. The chain to the twins](15_ToTwins.md) · [Table of contents](00_Overview.md) · [17. The payment law →](17_PaymentLedger.md)
<!--/navbot-->
