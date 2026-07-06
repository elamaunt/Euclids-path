# 26. Separating scale: no ProductHall, by arithmetic

<!--navtop-->
[← 25. Rigid closure](25_RigidClose.md) · [Table of contents](00_Overview.md) · [27. Product-core →](27_ProductCore.md)
<!--/navtop-->



In the previous chapter (25, rigid) we dissected the local fan-in `RigidStep X₁ Y`, `RigidStep X₂ Y` and saw that a collision of two legal lifts of one passport over a common base runs into the node `uniqueLegalLift`: the passport is obliged simultaneously to *distinguish* the two factors (otherwise uniqueness of the lift is false) and *not to distinguish* them (otherwise the `ProductHall` configuration is empty).

This trilemma — coarse yields falsity, fine yields emptiness, tautological yields circularity — was left open.

In the present chapter we go around it honestly: not by strengthening the passport, but by changing the *scale*. We introduce the separating scale and show that under it the node `ProductHall` on the legal layer closes by **pure arithmetic** — no EPMI, no payment, no steering.

> **Note.** Below we carefully separate two levels. At the level of *zone logic* (chapter 25), `ProductHall` was resolved by the branching `uniqueLegalLift`/`steering`, and both ends were hypotheses. At the level of the *arithmetic of scale* (this chapter) we eliminate the very possibility of a collision: we show that under the separating scale the passport map is already injective on the legal region, so the branch "both legal, yet `a₁ ≠ a₂`" is impossible as such. This is not a renaming of the wall — it is its local removal.

## The setup: legal carrier and separating scale

Fix a threshold `A` and work on the legal carrier layer. The active factor is a divisor `a ∣ N` of the carrier `N = 6m + σ`, where $σ ∈ \{-1, +1\}$. The legal restriction on the carrier gives the bound

$$
0 < N \le 6X_A + 1,
$$

where `X_A` is the upper bound on the centre `m` on the layer under consideration. Alongside this we have the primorial $P_A = \prod_{p \le A} p$, which defines the coarse passport of the active factor as the residue $a \bmod P_A$.

> **Definition 26.1** (separating scale). We say the scale is *separating* (a separating scale) if the primorial outruns the carrier bound:
>
> $$
> 6X_A + 1 < P_A . \tag{26.1}
> $$
>
> Put differently — and this is the central definition — it is the condition under which a legal factor is guaranteed to be *smaller* than the passport's modulus.

The intuition: the passport $a \bmod P_A$ is coarse as a map on all natural numbers, but on the legal region it sees the factor in full, provided the factor itself does not reach `P_A`. It is precisely the separating scale that secures `a < P_A`, turning coarse data into exact data *without changing the passport itself*.

## The separating congruence

The first brick is an elementary lemma on the uniqueness of a residue below the modulus.

> **Lemma 26.2** (`eq_of_modEq_of_lt`). Let `a₁ < P`, `a₂ < P` and `a₁ ≡ a₂ [MOD P]`. Then `a₁ = a₂`.

In Lean form:

```
theorem eq_of_modEq_of_lt {P a₁ a₂ : ℕ} (h1 : a₁ < P) (h2 : a₂ < P)
    (hcong : a₁ ≡ a₂ [MOD P]) : a₁ = a₂
```

The proof is exhaustively short: by the definition of `Nat.ModEq`, the congruence `a₁ ≡ a₂ [MOD P]` is an equality of remainders `a₁ % P = a₂ % P`; but with `a₁ < P` we have `a₁ % P = a₁` (`Nat.mod_eq_of_lt`), and likewise for `a₂`, whence `a₁ = a₂`.

Substantively: the difference `a₁ - a₂` is a multiple of `P`, yet in absolute value strictly less than `P`, hence zero. This is a standard fact, and we record it as a lemma in its own right because it is exactly what carries the whole arithmetic meaning of the chapter — *injectivity of the residue on a region where the representatives do not reach the modulus*.

## The bound on a legal lift

The second brick ties the separating scale to the position of the factor relative to the modulus.

> **Lemma 26.3** (`legal_lift_lt_primorial`). Let `a ∣ N` with `0 < a`, let the carrier be bounded by `N ≤ 6·X_A + 1`, `0 < N`, and let the separating scale `6·X_A + 1 < P_A` hold. Then `a < P_A`.

In Lean form:

```
theorem legal_lift_lt_primorial {a N X_A P_A : ℕ}
    (hsep : 6 * X_A + 1 < P_A) (hN : N ≤ 6 * X_A + 1) (hdvd : a ∣ N)
    (_hpos : 0 < a) (hNpos : 0 < N) : a < P_A
```

The proof is a chain of inequalities. Divisibility `a ∣ N` with `0 < N` gives `a ≤ N` (`Nat.le_of_dvd`); then `a ≤ N ≤ 6X_A + 1 < P_A`, whence `a < P_A` (closed in Lean by `omega`).

Note exactly where each hypothesis is used: divisibility gives `a ≤ N`, the legal carrier bound gives `N ≤ 6X_A + 1`, and the separating scale supplies the final strict step `6X_A + 1 < P_A`. Remove any one of them — and the conclusion `a < P_A` collapses.

> **Note.** This is precisely where the separating scale "does the work". Without it the factor could climb past `P_A`, and then $a \bmod P_A$ would no longer recover `a` — the coarse passport would remain genuinely coarse. The condition `P_A > 6X_A + 1` is exactly the point at which a coarse passport becomes exact on the legal region.

## The ProductHall configuration on the legal layer

The abstract collision we want to exclude is conveniently packaged as a structure: two *distinct* legal factors over a common base, congruent modulo the passport, and both bounded by the carrier.

> **Definition 26.4** (`LegalProductHall X_A P_A`). The data:
> - `a₁, a₂ : ℕ` — two active factors, `hne : a₁ ≠ a₂`;
> - `hcong : a₁ ≡ a₂ [MOD P_A]` — coincidence of the coarse passports;
> - carriers `N₁, N₂` with `hdvd₁ : a₁ ∣ N₁`, `hdvd₂ : a₂ ∣ N₂`;
> - positivity `hpos₁ : 0 < a₁`, `hpos₂ : 0 < a₂`;
> - legal bounds `hN₁ : 0 < N₁ ∧ N₁ ≤ 6·X_A + 1` and likewise `hN₂`.

This is exactly the object whose existence was required in chapter 25 for the branch "both legal, yet distinct": identical passport (`hcong`) with distinct factors (`hne`). We claim that under the separating scale such an object is contradictory.

## The main theorem: ProductHall is impossible

> **Theorem 26.5** (`no_productHall`). Under the separating scale `6·X_A + 1 < P_A` the configuration `LegalProductHall X_A P_A` is impossible: `False` is derivable from it.

In Lean form:

```
theorem no_productHall {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A)
    (PH : LegalProductHall X_A P_A) : False
```

The proof assembles the three previous bricks. From Lemma 26.3 (`legal_lift_lt_primorial`) (applied to both factors with their carrier bounds) we obtain `PH.a₁ < P_A` and `PH.a₂ < P_A`. Then Lemma 26.2 (`eq_of_modEq_of_lt`), applied to `PH.hcong`, gives `PH.a₁ = PH.a₂`. But this directly contradicts `PH.hne : a₁ ≠ a₂`. Formally — `PH.hne (eq_of_modEq_of_lt h1 h2 PH.hcong)`.

What is proven: under the separating scale, two legal factors congruent modulo `P_A` are *forced to coincide*, so a pair "distinct yet congruent" does not exist. Why this is true: the separating scale drives both factors below the modulus (`< P_A`), and below the modulus congruence is equivalent to equality.

**Conclusion.** The coarse passport $a \bmod P_A$ is injective on the legal region — it distinguishes everything that ever occurs there — and therefore cannot "glue" two distinct factors together. The trilemma of chapter 25 is bypassed honestly: the passport remained coarse (we gave it no extra distinguishing power), yet on the legal domain it became exact *automatically*.

> **Note (minimal axioms).** The formalisation of `no_productHall` rests only on `propext` and `Quot.sound` and *does not use* `Classical.choice`. This is constructive arithmetic: the node is closed by computation, not by choice. For the first time in the programme a pump node has been closed by a genuine proof rather than a renaming of the wall.

As a corollary, a passport collision on the legal layer yields anything at all by the principle "from falsehood, everything" (ex falso, see the [glossary](GLOSSARY.md)):

> **Corollary 26.6** (`productHall_bridge`). For any statement `Engine`, under the separating scale `LegalProductHall X_A P_A` implies `Engine` (via `False.elim`).

This is not a substantive conclusion about the engine but an honest record: since the configuration is empty, any bridge across it is trivial. We note it so as not to pass a reduction off as a proof: `productHall_bridge` is useful only as a logical stub over an already-established emptiness.

## The separating scale is attainable — with an enormous margin

The condition `P_A > 6X_A + 1` would be useless if it were unattainable. The observation: the primorial grows exponentially in `A`, whereas the carrier bound grows polynomially. By Chebyshev's theorem

$$
\log P_A = \sum_{p \le A} \log p = \vartheta(A) \sim A,
\qquad\text{in the decimal scale}\quad \log_{10} P_A \sim \frac{A}{\ln 10}.
$$

If we take the most pessimistic carrier estimate of the form $6X_A + 1 \lesssim 6\,A^{4.5}$, then its logarithm $\log_{10}(6A^{4.5}) \approx 4.5\log_{10}A + \log_{10}6$ grows only like `A^{4.5}` on the logarithmic scale, whereas $\log_{10}P_A$ grows linearly in `A`. The linear $A/\ln 10$ overtakes $4.5\log_{10}A$ already at `A ≈ 50`, and beyond that the gap only widens:

| `A` | $\log_{10} P_A$ | $\log_{10}(6\,A^{4.5})$ | `P_A > 6X_A + 1` |
|---|---|---|---|
| 50 | 17.0 | 8.4 | ✓ |
| 200 | 81.1 | 11.1 | ✓ |
| 1000 | 414.5 | 14.3 | ✓ |

By `A = 200` the gap is seventy orders of magnitude (81 against 11).

**Section takeaway.** The separating scale is not merely attainable — it holds with a colossal margin: the primorial's exponential instantly overwhelms any polynomial carrier bound. The condition is realistic, and one can build on it.

## Where the difficulty has moved (honestly)

Closing `ProductHall` does not close the whole programme — it *narrows* it. The energy-defect trichotomy had the form `LowerRankCollision ∨ ProductHall`; having removed the right branch, we collapse it to a single one:

> **Lemma 26.7** (`trichotomy_collapses`). `(L ∨ PH) ∧ ¬PH ⟹ L`.

This is pure logic (`Or.resolve_right`), and it is honestly framed as a reduction, not a result: the predicate `energy_defect_trichotomy` itself, which produces the disjunction `L ∨ PH`, remains an open node. In the same spirit we record the skeleton of the rank descent:

> **Skeleton lemma 26.8 (`rank_descent_terminates`).** Given a rank reduction `r → r-1` on the range `1 < r ≤ 4` and a closure of rank 1 (SNOL), the descent $r → \dots → 1$ is finite.

Here `lower_step` (the actual rank reduction) and `rank1_closes` (the closure of rank 1 via SNOL) are explicit hypotheses, not theorems. We do not pass the scaffold off as a proof: it merely shows that *if* the substantive steps are supplied, a well-founded induction on `r ≤ 4` assembles them.

> **Hypothesis and closure plan.** The hole has not vanished — it has moved to the rank level and become sharper. Still open are: (1) `energy_defect_trichotomy` — that a collision of the product signature with a mismatch yields `LowerRankCollision ∨ ProductHall`; (2) the closure of rank 1 via SNOL; (3) the bounded rank induction `r ≤ 4`. The plan: a global pigeonhole (infinitely many pedigrees against a finite key — the pigeonhole, see the [glossary](GLOSSARY.md)) should deliver `LowerRankCollision` at *every* rank — the same fan-in argument, one rank down, — while the separating scale proven here supplies injectivity of the passport on the top legal layer as the base of that descent. The key tension yet to be resolved: the passport must be fine for the uniqueness lemma and coarse for the pigeonhole at the same time — the same trilemma, lifted one rank up.

## Summary and bridge to the next chapter

We introduced the separating scale `P_A > 6X_A + 1`, showed it attainable with exponential margin, and on three arithmetic lemmas (`eq_of_modEq_of_lt`, `legal_lift_lt_primorial`, `no_productHall`) closed the node `ProductHall` on the legal layer constructively, without `Classical.choice`. The `uniqueLegalLift` trilemma is bypassed not by strengthening the passport but by squeezing the factors below the modulus: on the legal region the coarse passport $a \bmod P_A$ is injective, and so "distinct yet congruent" factors are impossible.

Yet all this arithmetic worked with a *flat* factor `a ∣ N`. To carry injectivity through the entire rank descent, a single number is not enough — one needs an extensional model of the state, one that distinguishes the roles of the factors and does not drag along the many-to-one tail of the absorber.

In the next chapter (27, product-core) we introduce `RankNode r` — a concrete product core `factors : Fin r → ℕ` with a sign — and transfer `no_productHall` from the flat factor to that core: we will show that for factors `< P_A` a coincidence of the core signature entails componentwise equality. This turns one chapter's arithmetic into an extensionality on which rank descent can be built.

<!--navbot-->

---

[← 25. Rigid closure](25_RigidClose.md) · [Table of contents](00_Overview.md) · [27. Product-core →](27_ProductCore.md)
<!--/navbot-->
