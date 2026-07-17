# 61. The twin variety: three keys, the fourth moment, and windows at the ℓ^{2/3} threshold

<!--navtop-->
[← 60. The Type II wall](60_TypeIIWall.md) · [Contents](00_Overview.md)
<!--/navtop-->

> Lean: `Engine/GeometricTypeIITwinVariety.lean` (`twinV_apply`, `twin_fiber`,
> `twinN4_card`, `twinV_family_fourth_full`, `twinV_family_M4_norm`,
> `twinV_family_M4_le`, `twinV_markov`, `twinN4CountN_5`, `twinN4CountN_7`,
> `twinN4TwoKeyCountN_7`), `Engine/GeometricTypeIITwinWindow.lean`
> (`twinShort`, `twin_transform_eq_twinV`, `twin_short_completion`,
> `twin_short_fourth_bound`, `twin_short_good_pairs`),
> `Engine/GeometricTypeIISalie.lean` (`salie`, `salie_eval`, `gauss_norm`,
> `salie_norm_le`, `salie_eq_zero_of_nonsquare`).

The wall lives in the correlation of the two wings $6m\pm1$ on short windows. This chapter
builds an object that sees **both wings at once** — a complete exponential sum with two
poles — and extracts from its *family* fourth moment an unconditional short-window
cancellation: for almost all wing frequencies, at the $\ell^{2/3}$ threshold, strictly
below the engine's $\ell^{3/4}$ of chapter [60](60_TypeIIWall.md). The honest frame is
declared up front: almost all frequencies, not all; the averaged count is the entire cash
value (no pointwise extraction exists for this family); no §110 event is claimed.

## 1. The domain and the three keys

> **Definition 61.1** (twin variety). At a prime $\ell > 2$, on the doubly punctured
> domain $x \notin \{0, -2\}$, set
>
> $$
> V(a, b_1, b_2) \;=\; \sum_{x} \psi\bigl(a x + b_1 x^{-1} + b_2 (x+2)^{-1}\bigr) \tag{61.1}
> $$
>
> (Lean: `twinV_apply`) — a linear frequency $a$ and one frequency per pole-wing. The
> two-frequency version (without the $a$ slot) was rejected by the pre-pass: its exact
> count runs into genus-one character sums, and extraction breaks for lack of scaling.
> The third frequency is not decoration but a key.

The counting backbone of the fourth moment is the variety of quadruples with **three
keys**: $x_1{+}x_2 = x_3{+}x_4$, $x_1^{-1}{+}x_2^{-1} = x_3^{-1}{+}x_4^{-1}$, and
$(x_1{+}2)^{-1}{+}(x_2{+}2)^{-1} = (x_3{+}2)^{-1}{+}(x_4{+}2)^{-1}$.

> **Theorem 61.2** (`twin_fiber`). The uniform fiber law: for $2 < \ell$ every nonempty
> fiber of the variety has cardinality exactly $2$. For $x + z \ne 0$ the Vieta spine
> works; on the antipodal stratum $x + z = 0$, the corner spine $4/(4 - x^2)$. The third
> key cuts the antipodal "fattening" of the Kloosterman variety from fiber $\ell - 1$
> down to fiber $2$. 🟢

> **Theorem 61.3** (`twinN4_card`). The variety count is exact and cleaner than
> Kloosterman's:
>
> $$
> N_4 \;=\; (\ell - 2)(2\ell - 5) \tag{61.2}
> $$
>
> — with no stratum trisection (Kloosterman's was $3(\ell-1)(\ell-2)$, chapter
> [60](60_TypeIIWall.md)). Kernel demos are attached: `twinN4CountN_5` $= 15$,
> `twinN4CountN_7` $= 45$; the two-key control counter `twinN4TwoKeyCountN_7` $= 53$
> exhibits exactly the volume the third key cuts. 🟢

## 2. The exact family fourth moment and the bad-pair count

> **Theorem 61.4** (`twinV_family_M4_norm`). Triple orthogonality over all three
> frequency slots collapses the family fourth moment into an exact identity:
>
> $$
> \sum_{a,\,b_1,\,b_2} \|V(a, b_1, b_2)\|^4 \;=\; \ell^3\,(\ell-2)(2\ell-5)
> \;\le\; 2\ell^5 \tag{61.3}
> $$
>
> (`twinV_family_fourth_full`; the bound is `twinV_family_M4_le`). 🟢

> **Theorem 61.5** (`twinV_markov`). For every $K > 0$, the wing-frequency pairs
> $(b_1, b_2)$ whose $a$-averaged moment reaches $K\ell^3$ number at most $2\ell^2/K$ —
> an explicit small exceptional set out of $\ell^2$ possible pairs. This is the module's
> entire cash value: no pointwise extraction exists for this family. 🟢

## 3. The short window: the ℓ^{2/3} threshold

The short two-wing sum $S(b_1,b_2) = \sum_{m<M} \psi(b_1 m^{-1} + b_2 (m+2)^{-1})$
(Lean: `twinShort`) completes exactly, and the completion frequency lands precisely on
the family's linear slot.

> **Theorem 61.6** (`twin_short_completion`). For all $M$,
> $S(b_1,b_2) = \frac1\ell \sum_h W_M(h)\, V(h, b_1, b_2)$ — exact
> (`twin_transform_eq_twinV`: the completing shift lands on the named parameter $a$). 🟢

> **Theorem 61.7** (`twin_short_fourth_bound`). The weighted double Cauchy–Schwarz in
> fourth-power form, $(\sum wU)^4 \le (\sum w)^3(\sum wU^4)$ — no roots anywhere — turns
> the moment into a window bound: if $\sum_a \|V(a,b_1,b_2)\|^4 \le K\ell^3$, then
>
> $$
> \|S(b_1,b_2)\|^4 \;\le\; \Bigl(\frac{M}{\ell} + 1 + \log \ell\Bigr)^3 K M \ell^2. \tag{61.4}
> $$
>
> The pre-pass correction is load-bearing: the naive L¹×L∞ route gives only
> $\ell^{3/4}$; the double Cauchy–Schwarz, reusing the weight inside the moment, is the
> source of the $2/3$. 🟢

> **Theorem 61.8** (`twin_short_good_pairs`). For every $K > 0$ there is an explicit bad
> set of at most $2\ell^2/K$ pairs outside which (61.4) holds. The threshold reading
> (prose, not a Lean statement): for $M \le \ell$ the bound is $o(M^4)$ exactly when
> $M \gg K^{1/3}\ell^{2/3}(2 + \log \ell)$ — joint equidistribution of both wings on
> windows of length $\ell^{2/3+\varepsilon}$, almost all frequencies. 🟢

## 4. Salié: all frequencies at one pole

What blocks removing "almost all"? For the one-pole family with a quadratic twist the
answer is classical — and now machine-checked.

> **Theorem 61.9** (`salie_eval`). The classical Salié evaluation: for $a, b \ne 0$,
>
> $$
> T(a,b) \;=\; \chi(a)\, g(\chi) \sum_{v^2 = ab} \psi(2v), \tag{61.5}
> $$
>
> where $\chi$ is the quadratic character and $g(\chi)$ the Gauss sum. The twist
> $\chi(a)$ is **load-bearing**: without it the identity already fails at $\ell = 7$,
> $a = 3$, $b = 6$ (checked by the pre-pass); for nonsquare $ab$ the sum vanishes
> (`salie_eq_zero_of_nonsquare`). 🟢

> **Theorem 61.10** (`salie_norm_le`). $\|g(\chi)\| = \sqrt{\ell}$ (`gauss_norm` —
> derived in the repository; the pin has no such Gauss-sum norm), and hence
> $\|T(a,b)\| \le 2\sqrt{\ell}$ for **all** frequencies $a, b \ne 0$ — pointwise, no
> averaging, no Weil input. 🟢

The honest boundary: this is ONE pole. The two-pole twin family $V(a,b_1,b_2)$ does
**not** reduce to Salié — its all-frequency problem at exponent $1/2$ remains open, and
the twin variety keeps its almost-all statement (Theorem 61.8).

**Chapter summary.** The two-wing correlation acquired a complete-sum carrier with an
exact count (61.2), an exact family moment (61.3), and an explicit small exceptional set
(61.5); completion plus the double Cauchy–Schwarz produced unconditional joint
cancellation of both wings at the $\ell^{2/3}$ threshold — almost all frequencies (61.4,
Theorem 61.8); the one-pole Salié closed all frequencies at exponent $1/2$ (61.5,
Theorem 61.10) and delineated exactly what the two poles still lack. The wall is
untouched: short windows with $\mu$-signs are exactly where they were.
