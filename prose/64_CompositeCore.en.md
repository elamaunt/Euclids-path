# 64. The composite core: the CRT cocycle, twisted factorizations, and leaving the prime line

<!--navtop-->
[← 63. The Brun track](63_BrunTrack.md) · [Contents](00_Overview.md)
<!--/navtop-->

> Lean: `Engine/GeometricTypeIICocycle.lean` (`crt_cocycle_dvd`,
> `stdAddChar_crt_factor`), `Engine/GeometricSegreFarey.lean` (`crt_sum_factor`,
> `exterior_energy_kills_flat_modes`, `two_freq_orthogonal`),
> `Engine/GeometricTypeIITwinVarietyCRT.lean` (`twinDomU`, `mem_twinDomU`,
> `twinVU_crt_factor`, `twinVU_family_M4_norm_general`, `twinN4U_card_crt`,
> `twinVU_family_M4_semiprime`), `Engine/GeometricTypeIITwinVarietyCRTMarkov.lean`
> (`twinVU_moment_crt_factor`, `twinVU_markov_general`, `twinVU_markov_semiprime`),
> `Engine/GeometricTypeIITwinWindowU.lean` (`intervalWeight_L1_general`,
> `twin_short_completion_U`, `twin_short_good_pairs_semiprime`),
> `Engine/GeometricTypeIIKloostermanCRT.lean` (`kloosU_crt_factor`,
> `kloosU_norm_semiprime_rpow`), `Engine/GeometricTypeIISalieCRT.lean`
> (`salieU_crt_factor`, `salieU_norm_semiprime`).

Face E of the wall lives on **incommensurable moduli**: the $\mu$-signed aggregation
across different $q$. Before one can speak of two moduli at once, one must master a single
*composite* one — and that is a discipline of its own: $\mathbb{Z}/q_1q_2$ is not a field,
inverses are temperamental, and naive domains break. This chapter builds the composite
core in full: the exact cocycle of the standard character, CRT Fubini, unit domains, the
twisted factorizations of all three families of the repository — and the short window at
a semiprime modulus. The honest frame: one composite modulus is still **one** modulus;
face E is untouched, and every disclosure says so.

## 1. The cocycle: $1/(q_1q_2)$ splits with an integer correction

> **Theorem 64.1** (`stdAddChar_crt_factor`). For coprime $q_1, q_2$ and
> $u_1 = q_2^{-1} \bmod q_1$, $u_2 = q_1^{-1} \bmod q_2$, the partial-fraction split
> closes with an integer: $q_1q_2 \mid u_1q_2 + u_2q_1 - 1$ (`crt_cocycle_dvd`), and so
>
> $$
> \psi_{q_1q_2}(x) \;=\; \psi_{q_1}(u_1 x_1)\,\psi_{q_2}(u_2 x_2) \tag{64.1}
> $$
>
> exactly, for **all** $x$ — the pin has no such factorization; verified numerically up
> to the non-prime pair $(4,9)$. An exact rewrite creates no cancellation: this is
> infrastructure, and the $\mu$-signs across moduli are untouched by construction. 🟢

## 2. CRT Fubini and the collective annihilation of flat modes

> **Theorem 64.2** (`crt_sum_factor`). Over the complete semiprime period, a product of a
> purely-left and a purely-right field sums to the product of marginals:
> $\sum_x f_1(x_1) f_2(x_2) = (\sum f_1)(\sum f_2)$ — the two CRT directions are exactly
> independent. 🟢

> **Theorem 64.3** (`exterior_energy_kills_flat_modes`). The exterior (Segre) energy of
> any purely-left × purely-right pair over the complete period is **zero** — a collective
> cancellation: at $(5,7)$, $840$ of the $1225$ terms are individually nonzero yet the
> sum vanishes. The complete CRT frame sits **on** the Segre quadric. The Fourier slice:
> over the full period only the doubly flat mode $(0,0)$ survives
> (`two_freq_orthogonal`). The load-bearing disclosure: the short-window version is
> **false** — measured defects $-2, -6, -12$ at $M = 12, 16, 23$ for $(5,7)$; that
> nonzero short-window defect *is* face E. The module **confines** the open content to
> the incommensurable short window; it does not reduce it. 🟢

## 3. The unit domain: the twin family leaves the prime line

At a composite modulus the correct domain is not $x \ne 0$ but **invertibility**.

> **Definition 64.4** (unit domain). `twinDomU` $q = \{x : x$ and $x+2$ are units$\}$
> (`mem_twinDomU`). The naive domain $x \notin \{0,-2\}$ is **refuted** at $q = 35$:
> $33 \ne 15$ already at zero frequency, violation on all $42875$ triples; $x \ne 0$ is
> not CRT-componentwise — invertibility is.

> **Theorem 64.5** (`twinVU_crt_factor`). The twisted factorization of the unit family:
>
> $$
> V^U_{q_1q_2}(a, b_1, b_2)
> \;=\; V^U_{q_1}(u_1a_1, u_1b_{1,1}, u_1b_{2,1}) \cdot
>       V^U_{q_2}(u_2a_2, u_2b_{1,2}, u_2b_{2,2}) \tag{64.2}
> $$
>
> — cocycle units on all three frequency slots, the domain untwisted. Verified
> numerically: all triples at $(5,7)$ and $(5,11)$. 🟢

> **Theorem 64.6** (`twinN4U_card_crt`). $M4^U(q) = q^3 \cdot N4^U(q)$ at **every**
> modulus ($\psi$ is primitive throughout — `twinVU_family_M4_norm_general`), and $N4^U$
> is multiplicative via a quadruple CRT bijection; the uniform fiber law of chapter
> [61](61_TwinVariety.md) does **not** transfer — composite fibers are $\{1,2,4\}$. The
> semiprime closed form:
> $M4^U(\ell_1\ell_2) = (\ell_1\ell_2)^3(\ell_1-2)(2\ell_1-5)(\ell_2-2)(2\ell_2-5)$
> (`twinVU_family_M4_semiprime`). 🟢

## 4. Moment factorization, Markov, and the window at a composite modulus

> **Theorem 64.7** (`twinVU_moment_crt_factor`). The $a$-averaged fourth moment
> **factors** through CRT: the composite moment of a pair $(b_1,b_2)$ equals the product
> of the component moments at the twisted frequencies — a pair is exceptional mod
> $q_1q_2$ iff its twisted components are jointly exceptional. Verified on all $1225$
> pairs at $(5,7)$. 🟢

> **Theorem 64.8** (`twinVU_markov_semiprime`). Markov at every modulus: the bad pairs
> number $\le N4^U(q)/K$ (`twinVU_markov_general`); at a semiprime $q = \ell_1\ell_2$ —
> $\le 4q^2/K$. The exceptional frequency set has left the prime line. 🟢

> **Theorem 64.9** (`twin_short_good_pairs_semiprime`). The short window too: the kernel
> $L^1$ bound of completion holds at every modulus (`intervalWeight_L1_general` — the
> wave-1 prime hypothesis was inessential), completion is exact on the unit domain
> (`twin_short_completion_U`), and at $q = \ell_1\ell_2$, outside $\le 4q^2/K$ pairs,
> the $q^{2/3}$-threshold window bound of chapter [61](61_TwinVariety.md) holds. Joint
> two-wing cancellation at a **composite** modulus, almost all pairs. 🟢

## 5. The classical multiplicativities: 1926 and 1932

The one-pole families receive their composite versions — classical results absent from
the pin.

> **Theorem 64.10** (`kloosU_crt_factor`). Kloosterman's multiplicativity (1926):
> $\mathrm{Kl}_{q_1q_2}(a,b) = \mathrm{Kl}_{q_1}(u_1a_1, u_1b_1)\,
> \mathrm{Kl}_{q_2}(u_2a_2, u_2b_2)$ on the unit domain; as a consequence, the pointwise
> bound $\|\mathrm{Kl}_{\ell_1\ell_2}\| \le \sqrt2\,(\ell_1\ell_2)^{3/4}$ for
> componentwise nondegenerate frequencies (`kloosU_norm_semiprime_rpow`). The exponent
> $3/4$ is fourth-moment strength, not Weil; the degenerate strata are named, not
> claimed. 🟢

> **Theorem 64.11** (`salieU_crt_factor`, `salieU_norm_semiprime`). Salié's
> multiplicativity (1932): the correct composite character is the Jacobi symbol (which
> the pin has); the character splits **without** a twist, the frequencies carry the
> cocycle units, and
>
> $$
> \|T_{\ell_1\ell_2}(a,b)\| \;\le\; 4\sqrt{\ell_1\ell_2} \tag{64.3}
> $$
>
> for all componentwise nondegenerate pairs — **a pointwise exponent-$1/2$ bound at a
> composite modulus**, no averaging ($1.37\times$ slack at $(5,7)$). One pole with a
> $\chi$-twist: the two-pole family does not reduce to Salié (the chapter-
> [61](61_TwinVariety.md) disclosure stands verbatim). 🟢

**Chapter summary.** The composite core is built in full: the cocycle (64.1), Fubini and
the flat-mode annihilation with the honest confinement of face E to the short window
(Theorem 64.3), the unit domain and the twisted factorization of the twin family (64.2),
the multiplicative moment and Markov off the prime line (Theorems 64.7–64.8), the short
window at a semiprime modulus (Theorem 64.9), and both classical multiplicativities with
the $3/4$ and $1/2$ exponents (Theorems 64.10–64.11). Complete sums throughout, unsigned,
one composite modulus. Face E — the $\mu$-signed aggregation across **incommensurable**
moduli — is untouched: one composite modulus is still one modulus. The wall stands where
it stood, named as it was named.
