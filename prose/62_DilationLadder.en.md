# 62. The dilation ladder and sign blindness: the unique odd mechanism

<!--navtop-->
[← 61. The twin variety](61_TwinVariety.md) · [Contents](00_Overview.md)
<!--/navtop-->

> Lean: `Engine/GeometricTypeIIDilation.lean` (`strikePairs`,
> `strikePairs_lambda_sum`, `wing_dilation_identity`,
> `wing_dilation_identity_of_squarefree`, `minus_wing_no_square`,
> `rough_minus_moebius_eq_liouville`, `moebius_ne_liouville_125`,
> `rough_window_omega_lambda_sum`), `Engine/GeometricTypeIISignBlind.lean`
> (`cross_conductor_sign_eating`, `one_defect_tower_ge_S2`,
> `signed_conjugation_trace_blind`, `exchange_invariant_sign_eq_one_or_liouville`),
> `Engine/GeometricTypeIILadderWindow.lean` (`minus_wing_rung_criterion`,
> `minus_window_semiprime_rung_decomposition`, `rough_window_prime_semiprime_split`,
> `rough_minus_window_rung_ladder`, `rung_count_eq_cofactor_count`).

The wall is a sign: the cofinal behavior of $\lambda(6m\pm1)$ on short windows. This
chapter answers two questions. *Which operations see the sign at all?* — exactly two:
log-weights and the dilation $\lambda(pn) = -\lambda(n)$; and this is a machine
classification, not an observation. *What does the unique sign-odd mechanism yield?* — an
exact input identity (the "ladder") and an exact window form of face B, but not an
estimate: the sign stays open exactly where it was. Plus three no-gos closing the class
of "clever" detours through $\mu$-oscillation and spectra.

## 1. Strikes and the forced sign flip

> **Definition 62.1** (strike pairs). `strikePairs` $N$ is the finite set of pairs
> $(p, n)$ with $p$ prime and $pn = N$; it has exactly $\omega(N)$ elements. The
> hypothesis $N \ne 0$ is load-bearing: at $N = 0$ the pair set is infinite.

> **Theorem 62.2** (`strikePairs_lambda_sum`). $\sum_{(p,n)} \lambda(n) = -\,\omega(N)\,\lambda(N)$:
> every step one rung down the scale ladder $X \to X/p$ is **forced** to flip the
> Liouville sign. Dilation is the arsenal's unique exact sign-odd operation (the exchange
> symmetry is even — a machine theorem of chapter [60](60_TypeIIWall.md)). 🟢

> **Theorem 62.3** (`wing_dilation_identity`). The ladder identity on any window — with
> the **explicit** correction $(\Omega - \omega)\lambda$: the correction-free version is
> false on non-squarefree wings (pre-pass counterexample); on squarefree wings the
> correction vanishes (`wing_dilation_identity_of_squarefree`). An identity, not an
> estimate. 🟢

## 2. The minus wing's gift: μ = λ for free

> **Theorem 62.4** (`rough_minus_moebius_eq_liouville`). The square of an odd prime
> $p \ge 5$ satisfies $p^2 \equiv 1 \pmod 6$, so the minus wing $6m-1$ carries no squares
> (`minus_wing_no_square`); the rough minus wing is squarefree, and **$\mu = \lambda$ on
> it for free**. Roughness is load-bearing: $\mu(125) \ne \lambda(125)$
> (`moebius_ne_liouville_125`, $125 = 5^3$). Face B's Liouville data on the minus wing
> is literally the $\mu$-frame of faces C/E: a unification with no translation. 🟢

The integer window form: $2\sum_I \Omega\lambda = |I| + 3L$
(`rough_window_omega_lambda_sum`) — the bias $L$ enters an exact integer balance.

## 3. The ladder on a real window: face B in Buchstab form

> **Theorem 62.5** (`minus_wing_rung_criterion`). The pointwise rung criterion: on
> $N \equiv 5 \pmod 6$, the condition "$\Omega(N) = 2$ and $\operatorname{minFac} N = p$"
> is equivalent to "$p \mid N$, $(N/p)$ is prime, and $p < N/p$". Both hypothesis
> ingredients are load-bearing: the primality of $p$ ($N = 725$, $p = 25$) and the mod-6
> congruence ($N = 25$, $p = 5$) — counterexamples attached. 🟢

> **Theorem 62.6** (`rough_minus_window_rung_ladder`). The headline: on a rough minus
> window,
>
> $$
> \sum_{m \in I} \lambda(6m-1) \;=\; \sum_p R_p \;-\; P, \tag{62.1}
> $$
>
> where $P$ counts prime wings and the $R_p$ are the "rungs": cofactor-prime counts at
> the scales $X/p$ (`rung_count_eq_cofactor_count`: each rung literally counts primes
> $q > p$ with $pq$ on the wing). The Liouville bias **is** the excess of prime counts at
> the lower scales over the prime count at the top scale — the entropy-decrement skeleton
> in exact window form. Pre-pass on a real window: $|I| = 103$, $P = 74$, $S = 29$,
> $\sum\lambda = -45 = 29 - 74$; the fibering $29 = 9+8+4+4+3+1$ over
> $p \in \{11,\dots,29\}$. On a raw (non-rough) window the headline is FALSE
> ($-24 \ne -12$) — the dichotomy carries weight exactly where disclosed. 🟢

The split $P + S = |I|$ (`rough_window_prime_semiprime_split`) and the semiprime fibering
by smallest prime (`minus_window_semiprime_rung_decomposition`) need no roughness; the
headline (62.1) does.

## 4. Three no-gos: how the sign cannot be taken

> **Theorem 62.7** (`cross_conductor_sign_eating`). $\mu(q) \cdot B_q(j) = A_q(j)/(q-2) > 0$
> at **every** prime conductor and every moment index: the Möbius sign is exactly eaten
> by the parity eigenvalue $-1/(q-2)$. Telescoping $\mu$ against the one-defect tower is
> structurally impossible; the "Euler derivative" is the $S_2$ divergence renamed
> (`one_defect_tower_ge_S2`). 🟢

> **Theorem 62.8** (`signed_conjugation_trace_blind`).
> $\operatorname{Tr}((D_\varepsilon A D_\varepsilon)^k) = \operatorname{Tr}(A^k)$ for any
> $\pm1$ diagonal: **all** spectral moments are blind to signs. The $\mu$-signs enter the
> Gram frame only as such a conjugation — spectra and norms do not see $\mu$. 🟢

> **Theorem 62.9** (`exchange_invariant_sign_eq_one_or_liouville`). Completeness of the
> filter: a completely multiplicative sign function constant on primes is either $1$ or
> $(-1)^\Omega = \lambda$. There are exactly two exchange-invariant sign characters;
> log-weights and dilation are the only sign-seeing mechanisms — now certified, not
> merely observed. 🟢

**Chapter summary.** Dilation is the unique exact sign-odd mechanism (62.2, 62.9); its
input identity is exact on every window (62.3) and takes the Buchstab form (62.1) on
rough minus windows, with a full numerical cross-check; $\mu = \lambda$ on the minus wing
for free (Theorem 62.4) — the C/E frame and the B data glued. Three no-gos close
$\mu$-telescopes, spectral detours, and nonexistent "third" sign characters (62.7–62.9).
All of it is visibility and cartography: neither the $R_p$ nor $P$ is bounded, and the
sign of face B is exactly as open as before this chapter.
