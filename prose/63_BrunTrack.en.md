# 63. The Brun track: density zero and unconditional rates — formalization-first

<!--navtop-->
[← 62. The dilation ladder](62_DilationLadder.md) · [Contents](00_Overview.md)
<!--/navtop-->

> Lean: `Engine/GeometricTypeIIBrun.lean` (`alternating_partial_binomial`,
> `moebius_truncated_divisor_sum`, `bonferroni_isUpperMoebius`),
> `Engine/GeometricTypeIIBrunTwin.lean` (`twinValue`, `sievePrimes`, `twinNu`,
> `twinSieve`, `root_res_card`, `twinSieve_rem_bound`, `brun_twin_upper`,
> `esymmOn_le_pow_div_factorial`), `Engine/GeometricTypeIIBrunTwinDensity.lean`
> (`twin_mainSum_eq`, `twin_errSum_le_const`, `twin_count_le_eps`,
> `twin_density_zero`), `Engine/GeometricTypeIIBrunTwinRate.lean`
> (`twin_count_of_prod_le`, `twin_count_log_rate`),
> `Engine/GeometricTypeIIBrunTwinMertens.lean`
> (`sievePrimes_prod_le_nine_div_log_sq`, `twin_count_log_rate_unconditional`),
> `Engine/GeometricTypeIIBrunTwinMertensUpper.lean` (`sum_primesLE_inv_le`,
> `sievePrimes_sum_two_div_le`), `Engine/GeometricTypeIIBrunTwinTruncated.lean`
> (`twin_mainSum_truncated_le`, `esymm_tail_le`, `twin_errSum_truncated_le`,
> `twin_count_brun_truncated`).

Brun's method is an upper-bound method: it is structurally blind to the parity wall — and
**that is exactly why** it can be carried to completion unconditionally. This chapter is
the formalization-first track: from a bridge into mathlib's dormant sieve frame to the
machine theorems "twin primes have density zero" and
"twins$(N) \le 9N/\log^2 z + 3^z + z/6 + 1$", and onward to the truncated sieve with the
true Brun shape. None of these statements says anything about the *infinitude* of twins;
an upper bound does not touch the wall — and every disclosure says so.

## 1. Stage 1: the Bonferroni bridge into the dormant frame

The mathlib pin contains a sieve frame (`BoundingSieve`) with the theorem
`siftedSum_le_mainSum_errSum_of_upperMoebius` — but not a single usable weight.

> **Theorem 63.1** (`moebius_truncated_divisor_sum`). The closed form of the truncated
> Möbius divisor sum: for $n \ge 2$,
>
> $$
> \sum_{d \mid n,\ \omega(d) \le t} \mu(d) \;=\; (-1)^t \binom{\omega(n)-1}{t} \tag{63.1}
> $$
>
> — each truncation closes in a single Pascal term (`alternating_partial_binomial`). For
> even $t$ the right side is $\ge 0$: the Bonferroni weight is upper-Möbius
> (`bonferroni_isUpperMoebius`), and the mathlib frame becomes applicable. 🟢

## 2. Stage 2: the twin sieve

> **Definition 63.2** (twin sieve). The support consists of the values
> `twinValue` $m = (6m-1)(6m+1)$; the sifting primes are `sievePrimes` $z$ = the primes
> in $[5, z]$; the density is `twinNu` $d = 2^{\omega(d)}/d$. The number of roots of
> $36r^2 \equiv 1 \pmod d$ is exactly $2^{\omega(d)}$ (`root_res_card`), and the
> remainder obeys $|r(d)| \le 2^{\omega(d)}$ (`twinSieve_rem_bound`).

> **Theorem 63.3** (`brun_twin_upper`). For all $N, z$ and even $t$,
>
> $$
> \#\{m \le N: \text{both } 6m\pm1 \text{ prime}\}
> \;\le\; N \cdot \mathrm{mainSum}(\mu^+_t) + \mathrm{errSum}(\mu^+_t) + \tfrac{z}{6} + 1. \tag{63.2}
> $$
>
> An exact, unconditional inequality; the sieve terms are still symbolic. 🟢

## 3. Stage 3: density zero

Choosing $t = 2k$ (with $k$ the number of sifting primes) makes the truncation vacuous:
$\mathrm{mainSum} = \prod_{5 \le p \le z}(1 - 2/p)$ **exactly** (`twin_mainSum_eq`), and
the error budget is $N$-free: $\mathrm{errSum} \le 3^k$ (`twin_errSum_le_const`). The
divergence of $\sum 1/p$ kills the Legendre product, and:

> **Theorem 63.4** (`twin_density_zero`). Twin centers have density zero:
>
> $$
> \frac{\#\{m \le N : \text{both } 6m\pm1 \text{ prime}\}}{N}
> \;\xrightarrow[N\to\infty]{}\; 0. \tag{63.3}
> $$
>
> The first standalone classical theorem of the formalization-first track — machine
> checked, standard axioms, no `sorry` (the workhorse form is `twin_count_le_eps`). 🟢

## 4. Stage 4a: the unconditional logarithmic rate

The parametric form `twin_count_of_prod_le` accepts any product bound. The Mertens input
was discharged by the **squaring trick**: $1 - 2/p \le (1 - 1/p)^2$ (the difference is
exactly $1/p^2$); the pin's finite Euler identity dominates the harmonic sum, and
$\prod_{5 \le p \le z}(1 - 2/p) \le 9/\log^2 z$ for all $z \ge 2$
(`sievePrimes_prod_le_nine_div_log_sq`; pre-pass: $\sup_z \mathrm{LHS}\cdot\log^2 z =
2.497$ — a $3.6\times$ margin; the true constant $4e^{-2\gamma} \approx 1.26$ is not
claimed).

> **Theorem 63.5** (`twin_count_log_rate_unconditional`). For all $N$ and all $z \ge 2$,
>
> $$
> \#\{m \le N: \text{both } 6m\pm1 \text{ prime}\}
> \;\le\; \frac{9N}{\log^2 z} + 3^z + \frac{z}{6} + 1. \tag{63.4}
> $$
>
> Prose reading: $z \approx \tfrac12\log N$ gives the crude Brun rate
> $O\bigl(N/(\log\log N)^2\bigr)$. 🟢

## 5. Stage 4b: the Mertens upper bound and the truncated sieve

The true Brun rate needs large $z$, hence truncation $t \ll k$ and tail control. The
required Mertens upper bound came by the "Chebyshev straight into Abel" route: the pin's
$\theta(x) \le x\log 4$ fed into the dormant Abel summation frame
(`sum_mul_eq_sub_integral_mul₁`), the boundary term cancelling the antiderivative
exactly:

> **Theorem 63.6** (`sum_primesLE_inv_le`). For $x \ge 2$,
>
> $$
> \sum_{p \le x} \frac1p \;\le\; \log 4 \cdot \log\log x
> + \log 4\Bigl(\frac{1}{\log 2} - \log\log 2\Bigr), \tag{63.5}
> $$
>
> and in sieve form $\sum_{p \in \text{sievePrimes } z} 2/p \le 3\log\log z + 6$ for
> $z \ge 3$ (`sievePrimes_sum_two_div_le`). The constant $\log 4$ is Chebyshev's, not
> optimal; PNT is used nowhere. 🟢

The truncation defect is bounded by the elementary-symmetric tail: divisors of $P(z)$
biject with subsets of the sifting primes, $e_j \le X^j/j!$
(`esymmOn_le_pow_div_factorial` — the stage-2 dormant tool, now consumed), and
$\sum_{j>t} e_j \le e^{3X}/2^{t+1}$ (`esymm_tail_le`); the truncated error is polynomial:
$\mathrm{errSum}(\mu^+_t) \le (t+1)(2z)^t$ (`twin_errSum_truncated_le`).

> **Theorem 63.7** (`twin_count_brun_truncated`). For all $N$, $z \ge 3$, and even $t$,
>
> $$
> \#\{m \le N\}
> \;\le\; N\Bigl(\frac{9}{\log^2 z} + \frac{e^{9\log\log z + 18}}{2^{t+1}}\Bigr)
> + (t+1)(2z)^t + \frac{z}{6} + 1. \tag{63.6}
> $$
>
> Prose reading (not Lean): $2^t \approx \log^{11} z$, $z \approx N^{1/4t}$ give the true
> Brun shape $O\bigl(N(\log\log N)^2/\log^2 N\bigr)$. The constants are honest and crude;
> the numerical applicability thresholds are astronomical — as in every honest chain of
> Brun constants; the value is the machine-checked parametric family. 🟢

**Chapter summary.** The Bonferroni bridge opened the dormant frame (63.1); the twin
sieve is instantiated with the exact root count (Definition 63.2, 63.2); density zero is
machine-checked (63.3); the $9N/\log^2 z$ rate is unconditional (63.4); the Mertens upper
bound was taken by Chebyshev-through-Abel with no PNT (63.5); the truncated sieve
delivered the parametric true Brun shape (63.6). All of it is upper bounds: the method is
blind to the parity wall, the infinitude of twins is untouched in every line, and no §110
event is claimed.
