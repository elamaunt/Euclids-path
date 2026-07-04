# twin_certify — a deterministic twin certifier from proved laws

> 🇷🇺 **Русская версия:** [`README_twin_certify.md`](README_twin_certify.md) · 🇬🇧 English version.

A tool that is a corollary of the programme's machine-checked lemmas. It does **not** speed up
factorisation and does **not** threaten RSA — it certifies twin pairs in its own niche faster and more
strictly than probabilistic tests.

## What it rests on (what is proved in Lean)

`EuclidsPath/Engine/Residuals.lean`, theorem **`oldfree_below_sq_prime`** (standard axioms, no `sorry`):

> If no prime `p`, `5 ≤ p ≤ A`, divides `6m−1` and `6m+1`, and `6m+1 < A²`,
> then `6m−1` and `6m+1` are **both prime**.

Plus the channel-law wheel (`PaymentLedger.lean`): a twin-centre avoids `m ≡ ±6⁻¹ (mod q)`.

This yields a **deterministic certificate** of the pair's primality through **a single sieve** up to
`A=⌈√(6m+1)⌉`, amortised across the whole window, without a separate primality test / factorisation of
each side.

## Input / usage

The input is a **centre `m`** (the pair is `(6m−1, 6m+1)`), a single one or a window.

```
python twin_certify.py certify 18            # one centre -> OK (107,109) / NO divisor
python twin_certify.py window 1000000 1001000  # all twin-centres in the window
python twin_certify.py list 1 18 4 2         # a list of centres
python twin_certify.py bench 3000000         # a benchmark against baseline
```

## The niche (where it beats the alternatives) — with measurements

| mode | best method | why |
|---|---|---|
| **sparse candidates in a large window** | **this tool** | a single sieve up to `√(6·hi)` amortises; **deterministic** |
| you need a **certificate**, not a probability | **this tool** | it gives a proof of primality; Miller–Rabin is only a probability |
| all twins in a row in a window | a full sieve of Eratosthenes | a range sieve is faster for a dense sweep |
| a single giant number (RSA-scale) | — | it hits `√n`, like trial division (not the niche) |

Measurement (`bench 3000000`, numbers up to 1.8·10⁷, 20000 sparse centres):
- **the lemma-certificate is ~4.3× faster than Miller–Rabin ×2**, the result is **identical**, and it is
  a **proof**, not a probability;
- the full sieve wins only in the "all in a row" mode.

## The applicability boundary (honestly)

The lemma needs primes up to `A=√(6m+1)`. The practical limit is `A ≲ 2·10⁸`, i.e. centres `m` up to
about **10¹⁵** (numbers up to ~10¹⁵). For larger ones the tool **refuses** (`size_guard`), because it
does not bypass the `√n` barrier. This is not a factorisation algorithm and not a speed-up for giant
numbers.

## What it gives a researcher

- A **reproducible** deterministic certificate of twin pairs, grounded in a machine-checked lemma (not a
  heuristic);
- in the niche of sparse checking — **faster than probabilistic Miller–Rabin** and stricter at the same
  time (a certificate);
- honest bounds: the niche and the `√n` limit are explicit, without exaggeration.
