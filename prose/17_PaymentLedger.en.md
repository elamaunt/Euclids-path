# 17. The payment law and the defect

<!--navtop-->
[← 16. By contradiction](16_FiniteContradiction.md) · [Table of contents](00_Overview.md) · [18. SNOL →](18_SNOL.md)
<!--/navtop-->



> Lean source: `Engine/PaymentLedger.lean` (5 theorems, standard axioms, no `sorry`).
> Numerical stress test: `tools/RESULTS_payment_budget.md`.

## Where we are

In chapter 16 we reduced the whole programme to a single typed hypothesis `H` and showed that it
runs verbatim into the parity wall: the conditional theorem `twin_finite_contradiction` ("finiteness
of twins together with `H` entails `False`") is assembled and machine-checked, but `H` itself — a
strict real four-corner plus a lower bound on the carrier — cannot be derived distribution-free from
the ideas at hand.

It is natural to ask: does the engine's halting have an *algebraic* price, one that can be presented
without any distribution? In this chapter we introduce such a price — the **payment law** — and prove
its core elementarily (only `Nat`/`Int` and `Finset`, no analysis and no sieve). At the same time we
honestly localize where this route meets the same wall once more.

The guiding intuition is this: when Euclid's engine halts — it *pays*, and the payment is governed by
a strict order. The boundary death `S → ⊥` is not free; every free passage to an ordered prime `p`
must deposit a divisibility **charge**, and if no such charge exists, a **compatibility tax** is paid.
The payment is spread over the small primes, and each of them has a finite **capacity**. Below we
make this picture precise.

## The channel law: exactly `p − 2` compatible channels

Let us fix the geometry. The centres of twin candidates lie in the class `6ℤ`, and the sides have the
form `6n ± 1`; we denote the signs by `ε, σ ∈ {+1, −1}`. The lift of a source `m` to an active prime `a`
through a boundary with parameter `n` is described by the linear relation

$$
6m + \sigma \;=\; a\,(6n + \varepsilon).
$$

Suppose a prime `p > 3` catches the opposite side of the boundary, that is, `p ∣ 6n − ε`. The question
is: in which residue class modulo `p` is the source `m` forced to lie?

> **Definition 17.1** (channel class). For given `a, ε, σ` and a prime `p`, a source `m` is called a
> *compatible channel modulo `p`* if the lift relation and the boundary condition
> `p ∣ 6n − ε` hold. By a channel we mean the admissible residue class `6m \bmod p`.

**Theorem 17.2** (`channel_residue`). If `p > 3`, `6m + σ = a(6n + ε)` and `p ∣ 6n − ε`, then

$$
6m \;\equiv\; 2a\varepsilon - \sigma \pmod p.
$$

The proof is pure CRT algebra. From `6n ≡ ε (mod p)` we get `6n + ε ≡ 2ε`, hence
`a(6n + ε) ≡ 2aε`; substituting `6m + σ = a(6n + ε)` gives `6m + σ ≡ 2aε`, that is,
`6m ≡ 2aε − σ`. In Lean this is exactly two identical ring rearrangements: first
`a(6n + ε) − 2aε = a(6n − ε)` (divisible by `p` by the boundary condition), then
`6m − (2aε − σ) = a(6n + ε) − 2aε`.

What this *means*. The class `6m` is not free — it is **pinned** to a single residue modulo `p`. So
out of the full set of residues a clean source may occupy not all of them, only the compatible ones.
The side itself and the class `0` (trivial divisibility by `p`) are excluded, and the count of
compatible channels comes out to exactly `p − 2` — precisely as many as the carrier holds
(cf. §13.1). In other words, a small prime `p` creates no crude capacity deficit: it has `p − 2`
channels, and there is *no* single-prime overflow of one `p`.

> **Note.** This is the chapter's first honest lesson: the naive hope that "the capacity of one prime
> will overflow and break the structure" is not confirmed numerically. `p` has exactly as many
> channels as are needed. The lever will have to be sought not in a single `p`, but in *joint
> compatibility across all the small `q` at once*.

## The tax law: the θ-dichotomy

Let us turn to the opposite side `6m − σ`. On it a small prime `q` may impose an *additional*
prohibition — a new excluded class — and that costs capacity. The key observation: this additional
prohibition sometimes **vanishes**, namely when it coincides with an already-forbidden class.

> **Definition 17.3** (the shift θ). We set `θ := σε`. A passage through `q` is called *tax-free* if the
> additional prohibition modulo `q` on the side `6m − σ` coincides with a previously excluded class,
> that is, takes away no new capacity.

**Theorem 17.4** (`no_tax_iff_shifted`). Tax-freedom at `q` is equivalent to divisibility of the shift:

$$
q \mid a - \theta \quad\Longleftrightarrow\quad a \equiv \theta \pmod q.
$$

Formally, in Lean this is the identity `Int.modEq_iff_dvd` together with `dvd_sub_comm`: `q ∣ a − θ`
is exactly `a ≡ θ [ZMOD q]`. Substantively the dichotomy reads as follows:

$$
\text{tax at } q \;=\;
\begin{cases}
0, & q \mid a - \theta \quad(\text{compatible, the shift divides}),\\[4pt]
\dfrac{q-3}{q-2}, & q \nmid a - \theta \quad(\text{a new prohibition, capacity drops}).
\end{cases}
\tag{17.1}
$$

The factor `(q-3)/(q-2)` is the fraction of surviving capacity after the additional prohibition
strikes one more out of the `q − 2` compatible channels. Thus the payment law acquires an **exact
price**: for every small prime `q` at which the active `a` is *not* aligned with the shift `θ`, the
engine pays by a factor of `(q-3)/(q-2)`.

> **Note.** The dichotomy is deterministic and algebraic: there is no distribution here yet.
> "Free" happens only when `q ∣ a − θ`; in all other cases — a fixed tax. This is the formal
> rendering of the thesis "payment is not free" at the level of a single prime.

## The primorial divides the shift

Let us gather the tax-free primes together. Let `G` be the set of small primes at each of which the
passage is tax-free. Then all the divisibilities `q ∣ a − θ` add up, and — since distinct primes are
pairwise coprime — their product divides the shift as well.

> **Definition 17.5** (primorial over `G`). For a finite set of pairwise coprime `q` we write
> `P := \prod_{q \in G} q`. This is the primorial (product) of the small primes at which the passage
> is tax-free.

**Theorem 17.6** (`primorial_dvd_shift`). If `(G).Pairwise Nat.Coprime` and `∀ q ∈ G, q ∣ a − θ`, then

$$
\Bigl(\prod_{q \in G} q\Bigr) \;\Bigm|\; a - \theta.
$$

The proof is `Finset.prod_dvd_of_coprime`: the product of pairwise coprime divisors of a common
argument divides that argument (divisibilities combine as an lcm, and for coprime numbers the lcm
coincides with the product). Coprimality of the `q` over `ℤ` is transported from `Nat.Coprime` via
`isCoprime.intCast`.

*Why* this matters. The individual taxes were cheap and local; but their *absence* at many `q` at
once is not free — it imposes a **global** divisibility condition on the shift: the entire primorial
of the tax-free primes must divide `a − θ`. Joint compatibility across all `q < p` is the true lever,
not the capacity of a single prime.

## The defect law

Now the primorial comes into conflict with the size of the active prime. A divisor cannot exceed a
nonzero dividend — whence a hard lower bound on the difference.

**Theorem 17.7** (`shifted_primorial_bound`). If `P ∣ a − θ` and `a ≠ θ`, then

$$
P \;\le\; |a - \theta|.
$$

Proof: from `a ≠ θ` it follows that `a − θ ≠ 0`, hence `|a − θ| > 0`; then `Int.le_of_dvd` together
with `dvd_abs` gives `P ≤ |a − θ|`. This is the **defect law** in its exact form.

The meaning is direct and strong. A free passage to an ordered prime `p` requires tax-freedom at all
the smaller small primes, and therefore — that `a − θ` is divisible by the *entire primorial* `P_{<p}`
of the small primes below `p`. But then either `a = θ` (the trivial, degenerate case), or the
primorial is bounded by the active divisor: `P_{<p} \le |a - θ|`.

**Conclusion.** As soon as the primorial outgrows the active divisor, there simply *is no*
nontrivial tax-free passage.

> **Definition 17.8** (the threshold `Y_A`). Let `Z` be the upper bound on the active divisor at scale `A`
> (`|a − θ| ≤ Z`). The threshold `Y_A` is the smallest prime `p` for which the primorial of the small
> primes below `p` exceeds `Z`, that is, `P_{<p} > Z`. For `p ≥ Y_A` a free passage requires
> `a = θ`.

**Theorem 17.9** (`late_boundary_not_free`). If `P ∣ a − θ`, `|a − θ| ≤ Z` and `Z < P`, then `a = θ`.

This is the contrapositive of the defect law: assuming `a ≠ θ`, from Theorem 17.7 (`shifted_primorial_bound`) we get
`P ≤ |a − θ| ≤ Z < P` — a contradiction (closed in Lean by `omega`). Hence a **late boundary is not
free**: beyond the threshold `Y_A` there is no nontrivial `a ≤ Z` divisible by the primorial, and so
a tax-free (free) passage to a late `p` is impossible.

> **Note.** Numerically (`tools/RESULTS_payment_budget.md` and the accompanying audit) the threshold
> arrives early: `Y_A / A ≈ 0.15\text{–}0.6`, and this fraction **drops** as the scale grows. That is,
> free late boundaries are almost nonexistent — the primorial of the small primes overtakes the
> active divisor, and the defect law bites for the overwhelming majority of late `p`.

## Where the capacity overflows — and where the wall is

The assembled core — five proven theorems — gives a deterministic, purely algebraic form of the thesis
"payment is not free": `channel_residue`, `no_tax_iff_shifted`, `primorial_dvd_shift`,
`shifted_primorial_bound`, `late_boundary_not_free`. The honest question: does this close the
programme?

No — and it is important to understand *why*. There is no crude overflow of a single prime: `p` has
exactly `p − 2` channels, just like the carrier. The real lever is joint compatibility across **all**
`q < p`, that is, the shifted primorial, and it drives everything into a single quantitative
question: how many active `a \le A^\kappa` have a *large* shifted gcd `\gcd(a - \theta,\, P_{<p})`?
The harness stress test gives an unpleasant answer:

| `D` | `A=70, p=29` | `A=130, p=31` | `A=240, p=37` |
|---|---|---|---|
| `p²` | 0.031 | 0.074 | **0.128** |
| 1000 | 0.027 | 0.074 | 0.147 |
| 100 | 0.099 | 0.262 | 0.526 |

The fraction `\mathrm{frac}(\gcd \ge p^2)` *grows* with the scale (3% → 7% → 13%). The two budgets —
shifted-charge and tax — pull in opposite directions and **do not close simultaneously**
distribution-free:

- if the shifted-charge is small (a large threshold `D` is needed), then the "tax" part `\gcd < D` is
  almost everything, but its capacity is lost only as

  $$
  \prod_{q \le A} \frac{q-2}{q-1} \;\sim\; \frac{1}{\ln A}
  \tag{17.2}
  $$

  (Mertens: divergence of `\sum 1/q`) — that is, the total capacity loss over the small primes is
  vanishingly slow;
- if the tax is small (small `D`), then the shifted-charge is `\ge 13\%` and keeps growing.

**Section takeaway.** There is no `D = D(A)` for which *both* budgets are simultaneously `o(|S_0|)`
without appealing to distribution.

> **Conjecture 17.10** (the payment route's single open input). There exists a function `D(A)` for which
> both the shifted-charge and the tax simultaneously amount to `o(|S_0|)` on a real interval at
> scale `A`. "Input" here is in the house sense: an honestly named unproven gate statement
> (see the [glossary](GLOSSARY.md)).
>
> **Closure plan.** What is required is a correlation of the shift `a - θ` with the primorial `P_{<p}`
> *stronger than average*: one must show that the fraction of active `a` with a large shifted gcd is
> small not on average, but on the concrete Euclidean set `S_0`. This is exactly the **distribution of
> the shift's divisors** — the territory of Brun/Selberg (the sieve) and of controlling the remainder
> on a real interval (Bombieri–Vinogradov). That is, the red parity line, not elementary algebra.
>
> We do *not* pass this reduction off as a proof: the total capacity loss `\sim 1/\ln A` (Mertens) is
> a wall, and it cannot be broken through distribution-free.

## Summary and the bridge to chapter 18

The algebra of payment is the best form to date of the thesis "payment is not free": deterministic,
algebraic, mostly *proven* (five theorems under standard axioms). It does *not* bypass the parity
wall, but it **maps it precisely**: the single distributional input is isolated into one scalar
`D(A)` — the balance of shifted-charge against tax. The defect law is fixed once and for all; the
quantitative budget remains an explicit open input — like `H` for the four-corner of chapter 16, it
is the same parity wall, but from a more algebraic angle.

Hence the natural next step. If the counting balance `D(A)` runs into Mertens, then perhaps victory
lies not in *counting*, but in the **structure of the pedigree** of the active prime — in the fact
that `a` arrived from the descent of a wedge centre rather than being taken at random.

In chapter 18 we make exactly this strategic shift: via rank descent (the rank is the "height" of a
state, strictly dropping along permitted steps; see the [glossary](GLOSSARY.md)) all product-state
defects are reduced to rank-1, and rank-1 — to a single SNOL lemma, **non-counting by construction**,
about the terminal shifted neighbour `p \mid a - 2\varepsilon`. Where the payment route secretly
called for distribution, SNOL *forbids* it and demands a Euclidean pedigree of `a`.

<!--navbot-->

---

[← 16. By contradiction](16_FiniteContradiction.md) · [Table of contents](00_Overview.md) · [18. SNOL →](18_SNOL.md)
<!--/navbot-->
