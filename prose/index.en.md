# Euclid's Path

> A single impossibility — **Euclid's perpetual engine**, an infinite strictly-descending chain on a
> well-ordered line, which does not exist — read underneath eight masks and a whole
> arithmetic tail. One programme, one axiom, machine-checked in **Lean 4**.

We take the oldest proof object in mathematics — Fermat's infinite descent, rewritten
multiplicatively — and show that it is forbidden strictly, with no assumptions. Then we read one
problem after another through this single prohibition: twin primes, Riemann, P/NP, Yang–Mills,
Navier–Stokes, Hodge, Collatz, Birch–Swinnerton-Dyer. Everywhere the "deviation" from the norm turns
out to be a disguised perpetual engine — and the prohibition kills it.

No millennium problem is solved here. Something else is proven, and it may matter more: **they are all
one problem.**

## Honesty first

The programme rests on a cardinal discipline of honesty. Everything proven by machine under the
standard Lean/mathlib axioms is marked 🟢. Everything conditional on the repository's **single axiom**
`step00FirstCause` (the intentional event "0 → 1" with three causal boundaries) is marked 🟡 —
**AXIOM-TAINTED**, and a verifier recounts every such declaration on every build. Everything open is 🔴.

!!! note "Status legend"
    - 🟢 — machine-proven under the standard Lean/mathlib axioms;
    - 🟡 — **AXIOM-TAINTED**: conditional on the single axiom `step00FirstCause`;
    - 🔴 — an open node or a named entry point.

At build time: **exactly one** non-standard axiom, **47** declarations depending on it, **one**
remaining `sorry` (the target `twin_prime_conjecture` itself). Nothing leaks into the green line —
the verifier tracks each case.

## Where to start

- **[Programme glossary](GLOSSARY.md)** — all key notions in one list.
- **[Prologue and map](00_Overview.md)** — what is proven, what is decreed, what is open; the map of all parts.
- **[Euclid's engine (ch. 01)](01_EPMI.md)** — the prohibition itself: why no perpetual descent exists.
- **[First cause and the main theorem (ch. 33)](33_CausalFirstCause.md)** — why the node cannot be closed from within.
- **[Coda (ch. 50)](50_Coda.md)** — one prohibition, seven masks, and spacetime as its shadow.

Sources and machine verification are in the [GitHub repository](https://github.com/elamaunt/Euclids-path).

> **Bilingual.** The site is being prepared in two languages — Russian and English. The Russian
> version is the source; the English translation appears page by page, and until a page is translated
> it is shown in Russian.
