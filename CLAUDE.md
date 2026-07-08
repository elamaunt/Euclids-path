# Euclids-path — working conventions

## Bilingual corpus: EN + RU are maintained together

This repository is bilingual. Both language versions are first-class and kept **in sync in the
same change** — never let them drift.

- **Prose.** Every chapter is a pair: `prose/NN_Name.md` (Russian — the site default) and
  `prose/NN_Name.en.md` (English). When you add or edit one, update its sibling in the same pass.
  A new chapter must be added to both, and to the `nav:` in `mkdocs.yml`.
- **README.** `README.md` is the English version (the repo's face); `README.ru.md` is the Russian
  copy. Both carry reciprocal 🇷🇺/🇬🇧 switcher headers and must stay consistent.
- **Tool docs.** Where an English sibling exists (e.g. `tools/README_twin_certify.en.md`), keep it
  in sync with the Russian original.
- **Site.** Published via MkDocs Material + `mkdocs-static-i18n` (suffix strategy `.en.md`, RU
  default with fallback). Navigation headings are translated under `nav_translations` in
  `mkdocs.yml`. Validate with `mkdocs build --strict` (both locales must build with no warnings).

## Prose is journal style (Tao / AMS level)

The prose is written so a researcher follows every result WITHOUT opening the Lean code, and is the
basis for a future LaTeX/arXiv compilation.

- **Numbered blocks.** Every Definition/Theorem/Lemma/Proposition/Corollary uses ONE shared counter
  per chapter, format `**Kind N.k** (descriptor).` — kind + number in bold, descriptor in parens
  after (the Lean name in backticks for theorems, a short title for definitions). N = chapter number.
- **Numbered equations.** Argument-carrying displays are tagged `\tag{N.k}` (a separate per-chapter
  counter), portable to LaTeX.
- **Cross-references** within a chapter cite the number AND the Lean name: "by Theorem N.2 (`name`)".
- **Figures** carry a `> **Generation algorithm (Figure N.k).**` block: the source function
  (`tools/fractal/*.py::function` path form), the construction as formulas, and parameters. Do NOT
  backtick non-Lean tokens (Python identifiers, colormap names) — the auditor reads decl-shaped
  backticks as Lean names and flags them as phantom.
- **Honesty in labels.** A badge must match the Lean status: 🟢 = machine-proved under standard
  axioms (INCLUDING a green conditional theorem whose condition is a named hypothesis); 🟡 =
  AXIOM-TAINTED (depends on `step00FirstCause`); 🔴 = open. Never badge an axiom-clean result 🟡.
- **Verification:** RU/EN numbering must match 1:1 (same N.k blocks, same equation tags); run the
  prose↔Lean audit (phantom/label/counter all 0) and `mkdocs build --strict` before committing.

## Code is always English

- All Lean code is English: comments, docstrings, identifiers, and the output string literals in
  `scripts/VerifyAll.lean`. **No Cyrillic in `.lean` files** — a repo-wide search must return zero.
- Git commit messages are in English.
- When translating comments, change **only** comment text — code must stay byte-for-byte identical
  (verify by stripping comments and diffing against HEAD). Never introduce a UTF-8 BOM.

## Consistency gates (keep green)

- `lake build` — the whole Engine line compiles (exit 0). A full rebuild can hit transient Windows
  file-sharing errors on mathlib `.olean.private`; just re-run.
- `lake env lean scripts/VerifyAll.lean` — self-checks the honesty invariants: a single non-standard
  axiom `step00FirstCause` (now decreeing ONLY the twin seriality boundary — Riemann/NS/Collatz were
  withdrawn, Option A), and a single `sorryAx`-tainted declaration `twin_prime_conjecture` (taint count
  is reported, currently 16 — all asserting twins — and is not hard-pinned).
- `python scripts/audit_prose.py --data <oracles> --root .` — prose↔Lean audit over the RU **and**
  EN corpus plus both READMEs (phantom names, label mismatches, taint counters). Must be CLEAN.
