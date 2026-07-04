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
  axiom `step00FirstCause`, and a single `sorryAx`-tainted declaration `twin_prime_conjecture`
  (taint count is reported, currently 47, and is not hard-pinned).
- `python scripts/audit_prose.py --data <oracles> --root .` — prose↔Lean audit over the RU **and**
  EN corpus plus both READMEs (phantom names, label mismatches, taint counters). Must be CLEAN.
