# The article (arXiv preprint), English & Russian

Two identical editions of a single scholarly article compiling the machine-verified
*Euclid's-path* programme:

- `euclids-path.en.tex` — English edition (the arXiv face).
- `euclids-path.ru.tex` — Russian edition (identical content, numbering, and figures).

Both share `macros.tex` (packages, theorem environments, notation, honesty-status macros),
`refs.bib` (bibliography), and the figures in `figures/`. The body is split into
`sections/NN-name.{en,ru}.tex`; each theorem carries the name of the corresponding
machine-verified Lean declaration.

## Build

Compile with `pdflatex` (Cyrillic in the Russian edition uses `fontenc[T2A]` + `babel[russian]`,
both bundled in standard TeX Live):

```sh
# English edition
pdflatex euclids-path.en && bibtex euclids-path.en && pdflatex euclids-path.en && pdflatex euclids-path.en
# Russian edition
pdflatex euclids-path.ru && bibtex euclids-path.ru && pdflatex euclids-path.ru && pdflatex euclids-path.ru
```

or, with `latexmk`:

```sh
latexmk -pdf euclids-path.en.tex
latexmk -pdf euclids-path.ru.tex
```

## Relation to the repository

This paper is a reflection of the Lean 4 source in the parent directory. Nothing here is proved
that is not proved there. The honesty invariants (single axiom `step00FirstCause`, single `sorry`
`twin_prime_conjecture`, the axiom-taint count) are checked by
`../scripts/VerifyAll.lean`; the same content is published as a bilingual site
(`../mkdocs.yml`) at <https://elamaunt.github.io/Euclids-path/>.
