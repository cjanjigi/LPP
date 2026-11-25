# Formalization guides

[Paper catalogue and build instructions](../README.md) · [Common LPP notation](notation.md)

These guides document the collection's current paper coverage.

## Strong existence and uniqueness of the tilt-indexed Busemann process in the planar corner growth model

Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.

[*Electronic Journal of Probability* **31** (2026), 1–35](https://doi.org/10.1214/26-EJP1634).

[Formalization guide](guides/strong-existence.md) · [Interactive dependency graph](https://cjanjigi.github.io/LPP/?paper=strong-existence) · [Static graph and coverage notes](graphs/paper-results/strong-existence.md)

## Busemann functions and Gibbs measures in directed polymer models on ℤ²

Christopher Janjigian and Firas Rassoul-Agha.

[Formalization guide](guides/busemann-functions-and-gibbs-measures.md)

## Differentiability of the shape function in the planar corner growth model

Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.

[Formalization guide](guides/differentiability.md) · [Interactive dependency graph](https://cjanjigi.github.io/LPP/?paper=differentiability) · [Static graph and coverage notes](graphs/paper-results/differentiability.md)

## Limiting shape for directed percolation models

James B. Martin.

[Formalization guide](guides/martin-2004.md) · [Interactive dependency graph](https://cjanjigi.github.io/LPP/?paper=martin-2004) · [Static graph and coverage notes](graphs/paper-results/martin-2004.md)

## Inequalities with applications to percolation and reliability

J. van den Berg, H. Kesten.

[Formalization guide](guides/bk-1985.md) · [Interactive dependency graph](https://cjanjigi.github.io/LPP/?paper=bk-1985) · [Static graph and coverage notes](graphs/paper-results/bk-1985.md)

## An improved subadditive ergodic theorem

Thomas M. Liggett.

[Formalization guide](guides/liggett-1985.md) · [Interactive dependency graph](https://cjanjigi.github.io/LPP/?paper=liggett-1985) · [Static graph and coverage notes](graphs/paper-results/liggett-1985.md)

## Interactive graphs

Each paper's interactive graph is hosted publicly. The Markdown maps and coverage notes remain available directly in this repository.

### Local preview

To preview the interactive maps from a local checkout, run from the repository root:

```sh
node scripts/serve-docs.mjs
```

Open the address printed by the command, normally `http://127.0.0.1:4173/`. Use the paper selector to choose a guide. The viewer uses the same result data as the Markdown graphs. Its mathematics and graph libraries load from jsDelivr. Stop the local server with Ctrl-C.
