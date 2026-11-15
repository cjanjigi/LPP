# Formalization guides

[Paper catalogue and build instructions](../README.md) · [Common LPP notation](notation.md) · [Documentation style](../STYLE.md)

## Differentiability of the shape function in the planar corner growth model

Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.

[Formalization guide](guides/differentiability.md) · [Full result graph](graphs/paper-results/differentiability.md)

## Limiting shape for directed percolation models

James B. Martin.

[Formalization guide](guides/martin-2004.md) · [Full result graph](graphs/paper-results/martin-2004.md)

## Inequalities with applications to percolation and reliability

J. van den Berg, H. Kesten.

[Formalization guide](guides/bk-1985.md) · [Full result graph](graphs/paper-results/bk-1985.md)

## An improved subadditive ergodic theorem

Thomas M. Liggett.

[Formalization guide](guides/liggett-1985.md) · [Full result graph](graphs/paper-results/liggett-1985.md)

## Interactive graphs

The guides and full result graphs render directly on GitHub. The interactive viewer adds collapsible sections, search, result statements and certificate links.

From the repository root, run:

```sh
node scripts/serve-docs.mjs
```

Open the address printed by the command, normally `http://127.0.0.1:4173/`. Use the paper selector to choose a guide. The viewer uses the same result data as the Markdown graphs. Its mathematics and graph libraries load from jsDelivr. Stop the local server with Ctrl-C.

Graph presentation based on Scott Armstrong’s visual paper design for [*Homogenization at a polynomial scale in high contrast*](https://scottnarmstrong.github.io/hcp-visual-paper/).

## Updating the documentation

Follow [STYLE.md](../STYLE.md). Update result statements, source dependencies and certificate coverage in `docs/graphs/paper-results/*.json`, keeping those roles separate. Regenerate the graph sections and full maps from the repository root:

```sh
node scripts/render-doc-graphs.mjs
```

The generator preserves the mathematical prose outside the marked graph sections in each guide. Review all changed statements, scope descriptions and certificate links before publishing an update. Source papers, manuscript files and development records are not distributed with this library.
