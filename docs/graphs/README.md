# Paper dependency maps

The maps organize each paper's named results into sections. Expanding a section reveals the individual results and their formalization status. Selecting a result in the interactive viewer shows what it uses, what uses it, and links to the relevant Lean certificates.

Graph presentation based on Scott Armstrong’s visual paper design for [*Homogenization at a polynomial scale in high contrast*](https://scottnarmstrong.github.io/hcp-visual-paper/).

- [Differentiability of the shape function in the planar corner growth model](paper-results/differentiability.md)
- [Limiting shape for directed percolation models](paper-results/martin-2004.md)
- [Inequalities with applications to percolation and reliability](paper-results/bk-1985.md)
- [An improved subadditive ergodic theorem](paper-results/liggett-1985.md)

The GitHub version includes every result as a node in a Mermaid diagram, with an accompanying progress list. The [interactive viewer](../README.md#interactive-graphs) adds collapsible sections, search and a reading panel. Both use the same result records.

Dependencies come from the paper's proofs. Certificate links and their scope are assessed separately against release `5a3c7a6`. A certificate's inclusion of several conclusions does not create a dependency in the paper. Related formulations and proof adaptations are recorded separately from prerequisites. Results whose certificate correspondence has not been checked are marked **Not assessed**.

Source versions are identified in each guide. Public graph records identify named results and printed pages where available; source papers, manuscript files and development records are not included.
