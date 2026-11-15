# LPP

Lean formalizations of limit shapes, differentiability and their probability foundations in planar directed percolation.

Choose a paper below to read its main theorems, follow formalization progress, and see any changes to the written proofs. All guides use [the same LPP notation](docs/notation.md).

## Paper catalogue

| Paper and guide | Main certified theorems |
| --- | --- |
| **Differentiability of the shape function in the planar corner growth model**<br>Christopher Janjigian, Firas Rassoul-Agha and Timo Seppäläinen.<br>Preprint.<br>[Formalization guide](docs/guides/differentiability.md) | **Theorem 2.1.** Differentiability of the planar limit shape under the stated moment hypotheses. |
| **[Limiting shape for directed percolation models](https://doi.org/10.1214/009117904000000838)**<br>James B. Martin.<br>*The Annals of Probability* **32** (2004), 2908–2937.<br>[Formalization guide](docs/guides/martin-2004.md) | **Theorem 2.3.** Finite, continuous limit shape.<br>**Theorem 2.4.** Square-root boundary asymptotics.<br>**Corollary 2.5.** First-passage shape and boundary asymptotics.<br>**Theorem 5.1.** Last- and first-passage growth sets.<br>These certificates cover the planar case, under the hypotheses stated in the guide. |
| **[Inequalities with applications to percolation and reliability](https://doi.org/10.2307/3213860)**<br>J. van den Berg and H. Kesten.<br>*Journal of Applied Probability* **22** (1985), 556–569.<br>[Formalization guide](docs/guides/bk-1985.md) | **Theorem 3.3.** The BK inequality for increasing events under independent Bernoulli coordinates.<br>**Extensions.** Completed ordered-coordinate, finite-family and countable-coordinate versions are stated in the guide. |
| **[An improved subadditive ergodic theorem](https://doi.org/10.1214/aop/1176992811)**<br>Thomas M. Liggett.<br>*The Annals of Probability* **13** (1985), 1279–1285.<br>[Formalization guide](docs/guides/liggett-1985.md) | **Theorem 1.10.** The subadditive ergodic theorem, including its nonergodic conclusion, under Liggett's hypotheses. |

The guides also document certified auxiliary results, exact hypotheses, proof choices and coverage limits. The catalogue highlights the main theorems; it does not inventory every supporting lemma.

Mathlib supplies the underlying analysis and measure theory; the listed results are proved in this project.

## Progress key

**Certified** links to a released Lean proof. **Restricted** covers only the stated case or part. **Not assessed** means that this guide has not checked for a matching certificate. Supporting lemmas are included in each paper's progress list.

The maps follow results in the papers, rather than the organization of the code. Proof replacements chosen to simplify formalization are recorded separately from missing results and corrections to the text.

[LPP notation and conventions](docs/notation.md) · [Building the library](#build-and-checks)

<details>
<summary>About this documentation and its coverage</summary>

The certificate links describe formalization release [`5a3c7a6`](https://github.com/cjanjigi/LPP/tree/5a3c7a612144b68468559ea1800bf7f39a5d3ef1). Later development results are not counted. The guides distinguish paper statements from formalization extensions and assess only the certificate coverage explicitly listed. This documentation update adds no new Lean results.

</details>

The guides and full graphs render directly on GitHub. See the [interactive graph instructions](docs/README.md#interactive-graphs) and [documentation style](STYLE.md).

## Guarantees and limits

The main results have Lean proofs whose axiom dependencies are `propext`, `Classical.choice` and `Quot.sound`. Each theorem has a version using the paper's definitions and a proved equivalence to its more literal formulation. This does not replace mathematical review of those definitions or the correspondence with the papers.

Challenge modules contain deliberate `sorry` proof holes. Solution modules supply proofs of the corresponding statements and must not depend on the Challenge modules. The holes are exercises for comparison, and are excluded from claims about completed proofs. No other proof holes are authorized.

Work on names, repeated definitions and proof presentation continues. External comparator verification, including an independent kernel replay, has not yet been run. The supplied structural checker and Lean type comparison do not constitute that external verification.

## Build and checks

Install Elan and Node.js, then run from this directory:

```sh
lake exe cache get
lake build
node scripts/check-challenges.mjs
```

Validation environment: Node.js `v26.8.1` was used for the release-tool checks. This records the tested environment and does not set a minimum supported Node.js version. The pinned compiler is Lean `v4.35.0-rc2`. Mathlib is pinned to commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`; `lake-manifest.json` also pins its transitive dependencies. Keep these pins when reproducing the build. For each of BK, Liggett, Concentration, Martin2004 and Differentiability, generate and compile two separate probes, then compare their logs. For example:

```sh
work=$(mktemp -d)
config=comparator/Differentiability/comparator.json
node scripts/compare-challenge-types.mjs probe "$config" challenge "$work/challenge.lean"
node scripts/compare-challenge-types.mjs probe "$config" solution "$work/solution.lean"
probe_flags=(
  -DautoImplicit=false
  -DrelaxedAutoImplicit=false
  -Dlinter.unusedVariables=true
  -Dlinter.unusedSectionVars=true
  -Dlinter.unusedSimpArgs=true
  -Dlinter.unnecessarySimpa=true
  -Dlinter.deprecated=true
)
lake env lean "${probe_flags[@]}" "$work/challenge.lean" > "$work/challenge.log" 2>&1
lake env lean "${probe_flags[@]}" "$work/solution.lean" > "$work/solution.log" 2>&1
node scripts/compare-challenge-types.mjs compare "$config" "$work/challenge.log" "$work/solution.log"
```

Check both Lean exit codes before accepting the comparison. This also audits the axioms of each configured Solution theorem. Repeat with the other four comparator configurations.

To inspect a theorem's axioms, create a temporary Lean file importing its statement module and containing, for example:

```lean
import Differentiability.Statements

#print axioms LPPStatements.Differentiability.shape_exists_unique_and_differentiable
```

Run it with `lake env lean "${probe_flags[@]}" /absolute/path/to/the/file.lean`. Repeat for all advertised results when auditing a release. A build alone is not an axiom audit.

The four folders are `ProbabilityBasics/` for general probability, `LPP_Foundations/` for directed percolation models, `Martin2004/` for shape results and `Differentiability/` for the differentiability theorem. The statement entry points are `ProbabilityBasics.Statements`, `LPP_Foundations.Statements`, `Martin2004.Statements` and `Differentiability.Statements`. Module placement does not change theorem namespaces. Comparator descriptions live in `comparator/`.

## How the formalization relates to the manuscripts

The mathematical source for differentiability is C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the planar corner growth model*, preprint. Other inputs include Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), cited by statement name. Manuscript text and reading copies are not distributed here.

The formalization makes several changes to proofs and conventions. Weights live on a canonical product probability space. Shape functions are characterized by uniform lattice limits. The expected-rate existence argument uses a random phase to handle real directions. The boundary asymptotics use the central limit theorem with domination instead of a nonuniform Berry–Esseen estimate. The column-model comparison uses a direct stationary construction and a one-cell Burke identity. The concentration bound uses entropy tensorization and the Herbst argument instead of Talagrand's theorem; it yields the stronger bound `2 exp(−u²/(16 R L²))`. First-passage results are transferred through negation of the weights. The BK theorem is extended from Bernoulli coordinates to ordered coordinate spaces. These changes are part of the Lean proofs, rather than additional hypotheses replacing proof steps.

## How this was made

Christopher Janjigian directed the formalization with coding assistants. Human decisions determined the intended mathematical statements and changes of proof; separate reviews compared statements and proof structure with their sources. The Lean kernel checks the resulting proof terms. Those roles give different kinds of evidence and should be assessed separately.

## License and citation

Project code is released under Apache 2.0; see `LICENSE`. Dependencies retain their own licenses. The code license does not grant rights to the cited manuscripts, papers or books. Cite the mathematical sources as well as this software; machine-readable software authorship is in `CITATION.cff`.
