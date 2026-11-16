# LPP

Lean formalizations of last-passage percolation and related probability.

This repository collects formalizations from multiple papers and projects. The catalogue below records the current coverage and will grow as further results are completed.

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

**Certified** links to a released Lean proof. Each **Restricted** entry names its limitation and links to a comparison of the paper's claim, the certified part and the remaining gap. **Not assessed** means that the full certificate correspondence has not been checked. Supporting lemmas are included in each paper's progress list.

“Restricted” compares mathematical scope with the paper. Each entry explains the proof's scope and its effect on the main results. For example, a **Planar case only** entry covers the full two-dimensional result, while the paper also treats higher dimensions.

The maps follow results in the papers, rather than the organization of the code. Proof replacements chosen to simplify formalization are recorded separately from missing results and corrections to the text.

[LPP notation and conventions](docs/notation.md) · [Building the library](#build-and-checks)

<details>
<summary>About this documentation and its coverage</summary>

The certificate links describe formalization release [`5a3c7a6`](https://github.com/cjanjigi/LPP/tree/5a3c7a612144b68468559ea1800bf7f39a5d3ef1). Later development results are not counted. The guides distinguish paper statements from formalization extensions and assess only the certificate coverage explicitly listed. This documentation update adds no new Lean results.

</details>

The guides, dependency graphs and coverage notes are readable directly on GitHub. The interactive viewer remains a local preview while hosting is deferred. See the [graph instructions](docs/README.md#interactive-graphs) and [documentation style](STYLE.md).

## Guarantees and limits

The main results have Lean proofs whose axiom dependencies are `propext`, `Classical.choice` and `Quot.sound`. Each theorem has a version using the paper's definitions and a proved equivalence to its more literal formulation. This does not replace mathematical review of those definitions or the correspondence with the papers.

Challenge modules contain deliberate `sorry` proof holes. Solution modules supply proofs of the corresponding statements and must not depend on the Challenge modules. The holes are exercises for comparison, and are excluded from claims about completed proofs. No other proof holes are authorized.

Work on names, repeated definitions and proof presentation continues. The [CI workflow](.github/workflows/ci.yml) runs the build, source guards, statement and axiom comparisons, kernel replay and Nanoda-backed comparator audits. See [GitHub Actions](https://github.com/cjanjigi/LPP/actions/workflows/ci.yml) for the results for each revision. Structural checks and printed type comparisons are separate from kernel replay and independent checking by Nanoda.

## Build and checks

The Lake package is named `LastPassagePercolation`. Its library entry points are listed below.

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

Check both Lean exit codes before accepting the comparison. This also audits the axioms of each configured Solution theorem. Repeat with the other comparator configurations.

To inspect a theorem's axioms, create a temporary Lean file importing its statement module and containing, for example:

```lean
import Differentiability.Statements

#print axioms LPPStatements.Differentiability.shape_exists_unique_and_differentiable
```

Run it with `lake env lean "${probe_flags[@]}" /absolute/path/to/the/file.lean`. Repeat for all advertised results when auditing a release. A build alone is not an axiom audit.

The full automated suite runs on Linux with `bubblewrap` and the pinned toolchain's bundled checkers available on `PATH`:

```sh
node scripts/run-audits.mjs
```

It discovers every `comparator/*/comparator.json`, checks both probe exit codes before comparing their output, and runs `lake comparator` with Nanoda enabled for each configuration. Kernel replay checks all tracked project modules: proof modules are imported together and replayed in a fresh environment; the deliberate Challenge modules are replayed separately. The build rejects warnings other than the configured Challenges' deliberate `sorry` warnings. Logs and command exit codes are retained as private CI artifacts. `node --test scripts/run-audits.test.mjs` tests the audit runner without compiling Lean.

This follows Scott Armstrong's [build](https://github.com/scottnarmstrong/MarkovProcess/blob/main/.github/workflows/build.yml) and [comparator](https://github.com/scottnarmstrong/MarkovProcess/blob/main/.github/workflows/comparator.yml) checks for *MarkovProcess* and the [kernel-replay design](https://github.com/scottnarmstrong/KAM-dev/blob/main/scripts/kernel_replay.sh) in *KAM-dev*. The checker and exporter here come from the pinned Lean toolchain.

The current release is organized into `ProbabilityBasics/` for general probability, `LPP_Foundations/` for directed percolation models, `Martin2004/` for shape results and `Differentiability/` for the differentiability theorem. Its statement entry points are `ProbabilityBasics.Statements`, `LPP_Foundations.Statements`, `Martin2004.Statements` and `Differentiability.Statements`. Module placement does not change theorem namespaces. Comparator descriptions live in `comparator/`.

## Sources and formalization guides

The [paper guides](docs/README.md) state the certified results and record coverage limits, formulation choices, source corrections and changes of proof. They distinguish changes of proof from restrictions on the certified results. The [common notation page](docs/notation.md) fixes the model and path conventions.

## How this was made

Christopher Janjigian directed the formalization with coding assistants. Human decisions determined the intended mathematical statements and changes of proof; separate reviews compared statements and proof structure with their sources. The Lean kernel checks the resulting proof terms. Those roles give different kinds of evidence and should be assessed separately.

## License and citation

Project code is released under Apache 2.0; see `LICENSE`. Dependencies retain their own licenses. The code license does not grant rights to the cited manuscripts, papers or books. Cite the mathematical sources as well as this software; machine-readable software authorship is in `CITATION.cff`.
