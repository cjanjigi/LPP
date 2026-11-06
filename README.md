# LPP

Lean formalizations of limit shapes, differentiability and their probability foundations in planar directed percolation.

## What is proved

For an iid real weight law that is not a point mass, with a negative-part moment of order greater than 1 and a positive-part moment of order greater than 4, the last-passage shape exists, is unique and is differentiable on the open quadrant. The exact hypotheses and conclusions are in the statement modules.

The seventeen main results are listed below. Names in the second column have prefix `LPPStatements.`.

| Source result | Lean theorem |
| --- | --- |
| Differentiability preprint, Theorem 2.1 | `Differentiability.shape_exists_unique_and_differentiable` |
| Martin (2004), Proposition 2.1 | `Martin2004.extendedShape_limits_of_finite_mean` |
| Martin (2004), Propositions 2.1–2.2 and Theorem 2.3 | `Martin2004.shape_continuous_of_finite_mean` |
| Martin (2004), Section 5.3, uniform shape theorem | `Martin2004.shape_function_exists_unique` |
| Martin (2004), Theorem 2.4 | `Martin2004.shape_boundary_asymptotics` |
| Martin (2004), Corollary 2.5(i) | `Martin2004.firstPassageShape_continuous` |
| Martin (2004), Corollary 2.5(ii) | `Martin2004.firstPassageShape_boundary_asymptotics` |
| Martin (2004), Theorem 5.1(i) | `Martin2004.lastPassage_growthSets_converge` |
| Martin (2004), Theorem 5.1(ii) | `Martin2004.firstPassage_growthSets_converge` |
| Martin (2004), Remark 5.1(i), first sentence | `Martin2004.taxicab_lower_bound_of_subadditive` |
| van den Berg and Kesten (1985), Theorem 3.3 | `BK.bk_inequality_bernoulli_cube` |
| Extension to finitely many ordered coordinates | `BK.bk_inequality` |
| Finite-family extension, finitely many coordinates | `BK.bk_inequality_family` |
| Extension to countably many ordered coordinates | `BK.bk_inequality_countable` |
| Finite-family extension, countably many coordinates | `BK.bk_inequality_family_countable` |
| Liggett (1985), Theorem 1.10 | `Liggett.subadditive_ergodic_theorem` |
| Martin (2004), Lemma 3.1 | `Concentration.concentration_of_max_of_sums` |

The Martin shape results concern dimension two. The BK extensions concern increasing events with the precise measurability and order hypotheses in the statements. Mathlib supplies the underlying analysis and measure theory; the results above are proved in this project.

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
