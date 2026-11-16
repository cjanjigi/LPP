# LPP documentation style

This file records the documentation conventions for LPP. Use it for the paper catalogue, formalization guides, shared notation and dependence graphs, including future additions. The documentation starts at the [paper catalogue](README.md). Record changes to these conventions here and apply them consistently across those documents.

## Organize around papers

- Describe LPP as a growing collection of formalizations in last-passage percolation and related probability. The current paper catalogue and package layout record released coverage, rather than defining the repository's permanent scope. Keep whole-repository descriptions distinct from the precise scope of individual papers and certificates.
- Group results by their source paper, rather than by development project or Lean module.
- Give every paper its full, proper title and author attribution, publication information or identified preprint version, and a link to its formalization guide. Use full paper titles in navigation and cross-paper references. Avoid vague labels such as “the differentiability project.”
- Focus the catalogue on the main theorem formalizations and their mathematical significance. Mention that supporting results are also formalized and can be found in the guides; do not turn the entrance page into one long theorem inventory.
- Use a common core page for LPP definitions and notation. Translate each paper's notation into this common notation, with a short explanation where conventions differ.

## Write for mathematical readers

Give context before detail. Put the paper's contribution and precise main theorem statements before its progress list and dependence graph. Describe auxiliary results briefly in original prose and link to their numbered locations in the paper and to their certificates. Do not reproduce a paper-wide inventory of statements, definitions or proofs in the graph pages or their reading panels. Include only the definitions needed to understand a short description or a coverage difference.

Omit detailed walkthroughs of proofs from the papers. Keep statements, mathematical context, exact certificate scope and brief factual records of deviations and their reasons. Dependency arrows may cite the source results without restating their arguments.

Use plain, specific prose. Edit jargon out of box titles and explanations; when a technical term is needed, define it. A label such as “defect,” “witness” or “coercivity” is not an explanation. State the relevant event, set, function or inequality in standard mathematical notation and define its symbols and parameters. Short box titles can lead to a panel containing the definitions and precise statement.

Keep headings short. Avoid long subtitles or explanatory phrases after a colon. Put the explanation in a separate sentence or paragraph. Preserve punctuation that belongs to a paper's actual title.

State mathematical claims precisely, including hypotheses, quantifiers, dimensions and parameter dependence. Make restrictions on signed, unbounded or atomic weights explicit where relevant. A summary should introduce a statement, not replace it with an undefined slogan. Keep reader-facing mathematics distinct from Lean names and internal proof organization.

## Maintain the common notation

The [notation page](docs/notation.md) gives the full definitions. The current conventions are:

| Object | Notation and convention |
| --- | --- |
| Nonnegative quadrant | $`\mathbb{R}_{\geq 0}^2`$, never an abbreviation $`Q`$. In genuinely general-dimensional statements, use $`\mathbb{R}_{\geq 0}^d`$. |
| Site weights and law | $`\omega_x`$, with common law $`\mu`$; probability $`\mathbb P`$ and expectation $`\mathbb E`$. |
| Positive and negative parts | $`\omega_x^+=\max\{\omega_x,0\}`$ and $`\omega_x^-=\max\{-\omega_x,0\}`$. |
| Level | $`\ell(x)=x_1+x_2`$. It agrees with $`\lVert x\rVert_1`$ in the nonnegative quadrant, but can be negative elsewhere. |
| Paths and weight | $`x_{m:n}`$ and $`W(x_{m:n})=\sum_{k=m}^{n-1}\omega_{x_k}`$. Include the starting weight and exclude the terminal weight. |
| Passage times | $`L_{u,v}`$ for the maximum path weight and $`S_{u,v}`$ for the minimum, using endpoints $`u,v`$. In particular, $`L_{u,u}=S_{u,u}=0`$. |
| Shapes | $`g`$ for last passage and $`h`$ for first passage. |
| Directions | $`\mathcal U=\{(t,1-t):0\le t\le1\}`$, with interior directions in $`\textup{ri}\,\mathcal U`$. |
| Mean and variance | $`m=\mathbb E\omega_0`$ and $`\sigma^2=\mathbb E[(\omega_0-m)^2]`$ when finite. Reserve $`\mu`$ for the weight law. |

Define the shape first by the deterministic fixed-direction almost-sure limits

```math
g(x)=\lim_{n\to\infty}\frac{L_{0,\lfloor nx\rfloor}}n,
\qquad x\in\mathbb{R}_{\geq 0}^2.
```

Existence, finiteness, continuity, homogeneity, concavity and uniform approximation are proved under their respective hypotheses. Uniform convergence is not part of the definition of the directional shape. Distinguish convergence for each fixed direction from a uniform bound on one common event of probability one.

When a Lean certificate packages several properties of the shape into one conclusion, explain it using this same limit-defined function. Packaging the properties is a representation choice, not by itself a mathematical deviation.

## Show the paper's argument and its progress

- Extract dependencies from the paper using the source-dependency workflow in the relevant lower project folder. Lean imports and certificate packaging do not determine the paper's graph.
- Every named result must be an individual graph node, including supporting results outside the closure of a selected main theorem. Include separately claimed remarks, extensions and examples, and identify explanatory remarks and historical questions accurately.
- Cluster results into sections or related blocks to reduce visual clutter. Blocks may collapse, but expanding them must reveal their individual results and statuses. Preserve independent branches and the distinction between proofs under different hypotheses.
- An arrow $`A\to B`$ means that $`A`$ is used to prove $`B`$. Retain source evidence for the use. Keep equivalent formulations and reuse of proof ideas distinct from prerequisite arrows.
- Let readers select a result to see a short description, necessary notation, prerequisites, later uses and certificate links. Keep precise main theorem statements in the guide. Show coverage for individual results; a mixed block must not appear wholly formalized.
- Credit Scott Armstrong's visual-paper design only in a short footnote below each interactive dependency viewer. Put the link to his visual paper in that footnote. Static diagrams, Markdown guides and graph indexes are ordinary dependency graphs and must not carry this design credit. Mathematical dependencies retain their source-paper references.

Use progress listings to help readers assess coverage. Keep the overall documentation tailored to this project.

## Describe coverage and deviations separately

Use the current status vocabulary consistently:

- **Certified** links to a released certificate for the stated scope.
- **Restricted** names the limitation in the progress list and gives a separate comparison of the paper's scope, the certified scope and the remaining gap. Every entry must explain why the checked proof has that scope and what this means for the main results. Describe the actual proof or hypothesis boundary; attribute a historical reason for choosing it only when documented.
- **Not in this release** requires evidence that the described release does not include the result.
- **Not assessed** means that the certificate correspondence has not been checked. It does not mean “unformalized.”

Pin certificate links to the release being described. Distinguish source statements from formalization extensions, and do not report whole-paper completion percentages without a complete inventory and checked coverage.

Record deviations from the printed argument and why they occurred. Keep separate entries for replacements of believed-correct proofs chosen to simplify formalization, changes of formulation or notation, corrections to the source, and results that have not been formalized. An alternative complete proof does not make its bypassed source lemmas missing parts of the certified theorem.

A different supporting declaration is not by itself a restriction. Check whether the complete released theorem or another released lemma covers the paper's mathematical conclusion under the same hypotheses. Explain such a correspondence explicitly. If the full correspondence has not been checked, mark it **Not assessed** and identify the part already verified; do not turn a missing interface into an asserted mathematical gap.

Check intermediate inequalities before treating a weaker final bound as a restriction. A sharper source estimate may already follow from checked components of the same proof. When that correspondence has been verified, link those components and explain the final bound as a formulation choice. Keep a verified correspondence distinct from adding a new standalone Lean theorem.

## Keep the documents usable

For upright function names in GitHub mathematics, use `\textup{...}`, such as `\textup{ri}` and `\textup{dist}`. Check GitHub’s Markdown output as well as the local preview; a successful local rendering does not establish GitHub compatibility.

Use GitHub's protected inline-math delimiters and fenced math blocks so Markdown does not consume TeX escapes or interpret subscripts as emphasis. Keep ordinary TeX in the graph data and apply this protection when generating Markdown.

Use Markdown and standard LaTeX mathematics that render natively on GitHub and remain useful when printed. The interactive graph adds collapsible sections, search and a reading panel; retain a GitHub-readable graph and progress list using the same records.

When interactive hosting is approved, make dependency-graph links open that viewer by default, with direct links for papers and selected results. Until then, link readers to the GitHub-readable diagrams and coverage notes. Publish only the viewer's explicit public file list if GitHub Pages hosting is later approved.

Interactive hosting is currently deferred. The written guides, coverage records and Markdown generators may be updated in the private repository when the author authorizes that push. Keep pending interactive-page assets and deployment changes local. Do not enable automatic publication. Approval to push written documentation to the private repository does not authorize a public graph website.

Format tables clearly, allow full words and titles to wrap, and avoid clipping or truncating their contents. Keep the main catalogue compact and put supporting detail in the guides. Prefer mathematical content and useful progress information over internal node counts, review bookkeeping or implementation details in the main reading path.
