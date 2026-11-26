# Differentiability of the shape function in the planar corner growth model

**Christopher Janjigian, Firas Rassoul-Agha and Timo Seppäläinen**<br>
[arXiv:2611.33433](https://arxiv.org/abs/2611.33433) (2026). This guide follows the author draft of 23 November 2026.

[**Interactive dependency graph**](https://cjanjigi.github.io/LPP/?paper=differentiability) · [Static graph and coverage notes](../graphs/paper-results/differentiability.md)

[All papers](../../README.md) · [Common LPP notation](../notation.md) · [Source record](../../sources/current-differentiability.json) · [Paper map](../differentiability-paper-map.json) · [Source review](../reviews/differentiability-final.md)

The limit shape gives the leading-order passage time over long distances.
The main theorem rules out corners of the shape at every interior
direction under separate moment assumptions on the positive and negative
parts of the weights. The flat-top theorem classifies the directions at
which the shape reaches the largest possible weight.

## Main theorem

**Differentiability of the shape** (`thm:main`).
Let the real site weights be i.i.d. with law $`\mu`$.

- **A1.** The law is nondegenerate, so $`\mu(\{c\})\lt 1`$ for every real $`c`$.
- **A2.** There is a real $`p_-\gt 1`$ with $`\mathbb E[(\omega_0^-)^{p_-}]\lt\infty`$.
- **A3.** There is a real $`p_+\gt 4`$ with $`\mathbb E[(\omega_0^+)^{p_+}]\lt\infty`$.

The hypotheses allow signed, unbounded and atomic weights. A path
collects its starting vertex and excludes its terminal vertex, and
$`L_{u,v}`$ is the maximum over the admissible paths. The fixed-direction
limits define the deterministic shape.

```math
g(x)=\lim_{n\to\infty}\frac{L_{0,\lfloor nx\rfloor}}n,
\qquad x\in\mathbb R_{\geq 0}^2.
```

The shape is finite, continuous on the closed quadrant, positively
homogeneous of degree one and concave. It satisfies the almost-sure
[uniform shape approximation](../notation.md#uniform-shape-approximation)
and is differentiable at every direction in $`\textup{ri}\,\mathcal U`$,
equivalently at every point of the open quadrant.

The Lean statement `LPPStatements.Differentiability.shape_differentiable_on_unit_segment`
takes the shape supplied by the shape theorem, and
`shape_exists_unique_and_differentiable` also constructs it uniquely.
Use `import Differentiability.Paper` for the paper-ordered library and
`import Differentiability.Statements` for the main statement forms.
[Statements](../../Differentiability/Statements.lean) · [Assembled proof](../../Differentiability/Full/Differentiability.lean)

### Reading the Lean statements

Several definitions name the recurring objects used in the proofs. [`Path.reaches_stage_cut`](../../Differentiability/Model/Paths/StageCuts.lean) tests whether the path segment from index `k` to `l` reaches either the stage-length or transverse cutoff. The first-cut theorem chooses the least qualifying `l`. [`finiteThresholdMaskCube`](../../Differentiability/Probability/FiniteBadMaskLaw.lean) records a finite pattern of sites below the threshold. Equality at the threshold belongs to the good half-line. [`restrictedPathMarkedCountMaximum`](../../Differentiability/Probability/RestrictedPathMaximum.lean) is the maximum number of marked sites collected by a path confined to a finite region, with the terminal site excluded.

The public event definitions make the proof interfaces easy to locate. [`travelPathEvent`](../../Differentiability/Probability/Travel.lean) asks for a near-optimal path close to one segment. [`levelIntervalConnectionEvent`](../../Differentiability/Probability/GeneralIntervals.lean) asks for such a connection for every eligible endpoint pair. [`boundedGridConnectionEvent`](../../Differentiability/Probability/GridSimultaneous.lean) supplies one path for every eligible pair in the bounded grid, satisfying both support bounds and the confinement bound.

## Where the shape reaches the top weight

**Flat-top theorem** (`thm:flat-top`).
Assume a nondegenerate law with a finite support top $`M`$ and the
negative moment in A2. On the same environment take the indicator
weights $`\mathbf1\{\omega_x=M\}`$, with shape $`g_{\mathrm{top}}`$.
Let $`p_1=\mu(\{M\})`$ and let $`p_c`$ be the critical density of
oriented site percolation. Define
$`\mathcal U_{\mathrm{perc}}=\{\xi\in\mathcal U:g_{\mathrm{top}}(\xi)=1\}`$.
Then $`\mathcal U_{\mathrm{perc}}=\{\xi\in\mathcal U:g(\xi)=M\}`$,
and $`g(\xi)\lt M`$ at every other unit direction.

| Density | Flat set and differentiability |
| --- | --- |
| $`p_1\lt p_c`$ | $`\mathcal U_{\mathrm{perc}}=\varnothing`$. |
| $`p_1=p_c`$ | $`\mathcal U_{\mathrm{perc}}=\{(1/2,1/2)\}`$ and $`g`$ is differentiable there. |
| $`p_1\gt p_c`$ | The actual origin cluster survives with positive probability. On survival, the first coordinate of its rightmost site at level $`n`$ divided by $`n`$ tends almost surely to $`\beta\in(1/2,1)`$. The flat set is $`\{(t,1-t):1-\beta\leq t\leq\beta\}`$ and $`g`$ is differentiable at both endpoints. |

The sealed statement `LPPDifferentiability.FinalDraft.flat_top` uses the
actual origin-cluster speed and the expected passage rates of the
indicator weights. [Flat-top statement](../../Differentiability/Frozen/FinalDraft/FlatTop.lean) · [Oriented site percolation](../../Differentiability/Frozen/FinalDraft/CriticalDensity.lean)

## Shape facts and supporting lines

The shape comes from Theorem 5.1 and its weaker-negative-tail extension
in Remark 5.1(ii) of [*Limiting shape for directed percolation models*](martin-2004.md).
A3 gives the positive integrated square-root tail used here.
Translation gives the uniform shape law from signed starts and a
uniform probability bound for large displacements (S1–S2). The mean
bound is $`g(x)\geq \ell(x)\mathbb E\omega_0`$ (S3). On compact
subsets of the open quadrant the shape is Lipschitz, with the adapted
cone estimate used in the crossing bounds (S4). [Shape theorem](../../Martin2004/Probability/WeakNegativeShape.lean) · [Mean bound](../../Martin2004/Probability/ShapeAboveMean.lean) · [Lipschitz estimate](../../LPP_Foundations/Analysis/HomogeneousShapeLipschitz.lean)

**Supporting-line lemma** (`lem:contact`). The one-sided slopes
on the unit segment determine two linear upper bounds and their
signed first-order remainders. The difference between the average
upper bound and passage weight is sublinear on a maximizing path
toward the fixed direction. A positive gap between slopes forces a
strict loss at transverse exits. [Supporting lines](../../LPP_Foundations/Analysis/ShapeSupportingFunctionals.lean)

## Crossings and characteristic lengths

| Source result | Certificate scope |
| --- | --- |
| `lem:travel` | A common success probability for high-weight paths near a prescribed segment, uniform over the eligible deterministic endpoints. [Travel](../../Differentiability/Probability/Travel.lean) |
| `lem:intervals` | A common event supplies a connection for every pair of endpoints in the two intervals. [Bounded weights](../../Differentiability/Probability/BoundedIntervals.lean) · [General weights](../../Differentiability/Probability/GeneralIntervals.lean) |
| `prop:rarefast` | A rare-crossing bound uniform over lengths for paths whose weights exceed the prescribed linear support by the stated width-scaled amount. [Crossing bound](../../Differentiability/Probability/RareFastCrossings.lean) |
| `lem:kernel` | The maximum-resampling law gives domination, the finite product density, the squared density bound, and a positive boost on the stated set of weights. [Resampling](../../Differentiability/Probability/MaximumModifiedFieldLaw.lean) · [Density bound](../../Differentiability/Probability/MaximumKernelRN.lean) |
| `lem:tilt` | Off the flat set, the cubic-length crossing probability tends to zero at the prescribed threshold. [Tilt estimate](../../Differentiability/Probability/TiltLimit.lean) |
| `prop:charlength` | The first dyadic length meeting the crossing probability test has the stated lower growth and cubic upper bound. [Characteristic lengths](../../Differentiability/Probability/CharacteristicLengths.lean) |
| `lem:records` | Infinitely many record scales give the required comparison with earlier characteristic lengths. [Record scales](../../Differentiability/Analysis/RecordScales.lean) |

The crossing remarks cover the fixed-length limit, strips with arbitrary
real centers, and the shape-centered threshold when the length divided
by width diverges. [Fixed length](../../Differentiability/FinalDraft/TailConsequences/FixedLength.lean) · [Translation](../../Differentiability/FinalDraft/CrossingRemarks/Translation.lean) · [Shape threshold](../../Differentiability/FinalDraft/CrossingRemarks/ShapeThreshold.lean)

## Grid, endpoints and long paths

| Source result | Certificate scope |
| --- | --- |
| `lem:grid` | The bounded grid event and the four-part general grid event give the stated connections and probability bounds. The general event uses the actual characteristic and minimizing trial lengths and the eligible path clauses on both staircase sides. [Bounded grid](../../Differentiability/Probability/GridSimultaneous.lean) · [General grid](../../Differentiability/FinalDraft/Grid/GeneralTheorem.lean) |
| `prop:endpoints` | A rare-event bound for all eligible endpoints in the parallelogram, including the trimmed endpoints for general weights. [Bounded endpoints](../../Differentiability/Probability/ArbitraryEndpoints.lean) · [General endpoints](../../Differentiability/Probability/ArbitraryEndpointsGeneral.lean) |
| `lem:chunk-witness` | A path stage with no qualifying subpath satisfies the two linear bounds. A complete longitudinal stage satisfies the stronger weight loss. [Stage bounds](../../Differentiability/Model/Paths/WitnessFreeStage.lean) |
| `lem:multiplicity` | The finite family of pairwise disjoint qualifying subpaths attains its maximum size, which controls the stage weight. [Maximum](../../Differentiability/FinalDraft/WitnessMultiplicity/Maximum.lean) · [Weight bound](../../Differentiability/FinalDraft/WitnessMultiplicity/StageBounds.lean) |
| `prop:longpaths` | One almost-sure bound holds for the total witness count over all sufficiently long paths, with the final remainder included. [Long paths](../../Differentiability/FinalDraft/WitnessMultiplicity/LongPaths.lean) |
| `lem:fulldefect` | The full-stage and whole-path inequalities control the losses and witness penalties, including the last remainder. [Whole-path bound](../../Differentiability/FinalDraft/WitnessMultiplicity/TotalBounds.lean) |

The general grid remarks identify the selected finite staircase family,
its two path windows, capped crossing trials on the fixed centers and the
endpoint reduction on that same event. The main argument combines the
off-flat crossing bounds and the finite-rate top-count differentiability
result. [Selected paths](../../Differentiability/FinalDraft/SelectedGridPaths/Family.lean) · [Capped trials](../../Differentiability/FinalDraft/Grid/HeavyTrials.lean) · [Off-flat proof](../../Differentiability/Probability/GeneralOffFlatDifferentiability.lean)

## Tail assumptions and conditional estimates

- A finite horizontal passage limit for upper-bounded weights forces a
  finite negative first moment. The sparse example
  gives, for each prescribed negative moment order between zero and one,
  a nonpositive law with that finite moment, infinite negative first
  moment, and normalized passage liminf minus infinity along the
  specified sparse interior set. [Moment necessity](../../Differentiability/FinalDraft/SourceConsequences/NegativeMean.lean) · [Example](../../Differentiability/Probability/LowerTailExample.lean)
- The endpoint event gives the necessary positive tail limit.
  The conditional global cap retains the logarithmic factor at the
  printed cutoff. For the earlier-scale coarse cap, an eventual improved
  growth bound $`\Lambda_r\leq (2^r)^\gamma`$ on the actual first dyadic
  characteristic lengths is a premise on all sufficiently large
  indices. For $`p\gt2`$ and $`p\gt1+\gamma`$, it yields a vanishing
  cap failure bound and the success bound and mutual independence for
  the same capped trials. The little-o threshold for the general-aspect
  excess estimate describes the upper envelope. [Endpoint necessity](../../Differentiability/FinalDraft/TailConsequences/EndpointNecessity.lean) · [Global cap](../../Differentiability/FinalDraft/TailConsequences/GlobalHeavySites.lean) · [Coarse cap](../../Differentiability/FinalDraft/Grid/CoarseHeavyScaling.lean) · [Excess envelope](../../Differentiability/FinalDraft/ExcessScaling/Threshold.lean)
- Upper clipping gives the quantitative uniform shape comparison on the
  closed direction segment and differentiability at each cutoff,
  including a constant clipped law.
  A first-order remainder uniform over cutoffs implies differentiability
  of the original shape. Availability of a common modulus and improved
  characteristic growth remains open. [Shape comparison](../../Differentiability/FinalDraft/Truncation/Shape.lean) · [Fixed-cutoff result](../../Differentiability/FinalDraft/Truncation/Differentiability.lean) · [Conditional modulus](../../Differentiability/FinalDraft/Truncation/UniformModulus.lean)
- In a fixed-width strip, eventually every sufficiently long confined
  path from a fixed level has weight strictly below its length times
  the support top. The threshold holds on one almost-sure event
  for all signed start levels and may depend on the level. The proposed
  exponential lifetime in tilted strips and the KPZ and Flory scaling
  discussion are conjectural or heuristic. The symmetric-strip and
  contact-process results are cited background. [Fixed-width extinction](../../Differentiability/FinalDraft/SourceConsequences/FixedWidthStrip.lean)

## Appendices

| Source result | Certificate scope |
| --- | --- |
| `lem:contour` | For every finite connected signed-lattice set and marked site, the square contour has both quarter-perimeter label bounds, the ray and area bounds, and at most $`m\cdot3^{m-1}`$ rooted candidates of length $`m`$. [Contour](../../Differentiability/FinalDraft/Contour/Existence.lean) · [Count](../../Differentiability/FinalDraft/Contour/Count.lean) |
| `lem:oriented` | The contour of the actual finite reachable endpoint set gives positive survival at sufficiently high density. [Oriented survival](../../Differentiability/Probability/HighDensityOrientedPaths.lean) |
| `lem:bk` | The BK bound applies to finite families of real-weight paths with pairwise disjoint collected sites as certificates. [Path-event BK](../../Differentiability/Probability/PathEventBK.lean) |
| `lem:weights` | A lower-tail weight bound for every admissible finite path family selected measurably from the very-bad mask, at arbitrary lattice locations. [Family weights](../../Differentiability/Paper/PathFamilyWeights.lean) |
| `lem:intervals-general` | One common all-endpoint-pairs event with the general-weight attachments. [General intervals](../../Differentiability/Probability/GeneralIntervals.lean) |
| `lem:attach-general` | The forward and backward attachment bounds for every prescribed admissible net, with probabilities tending uniformly to one. [Prescribed nets](../../Differentiability/FinalDraft/Attachments/PrescribedProbability.lean) |
| `lem:stair-geometry` | Both reach tails and the deterministic geometry clauses on the same staircase event, at the printed exponent. [Staircase geometry](../../Differentiability/Probability/StairGeometryEvent.lean) |
| `lem:stair-general` | The weight estimate for actual finite mask-measurable staircase families under the source count and length bounds. [Staircase weights](../../Differentiability/Paper/StaircaseWeights.lean) |
| `lem:heavy` | The region and coarse caps, and success probabilities and mutual independence of the same fixed-center capped trials, under the source cubic bound. [Heavy trials](../../Differentiability/FinalDraft/Grid/HeavyTrials.lean) |
| `lem:multiplicity-general` | The excess-corrected stage and whole-path inequalities with the actual witness maxima and the distinct visited blocks. [Total bounds](../../Differentiability/FinalDraft/WitnessMultiplicity/TotalBounds.lean) |
| `lem:excess` | The real limsup bound for the attained maximum over the exact finite rooted radius-two family with the cubic fourth-moment estimate. [Animal maximum](../../Differentiability/FinalDraft/ExcessScaling/Maximum.lean) |

Appendix C gives the symbol glossary. The [paper map](../differentiability-paper-map.json)
locates the rigorous remarks, examples and proof statements, along with the
scope of cited background and research discussion. [Proof choices and source review](../reviews/differentiability-final.md)

<!-- PAPER_MAP_COMPACT -->
<!-- PAPER_MAP_START -->
## Progress and dependencies

[Interactive dependency graph](https://cjanjigi.github.io/LPP/?paper=differentiability) · [Static graph and coverage notes](../graphs/paper-results/differentiability.md)

The map follows the finalized paper and includes every named result, with certificate links and coverage notes for its remarks and examples.

<!-- PAPER_MAP_END -->
