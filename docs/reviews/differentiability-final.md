# Source review of the 23 November 2026 differentiability draft

[Formalization guide](../guides/differentiability.md) · [Source record](../../sources/current-differentiability.json) · [Paper map](../differentiability-paper-map.json)

The selected draft has SHA-256
`6d9253d4c96cc82686afa9944c0e3299bac6ef65d9c9c682a4137edec81db3b6`.
The paper is available as [arXiv:2611.33433](https://arxiv.org/abs/2611.33433).
This review used the author-supplied TeX draft identified above. The independent source and
quality reviews passed for the 27 named results and the rigorous
supporting claims. The map gives the statement ranges, 58 unnumbered
proof entries, and the 21 active remark and example environments.
Its status fields identify proofs, checked compositions and conditional
claims at their stated scopes.

## Source correspondence

| Source area | Correspondence checked |
| --- | --- |
| Shape facts | The model uses the actual i.i.d. law, signed lattice starts, and path weights that exclude the terminal vertex. The mean bound follows the fixed-path strong law and extends by homogeneity and continuity. [Shape facts](../../LPP_Foundations/Statements/ShapeDefinitions.lean) · [Mean bound](../../Martin2004/Probability/ShapeAboveMean.lean) |
| Crossings, scales and the grid | The characteristic lengths and minimizing trial lengths refer to the same tests used for the record comparison. Both grid formulations identify the actual events and path clauses, including the selected staircase and capped trial family for general weights. [Characteristic lengths](../../Differentiability/Probability/CharacteristicLengths.lean) · [General grid](../../Differentiability/FinalDraft/Grid/GeneralTheorem.lean) |
| Stage and path bounds | The finite stage maximum represents the source's pairwise disjoint witness count, including the final remainder. The real maximum in the animal bound attains the same block sum on the specified finite rooted family. [Witness maxima](../../Differentiability/FinalDraft/WitnessMultiplicity/Maximum.lean) · [Animal maximum](../../Differentiability/FinalDraft/ExcessScaling/Maximum.lean) |
| Appendices | The high-density survival proof uses the current square contour on the actual endpoint cluster. The attachment theorem accepts prescribed nets. The staircase and capped-trial results use the exact geometry, selected paths and event families. [Oriented survival](../../Differentiability/Probability/HighDensityOrientedPaths.lean) · [Prescribed attachments](../../Differentiability/FinalDraft/Attachments/PrescribedProbability.lean) · [Capped trials](../../Differentiability/FinalDraft/Grid/HeavyTrials.lean) |

## Flat-top classification

The frozen flat-top proof applies the classification to the normalized
original law and the top-indicator law. Its supercritical conclusion uses
the survival probability and speed of the actual origin cluster.
It proves the strict complement of the flat set and differentiability
at the endpoints in the stated scope. The four current-draft frozen
anchors are sealed.

- [Oriented site survival](../../Differentiability/Frozen/FinalDraft/SiteSurvival.lean)
- [Critical density](../../Differentiability/Frozen/FinalDraft/CriticalDensity.lean)
- [Origin-cluster right-edge speed](../../Differentiability/Frozen/FinalDraft/OriginRightEdgeSpeed.lean)
- [Flat-top theorem](../../Differentiability/Frozen/FinalDraft/FlatTop.lean)

The previously released frozen main theorem retains its statement.
Its proof uses the approved finite-rate top-count differentiability
result in the flat branch. The separate flat-top theorem gives the
current classification. [Main theorem](../../Differentiability/Frozen/Main/Differentiability.lean)

## Proof choices

- The equivalence between the open-quadrant and unit-segment
  formulations uses a direct argument for degree-one homogeneous
  functions. The canonical product space represents the i.i.d. law,
  and the formal shape predicate collects the proved regularity and
  uniform approximation properties. [Normalization](../../Differentiability/Paper/Setting.lean) · [Statements](../../Differentiability/Statements.lean)
- The shape input uses Martin's weaker-negative-tail extension.
  The positive moment in A3 gives the corresponding integrated
  square-root upper-tail condition. [Shape theorem](../../Martin2004/Probability/WeakNegativeShape.lean)
- The real-weight path BK proof uses the approved countable-product
  discretization and collected-site certificates. This proves the
  finite-family inequality at the same strict weight thresholds as the
  source. [Path-event BK](../../Differentiability/Probability/PathEventBK.lean)
- In Durrett (1984), Section 3, the calculation following display (14)
  uses the outer complement. The formalization follows that calculation
  in the density comparison. The differentiability draft also corrects
  an earlier sign in the supporting-line remainder. [Density comparison](../../Differentiability/FinalDraft/FlatDensitySource/DensityInterpolation.lean) · [Supporting lines](../../LPP_Foundations/Analysis/ShapeSupportingFunctionals.lean)

## Conditional claims and research scope

The first-negative-moment necessity and fixed-width extinction are
proved at their stated scopes. The endpoint tail calculation uses the
actual strict one-step event. The conditional cap at the earlier
coarse scales uses the eventual improved growth premise on the actual
first dyadic lengths at all sufficiently large indices. The general
excess little-o criterion describes the stated upper envelope.
[Moment necessity](../../Differentiability/FinalDraft/SourceConsequences/NegativeMean.lean) · [Fixed-width extinction](../../Differentiability/FinalDraft/SourceConsequences/FixedWidthStrip.lean) · [Endpoint necessity](../../Differentiability/FinalDraft/TailConsequences/EndpointNecessity.lean) · [Coarse cap](../../Differentiability/FinalDraft/Grid/CoarseHeavyScaling.lean) · [Excess criterion](../../Differentiability/FinalDraft/ExcessScaling/Threshold.lean)

The uniform-modulus implication keeps its first-order remainder premise
shared across upper cutoffs. The availability of that modulus and of
improved characteristic growth remains open. The main theorem uses
A1–A3. The proposed exponential lifetime in tilted strips and the KPZ
and Flory scaling discussion retain their conjectural or heuristic
scope. The map separates these from cited background, including the
symmetric-strip and contact-process results. [Conditional modulus](../../Differentiability/FinalDraft/Truncation/UniformModulus.lean)

## Verification

The approved development source at the reviewed revision passed the five-library build (5,424 jobs), the 136 frozen-source checks with zero mismatches, and both authorized source guards across 1,552 Lean files in five comparator configurations. Eight replay clients exited successfully: seven statement/type clients and the mapped-export client resolving all 185 names. The axiom report contains 404 rows, each with only the standard axiom set or no axioms. The 134 earlier warning headers were unchanged, with none added.

The map records stable result labels, Lean declarations, status, and 146 source-span anchors (438 SHA-256 fields) without publishing manuscript line coordinates. The transfer package's validation record gives the fresh build and replay results for its exact public target. The [cited-draft comparison](grs-final-comparison.md) documents the already-formalized portions of the related GRS manuscript at their reviewed scopes.
