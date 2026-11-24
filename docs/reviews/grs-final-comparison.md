# Comparison with the cited GRS draft

[Formalization guide](../guides/differentiability.md) · [Source and export record](../../sources/current-grs.json)

The comparison uses the author-supplied draft of 23 November 2026,
identified by SHA-256
`db123fc668e5cedccdb4110fb4ff9e44f11c0a91dc8717083b530120ecebc8e4`
and 5,367 logical lines. The earlier source identity and all 48 reviewed
Lean export names are recorded as metadata. The comparison was reviewed
at the approved scopes of the already-formalized material.

## Public availability

Forty-six reviewed exports have providers in the public source.
Thirty-six provider files match the reviewed bytes. The public rightmost
coalescence file retains its own comment wording and has identical Lean
code. The two reviewed declarations below are recorded for provenance
and remain available only in the development comparison.

- `LPP.Busemann.passageDifferenceOnTail`
- `LPP.Busemann.exists_coupled_busemann_process_and_fixed_direction_squeeze`

## Statement scopes

The outside-field definitions cover a fixed cocycle, and the
finite-energy definition has the approved singleton scope. The
ordinary-geodesic result gives support-face directions. The rightmost
coalescence result retains its finite-block conditional-expectation
premise. [Outside field](../../Busemann/Frozen/Definitions/OutsideSigma.lean) · [Rightmost coalescence](../../Busemann/Process/RightmostPathCoalescence.lean)

The flat helpers retain the accepted finite-rate and endpoint scopes.
The start-set deviation comparison uses the matching window at
`C = 1` under the existing stronger Lean inputs. The larger
labelled outside field and full formalization of the GRS draft are
outside this comparison.

<details>
<summary>Reviewed groups and Lean exports</summary>

| Reviewed scope | Lean exports |
| --- | --- |
| Direction and support-face definitions | [InteriorDirection](../../Busemann/Frozen/Definitions/InteriorDirection.lean) · [supportFace](../../Busemann/Frozen/Definitions/SupportFace.lean) · [supportFacesUnion](../../Busemann/Frozen/Definitions/SupportFacesUnion.lean) |
| Endpoints, face approach and tail differences | [latticeEndpoint](../../Busemann/Frozen/Definitions/LatticeEndpoint.lean) · [approachesFaceInterval](../../Busemann/Frozen/Definitions/ApproachesFaceInterval.lean) · `passageDifferenceOnTail` (development only) |
| Outside lower orthants for finite modification sets | [outsideLowerOrthants](../../Busemann/Frozen/Definitions/OutsideLowerOrthants.lean) |
| Fixed-cocycle outside field | [OutsideIndex](../../Busemann/Frozen/Definitions/OutsideIndex.lean) · [outsideWeightsAndCocycleIncrements](../../Busemann/Frozen/Definitions/OutsideWeightsAndCocycleIncrements.lean) · [outsideSigma](../../Busemann/Frozen/Definitions/OutsideSigma.lean) |
| Singleton finite energy | [HasDownwardFiniteEnergy](../../Busemann/Frozen/Definitions/DownwardFiniteEnergy.lean) |
| Extreme tilts and face endpoints | [exists_unique_left_extreme_tilt](../../Busemann/Frozen/Geometry/LeftExtremeTiltExistsUnique.lean) · [exists_unique_right_extreme_tilt](../../Busemann/Frozen/Geometry/RightExtremeTiltExistsUnique.lean) · [exists_unique_left_face_endpoint](../../Busemann/Frozen/Geometry/LeftFaceEndpointExistsUnique.lean) · [exists_unique_right_face_endpoint](../../Busemann/Frozen/Geometry/RightFaceEndpointExistsUnique.lean) |
| Coupled process with nested readouts and conditional unit-edge convergence | `exists_coupled_busemann_process_and_fixed_direction_squeeze` (development only) |
| Ordinary geodesic directions in support faces | [exists_full_event_ordinary_geodesics_directed_into_support_faces](../../Busemann/Process/OrdinaryGeodesicDirectedness.lean) |
| Rightmost coalescence under finite-block conditional expectations | [hasCoalescingRightmostPaths_of_finite_block_condExp](../../Busemann/Process/RightmostPathCoalescence.lean) |
| Specialized sparse coarse cutoff | [exists_sparse_good_coarse_path_cutoff](../../Differentiability/Probability/SparseCoarsePaths.lean) |
| Block and edge estimates in the finite-rate proof | [white_block_probability_le](../../Differentiability/Probability/WhiteBlockBound.lean) · [coarse_path_few_black_blocks](../../Differentiability/Model/CoarseBlackBlocks.lean) · [halfLineEdge_upper_deviation](../../Differentiability/Probability/HalfLineEdgeDeviation.lean) · [top_passage_beyond_edge_decay_total](../../Differentiability/Probability/TopPassageDecay.lean) · [top_passage_beyond_edge_decay](../../Differentiability/Probability/TopPassageDecay.lean) · [gtop_lt_one_beyond_edge](../../Differentiability/Probability/TopShapeBeyondEdge.lean) |
| Right block gain in pathwise and integral forms | [openEdge_union_gain_antitone](../../Differentiability/Probability/RightBlockGain.lean) · [integral_halfLine_rightBlock_gain](../../Differentiability/Probability/RightBlockGain.lean) · [lintegral_rightBlock_gain_ge](../../Differentiability/Probability/RightBlockGain.lean) |
| Supporting triangle results | [triangle_target_passage](../../Differentiability/Model/PercolationTriangles.lean) · [openReachSet_left_of_triangle](../../Differentiability/Model/PercolationTriangles.lean) · [triangle_probability](../../Differentiability/Probability/TriangleProbability.lean) · [exists_triangle_floor](../../Differentiability/Probability/TriangleProbability.lean) |
| Augmented count and gain estimates | [openEdge_triangle_gain_ge](../../Differentiability/Model/AugmentedProcessLaws.lean) · [measurable_maxFirst_augmentedProcess](../../Differentiability/Probability/AugmentedMeasurability.lean) · [measurableSet_isTriangle_lowestPoint](../../Differentiability/Probability/AugmentedMeasurability.lean) · [measure_isTriangle_lowestPoint](../../Differentiability/Probability/AugmentedBlockLaws.lean) · [integral_isTriangle_lowestPoint_mul_shifted_gain](../../Differentiability/Probability/AugmentedBlockLaws.lean) · [integral_augmented_count](../../Differentiability/Probability/AugmentedExpectation.lean) · [integral_augmented_edge_gain](../../Differentiability/Probability/AugmentedExpectation.lean) |
| Block-end augmented passage | [augmentedProcess_subset_levelSet](../../Differentiability/Model/AugmentedPassage.lean) · [augmentedProcess_passage_lower](../../Differentiability/Model/AugmentedPassage.lean) |
| Start-set deviation at `C = 1` under the stronger Lean inputs | [expected_max_positive_deviation_startSet](../../Differentiability/Probability/StartSetDeviation.lean) |
| Finite-rate flat segment | [exists_gtop_eq_one_ge_edgeSpeed](../../Differentiability/Probability/TopFlatBeyondEdge.lean) · [gtop_flat_segment_route_h](../../Differentiability/Probability/TopFlatSegment.lean) · [gbar_eq_one_of_gtop_eq_one](../../Differentiability/Probability/FlatTopThinning.lean) |
| Endpoint differentiability in the finite-rate setting | [gbar_differentiableAt_edge_route_h](../../Differentiability/Probability/FlatEdgeDifferentiability.lean) · [flat_top_route_h](../../Differentiability/Probability/FlatTopRouteH.lean) · [differentiableAt_of_top_flat](../../Differentiability/Probability/FlatTopDifferentiability.lean) |

</details>
