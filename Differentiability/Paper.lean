/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

-- Section 2, setting and main result
public import Differentiability.Paper.Setting
public import Differentiability.Probability.TranslatedShape
public import LPP_Foundations.Model.LastPassage.UniformShapeAllStarts
public import Differentiability.Probability.UniformShapeProbability
public import Martin2004.Probability.ShapeAboveMean
public import Differentiability.Probability.TopIndicatorShape
public import Differentiability.Frozen.FinalDraft.FlatTop
public import Differentiability.Probability.FlatTopRouteH
public import Differentiability.Probability.FlatTopDifferentiability
public import Differentiability.Probability.GeodesicDefect

-- Section 4, localized crossings
public import Differentiability.Probability.Travel
public import Differentiability.Probability.BoundedIntervals
public import Differentiability.Probability.RareFastCrossings
public import Differentiability.FinalDraft.CrossingRemarks.Translation
public import Differentiability.FinalDraft.CrossingRemarks.ShapeThreshold
public import Differentiability.FinalDraft.TailConsequences.FixedLength

-- Section 5, characteristic scale
public import Differentiability.Probability.MaximumKernelRN
public import Differentiability.Probability.TiltLimit
public import Differentiability.Probability.CharacteristicLengths

-- Section 6, control over a parallelogram
public import Differentiability.Probability.GridSimultaneous
public import Differentiability.Probability.GridSimultaneousGeneral
public import Differentiability.FinalDraft.Grid.Events
public import Differentiability.FinalDraft.Grid.GeneralTheorem
public import Differentiability.Probability.ArbitraryEndpoints
public import Differentiability.Probability.ArbitraryEndpointsGeneral

-- Section 7, disjoint witnesses and the main theorem
public import Differentiability.Probability.BlockDefectRarity
public import Differentiability.Probability.LongPathWitnessBound
public import Differentiability.Model.Paths.StageDefectTotal
public import Differentiability.FinalDraft.WitnessMultiplicity.Maximum
public import Differentiability.FinalDraft.WitnessMultiplicity.Cuts
public import Differentiability.FinalDraft.WitnessMultiplicity.StageBounds
public import Differentiability.FinalDraft.WitnessMultiplicity.TotalBounds
public import Differentiability.FinalDraft.WitnessMultiplicity.LongPaths
public import Differentiability.Probability.BoundedOffFlatDifferentiability
public import Differentiability.Probability.GeneralOffFlatDifferentiability
public import Differentiability.Statements

-- Section 8, rigorous claims and conditional calculations in the remarks
public import Differentiability.FinalDraft.SourceConsequences.NegativeMean
public import Differentiability.FinalDraft.SourceConsequences.FixedWidthStrip
public import Differentiability.Probability.LowerTailExample
public import Differentiability.FinalDraft.TailConsequences.EndpointNecessity
public import Differentiability.FinalDraft.TailConsequences.GlobalHeavySites
public import Differentiability.FinalDraft.Grid.CoarseHeavyScaling
public import Differentiability.FinalDraft.ExcessScaling.AnimalBound
public import Differentiability.FinalDraft.ExcessScaling.Threshold
public import Differentiability.FinalDraft.Truncation.Shape
public import Differentiability.FinalDraft.Truncation.Differentiability
public import Differentiability.FinalDraft.Truncation.UniformModulus

-- Appendix A, oriented percolation and the BK inequality
public import Differentiability.FinalDraft.Contour.Existence
public import Differentiability.Probability.HighDensityOrientedPaths
public import Differentiability.Probability.PathEventBK

-- Appendix B, extension to unbounded weights
public import Differentiability.Paper.PathFamilyWeights
public import Differentiability.Probability.GeneralIntervals
public import Differentiability.FinalDraft.Attachments.UniformEstimate
public import Differentiability.FinalDraft.Attachments.PrescribedProbability
public import Differentiability.Probability.StaircaseGeneral
public import Differentiability.Paper.StaircaseWeights
public import Differentiability.FinalDraft.StairGeometry.Event
public import Differentiability.FinalDraft.Grid.HeavyTrials
public import Differentiability.Probability.ExcessAnimalBound
public import Differentiability.FinalDraft.ExcessScaling.Maximum
public import Differentiability.Probability.StageExcessItinerary

/-! # Differentiability of the shape function in paper order

The supplied-shape main result is
`LPPStatements.Differentiability.shape_differentiable_on_unit_segment`. The complete
current flat-top theorem is `LPPDifferentiability.FinalDraft.flat_top`, with the critical
density, actual origin-cluster speed, closed flat segment and endpoint derivatives.

The imports follow the November 23 final draft. Section 3 connects Sections 4–7.
Section 8 exports its rigorous assertions and conditional calculations: in particular,
the uniform differentiability modulus remains an explicit premise, whose availability
is not proved. The current source map records each result's exact scope and proof route.
-/
