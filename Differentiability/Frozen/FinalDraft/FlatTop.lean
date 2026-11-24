-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.Percolation
public import Differentiability.Probability.TopIndicatorLaw
public import LPP_Foundations.Frozen.Analysis.UnitDirectionInterval
public import LPP_Foundations.Statements.ShapeDefinitions
import Differentiability.FinalDraft.FlatTop.Theorem

/-! The flat-top theorem of the final differentiability manuscript. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- The finite support top is attained exactly on the top-indicator flat
segment. The critical density and the origin cluster's speed determine this
segment and its endpoints are differentiability points. -/
theorem flat_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnondegenerate : ∀ c : ℝ, μ ({c} : Set ℝ) < 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (M : ℝ) (hM : (M : EReal) = supportTop μ)
    (g : Quadrant → ℝ) (hg : LPPStatements.IsShapeFunction μ g)
    (gtop : Quadrant → ℝ)
    (hgtop : ∀ x : Quadrant,
      Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gtop x))) :
    let p₁ : ℝ := μ.real {M}
    let Uperc : Set Quadrant := {x ∈ closedUnitDirections | gtop x = 1}
    Uperc = {x ∈ closedUnitDirections | g x = M} ∧
    (∀ x ∈ closedUnitDirections, x ∉ Uperc → g x < M) ∧
    (p₁ < orientedSiteCriticalDensity → Uperc = ∅) ∧
    (p₁ = orientedSiteCriticalDensity →
      Uperc = {((1 / 2, 1 / 2) : Quadrant)} ∧
        DifferentiableAt ℝ (quadrantExtension g) (1 / 2, 1 / 2)) ∧
    (orientedSiteCriticalDensity < p₁ →
      0 < environmentLaw μ (orientedSiteSurvival M) ∧
      ∃ β : ℝ, 1 / 2 < β ∧ β < 1 ∧ IsOriginRightEdgeSpeed μ M β ∧
        Uperc = unitDirectionInterval (1 - β) β ∧
        DifferentiableAt ℝ (quadrantExtension g) (1 - β, β) ∧
        DifferentiableAt ℝ (quadrantExtension g) (β, 1 - β)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.FinalDraft.FlatTop.flat_top μ hnondegenerate hneg M hM g hg gtop hgtop
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability.FinalDraft

-- FROZEN_ANCHOR_SUFFIX_END
