module

public import Busemann.Frozen.Definitions.OutsideSigma
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

open LPPDifferentiability MeasureTheory

namespace LPP.Busemann

/-- Positive-probability lower weight events have positive conditional probability
almost everywhere given the outside weights and cocycle increments. -/
noncomputable def HasDownwardFiniteEnergy {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (weights : Ω → Environment)
    (B : Lattice → Lattice → Ω → ℝ) : Prop := by
  classical
  exact ∀ K : ℝ, 0 < P {ω | weights ω 0 ≤ K} →
    ∀ᵐ ω ∂P, 0 < P[(Set.indicator {ω | weights ω 0 ≤ K} (fun _ => (1 : ℝ))) |
      outsideSigma weights B {0}] ω

end LPP.Busemann
