module

public import LPP_Foundations.Frozen.Model.Environment
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- The canonical iid site environment with marginal probability law mu. -/
noncomputable def environmentLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure Environment :=
  Measure.infinitePi (fun _ : Lattice => μ)

end LPPDifferentiability
