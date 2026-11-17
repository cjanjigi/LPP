-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import ProbabilityBasics.Probability.UniformOrigin

@[expose] public section

open LPPDifferentiability MeasureTheory

namespace LPP.Busemann

/-- The product law pairs the environment with one horizon shared by all array coordinates. -/
noncomputable def finiteBusemannSharedHorizonLaw (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n : ℕ) :
    Measure (Environment × Fin (n + 1)) :=
  uniformOriginProduct (environmentLaw μ) n

end LPP.Busemann
