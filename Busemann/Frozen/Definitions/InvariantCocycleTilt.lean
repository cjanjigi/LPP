module

public import Busemann.Frozen.Definitions.GeneralizedBusemann

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The random invariant tilt, with the source's negative sign. The source domain is Khat;
no value is exported for a nonintegrable field. Strong Existence, lines 354–358. -/
noncomputable def invariantCocycleTilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Lattice → Ω → Ω)
    (weights : Ω → Environment) (B : Lattice → Lattice → Ω → ℝ)
    (_hB : IsGeneralizedBusemann P T weights B) (ω : Ω) : ℝ × ℝ :=
  (-(P[B 0 (1, 0) | latticeInvariantSigma T] ω),
    -(P[B 0 (0, 1) | latticeInvariantSigma T] ω))

end LPP.Busemann
