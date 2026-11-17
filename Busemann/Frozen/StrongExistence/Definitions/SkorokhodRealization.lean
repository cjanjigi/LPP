module

public import Busemann.Frozen.StrongExistence.Definitions.TimeIndex

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The same two fields admit a measurable paired path on one full-measure event. -/
def SkorokhodRealization (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  IsClosed (timeSet μ) ∧
    ∃ Φ : Environment → PairedSkorokhodPath (timeSet μ) (Lattice × Lattice),
          @Measurable Environment
            (PairedSkorokhodPath (timeSet μ) (Lattice × Lattice))
            (inferInstance : MeasurableSpace Environment)
            (pairedSkorokhodPathBorel (timeSet μ) (Lattice × Lattice)) Φ ∧
      ∀ᵐ ω ∂environmentLaw μ,
        ∀ h : CoalescingTilt μ, ∀ x y : Lattice,
          evalMinus (Φ ω) (timeIndex μ h) (x, y) = Bm h x y ω ∧
          evalPlus (Φ ω) (timeIndex μ h) (x, y) = Bp h x y ω

-- The proposed full conclusion keeps the six paper components as the uniqueness

end LPP.Busemann
