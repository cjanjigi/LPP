module

public import Busemann.Frozen.Definitions.Recovery
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Almost-sure zero-temperature recovery relative to a supplied weight map. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- Definition 4.3 at zero temperature, using the approved pointwise recovery predicate. -/
def recovers_weight_map_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (weights : Ω → Environment)
    (B : Lattice → Lattice → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, recovers_environment (weights ω) (fun x y => B x y ω)

end LPP.Busemann
