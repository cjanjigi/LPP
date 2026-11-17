module

public import Busemann.Frozen.Definitions.CoalescingRightmostPaths

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The class Khat: measurable covariant recovering cocycles, integrable for every pair
of lattice points. Strong Existence, accepted source, lines 328–349. -/
def IsGeneralizedBusemann {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : Lattice → Ω → Ω) (weights : Ω → Environment)
    (B : Lattice → Lattice → Ω → ℝ) : Prop :=
  is_shift_covariant_cocycle P T B ∧
  recovers_weight_map_ae P weights B ∧
  ∀ x y : Lattice, Integrable (B x y) P

end LPP.Busemann
