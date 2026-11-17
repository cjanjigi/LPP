-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.SupportTilt
public import LPP_Foundations.Frozen.Model.Lattice

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- A source future-cone cocycle index with a root in I and a target northeast of it. -/
structure FutureCocycleIndex (g : Quadrant → ℝ) (I : Set Lattice) where
  root : Lattice
  root_mem : root ∈ I
  target : Lattice
  target_ge : root ≤ target
  tilt : SupportTilt g
  right : Bool

end LPP.Busemann
