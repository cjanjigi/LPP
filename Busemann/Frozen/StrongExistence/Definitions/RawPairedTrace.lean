module

public import Busemann.Frozen.StrongExistence.Definitions.SqueezedStateTopologicalSpace

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Two functions of state and time, one for each ordered trace. -/
abbrev RawPairedTrace (S : Set ℝ) (J : Type*) :=
  ((t : {u : ℝ // u ∈ S}) → J → ℝ) × ((t : {u : ℝ // u ∈ S}) → J → ℝ)

end LPP.Busemann
