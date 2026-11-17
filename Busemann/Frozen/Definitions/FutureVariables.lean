-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.FutureCocycleIndex
public import Busemann.Frozen.Definitions.ProcessSample
public import LPP_Foundations.Frozen.Model.Quadrant

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The source future variables: weights at I and both cocycles at all valid pairs rooted in I. -/
def futureVariables (g : Quadrant → ℝ) (I : Set Lattice)
    (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
    (s : ProcessSample) :
    Sum {x : Lattice // x ∈ I} (FutureCocycleIndex g I) → ℝ :=
  fun j => match j with
  | .inl x => s.1 x.1
  | .inr q =>
      if q.right then Bplus q.tilt q.root q.target s
      else Bminus q.tilt q.root q.target s

end LPP.Busemann
