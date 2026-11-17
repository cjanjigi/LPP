module

public import Busemann.Frozen.StrongExistence.Definitions.SqueezeScale

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The explicit embedding used to induce the state and time topology. -/
noncomputable def squeezedStateEmbedding (J : Type*) :
    SqueezedState J → ℝ × (J → ℝ)
  | .finite state t =>
      (compressReal t, fun i => squeezeScale t * compressReal (state i))
  | .bottom => (-1, fun _ => 0)
  | .top => (1, fun _ => 0)

end LPP.Busemann
