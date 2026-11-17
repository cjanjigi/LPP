-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.ProcessSample
public import LPP_Foundations.Probability.TranslationEquiv

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Translation of both the original weights and the edge array by the same lattice vector. -/
def processShift (z : Lattice) (s : ProcessSample) : ProcessSample :=
  (environmentTranslationEquiv z s.1, fun j x i => s.2 j (z + x) i)

end LPP.Busemann
