-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.ProcessSample

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The original environment coordinate of the extension. -/
def processEnvironment (s : ProcessSample) : Environment := s.1

end LPP.Busemann
