module

public import Busemann.Frozen.Definitions.InvariantCocycleTilt

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- H consists of deterministic tilts of canonical coalescing generalized Busemann
functions. Membership is an existence condition; no cocycle witness is selected.
Strong Existence, accepted source, lines 576–580. -/
def coalescingTilts (μ : Measure ℝ) [IsProbabilityMeasure μ] : Set (ℝ × ℝ) :=
  {h | ∃ B : Lattice → Lattice → Environment → ℝ,
    ∃ hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B,
      HasCoalescingRightmostPaths (environmentLaw μ) B ∧
      ∀ᵐ ω ∂environmentLaw μ,
        invariantCocycleTilt (environmentLaw μ)
          (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B hB ω = h}

end LPP.Busemann
