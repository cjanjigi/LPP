module

public import Busemann.Frozen.StrongExistence.Definitions.BranchAgreement

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- At each tilt, the minus branch is generalized, coalescing and forward measurable, and the plus branch is jointly measurable; source lines 635–636. -/
def ForwardCoalescingClass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  ∀ h : CoalescingTilt μ, Measurable (fun q : (Lattice × Lattice) × Environment => Bp h q.1.1 q.1.2 q.2) ∧
    IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) (Bm h) ∧
    HasCoalescingRightmostPaths (environmentLaw μ) (Bm h) ∧
    IsForwardMeasurable (Bm h)

end LPP.Busemann
