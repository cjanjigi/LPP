-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Full.StrongExistence

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The accepted full strong Busemann process target. Its proof remains open. -/
theorem exists_unique_strong_busemann_process :
∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
  LPPStatements.NotAPointMass μ →
  (∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) →
  ∃ Bm Bp : StrongField μ,
    BranchAgreement μ Bm Bp ∧ ForwardCoalescingClass μ Bm Bp ∧ MeanTilt μ Bm ∧
    WithinTiltOrder μ Bm Bp ∧ StrictCrossTiltOrder μ Bm Bp ∧ OneSidedLimits μ Bm Bp ∧
    SkorokhodRealization μ Bm Bp ∧
    (∀ Bm' Bp' : StrongField μ,
      (BranchAgreement μ Bm' Bp' ∧ ForwardCoalescingClass μ Bm' Bp' ∧
       MeanTilt μ Bm' ∧ WithinTiltOrder μ Bm' Bp' ∧
       StrictCrossTiltOrder μ Bm' Bp' ∧ OneSidedLimits μ Bm' Bp') →
      ∀ᵐ ω ∂environmentLaw μ, ∀ (h : CoalescingTilt μ) (x y : Lattice),
        Bm' h x y ω = Bm h x y ω ∧ Bp' h x y ω = Bp h x y ω) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by
  exact LPP.Busemann.Proof.exists_unique_strong_busemann_process
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPP.Busemann

-- FROZEN_ANCHOR_SUFFIX_END
