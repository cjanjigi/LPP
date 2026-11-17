module

public import Busemann.Frozen.StrongExistence.Definitions.StrictCrossTiltOrder

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- One event supports all one-sided tilt limits at every pair of lattice points; source lines 646–649. -/
def OneSidedLimits (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  ∀ᵐ ω ∂environmentLaw μ, ∀ (h : CoalescingTilt μ) (x y : Lattice),
    (∀ hs : ℕ → CoalescingTilt μ,
      (∀ n, (hs n).val.1 < h.val.1) → Tendsto hs atTop (𝓝 h) →
      Tendsto (fun n => Bm (hs n) x y ω) atTop (𝓝 (Bm h x y ω)) ∧
      Tendsto (fun n => Bp (hs n) x y ω) atTop (𝓝 (Bm h x y ω))) ∧
    (∀ hs : ℕ → CoalescingTilt μ,
      (∀ n, h.val.1 < (hs n).val.1) → Tendsto hs atTop (𝓝 h) →
      Tendsto (fun n => Bm (hs n) x y ω) atTop (𝓝 (Bp h x y ω)) ∧
      Tendsto (fun n => Bp (hs n) x y ω) atTop (𝓝 (Bp h x y ω)))

end LPP.Busemann
