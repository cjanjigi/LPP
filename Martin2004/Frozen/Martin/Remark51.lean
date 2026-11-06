-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Full.Martin.Remark51Lower
public import LPP_Foundations.Frozen.Model.Quadrant

@[expose] public section

open scoped NNReal

namespace LPPDifferentiability

/-- A7. Remark 5.1(i), first sentence, d = 2 (lines 1067-1073). Reading: a
homogeneous, symmetric, subadditive function h on the quadrant satisfies
h(x) >= (||x||/2) h(1, 1). This is deterministic. -/
theorem martin_remark_5_1_i_lower (h : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x)
    (hsymm : ∀ x : Quadrant, h (x.2, x.1) = h x)
    (hsub : ∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y)
    (x : Quadrant) :
    ((x.1 : ℝ) + x.2) / 2 * h (1, 1) ≤ h x :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Full.martin_remark_5_1_i_lower h hhom hsymm hsub x
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
