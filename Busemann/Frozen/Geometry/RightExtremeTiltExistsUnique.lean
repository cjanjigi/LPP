-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Shape.ExpectedRateShape
public import Busemann.Frozen.Definitions.InteriorDirection
public import Busemann.Frozen.Definitions.SupportsAt
public import Busemann.Frozen.Definitions.SupportTilt
public import Busemann.Frozen.Definitions.SupportFace
public import Busemann.Frozen.Definitions.SupportFacesUnion
public import Busemann.Geometry.RightExtremeTilt

@[expose] public section

open LPPDifferentiability MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LPP.Busemann

/-- For a concave homogeneous shape, the negative right extreme support at
an interior direction is uniquely determined by the greatest first tilt
coordinate. Its identification with JR arXiv:1810.03580v3's right one-sided
gradient (Section 2.3; Lemma 4.7(c)) is a required source proof. -/
theorem exists_unique_right_extreme_tilt
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (ξ : InteriorDirection) :
    ∃! h : SupportTilt g,
      SupportsAt g ξ h.1 ∧
      ∀ k : SupportTilt g,
        SupportsAt g ξ k.1 → k.1.1 ≤ h.1.1 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPP.Busemann.Proof.exists_unique_right_extreme_tilt g hconc hhom ξ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPP.Busemann

-- FROZEN_ANCHOR_SUFFIX_END
