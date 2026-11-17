-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Shape.ExpectedRateShape
public import Busemann.Frozen.Definitions.InteriorDirection
public import Busemann.Frozen.Definitions.SupportsAt
public import Busemann.Frozen.Definitions.SupportTilt
public import Busemann.Frozen.Definitions.SupportFace
public import Busemann.Frozen.Definitions.SupportFacesUnion
public import Busemann.Geometry.RightFaceEndpoint

@[expose] public section

open LPPDifferentiability MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LPP.Busemann

/-- Under the native nonconstant finite-moment law, the right endpoint of
the union of the two extreme support faces exists uniquely in the interior.
The boundary-interiority proof is required by GRS arXiv:1510.00860v2,
(2.6)-(2.8); it is not an extra premise. -/
theorem exists_unique_right_face_endpoint
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (ξ : InteriorDirection) :
    ∃! right : InteriorDirection,
      ∃ hMinus hPlus : SupportTilt g,
        SupportsAt g ξ hMinus.1 ∧ SupportsAt g ξ hPlus.1 ∧
        (∀ k : SupportTilt g, SupportsAt g ξ k.1 →
          hMinus.1.1 ≤ k.1.1 ∧ k.1.1 ≤ hPlus.1.1) ∧
        right ∈ supportFacesUnion g hMinus hPlus ∧
        ∀ ζ ∈ supportFacesUnion g hMinus hPlus,
          (ζ.1.1 : ℝ) ≤ (right.1.1 : ℝ) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPP.Busemann.Proof.exists_unique_right_face_endpoint μ hmoment hnonconstant g hg ξ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPP.Busemann

-- FROZEN_ANCHOR_SUFFIX_END
