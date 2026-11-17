-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.OriginEdgeL1
public import LPP_Foundations.Probability.TranslationEquiv
public import Martin2004.Shape.ExpectedRateShape
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Data.EReal.Basic
public import Busemann.Analysis.VariationalBound

/-! The source-facing one-sided zero-temperature LPP cocycle variational bound. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal

namespace LPP.Busemann

/-- The upper-bound half of GRS arXiv:1311.3016v4, Theorem 4.4(4.8),
used after projection in JR arXiv:1810.03580v3, (4.21). -/
theorem exists_expected_rate_shape_le_cocycle_essSup
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ g : Quadrant → ℝ,
      IsExpectedRateShape μ g ∧
      ∀ (ξ : Quadrant), 0 < ξ.1 → 0 < ξ.2 → ξ.1 + ξ.2 = 1 →
        ∀ (C : Lattice → Lattice → Environment → ℝ),
          is_shift_covariant_cocycle (environmentLaw μ)
            (fun z ω => environmentTranslationEquiv z ω) C →
          has_integrable_origin_edges (environmentLaw μ) C →
          ((g ξ : ℝ) : EReal) ≤
            essSup (fun ω : Environment =>
              ((max (ω 0 - C 0 ((1 : ℤ), (0 : ℤ)) ω)
                    (ω 0 - C 0 ((0 : ℤ), (1 : ℤ)) ω) +
                (∫ η : Environment, C 0 ((1 : ℤ), (0 : ℤ)) η ∂environmentLaw μ) *
                  (ξ.1 : ℝ) +
                (∫ η : Environment, C 0 ((0 : ℤ), (1 : ℤ)) η ∂environmentLaw μ) *
                  (ξ.2 : ℝ) : ℝ) : EReal))
              (environmentLaw μ) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPP.Busemann.Proof.exists_expected_rate_shape_le_cocycle_essSup μ hmoment
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPP.Busemann

-- FROZEN_ANCHOR_SUFFIX_END
