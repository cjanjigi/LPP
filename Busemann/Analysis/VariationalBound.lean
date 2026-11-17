/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.OriginEdgeL1
public import LPP_Foundations.Probability.TranslationEquiv
public import Martin2004.Shape.ExpectedRateShape
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Data.EReal.Basic

import ProbabilityBasics.Probability.AbsoluteMomentTail
import ProbabilityBasics.Probability.RealEssSupUpper
import Martin2004.Probability.WeakNegativeShape
import Busemann.Analysis.VariationalRealBound

/-! The source-facing one-sided LPP cocycle variational inequality. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal

namespace LPP.Busemann.Proof

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
              (environmentLaw μ) := by
  -- Derive every shape and first-moment input from the native absolute moment.
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  obtain ⟨hneg, hpos⟩ :=
    ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
      μ hp hpMoment
  have hμ : Integrable id μ :=
    integrable_id_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨g, hg, _hunique⟩ :=
    exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail
      μ hneg hpos
  have hgExpected : IsExpectedRateShape μ g := hg.2.2.2.2.1
  refine ⟨g, hgExpected, ?_⟩
  intro ξ _hξ₁ _hξ₂ hξ C hC hL1

  let m₁ : ℝ :=
    ∫ η : Environment, C 0 ((1 : ℤ), (0 : ℤ)) η ∂environmentLaw μ
  let m₂ : ℝ :=
    ∫ η : Environment, C 0 ((0 : ℤ), (1 : ℤ)) η ∂environmentLaw μ
  let f : Environment → ℝ := fun ω =>
    max (ω 0 - C 0 ((1 : ℤ), (0 : ℤ)) ω)
      (ω 0 - C 0 ((0 : ℤ), (1 : ℤ)) ω) +
      m₁ * (ξ.1 : ℝ) + m₂ * (ξ.2 : ℝ)

  -- Every real upper bound for the corrected defect bounds the shape.
  have hupper (r : ℝ) (hr : ∀ᵐ ω ∂environmentLaw μ, f ω ≤ r) :
      g ξ ≤ r := by
    have hdefect : ∀ᵐ ω ∂environmentLaw μ,
        max (ω 0 - C 0 ((1 : ℤ), (0 : ℤ)) ω)
          (ω 0 - C 0 ((0 : ℤ), (1 : ℤ)) ω) ≤
          r - m₁ * (ξ.1 : ℝ) - m₂ * (ξ.2 : ℝ) := by
      filter_upwards [hr] with ω hω
      dsimp [f] at hω
      linarith only [hω]
    have hreal := expected_rate_le_cocycle_add_mean
      μ hμ g hgExpected C hC hL1
      (r - m₁ * (ξ.1 : ℝ) - m₂ * (ξ.2 : ℝ)) hdefect ξ hξ
    dsimp [m₁, m₂] at hreal ⊢
    linarith only [hreal]
  have hsup := ProbabilityBasics.coe_le_essSup_of_forall_ae_le
    (environmentLaw μ) f (g ξ) hupper
  exact hsup

end LPP.Busemann.Proof
