/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Variational.OneSidedBound
public import Busemann.Frozen.Definitions.SupportTilt
import Busemann.Geometry.SupportIdentities
import LPP_Foundations.Analysis.AbsoluteMomentShape
import Mathlib.Tactic

/-! Identification of the two canonical origin means from the one-sided LPP
variational inequality, following JR1810.03580v3 after (4.20)-(4.21). -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped NNReal ENNReal

namespace LPP.Busemann

/-- A canonical projected cocycle with the two separate lower edge bounds and
upper supporting-tilt means has exactly those two means. This is the LPP mean
identification in JR1810.03580v3 after (4.20)-(4.21); exact recovery is not assumed. -/
theorem integral_origin_edges_eq_neg_support_tilt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : SupportTilt g)
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (hL1 : has_integrable_origin_edges (environmentLaw μ) C)
    (hLower₁ : ∀ᵐ ω ∂environmentLaw μ, ω 0 ≤ C 0 ((1 : ℤ), (0 : ℤ)) ω)
    (hLower₂ : ∀ᵐ ω ∂environmentLaw μ, ω 0 ≤ C 0 ((0 : ℤ), (1 : ℤ)) ω)
    (hUpper₁ : (∫ ω : Environment, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ)
      ≤ -h.val.1)
    (hUpper₂ : (∫ ω : Environment, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ)
      ≤ -h.val.2) :
    (∫ ω : Environment, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) = -h.val.1 ∧
    (∫ ω : Environment, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) = -h.val.2 := by
  -- Identify the variational theorem's actual expected-rate witness with g.
  obtain ⟨g₀, hg₀, hvar⟩ := exists_expected_rate_shape_le_cocycle_essSup μ hmoment
  have hshape : g₀ = g := isExpectedRateShape_unique μ hg₀ hg
  rw [hshape] at hvar
  -- Homogeneity and contact are produced internally from the native assumptions.
  have hgeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hgeometry.2.1 c z
  obtain ⟨ξ, hsupport⟩ := h.property
  have hcontact :=
    ((supportsAt_iff_through_origin_majorant_and_contact g ξ h.val hhom).mp hsupport).2
  have hξsum : ξ.val.1 + ξ.val.2 = 1 := by exact_mod_cast ξ.property.2.2
  have hξ₁ : 0 < (ξ.val.1 : ℝ) := by exact_mod_cast ξ.property.1
  have hξ₂ : 0 < (ξ.val.2 : ℝ) := by exact_mod_cast ξ.property.2.1
  let m₁ : ℝ := ∫ ω : Environment, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ
  let m₂ : ℝ := ∫ ω : Environment, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ
  have hv := hvar ξ.val ξ.property.1 ξ.property.2.1 hξsum C hC hL1
  -- Separate lower bounds make both actual local defects nonpositive.
  have hpoint : ∀ᵐ ω ∂environmentLaw μ,
      ((max (ω 0 - C 0 ((1 : ℤ), (0 : ℤ)) ω)
        (ω 0 - C 0 ((0 : ℤ), (1 : ℤ)) ω) +
        m₁ * (ξ.val.1 : ℝ) + m₂ * (ξ.val.2 : ℝ) : ℝ) : EReal) ≤
      ((m₁ * (ξ.val.1 : ℝ) + m₂ * (ξ.val.2 : ℝ) : ℝ) : EReal) := by
    filter_upwards [hLower₁, hLower₂] with ω h₁ h₂
    apply EReal.coe_le_coe_iff.mpr
    have hdefect : max (ω 0 - C 0 ((1 : ℤ), (0 : ℤ)) ω)
        (ω 0 - C 0 ((0 : ℤ), (1 : ℤ)) ω) ≤ 0 :=
      max_le (sub_nonpos.mpr h₁) (sub_nonpos.mpr h₂)
    linarith only [hdefect]
  have hess := essSup_le_of_ae_le
    (((m₁ * (ξ.val.1 : ℝ) + m₂ * (ξ.val.2 : ℝ) : ℝ) : EReal)) hpoint
  have hweighted : g ξ.val ≤ m₁ * (ξ.val.1 : ℝ) + m₂ * (ξ.val.2 : ℝ) :=
    EReal.coe_le_coe_iff.mp (hv.trans hess)
  rw [hcontact] at hweighted
  have hm₁ : m₁ ≤ -h.val.1 := hUpper₁
  have hm₂ : m₂ ≤ -h.val.2 := hUpper₂
  -- A positive interior contact forbids either upper mean inequality being strict.
  have hother₂ := mul_le_mul_of_nonneg_right hm₂ hξ₂.le
  have hfirst : (-h.val.1) * (ξ.val.1 : ℝ) ≤ m₁ * (ξ.val.1 : ℝ) := by
    linarith only [hweighted, hother₂]
  have heq₁ : m₁ = -h.val.1 :=
    le_antisymm hm₁ (le_of_mul_le_mul_right hfirst hξ₁)
  have hother₁ := mul_le_mul_of_nonneg_right hm₁ hξ₁.le
  have hsecond : (-h.val.2) * (ξ.val.2 : ℝ) ≤ m₂ * (ξ.val.2 : ℝ) := by
    linarith only [hweighted, hother₁]
  have heq₂ : m₂ = -h.val.2 :=
    le_antisymm hm₂ (le_of_mul_le_mul_right hsecond hξ₂)
  exact ⟨heq₁, heq₂⟩

end LPP.Busemann
