/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.SupportsAt
public import Busemann.Frozen.Definitions.SupportTilt
import Busemann.Geometry.SupportOrder

@[expose] public section
open LPPDifferentiability
open scoped NNReal
namespace LPP.Busemann

/-- The two extremal selectors for one homogeneous shape agree pointwise.
This identifies the ordinary-direction selectors with the chosen native
family after the two actual expected-rate witnesses identify their shapes. -/
theorem extreme_support_selectors_eq
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (left₁ right₁ left₂ right₂ : InteriorDirection → SupportTilt g)
    (h₁ : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (left₁ ξ).1 ∧ SupportsAt g ξ (right₁ ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (left₁ ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (right₁ ξ).1.1)
    (h₂ : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (left₂ ξ).1 ∧ SupportsAt g ξ (right₂ ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (left₂ ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (right₂ ξ).1.1) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  constructor
  · funext ξ
    have hle := ((h₁ ξ).2.2 (left₂ ξ) (h₂ ξ).1).1
    have hge := ((h₂ ξ).2.2 (left₁ ξ) (h₁ ξ).1).1
    exact (supportTilt_coordinate_order g hhom (left₁ ξ) (left₂ ξ)).2
      (le_antisymm hle hge)
  · funext ξ
    have hle := ((h₂ ξ).2.2 (right₁ ξ) (h₁ ξ).2.1).2
    have hge := ((h₁ ξ).2.2 (right₂ ξ) (h₂ ξ).2.1).2
    exact (supportTilt_coordinate_order g hhom (right₁ ξ) (right₂ ξ)).2
      (le_antisymm hle hge)

end LPP.Busemann
