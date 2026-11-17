/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportsAt
public import LPP_Foundations.Frozen.Analysis.QuadrantSuperdifferential
public import Mathlib.Analysis.Convex.Extreme
import Busemann.Geometry.SupportIdentities

@[expose] public section
open LPPDifferentiability
open scoped NNReal
namespace LPP.Busemann

/-- At an interior contact, homogeneity places every supergradient on one
affine line. An endpoint of the first support coordinate is therefore an
extreme point of the full two-dimensional superdifferential.
Omitted convex geometry step in Strong Existence, `eq:Hinc`, lines 582–592. -/
theorem extremePoint_quadrantSuperdifferential_of_support_coordinate_endpoint
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (ξ : InteriorDirection) (h : ℝ × ℝ)
    (hSupport : SupportsAt g ξ h)
    (hEndpoint :
      (∀ k : ℝ × ℝ, SupportsAt g ξ k → h.1 ≤ k.1) ∨
      (∀ k : ℝ × ℝ, SupportsAt g ξ k → k.1 ≤ h.1)) :
    -h ∈ Set.extremePoints ℝ (quadrantSuperdifferential g ξ.1) := by
  -- Read support membership as membership in the full quadrant superdifferential.
  have hTargetMember : -h ∈ quadrantSuperdifferential g ξ.1 := by
    change SupportsAt g ξ h
    exact hSupport
  have hSupportOfMember : ∀ x : ℝ × ℝ,
      x ∈ quadrantSuperdifferential g ξ.1 → SupportsAt g ξ (-x) := by
    intro x hx
    change (-(-x.1), -(-x.2)) ∈ quadrantSuperdifferential g ξ.1
    simpa only [neg_neg] using hx
  -- Homogeneity gives contact uniqueness for supports with a fixed first coordinate.
  have hFirstEndpoint :
      (∀ x : ℝ × ℝ, x ∈ quadrantSuperdifferential g ξ.1 → x.1 ≤ -h.1) ∨
      (∀ x : ℝ × ℝ, x ∈ quadrantSuperdifferential g ξ.1 → -h.1 ≤ x.1) := by
    rcases hEndpoint with hLeast | hGreatest
    · left
      intro x hx
      have hBound := hLeast (-x) (hSupportOfMember x hx)
      change h.1 ≤ -x.1 at hBound
      linarith
    · right
      intro x hx
      have hBound := hGreatest (-x) (hSupportOfMember x hx)
      change -x.1 ≤ h.1 at hBound
      linarith
  -- A positive convex combination at the endpoint forces each first coordinate to agree.
  have hFirstEqOfSegment : ∀ x₁ x₂ : ℝ × ℝ,
      x₁ ∈ quadrantSuperdifferential g ξ.1 →
      x₂ ∈ quadrantSuperdifferential g ξ.1 →
      -h ∈ openSegment ℝ x₁ x₂ → x₁.1 = -h.1 := by
    intro x₁ x₂ hx₁ hx₂ hSegment
    rcases hSegment with ⟨a, b, ha, hb, hab, hCombination⟩
    have hFirstCombination : a * x₁.1 + b * x₂.1 = -h.1 := by
      have hFirst := congrArg Prod.fst hCombination
      change a * x₁.1 + b * x₂.1 = -h.1 at hFirst
      exact hFirst
    rcases hFirstEndpoint with hBelow | hAbove
    · have hx₁Below : x₁.1 ≤ -h.1 := hBelow x₁ hx₁
      have hx₂Below : x₂.1 ≤ -h.1 := hBelow x₂ hx₂
      have haTerm : a * x₁.1 ≤ a * (-h.1) :=
        mul_le_mul_of_nonneg_left hx₁Below ha.le
      have hbTerm : b * x₂.1 ≤ b * (-h.1) :=
        mul_le_mul_of_nonneg_left hx₂Below hb.le
      have hWeightedEndpoint :
          a * x₁.1 + b * x₂.1 = a * (-h.1) + b * (-h.1) := by
        calc
          a * x₁.1 + b * x₂.1 = -h.1 := hFirstCombination
          _ = a * (-h.1) + b * (-h.1) := by
            rw [← add_mul, hab, one_mul]
      have haEquality : a * x₁.1 = a * (-h.1) := by
        linarith
      exact mul_left_cancel₀ (ne_of_gt ha) haEquality
    · have hx₁Above : -h.1 ≤ x₁.1 := hAbove x₁ hx₁
      have hx₂Above : -h.1 ≤ x₂.1 := hAbove x₂ hx₂
      have haTerm : a * (-h.1) ≤ a * x₁.1 :=
        mul_le_mul_of_nonneg_left hx₁Above ha.le
      have hbTerm : b * (-h.1) ≤ b * x₂.1 :=
        mul_le_mul_of_nonneg_left hx₂Above hb.le
      have hWeightedEndpoint :
          a * (-h.1) + b * (-h.1) = a * x₁.1 + b * x₂.1 := by
        calc
          a * (-h.1) + b * (-h.1) = -h.1 := by
            rw [← add_mul, hab, one_mul]
          _ = a * x₁.1 + b * x₂.1 := hFirstCombination.symm
      have haEquality : a * (-h.1) = a * x₁.1 := by
        linarith
      exact (mul_left_cancel₀ (ne_of_gt ha) haEquality).symm
  -- Mathlib's full-space extreme-point criterion reduces the claim to open segments.
  rw [mem_extremePoints]
  refine ⟨hTargetMember, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hSegment
  constructor
  · have hFirst : x₁.1 = -h.1 := hFirstEqOfSegment x₁ x₂ hx₁ hx₂ hSegment
    have hTiltFirst : (-x₁).1 = h.1 := by
      change -x₁.1 = h.1
      rw [hFirst]
      ring
    have hTiltEq : -x₁ = h :=
      supporting_tilts_eq_of_first_coord_eq g ξ (-x₁) h hhom
        (hSupportOfMember x₁ hx₁) hSupport hTiltFirst
    calc
      x₁ = -(-x₁) := by simp
      _ = -h := congrArg Neg.neg hTiltEq
  · have hSegmentSymm : -h ∈ openSegment ℝ x₂ x₁ := by
      rw [openSegment_symm]
      exact hSegment
    have hFirst : x₂.1 = -h.1 := hFirstEqOfSegment x₂ x₁ hx₂ hx₁ hSegmentSymm
    have hTiltFirst : (-x₂).1 = h.1 := by
      change -x₂.1 = h.1
      rw [hFirst]
      ring
    have hTiltEq : -x₂ = h :=
      supporting_tilts_eq_of_first_coord_eq g ξ (-x₂) h hhom
        (hSupportOfMember x₂ hx₂) hSupport hTiltFirst
    calc
      x₂ = -(-x₂) := by simp
      _ = -h := congrArg Neg.neg hTiltEq

end LPP.Busemann
