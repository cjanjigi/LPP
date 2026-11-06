/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Constructions

/-! The literal proper-integer-interval array and its diagonal shift.
These are typing aliases, with no values on empty or reversed intervals. -/

@[expose] public section

namespace LPPDifferentiability

/-- Integer intervals with strictly ordered endpoints. -/
abbrev BilateralInterval := {p : ℤ × ℤ // p.1 < p.2}

/-- The full array on proper integer intervals. -/
abbrev BilateralArray := BilateralInterval → ℝ

/-- Translate both endpoints, preserving the proper-interval domain. -/
def bilateralIntervalTranslate (k : ℤ) (p : BilateralInterval) : BilateralInterval :=
  ⟨(p.val.1 + k, p.val.2 + k), by have hp := p.property; omega⟩

/-- Diagonal unit shift of the full array. -/
def bilateralArrayShift (x : BilateralArray) (p : BilateralInterval) : ℝ :=
  x (bilateralIntervalTranslate 1 p)

/-- Diagonal inverse unit shift of the full array. -/
def bilateralArrayUnshift (x : BilateralArray) (p : BilateralInterval) : ℝ :=
  x (bilateralIntervalTranslate (-1) p)

@[simp] theorem bilateralArrayShift_apply (x : BilateralArray) (a b : ℤ) (h : a < b) :
    bilateralArrayShift x ⟨(a, b), h⟩ = x ⟨(a + 1, b + 1), by omega⟩ := rfl

@[simp] theorem bilateralArrayUnshift_apply (x : BilateralArray) (a b : ℤ) (h : a < b) :
    bilateralArrayUnshift x ⟨(a, b), h⟩ = x ⟨(a - 1, b - 1), by omega⟩ := rfl

theorem bilateralArrayUnshift_shift (x : BilateralArray) :
    bilateralArrayUnshift (bilateralArrayShift x) = x := by
  funext p
  change x (bilateralIntervalTranslate 1 (bilateralIntervalTranslate (-1) p)) = x p
  congr 1
  apply Subtype.ext
  apply Prod.ext <;> dsimp only [bilateralIntervalTranslate] <;> omega

theorem bilateralArrayShift_unshift (x : BilateralArray) :
    bilateralArrayShift (bilateralArrayUnshift x) = x := by
  funext p
  change x (bilateralIntervalTranslate (-1) (bilateralIntervalTranslate 1 p)) = x p
  congr 1
  apply Subtype.ext
  apply Prod.ext <;> dsimp only [bilateralIntervalTranslate] <;> omega

theorem continuous_bilateralArrayShift : Continuous bilateralArrayShift :=
  continuous_pi fun p => continuous_apply (bilateralIntervalTranslate 1 p)

theorem continuous_bilateralArrayUnshift : Continuous bilateralArrayUnshift :=
  continuous_pi fun p => continuous_apply (bilateralIntervalTranslate (-1) p)

theorem measurable_bilateralArrayShift : Measurable bilateralArrayShift :=
  Measurable.of_eval fun p => measurable_pi_apply (bilateralIntervalTranslate 1 p)

theorem measurable_bilateralArrayUnshift : Measurable bilateralArrayUnshift :=
  Measurable.of_eval fun p => measurable_pi_apply (bilateralIntervalTranslate (-1) p)

/-- The literal shift is an invertible homeomorphism of the whole array space. -/
def bilateralArrayShiftHomeomorph : BilateralArray ≃ₜ BilateralArray where
  toFun := bilateralArrayShift
  invFun := bilateralArrayUnshift
  left_inv := bilateralArrayUnshift_shift
  right_inv := bilateralArrayShift_unshift
  continuous_toFun := continuous_bilateralArrayShift
  continuous_invFun := continuous_bilateralArrayUnshift

@[simp] theorem bilateralArrayShiftHomeomorph_apply (x : BilateralArray) :
    bilateralArrayShiftHomeomorph x = bilateralArrayShift x := rfl

@[simp] theorem bilateralArrayShiftHomeomorph_symm_apply (x : BilateralArray) :
    bilateralArrayShiftHomeomorph.symm x = bilateralArrayUnshift x := rfl

end LPPDifferentiability
