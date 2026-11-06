/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.Quadrant
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Differentiability of a homogeneous quadrant function

At an interior unit-sum point, differentiability of the transverse profile is
equivalent to ambient differentiability of the auxiliary extension. The proof uses only
homogeneity and ordinary local calculus.
-/

public section

open Set Filter
open scoped Topology NNReal

namespace LPPDifferentiability

private theorem quadrantExtension_perspective
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a : ℝ) (y : ℝ × ℝ) (hy₁ : 0 < y.1) (hy₂ : 0 < y.2) :
    quadrantExtension g y = (y.1 + y.2) *
      quadrantExtension g
        (a + (y.1 / (y.1 + y.2) - a), 1 - a - (y.1 / (y.1 + y.2) - a)) := by
  have hs : 0 < y.1 + y.2 := add_pos hy₁ hy₂
  let s : ℝ≥0 := ⟨y.1 + y.2, hs.le⟩
  let z : Quadrant := toQuadrant (y.1 / (y.1 + y.2), y.2 / (y.1 + y.2))
  have hscale : s • z = toQuadrant y := by
    apply Prod.ext
    · apply NNReal.coe_injective
      change (y.1 + y.2) * ((y.1 / (y.1 + y.2)).toNNReal : ℝ) =
        (y.1.toNNReal : ℝ)
      rw [Real.coe_toNNReal _ (div_nonneg hy₁.le hs.le), Real.coe_toNNReal _ hy₁.le]
      exact mul_div_cancel₀ y.1 hs.ne'
    · apply NNReal.coe_injective
      change (y.1 + y.2) * ((y.2 / (y.1 + y.2)).toNNReal : ℝ) =
        (y.2.toNNReal : ℝ)
      rw [Real.coe_toNNReal _ (div_nonneg hy₂.le hs.le), Real.coe_toNNReal _ hy₂.le]
      exact mul_div_cancel₀ y.2 hs.ne'
  have hcoords :
      (a + (y.1 / (y.1 + y.2) - a), 1 - a - (y.1 / (y.1 + y.2) - a)) =
        (y.1 / (y.1 + y.2), y.2 / (y.1 + y.2)) := by
    apply Prod.ext
    · dsimp
      ring
    · dsimp
      field_simp [hs.ne']
      ring
  change g (toQuadrant y) = (y.1 + y.2) * g (toQuadrant _)
  rw [hcoords, ← hscale, hhom]
  rfl

/-- Homogeneity reconstructs the extension from its transverse profile near an
interior point. No concavity or continuity premise is needed. -/
theorem differentiableAt_profile_iff_quadrantExtension
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    DifferentiableAt ℝ (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) 0 ↔
      DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) := by
  constructor
  · intro hprofile
    have hsum : DifferentiableAt ℝ (fun y : ℝ × ℝ => y.1 + y.2) (a, 1 - a) :=
      differentiableAt_fst.add differentiableAt_snd
    have hsum_ne : (a, 1 - a).1 + (a, 1 - a).2 ≠ (0 : ℝ) := by
      dsimp
      rw [show a + (1 - a) = 1 by ring]
      exact one_ne_zero
    have hratio : DifferentiableAt ℝ
        (fun y : ℝ × ℝ => y.1 / (y.1 + y.2) - a) (a, 1 - a) := by
      have hinv : DifferentiableAt ℝ
          (fun y : ℝ × ℝ => (y.1 + y.2)⁻¹) (a, 1 - a) :=
        hsum.fun_inv hsum_ne
      have hmul : DifferentiableAt ℝ
          (fun y : ℝ × ℝ => y.1 * (y.1 + y.2)⁻¹) (a, 1 - a) :=
        differentiableAt_fst.fun_mul hinv
      apply (hmul.sub_const a).congr_of_eventuallyEq
      exact Eventually.of_forall (fun y => by
        dsimp only
        rw [div_eq_mul_inv])
    have hprofile_at : DifferentiableAt ℝ
        (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
        ((a, 1 - a).1 / ((a, 1 - a).1 + (a, 1 - a).2) - a) := by
      have hzero : (a, 1 - a).1 / ((a, 1 - a).1 + (a, 1 - a).2) - a = 0 := by
        dsimp
        rw [show a + (1 - a) = 1 by ring, div_one, sub_self]
      rw [hzero]
      exact hprofile
    have hperspective : DifferentiableAt ℝ
        (fun y : ℝ × ℝ => (y.1 + y.2) *
          quadrantExtension g
            (a + (y.1 / (y.1 + y.2) - a), 1 - a - (y.1 / (y.1 + y.2) - a)))
        (a, 1 - a) := hsum.mul
          (hprofile_at.comp (f := fun y : ℝ × ℝ => y.1 / (y.1 + y.2) - a)
            (g := fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
            (a, 1 - a) hratio)
    apply hperspective.congr_of_eventuallyEq
    have h₁ : {y : ℝ × ℝ | 0 < y.1} ∈ 𝓝 (a, 1 - a) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ha₀
    have h₂ : {y : ℝ × ℝ | 0 < y.2} ∈ 𝓝 (a, 1 - a) :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds (sub_pos.mpr ha₁)
    filter_upwards [h₁, h₂] with y hy₁ hy₂
    exact quadrantExtension_perspective g hhom a y hy₁ hy₂
  · intro hambient
    have haffine : DifferentiableAt ℝ (fun h : ℝ => (a + h, 1 - a - h)) 0 :=
      ((differentiableAt_id).const_add a).prodMk
        ((differentiableAt_id).const_sub (1 - a))
    have hambient_at : DifferentiableAt ℝ (quadrantExtension g)
        ((fun h : ℝ => (a + h, 1 - a - h)) 0) := by
      simpa only [add_zero, sub_zero] using hambient
    exact hambient_at.comp (f := fun h : ℝ => (a + h, 1 - a - h))
      (g := quadrantExtension g) 0 haffine

end LPPDifferentiability
