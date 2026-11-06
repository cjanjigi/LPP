/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Prod
import ProbabilityBasics.Probability.FiberHoeffding

/-!
# Sharp fiber Hoeffding step

Pairwise oscillation puts each bounded fiber in an interval whose length is
the oscillation bound. Hoeffding's lemma then gives the sharp one-coordinate
MGF factor, and Fubini transfers it to one product step.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

/-- A bounded fiber with oscillation at most `b` has the sharp centered MGF bound.

The interval used in Hoeffding's lemma is the actual range interval
`[sInf (range (fun x => F (x,a))), sInf (range (fun x => F (x,a))) + b]`.
Its lower endpoint is constructed only in this proof.
-/
theorem integral_exp_centered_fiber_le_sharp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M b : ℝ) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) (a : A) (t : ℝ) :
    (∫ x, Real.exp (t * (F (x, a) - ∫ y, F (y, a) ∂μ)) ∂μ) ≤
      Real.exp (b ^ 2 * t ^ 2 / 8) := by
  have hΩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let L : ℝ := sInf (Set.range fun x : Ω => F (x, a))
  have hRangeNonempty : (Set.range fun x : Ω => F (x, a)).Nonempty := by
    rcases hΩ with ⟨x⟩
    exact ⟨F (x, a), Set.mem_range_self x⟩
  have hRangeBddBelow : BddBelow (Set.range fun x : Ω => F (x, a)) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (hbound (x, a))).1
  have hlow (x : Ω) : L ≤ F (x, a) := by
    dsimp [L]
    exact csInf_le hRangeBddBelow (Set.mem_range_self x)
  have hhigh (x : Ω) : F (x, a) ≤ L + b := by
    have hlower : F (x, a) - b ≤ L := by
      change F (x, a) - b ≤ sInf (Set.range fun y : Ω => F (y, a))
      apply le_csInf hRangeNonempty
      intro z hz
      rcases hz with ⟨y, rfl⟩
      have hxy : F (x, a) - F (y, a) ≤ b := (abs_le.mp (hosc a x y)).2
      linarith
    linarith
  have hm : Measurable (fun x => F (x, a)) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hinterval : ∀ᵐ x ∂μ, F (x, a) ∈ Set.Icc L (L + b) :=
    Filter.Eventually.of_forall (fun x => ⟨hlow x, hhigh x⟩)
  have h := hasSubgaussianMGF_of_mem_Icc hm.aemeasurable hinterval
  have hnorm : ‖(L + b) - L‖ = b := by
    rw [Real.norm_eq_abs]
    have hshift : (L + b) - L = b := by ring
    rw [hshift, abs_of_nonneg hb]
  have hcoef : (((‖(L + b) - L‖₊ / 2) ^ 2 : NNReal) : ℝ) = b ^ 2 / 4 := by
    push_cast
    rw [hnorm]
    ring
  have hmgf :
      (∫ x, Real.exp (t * (F (x, a) - ∫ y, F (y, a) ∂μ)) ∂μ) ≤
        Real.exp ((b ^ 2 / 4) * t ^ 2 / 2) := by
    simpa only [mgf, hcoef] using h.mgf_le t
  calc
    _ ≤ Real.exp ((b ^ 2 / 4) * t ^ 2 / 2) := hmgf
    _ = Real.exp (b ^ 2 * t ^ 2 / 8) := by congr 1; ring

/-- One independent fiber contributes the sharp Hoeffding factor to the full centered MGF.

This is the Fubini one-step estimate for the literal product `μ.prod ν`.
-/
theorem integral_exp_sub_integral_le_fiber_sharp (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M b : ℝ) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) (t : ℝ) :
    (∫ z, Real.exp (t * (F z - ∫ w, F w ∂μ.prod ν)) ∂μ.prod ν) ≤
      Real.exp (b ^ 2 * t ^ 2 / 8) *
        ∫ a, Real.exp (t * ((∫ x, F (x, a) ∂μ) - ∫ w, F w ∂μ.prod ν)) ∂ν := by
  let G : A → ℝ := fun a => ∫ x, F (x, a) ∂μ
  let c : ℝ := ∫ a, G a ∂ν
  have hmean : c = ∫ z, F z ∂μ.prod ν :=
    integral_integral_fiber μ ν F M hF hbound
  rw [← hmean]
  have hprod := integrable_exp_prod_sub_const μ ν F M hF hbound c t
  have havg := integrable_exp_integral_fiber_sub_const μ ν F M hF hbound c t
  have hsplit (a : A) :
      (∫ x, Real.exp (t * (F (x, a) - c)) ∂μ) =
        (∫ x, Real.exp (t * (F (x, a) - G a)) ∂μ) * Real.exp (t * (G a - c)) := by
    calc
      _ = ∫ x, Real.exp (t * (F (x, a) - G a)) * Real.exp (t * (G a - c)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          dsimp only
          rw [← Real.exp_add]
          congr 1
          ring)
      _ = _ := integral_mul_const _ _
  calc
    _ = ∫ a, ∫ x, Real.exp (t * (F (x, a) - c)) ∂μ ∂ν :=
      integral_prod_symm _ hprod
    _ ≤ ∫ a, Real.exp (b ^ 2 * t ^ 2 / 8) * Real.exp (t * (G a - c)) ∂ν := by
      apply integral_mono hprod.integral_prod_right (havg.const_mul _)
      intro a
      change (∫ x, Real.exp (t * (F (x, a) - c)) ∂μ) ≤
        Real.exp (b ^ 2 * t ^ 2 / 8) * Real.exp (t * (G a - c))
      rw [hsplit a]
      exact mul_le_mul_of_nonneg_right
        (integral_exp_centered_fiber_le_sharp μ F M b hb hF hbound hosc a t)
        (Real.exp_nonneg _)
    _ = _ := integral_const_mul _ _

end LPPDifferentiability
