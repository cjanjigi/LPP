/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.HomogeneousRescaling
public import LPP_Foundations.Analysis.ShapeProfileCalculus
public import Differentiability.Probability.BoundedIntervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Assembly of differentiability from the directional profile

Theorem 2.1 of the differentiability preprint says that the shape function is differentiable at
every point of the relative interior of the segment `{(t, 1 - t)}`, and that
this is equivalent to differentiability on the whole open quadrant, because of
homogeneity. This module states the deterministic parts of that assembly in
the forms used for the main theorem.

* If the two one-sided derivatives of the profile `h ↦ g (a + h, 1 - a - h)`
  at `0` agree, then the quadrant extension is differentiable at `(a, 1 - a)`.
* Differentiability at every point `(a, 1 - a)` with `0 < a < 1` gives
  differentiability at every point of the open quadrant.
* A law whose values are almost surely bounded satisfies the negative-moment
  and positive tail hypotheses.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LPPDifferentiability

/-- If the left and right derivatives of the profile at `0` agree, the quadrant
extension is differentiable at the point `(a, 1 - a)` of the segment. -/
theorem differentiableAt_quadrantExtension_of_profile_derivWithin_eq
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤
        g (r * x.1 + s * y.1, r * x.2 + s * y.2))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (heq :
      derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
          (Iio 0) 0 =
        derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
          (Ioi 0) 0) :
    DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) :=
  (differentiableAt_quadrantExtension_iff_profile_derivatives_eq g hconc hhom a
    ha₀ ha₁).mpr heq

/-- Differentiability at every point of the open segment gives
differentiability at every point of the open quadrant, by homogeneity. -/
theorem differentiableAt_quadrantExtension_of_segment
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hseg : ∀ a : ℝ, 0 < a → a < 1 →
      DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a)) :
    ∀ x : ℝ × ℝ, 0 < x.1 → 0 < x.2 →
      DifferentiableAt ℝ (quadrantExtension g) x := by
  intro x hx₁ hx₂
  have hs : 0 < x.1 + x.2 := add_pos hx₁ hx₂
  rw [differentiableAt_quadrantExtension_iff_normalized g hhom x hx₁ hx₂]
  have h₂ : x.2 / (x.1 + x.2) = 1 - x.1 / (x.1 + x.2) := by
    field_simp
    ring
  have hseg' := hseg (x.1 / (x.1 + x.2)) (div_pos hx₁ hs)
    ((div_lt_one hs).mpr (by linarith))
  rwa [← h₂] at hseg'

/-- The deterministic assembly: equal one-sided profile derivatives at every
point of the open segment give differentiability on the open quadrant. -/
theorem differentiableAt_quadrantExtension_of_profile_derivatives_eq
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤
        g (r * x.1 + s * y.1, r * x.2 + s * y.2))
    (heq : ∀ a : ℝ, 0 < a → a < 1 →
      derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
          (Iio 0) 0 =
        derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
          (Ioi 0) 0) :
    ∀ x : ℝ × ℝ, 0 < x.1 → 0 < x.2 →
      DifferentiableAt ℝ (quadrantExtension g) x :=
  differentiableAt_quadrantExtension_of_segment g hhom fun a ha₀ ha₁ =>
    differentiableAt_quadrantExtension_of_profile_derivWithin_eq g hhom hconc a
      ha₀ ha₁ (heq a ha₀ ha₁)

/-- A law that is almost surely bounded has a finite negative moment of some
order above one and a finite integrated positive square-root tail. -/
theorem bounded_law_negative_moment_and_positive_sqrt_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∃ M : ℝ, ∀ᵐ x ∂μ, |x| ≤ M) :
    (∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞) ∧
    (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  obtain ⟨_M, _hM, _hMb, _hint, hneg, hpos⟩ := bounded_marginal_shape_inputs μ hbound
  exact ⟨hneg, hpos⟩

/-- A law that is almost surely bounded has a finite positive moment of every
order, in particular of some order above four. -/
theorem bounded_law_positive_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∃ M : ℝ, ∀ᵐ x ∂μ, |x| ≤ M) :
    ∃ ppos : ℝ, 4 < ppos ∧
      (∫⁻ t, ENNReal.ofReal ((max t 0) ^ ppos) ∂μ) < ∞ := by
  obtain ⟨M, hM, hMb, _hint, _hneg, _hpos⟩ := bounded_marginal_shape_inputs μ hbound
  refine ⟨5, by norm_num, ?_⟩
  have hpt : ∀ᵐ x ∂μ,
      ENNReal.ofReal ((max x 0) ^ (5 : ℝ)) ≤ ENNReal.ofReal (M ^ (5 : ℝ)) := by
    filter_upwards [hMb] with x hx
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le ((le_abs_self x).trans hx) hM.le) (by norm_num)
  calc
    _ ≤ ∫⁻ _x : ℝ, ENNReal.ofReal (M ^ (5 : ℝ)) ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (M ^ (5 : ℝ)) := by simp
    _ < ∞ := ENNReal.ofReal_lt_top

end LPPDifferentiability
