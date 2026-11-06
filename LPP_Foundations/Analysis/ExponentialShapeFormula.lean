/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The exponential shape formula (pure real analysis)

In the proof of Martin (2004), Theorem 2.4, the boundary value of the shape for the
exponential law with mean 1 is `1 + 2 √α + α`. This module names the closed formula
`(√x + √y)^2` on the quadrant, the parameter `ρ = √y / (√x + √y)` at which the
stationary model matches a direction, and the finite grid bound used in the
lower bound. It proves only the algebra: the parameter lies strictly between
0 and 1, the stationary identity holds at that parameter, and the boundary
value on the ray `(1, a)` is `1 + 2 √a + a`.

The exponential shape is defined here by its closed formula. Deriving it from
the exponential last-passage model needs the stationary model with the Burke
property, so nothing in this file is a probabilistic result.
-/

@[expose] public section

open scoped NNReal

namespace LPPDifferentiability

/-- The exponential shape `(√x + √y)^2` on the closed quadrant. This is the
closed formula stated in the proof of Martin (2004), Theorem 2.4, for exponential
weights of mean 1. -/
noncomputable def exponentialShape (x : Quadrant) : ℝ :=
  (Real.sqrt (x.1 : ℝ) + Real.sqrt (x.2 : ℝ)) ^ 2

/-- The parameter `ρ = √y / (√x + √y)` of the stationary model adapted to the
direction `(x, y)`. -/
noncomputable def characteristicParameter (x y : ℝ≥0) : ℝ :=
  Real.sqrt (y : ℝ) / (Real.sqrt (x : ℝ) + Real.sqrt (y : ℝ))

/-- The maximum, over the `K` exit grid points `r`, of the two sums of the discretized
exit terms. The first sum uses the weight `1 - ρ` on the horizontal axis and the second
uses `ρ` on the vertical axis. This is a plain finite maximum of real numbers, with no
probability in it. -/
noncomputable def exitGridBound (g : Quadrant → ℝ) (ρ : ℝ) (x y : ℝ≥0) (K : ℕ) : ℝ :=
  ⨆ r : Fin K, max
    ((((r : ℕ) : ℝ) + 1) / K * x / (1 - ρ) + g (x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K, y))
    ((((r : ℕ) : ℝ) + 1) / K * y / ρ + g (x, y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K))

/-- Real algebra behind `characteristicParameter_spec`, stated for positive reals
`a = √x` and `b = √y`. With `ρ = b / (a + b)` we have `0 < ρ < 1`,
`1 - ρ = a / (a + b)`, and `a^2 / (1 - ρ) + b^2 / ρ = (a + b)^2`. -/
private theorem characteristicParameter_aux (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < b / (a + b) ∧ b / (a + b) < 1 ∧
      a ^ 2 / (1 - b / (a + b)) + b ^ 2 / (b / (a + b)) = (a + b) ^ 2 := by
  have hs : 0 < a + b := add_pos ha hb
  have hne : a + b ≠ 0 := ne_of_gt hs
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have h1 : 1 - b / (a + b) = a / (a + b) := by
    field_simp
    ring
  refine ⟨div_pos hb hs, ?_, ?_⟩
  · rw [div_lt_one hs]
    linarith
  · rw [h1]
    field_simp

/-- Algebra for the characteristic parameter. For `x, y > 0` the parameter
`ρ = √y / (√x + √y)` lies strictly between 0 and 1, and at this parameter
`x / (1 - ρ) + y / ρ` equals `(√x + √y)^2`, the exponential shape at `(x, y)`. -/
theorem characteristicParameter_spec {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    0 < characteristicParameter x y ∧ characteristicParameter x y < 1 ∧
    (x : ℝ) / (1 - characteristicParameter x y) + (y : ℝ) / characteristicParameter x y =
      exponentialShape (x, y) := by
  have hx' : (0 : ℝ) < (x : ℝ) := NNReal.coe_pos.mpr hx
  have hy' : (0 : ℝ) < (y : ℝ) := NNReal.coe_pos.mpr hy
  have ha : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hx'
  have hb : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.mpr hy'
  have hxa : (x : ℝ) = Real.sqrt (x : ℝ) ^ 2 := (Real.sq_sqrt hx'.le).symm
  have hyb : (y : ℝ) = Real.sqrt (y : ℝ) ^ 2 := (Real.sq_sqrt hy'.le).symm
  obtain ⟨hpos, hlt, hid⟩ := characteristicParameter_aux (Real.sqrt (x : ℝ))
    (Real.sqrt (y : ℝ)) ha hb
  rw [← hxa, ← hyb] at hid
  exact ⟨hpos, hlt, hid⟩

/-- The boundary value of the exponential shape on the ray `(1, a)`:
`(√1 + √a)^2 = 1 + 2 √a + a`. This is the formula stated in the proof of Martin (2004),
Theorem 2.4, for exponential weights of mean 1. -/
theorem exponentialShape_one_left (a : ℝ≥0) :
    exponentialShape (1, a) = 1 + 2 * Real.sqrt (a : ℝ) + a := by
  have h := Real.sq_sqrt (NNReal.coe_nonneg a)
  show (Real.sqrt ((1 : ℝ≥0) : ℝ) + Real.sqrt (a : ℝ)) ^ 2 = 1 + 2 * Real.sqrt (a : ℝ) + a
  rw [NNReal.coe_one, Real.sqrt_one]
  linear_combination h

end LPPDifferentiability
