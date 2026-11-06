/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinRayGeometry
import Mathlib.Topology.Algebra.Order.Field

/-! # Consistency of natural-direction rates

These are algebraic consequences of natural scaling and superadditivity.
The expected-ray corollaries use the conditional limits of expected passage
values from `MartinRayGeometry`. They do not define a shape on rational
or real directions, or establish that those expected limits exist.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- Natural scaling makes two representations of the same ray give the same
rate after division by their positive denominators. The function may take
signed values, and its numerator may be zero. -/
theorem natural_rate_eq_div_of_smul_eq
    (g : (ℕ × ℕ) → ℝ)
    (hscale : ∀ (k : ℕ) (a : ℕ × ℕ), g (k • a) = (k : ℝ) * g a)
    (a b : ℕ × ℕ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hray : n • a = m • b) :
    g a / (m : ℝ) = g b / (n : ℝ) := by
  have hscaled : (n : ℝ) * g a = (m : ℝ) * g b := by
    calc
      (n : ℝ) * g a = g (n • a) := (hscale n a).symm
      _ = g (m • b) := congrArg g hray
      _ = (m : ℝ) * g b := hscale m b
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [div_eq_div_iff hm0 hn0]
  calc
    g a * (n : ℝ) = (n : ℝ) * g a := mul_comm _ _
    _ = (m : ℝ) * g b := hscaled
    _ = g b * (m : ℝ) := mul_comm _ _

/-- Superadditivity remains valid after division by a positive natural
denominator shared by all three rates. -/
theorem natural_rate_add_div_le_of_superadditive
    (g : (ℕ × ℕ) → ℝ)
    (hadd : ∀ a b : ℕ × ℕ, g a + g b ≤ g (a + b))
    (a b : ℕ × ℕ) (d : ℕ) (hd : 0 < d) :
    g a / (d : ℝ) + g b / (d : ℝ) ≤ g (a + b) / (d : ℝ) := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdiv := div_le_div_of_nonneg_right (hadd a b) hdreal.le
  simpa only [add_div] using hdiv

/-- Expected-ray limits have consistent rates on two natural
representations of the same ray, whenever those conditional limits exist. -/
theorem martin_ray_limit_rate_eq_div_of_smul_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a)))
    (a b : ℕ × ℕ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hray : n • a = m • b) :
    g a / (m : ℝ) = g b / (n : ℝ) := by
  exact natural_rate_eq_div_of_smul_eq g
    (fun k a => martin_ray_limit_nsmul μ g hlim a k) a b m n hm hn hray

/-- Superadditivity of expected-ray limits also gives the normalized
addition inequality, provided the common denominator is positive. -/
theorem martin_ray_limit_add_div_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a)))
    (a b : ℕ × ℕ) (d : ℕ) (hd : 0 < d) :
    g a / (d : ℝ) + g b / (d : ℝ) ≤ g (a + b) / (d : ℝ) := by
  exact natural_rate_add_div_le_of_superadditive g
    (martin_ray_limit_superadditive μ hμ g hlim) a b d hd

end LPPDifferentiability
