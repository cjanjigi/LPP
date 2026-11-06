/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.PassageLaw
import Mathlib.Topology.Algebra.Order.Field

/-!
# Geometry of finite expected passage ray limits

These conditional helpers fill the natural lattice part of Martin (2004),
Proposition 2.1 (ii) and (iv). They take as a hypothesis the convergence of
the actual normalized passage expectations. Existence of those limits,
extension to real directions, and the shape theorem are handled in other
files. Signed weights and the zero direction are allowed.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- The zero direction has zero limiting expected passage rate. -/
theorem martin_ray_limit_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a))) :
    g 0 = 0 := by
  have hzero : ∀ (ω : Environment) (n : ℕ),
      lastPassage ω 0 (n • (0 : ℕ × ℕ)) = 0 := by
    intro ω n
    rw [smul_zero]
    exact lastPassage_zero ω 0
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (g 0)) := by
    simpa only [hzero, integral_zero, zero_div] using hlim 0
  exact tendsto_nhds_unique hz tendsto_const_nhds

/-- Natural scaling of a direction scales its limiting expected passage rate.
The positive case uses the actual subsequence with indices `n * k`. -/
theorem martin_ray_limit_nsmul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a)))
    (a : ℕ × ℕ) (k : ℕ) : g (k • a) = (k : ℝ) * g a := by
  by_cases hk : k = 0
  · simpa only [hk, zero_smul, Nat.cast_zero, zero_mul] using
      martin_ray_limit_zero μ g hlim
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hsub : Tendsto (fun n : ℕ => n * k) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hkpos) tendsto_id
  have hscaled := ((hlim a).comp hsub).const_mul (k : ℝ)
  have heq : (fun n : ℕ => (k : ℝ) *
      ((∫ ω : Environment, lastPassage ω 0 ((n * k) • a)
        ∂environmentLaw μ) / ((n * k : ℕ) : ℝ))) =
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • (k • a))
        ∂environmentLaw μ) / (n : ℝ)) := by
    funext n
    rw [mul_smul, Nat.cast_mul]
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, zero_mul, div_zero, mul_zero]
    · have hkreal : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp
  change Tendsto (fun n : ℕ => (k : ℝ) *
    ((∫ ω : Environment, lastPassage ω 0 ((n * k) • a)
      ∂environmentLaw μ) / ((n * k : ℕ) : ℝ))) atTop (𝓝 ((k : ℝ) * g a)) at hscaled
  rw [heq] at hscaled
  exact tendsto_nhds_unique (hlim (k • a)) hscaled

/-- The limiting expected passage rate is superadditive on natural directions.
The finite inequality comes from actual signed path concatenation, finite-passage
integrability, and translation invariance of the environment, as proved in
`integral_lastPassage_superadditive`. -/
theorem martin_ray_limit_superadditive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a)))
    (a b : ℕ × ℕ) : g a + g b ≤ g (a + b) := by
  apply le_of_tendsto_of_tendsto' ((hlim a).add (hlim b)) (hlim (a + b))
  intro n
  have hfinite := integral_lastPassage_superadditive μ hμ 0 (n • a) (n • b)
  have hdiv := div_le_div_of_nonneg_right hfinite (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [add_div, ← smul_add] using hdiv

end LPPDifferentiability
