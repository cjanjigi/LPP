/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinRayGeometry
public import Martin2004.Probability.MartinRayConvergence
public import LPP_Foundations.Probability.PassageAxisMean
public import LPP_Foundations.Probability.PassageMeanBounds

/-!
# The natural-direction passage rate

The ray theorem determines a unique rate function on natural planar
directions, with expected, almost-sure and mean convergence, natural geometry,
exact axis rates and a path-mean lower bound. The optional upper inequality is
an algebraic corollary with a law-dependent coefficient. No real-direction
extension, uniform convergence, or full shape theorem is asserted.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace LPPDifferentiability

/-- The horizontal limiting rate is its displacement times the marginal mean. -/
theorem martin_ray_limit_horizontal (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a))) (k : ℕ) :
    g (k, 0) = (k : ℝ) * ∫ x : ℝ, x ∂μ := by
  have haxis : Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • (k, 0))
        ∂environmentLaw μ) / (n : ℝ)) atTop
      (𝓝 ((k : ℝ) * ∫ x : ℝ, x ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hd : n • (k, 0) = (n * k, 0) := by ext <;> simp
    rw [hd, integral_lastPassage_horizontal μ hμ, Nat.cast_mul]
    have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp
  exact tendsto_nhds_unique (hlim (k, 0)) haxis

/-- The vertical limiting rate is its displacement times the marginal mean. -/
theorem martin_ray_limit_vertical (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a))) (k : ℕ) :
    g (0, k) = (k : ℝ) * ∫ x : ℝ, x ∂μ := by
  have haxis : Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • (0, k))
        ∂environmentLaw μ) / (n : ℝ)) atTop
      (𝓝 ((k : ℝ) * ∫ x : ℝ, x ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hd : n • (0, k) = (0, n * k) := by ext <;> simp
    rw [hd, integral_lastPassage_vertical μ hμ, Nat.cast_mul]
    have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp
  exact tendsto_nhds_unique (hlim (0, k)) haxis

/-- A fixed path bounds the natural limiting rate below by length times mean. -/
theorem martin_ray_limit_ge_path_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a))) (a : ℕ × ℕ) :
    ((a.1 + a.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤ g a := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlim a)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hfinite := integral_lastPassage_ge_path_mean μ hμ 0 (n • a)
  have hdiv := div_le_div_of_nonneg_right hfinite (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hlen : (((n • a).1 + (n • a).2 : ℕ) : ℝ) =
      (n : ℝ) * ((a.1 + a.2 : ℕ) : ℝ) := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Nat.cast_add, Nat.cast_mul]
    ring
  rw [hlen] at hdiv
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simpa only [mul_assoc, mul_div_cancel_left₀ _ hnreal] using hdiv


/-- A finite upper linear rate bound follows by completing a direction to a
square and bounding the complementary direction by its path mean. This
law-dependent coefficient is not the universal square-root-tail estimate. -/
theorem martin_ray_limit_le_diagonal_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0 (n • a)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g a))) (a : ℕ × ℕ) :
    g a ≤ ((a.1 + a.2 : ℕ) : ℝ) * (g (1, 1) - ∫ x : ℝ, x ∂μ) := by
  have hs := martin_ray_limit_superadditive μ hμ g hlim a (a.2, a.1)
  have hsum : a + (a.2, a.1) = (a.1 + a.2) • (1, 1) := by
    ext <;> simp [Nat.add_comm]
  rw [hsum, martin_ray_limit_nsmul μ g hlim] at hs
  have hlo := martin_ray_limit_ge_path_mean μ hμ g hlim (a.2, a.1)
  simp only [Nat.add_comm a.2 a.1] at hlo
  rw [mul_sub]
  linarith only [hs, hlo]


/-- Martin's two square-root tails determine a unique natural-direction rate
function for the terminal-excluded passage values. This is the natural
lattice stage, with no extension or continuity assertion on real directions. -/
theorem exists_unique_lastPassage_natural_shape_of_martin_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : (ℕ × ℕ) → ℝ,
      (∀ a : ℕ × ℕ,
        Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
          atTop (𝓝 (g a)) ∧
        g a = sSup (range (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 ((n + 1) • a) ∂environmentLaw μ) /
            ((n + 1 : ℕ) : ℝ))) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto
          (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a))) ∧
        Tendsto (fun n : ℕ => ∫ ω : Environment,
          |lastPassage ω 0 (n • a) / (n : ℝ) - g a| ∂environmentLaw μ)
          atTop (𝓝 0)) ∧
      g 0 = 0 ∧
      (∀ (a : ℕ × ℕ) (k : ℕ), g (k • a) = (k : ℝ) * g a) ∧
      (∀ a b : ℕ × ℕ, g a + g b ≤ g (a + b)) ∧
      (∀ k : ℕ, g (k, 0) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ k : ℕ, g (0, k) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ a : ℕ × ℕ,
        ((a.1 + a.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤ g a ∧
        g a ≤ ((a.1 + a.2 : ℕ) : ℝ) * (g (1, 1) - ∫ x : ℝ, x ∂μ)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a))) := by
  classical
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  have hrays := fun a : ℕ × ℕ =>
    exists_lastPassage_ray_convergence_of_martin_tails μ hneg hpos a
  choose g hg using hrays
  have hlim := fun a : ℕ × ℕ => (hg a).1
  refine ⟨g, ?_, ?_⟩
  · refine ⟨hg, martin_ray_limit_zero μ g hlim,
      martin_ray_limit_nsmul μ g hlim,
      martin_ray_limit_superadditive μ hμ g hlim,
      martin_ray_limit_horizontal μ hμ g hlim,
      martin_ray_limit_vertical μ hμ g hlim, ?_, ?_⟩
    · intro a
      exact ⟨martin_ray_limit_ge_path_mean μ hμ g hlim a,
        martin_ray_limit_le_diagonal_mean μ hμ g hlim a⟩
    · exact ae_all_iff.mpr (fun a => (hg a).2.2.1)
  · intro f hf
    funext a
    exact tendsto_nhds_unique (hf.1 a).1 (hlim a)

end LPPDifferentiability
