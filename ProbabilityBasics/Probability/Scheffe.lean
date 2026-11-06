/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Scheffe convergence from minima

For nonnegative integrable real functions, convergence of the integrals and
almost everywhere convergence of the minima with the limiting function imply
convergence in integral absolute difference. The ordinary almost everywhere
convergence version follows by continuity of minimum.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

private theorem abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

/-- Convergence of nonnegative integrable functions in integral absolute
difference, from convergence of their minima and their integrals. -/
theorem tendsto_integral_abs_sub_of_ae_min {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) ν) (hg : Integrable g ν)
    (hf_nonneg : ∀ n, ∀ᵐ ω ∂ν, 0 ≤ f n ω) (hg_nonneg : ∀ᵐ ω ∂ν, 0 ≤ g ω)
    (hmin : ∀ᵐ ω ∂ν, Tendsto (fun n => min (f n ω) (g ω)) atTop (𝓝 (g ω)))
    (hmean : Tendsto (fun n => ∫ ω, f n ω ∂ν) atTop (𝓝 (∫ ω, g ω ∂ν))) :
    Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂ν) atTop (𝓝 0) := by
  have hmin_integrable (n : ℕ) : Integrable (fun ω => min (f n ω) (g ω)) ν :=
    (hf n).inf hg
  have hmin_mean : Tendsto (fun n => ∫ ω, min (f n ω) (g ω) ∂ν)
      atTop (𝓝 (∫ ω, g ω ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω => |g ω|)
      (fun n => (hmin_integrable n).aestronglyMeasurable) hg.abs _ hmin
    intro n
    filter_upwards [hf_nonneg n, hg_nonneg] with ω hfω hgω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfω hgω), abs_of_nonneg hgω]
    exact min_le_right _ _
  have hint (n : ℕ) : (∫ ω, |f n ω - g ω| ∂ν) =
      (∫ ω, f n ω ∂ν) + (∫ ω, g ω ∂ν) - 2 * (∫ ω, min (f n ω) (g ω) ∂ν) := by
    calc
      _ = ∫ ω, (f n ω + g ω) - 2 * min (f n ω) (g ω) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all ν (fun ω => abs_sub_eq_add_sub_two_min _ _)
      _ = _ := by
        have hsum : Integrable (fun ω => f n ω + g ω) ν := (hf n).add hg
        rw [integral_sub hsum ((hmin_integrable n).const_mul 2),
          integral_add (hf n) hg, integral_const_mul]
  have hlim : Tendsto
      (fun n => (∫ ω, f n ω ∂ν) + (∫ ω, g ω ∂ν) -
        2 * (∫ ω, min (f n ω) (g ω) ∂ν)) atTop
      (𝓝 ((∫ ω, g ω ∂ν) + (∫ ω, g ω ∂ν) - 2 * (∫ ω, g ω ∂ν))) :=
    (hmean.add tendsto_const_nhds).sub (tendsto_const_nhds.mul hmin_mean)
  have hzero : (∫ ω, g ω ∂ν) + (∫ ω, g ω ∂ν) - 2 * (∫ ω, g ω ∂ν) = 0 := by ring
  rw [hzero] at hlim
  exact hlim.congr' (Eventually.of_forall fun n => (hint n).symm)

/-- Scheffe's conclusion for nonnegative integrable real functions with almost
everywhere convergence and convergence of their integrals. -/
theorem tendsto_integral_abs_sub_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) ν) (hg : Integrable g ν)
    (hf_nonneg : ∀ n, ∀ᵐ ω ∂ν, 0 ≤ f n ω) (hg_nonneg : ∀ᵐ ω ∂ν, 0 ≤ g ω)
    (hconv : ∀ᵐ ω ∂ν, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hmean : Tendsto (fun n => ∫ ω, f n ω ∂ν) atTop (𝓝 (∫ ω, g ω ∂ν))) :
    Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂ν) atTop (𝓝 0) := by
  apply tendsto_integral_abs_sub_of_ae_min hf hg hf_nonneg hg_nonneg _ hmean
  filter_upwards [hconv] with ω hω
  simpa only [min_self] using hω.min (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => g ω) atTop (𝓝 (g ω)))

end LPPDifferentiability
