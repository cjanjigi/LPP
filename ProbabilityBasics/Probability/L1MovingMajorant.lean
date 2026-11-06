/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral convergence with moving L1 majorants

Clipping against the limiting majorant reduces convergence to dominated
convergence. A second helper applies this to positive errors of signed
functions, then uses convergence of their actual integrals.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

private theorem abs_le_sub_add_min {a b c : ℝ} (hab : |a| ≤ |b|) :
    |a| ≤ |b - c| + min |a| |c| := by
  rcases le_total |a| |c| with hac | hca
  · rw [min_eq_left hac]
    exact le_add_of_nonneg_left (abs_nonneg _)
  · rw [min_eq_right hca]
    calc
      |a| ≤ |b| := hab
      _ = |(b - c) + c| := by rw [sub_add_cancel]
      _ ≤ |b - c| + |c| := abs_add_le _ _

/-- Almost everywhere convergence to zero and domination by an integrable
sequence converging in integral absolute difference imply convergence in
integral absolute value. No pointwise convergence of the majorants is needed. -/
theorem tendsto_integral_abs_of_ae_tendsto_of_l1_majorant
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h g : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hh : ∀ n, Integrable (h n) μ) (hg : ∀ n, Integrable (g n) μ)
    (hG : Integrable G μ)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => h n ω) atTop (𝓝 0))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, |h n ω| ≤ |g n ω|)
    (hgconv : Tendsto (fun n => ∫ ω, |g n ω - G ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |h n ω| ∂μ) atTop (𝓝 0) := by
  have hclip (n : ℕ) : Integrable (fun ω => min |h n ω| |G ω|) μ :=
    (hh n).abs.inf hG.abs
  have hclip_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun n => min |h n ω| |G ω|) atTop (𝓝 0) := by
    filter_upwards [hconv] with ω hω
    simpa only [abs_zero, min_eq_left (abs_nonneg (G ω))] using
      hω.abs.min (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => |G ω|) atTop (𝓝 |G ω|))
  have hclip_mean : Tendsto (fun n => ∫ ω, min |h n ω| |G ω| ∂μ)
      atTop (𝓝 0) := by
    have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
      (fun ω => |G ω|) (fun n => (hclip n).aestronglyMeasurable) hG.abs
      (fun n => ae_of_all μ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) (abs_nonneg _))]
        exact min_le_right _ _) hclip_conv
    simpa only [integral_zero] using hdct
  have hbound (n : ℕ) : (∫ ω, |h n ω| ∂μ) ≤
      (∫ ω, |g n ω - G ω| ∂μ) + ∫ ω, min |h n ω| |G ω| ∂μ := by
    have hdiff : Integrable (fun ω => |g n ω - G ω|) μ := ((hg n).sub hG).abs
    rw [← integral_add hdiff (hclip n)]
    apply integral_mono_ae (hh n).abs (hdiff.add (hclip n))
    filter_upwards [hdom n] with ω hω
    exact abs_le_sub_add_min hω
  have hsum := hgconv.add hclip_mean
  simp only [add_zero] at hsum
  exact squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hbound hsum

private theorem abs_eq_two_mul_pos_part_sub (x : ℝ) :
    |x| = 2 * max x 0 - x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring
  · rw [abs_of_nonpos hx, max_eq_right hx]
    ring

/-- Signed L1 convergence from almost everywhere convergence, convergence of
means, and a moving L1 majorant for the positive errors. These are
ordinary analytic hypotheses to be established by each later application. -/
theorem tendsto_integral_abs_sub_of_ae_tendsto_of_pos_l1_majorant
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ)
    (hg : ∀ n, Integrable (g n) μ) (hG : Integrable G μ)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)))
    (hmean : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, F ω ∂μ)))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, |max (f n ω - F ω) 0| ≤ |g n ω|)
    (hgconv : Tendsto (fun n => ∫ ω, |g n ω - G ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |f n ω - F ω| ∂μ) atTop (𝓝 0) := by
  have hdiff (n : ℕ) : Integrable (fun ω => f n ω - F ω) μ := (hf n).sub hF
  have hpos (n : ℕ) : Integrable (fun ω => max (f n ω - F ω) 0) μ :=
    (hdiff n).pos_part
  have hpos_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun n => max (f n ω - F ω) 0) atTop (𝓝 0) := by
    filter_upwards [hconv] with ω hω
    simpa only [sub_self, max_self] using
      (hω.sub (tendsto_const_nhds (x := F ω))).max (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hpos_mean : Tendsto (fun n => ∫ ω, max (f n ω - F ω) 0 ∂μ)
      atTop (𝓝 0) := by
    have h := tendsto_integral_abs_of_ae_tendsto_of_l1_majorant
      hpos hg hG hpos_conv hdom hgconv
    have habs (n : ℕ) (ω : Ω) : |max (f n ω - F ω) 0| = max (f n ω - F ω) 0 :=
      abs_of_nonneg (le_max_right (f n ω - F ω) (0 : ℝ))
    simpa only [habs] using h
  have hint (n : ℕ) : (∫ ω, |f n ω - F ω| ∂μ) =
      2 * (∫ ω, max (f n ω - F ω) 0 ∂μ) -
        ((∫ ω, f n ω ∂μ) - ∫ ω, F ω ∂μ) := by
    calc
      _ = ∫ ω, 2 * max (f n ω - F ω) 0 - (f n ω - F ω) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ fun ω => abs_eq_two_mul_pos_part_sub _
      _ = _ := by
        rw [integral_sub ((hpos n).const_mul 2) (hdiff n), integral_const_mul,
          integral_sub (hf n) hF]
  have hlim := ((tendsto_const_nhds (x := (2 : ℝ))).mul hpos_mean).sub
    (hmean.sub (tendsto_const_nhds (x := ∫ ω, F ω ∂μ)))
  simp only [mul_zero, sub_self] at hlim
  exact hlim.congr' (Eventually.of_forall fun n => (hint n).symm)

end LPPDifferentiability
