/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.WeakMoment
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# One-sided mean comparison under weak convergence

The tails below are integrals under the varying laws, not a fixed-measure
uniform-integrability predicate. This is the truncation and Fatou argument that
follows equation (2.13) of Liggett (1985).
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

private theorem integral_clip_error_le_tail (ρ : ProbabilityMeasure ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable g (ρ : Measure ℝ)) (m : ℕ) (R : ℝ) (hRm : R ≤ m) :
    (∫ x, g x ∂(ρ : Measure ℝ)) -
      (∫ x, nonnegativeClip m (g x) ∂(ρ : Measure ℝ)) ≤
        ∫ x in {x | R < g x}, g x ∂(ρ : Measure ℝ) := by
  have hs : MeasurableSet {x | R < g x} := measurableSet_lt measurable_const hg.measurable
  rw [← integral_sub hgi (integrable_nonnegativeClip ρ g hg m), ← integral_indicator hs]
  apply integral_mono (hgi.sub (integrable_nonnegativeClip ρ g hg m)) (hgi.indicator hs)
  intro x
  simp only [Pi.sub_apply]
  by_cases hx : R < g x
  · rw [Set.indicator_of_mem (show x ∈ {x | R < g x} from hx)]
    exact sub_le_self _ (nonnegativeClip_nonneg m (g x))
  · rw [Set.indicator_of_notMem (show x ∉ {x | R < g x} from hx)]
    have hgm : g x ≤ (m : ℝ) := (le_of_not_gt hx).trans hRm
    simp only [nonnegativeClip, max_eq_left (hg0 x), min_eq_left hgm, sub_self, le_refl]

private theorem tendsto_integral_nonneg_of_weak_tails
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν)) (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) (hμ : ∀ n, Integrable g (μ n : Measure ℝ))
    (hν : Integrable g (ν : Measure ℝ))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n,
      (∫ x in {x | R < g x}, g x ∂(μ n : Measure ℝ)) < ε) :
    Tendsto (fun n => ∫ x, g x ∂(μ n : Measure ℝ)) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he : 0 < ε / 3 := by linarith
  obtain ⟨R, hR⟩ := htail (ε / 3) he
  obtain ⟨K, hK⟩ := exists_nat_ge R
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp
    (tendsto_integral_nonnegativeClip ν g hg hg0 hν) (ε / 3) he
  let m := max K M
  have hRm : R ≤ (m : ℝ) := hK.trans (by exact_mod_cast (le_max_left K M))
  have hlimit := hM m (le_max_right K M)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_integral_nonnegativeClip_of_weak μ ν hweak g hg m) (ε / 3) he
  refine ⟨N, fun n hn => ?_⟩
  have herror : dist (∫ x, g x ∂(μ n : Measure ℝ))
      (∫ x, nonnegativeClip m (g x) ∂(μ n : Measure ℝ)) < ε / 3 := by
    rw [Real.dist_eq, abs_of_nonneg]
    · exact (integral_clip_error_le_tail (μ n) g hg hg0 (hμ n) m R hRm).trans_lt (hR n)
    · exact sub_nonneg.mpr (integral_mono (integrable_nonnegativeClip (μ n) g hg m)
        (hμ n) (fun x => nonnegativeClip_le_self m (hg0 x)))
  calc
    _ ≤ dist (∫ x, g x ∂(μ n : Measure ℝ))
          (∫ x, nonnegativeClip m (g x) ∂(μ n : Measure ℝ)) +
        dist (∫ x, nonnegativeClip m (g x) ∂(μ n : Measure ℝ))
          (∫ x, g x ∂(ν : Measure ℝ)) := dist_triangle _ _ _
    _ ≤ dist (∫ x, g x ∂(μ n : Measure ℝ))
          (∫ x, nonnegativeClip m (g x) ∂(μ n : Measure ℝ)) +
        (dist (∫ x, nonnegativeClip m (g x) ∂(μ n : Measure ℝ))
          (∫ x, nonnegativeClip m (g x) ∂(ν : Measure ℝ)) +
        dist (∫ x, nonnegativeClip m (g x) ∂(ν : Measure ℝ))
          (∫ x, g x ∂(ν : Measure ℝ))) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by linarith [hN n hn]

/-- Uniformly vanishing positive-part tails give convergence of positive means.
The uniform absolute moment bound proves the needed limit integrability. -/
theorem tendsto_integral_posPart_of_weak_abs_integral_le_tails
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hμ : ∀ n, Integrable (fun x : ℝ => x) (μ n : Measure ℝ))
    (C : ℝ) (hbound : ∀ n, (∫ x : ℝ, |x| ∂(μ n : Measure ℝ)) ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n,
      (∫ x in {x : ℝ | R < max x 0}, max x 0 ∂(μ n : Measure ℝ)) < ε) :
    Tendsto (fun n => ∫ x : ℝ, max x 0 ∂(μ n : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, max x 0 ∂(ν : Measure ℝ))) := by
  have hν := integrable_id_of_weak_abs_integral_le μ ν hweak hμ C hbound
  exact tendsto_integral_nonneg_of_weak_tails μ ν hweak (fun x : ℝ => max x 0)
    (continuous_id.max continuous_const) (fun x => le_max_right x 0)
    (fun n => (hμ n).pos_part) hν.pos_part htail

private theorem integral_id_eq_pos_sub_neg (ρ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => x) (ρ : Measure ℝ)) :
    (∫ x : ℝ, x ∂(ρ : Measure ℝ)) =
      (∫ x : ℝ, max x 0 ∂(ρ : Measure ℝ)) -
        ∫ x : ℝ, max (-x) 0 ∂(ρ : Measure ℝ) := by
  rw [← integral_sub hi.pos_part hi.neg_part]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : 0 ≤ x
  · simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    simp only [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), zero_sub, neg_neg]

/-- Weak convergence, bounded absolute moments, uniformly vanishing positive
tails and converging ordinary means imply the lower bound on the limit mean
used in the paper. The negative-part Fatou step uses bounded continuous clips. -/
theorem mean_le_of_weak_abs_integral_le_pos_tails
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hμ : ∀ n, Integrable (fun x : ℝ => x) (μ n : Measure ℝ))
    (C : ℝ) (hbound : ∀ n, (∫ x : ℝ, |x| ∂(μ n : Measure ℝ)) ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n,
      (∫ x in {x : ℝ | R < max x 0}, max x 0 ∂(μ n : Measure ℝ)) < ε)
    (γ : ℝ) (hmean : Tendsto (fun n => ∫ x : ℝ, x ∂(μ n : Measure ℝ)) atTop (𝓝 γ)) :
    γ ≤ ∫ x : ℝ, x ∂(ν : Measure ℝ) := by
  have hν := integrable_id_of_weak_abs_integral_le μ ν hweak hμ C hbound
  have hpos := tendsto_integral_posPart_of_weak_abs_integral_le_tails μ ν hweak hμ C hbound htail
  have hclip (m : ℕ) : (∫ x : ℝ, nonnegativeClip m (max (-x) 0) ∂(ν : Measure ℝ)) ≤
      (∫ x : ℝ, max x 0 ∂(ν : Measure ℝ)) - γ := by
    apply le_of_tendsto_of_tendsto
      (tendsto_integral_nonnegativeClip_of_weak μ ν hweak (fun x : ℝ => max (-x) 0)
        (continuous_id.neg.max continuous_const) m) (hpos.sub hmean)
    apply Eventually.of_forall
    intro n
    have hle := integral_mono
      (integrable_nonnegativeClip (μ n) (fun x : ℝ => max (-x) 0)
        (continuous_id.neg.max continuous_const) m)
      (hμ n).neg_part (fun x => nonnegativeClip_le_self m (le_max_right (-x) 0))
    have heq := integral_id_eq_pos_sub_neg (μ n) (hμ n)
    linarith only [hle, heq]
  have hneg : (∫ x : ℝ, max (-x) 0 ∂(ν : Measure ℝ)) ≤
      (∫ x : ℝ, max x 0 ∂(ν : Measure ℝ)) - γ := by
    apply le_of_tendsto (tendsto_integral_nonnegativeClip ν (fun x : ℝ => max (-x) 0)
      (continuous_id.neg.max continuous_const) (fun x => le_max_right (-x) 0) hν.neg_part)
    exact Eventually.of_forall hclip
  have heq := integral_id_eq_pos_sub_neg ν hν
  linarith only [hneg, heq]

end LPPDifferentiability
