/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions

import LPP_Foundations.Model.LastPassage.Axes
import LPP_Foundations.Probability.CoordinateLaw
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic

/-! A finite uniform shape for upper-bounded weights forces a finite negative mean. -/

public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators NNReal ENNReal

namespace LPPDifferentiability.FinalDraft

/-- The actual uniform shape estimate gives the normalized horizontal passage limit. -/
private theorem ae_horizontal_rate_of_shape (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → ℝ) (hg : LPPStatements.IsShapeFunction μ g) :
    ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (n, 0) / (n : ℝ)) atTop (𝓝 (g (1, 0))) := by
  filter_upwards [hg.2.2.2] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := hω (ε / 2) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n :=
    Nat.cast_pos.mpr ((le_max_right N 1).trans hn)
  have hb := hN (n, 0) (by simpa only [Nat.add_zero] using (le_max_left N 1).trans hn)
  have hs := hg.2.1 (n : ℝ≥0) (1, 0)
  simp only [mul_one, mul_zero, NNReal.coe_natCast] at hs
  dsimp only at hb
  simp only [Nat.cast_zero, Nat.add_zero] at hb
  rw [hs] at hb
  have heq : lastPassage ω 0 (n, 0) / (n : ℝ) - g (1, 0) =
      (lastPassage ω 0 (n, 0) - (n : ℝ) * g (1, 0)) / (n : ℝ) := by
    rw [sub_div, mul_div_cancel_left₀ _ hnR.ne']
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hnR, div_lt_iff₀ hnR]
  simpa only [Prod.zero_eq_mk] using hb.trans_lt (mul_lt_mul_of_pos_right (by linarith) hnR)

/-- Average a bounded negative-part truncation along the deterministic horizontal ray. -/
private theorem ae_horizontal_average (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (hfi : Integrable f μ) :
    ∀ᵐ ω ∂environmentLaw μ, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, f (ω ((k : ℤ), 0))) / (n : ℝ))
      atTop (𝓝 (∫ t : ℝ, f t ∂μ)) := by
  let z (k : ℕ) : Lattice := ((k : ℤ), 0)
  have hinj : Function.Injective z := fun _ _ h => Int.ofNat.inj (congrArg Prod.fst h)
  have hind := ((iIndepFun_environment_eval μ).precomp hinj).comp (fun _ => f) (fun _ => hf)
  have hmarginal (k : ℕ) :
      IdentDistrib (fun ω : Environment => ω (z k)) id (environmentLaw μ) μ :=
    ⟨(measurable_environment_eval _).aemeasurable, measurable_id.aemeasurable,
      (environmentLaw_map_eval μ _).trans Measure.map_id.symm⟩
  have hi (k : ℕ) : IdentDistrib (fun ω : Environment => f (ω (z k))) f
      (environmentLaw μ) μ := (hmarginal k).comp hf
  have hs := strong_law_ae_real (fun k (ω : Environment) => f (ω (z k)))
    ((hi 0).integrable_iff.mpr hfi)
    (fun _ _ h => hind.indepFun h) (fun k => (hi k).trans (hi 0).symm)
  simpa only [(hi 0).integral_eq, z] using hs

/-- For upper-bounded weights, a finite almost-sure horizontal passage rate
forces a finite negative first moment (differentiability final draft, subsection `sub:lb_mom_chat`). -/
theorem negative_mean_finite_of_upper_bound_and_horizontal_rate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ)
    (hb : ∀ᵐ t ∂μ, t ≤ b) (r : ℝ)
    (hlimit : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (n, 0) / (n : ℝ)) atTop (𝓝 r)) :
    (∫⁻ t, ENNReal.ofReal (max (-t) 0) ∂μ) < ∞ := by
  let f (m : ℕ) (t : ℝ) := min (max (-t) 0) (m : ℝ)
  have hf (m : ℕ) : Measurable (f m) := (measurable_id.neg.max measurable_const).min measurable_const
  have hf_nonneg (m : ℕ) (t : ℝ) : 0 ≤ f m t := le_min (le_max_right _ _) (Nat.cast_nonneg _)
  have hfi (m : ℕ) : Integrable (f m) μ := by
    refine Integrable.of_bound (hf m).aestronglyMeasurable m (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg m t)]
    exact min_le_right _ _
  have hupper : ∀ᵐ ω ∂environmentLaw μ, ∀ k : ℕ, ω ((k : ℤ), 0) ≤ b := by
    apply ae_all_iff.2
    intro k
    apply ae_of_ae_map (p := fun t : ℝ => t ≤ b) (measurable_environment_eval _).aemeasurable
    simpa only [environmentLaw_map_eval] using hb
  -- Bound each truncation mean using the original horizontal passage and its limit.
  have hmean (m : ℕ) : (∫ t, f m t ∂μ) ≤ max b 0 - r := by
    have htruncate := ae_horizontal_average μ (f m) (hf m) (hfi m)
    obtain ⟨ω, hωupper, hωaxis, hωtrunc⟩ := (hupper.and (hlimit.and htruncate)).exists
    have hterm (k : ℕ) : ω ((k : ℤ), 0) + f m (ω ((k : ℤ), 0)) ≤ max b 0 := by
      by_cases hk : 0 ≤ ω ((k : ℤ), 0)
      · simp only [f, max_eq_right (neg_nonpos.mpr hk), min_eq_left (Nat.cast_nonneg m), add_zero]
        exact (hωupper k).trans (le_max_left _ _)
      · have hneg := neg_nonneg.mpr (le_of_not_ge hk)
        have hf_le : f m (ω ((k : ℤ), 0)) ≤ -ω ((k : ℤ), 0) := by
          dsimp [f]
          rw [max_eq_left hneg]
          exact min_le_left _ _
        linarith only [hf_le, le_max_right b 0]
    have hsum (n : ℕ) : lastPassage ω 0 (n, 0) +
        (∑ k ∈ Finset.range n, f m (ω ((k : ℤ), 0))) ≤ (n : ℝ) * max b 0 := by
      have hhorizontal : lastPassage ω 0 (n, 0) =
          ∑ k ∈ Finset.range n, ω ((k : ℤ), 0) := by
        rw [lastPassage_horizontal]
        simp only [Prod.fst_zero, Prod.snd_zero, zero_add]
        exact Fin.sum_univ_eq_sum_range (fun k => ω ((k : ℤ), 0)) n
      rw [hhorizontal, ← Finset.sum_add_distrib]
      calc
        _ ≤ ∑ _k ∈ Finset.range n, max b 0 := Finset.sum_le_sum (fun k _ => hterm k)
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hle : r + (∫ t, f m t ∂μ) ≤ max b 0 := by
      apply le_of_tendsto (hωaxis.add hωtrunc)
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hh := div_le_div_of_nonneg_right (hsum n) hnR.le
      rwa [add_div, mul_div_cancel_left₀ _ hnR.ne'] at hh
    linarith only [hle]
  -- Monotone convergence recovers the negative part from the bounded truncations.
  have hsup (t : ℝ) : (⨆ m : ℕ, ENNReal.ofReal (f m t)) = ENNReal.ofReal (max (-t) 0) := by
    apply le_antisymm
    · exact iSup_le (fun m => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    · obtain ⟨m, hm⟩ := exists_nat_ge (max (-t) 0)
      simpa only [f, min_eq_left hm] using
        (le_iSup (fun m : ℕ => ENNReal.ofReal (f m t)) m)
  have hle : (∫⁻ t, ENNReal.ofReal (max (-t) 0) ∂μ) ≤
      ENNReal.ofReal (max b 0 - r) := by
    simp_rw [← hsup]
    rw [lintegral_iSup (fun m => (hf m).ennreal_ofReal)
      (fun m k hmk t => ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hmk)))]
    apply iSup_le
    intro m
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi m) (Eventually.of_forall (hf_nonneg m))]
    exact ENNReal.ofReal_le_ofReal (hmean m)
  exact hle.trans_lt ENNReal.ofReal_lt_top

/-- The negative first moment is finite whenever an upper-bounded marginal
admits the actual finite uniform shape (differentiability final draft, subsection `sub:lb_mom_chat`). -/
theorem negative_mean_finite_of_upper_bound_and_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ)
    (hb : ∀ᵐ t ∂μ, t ≤ b) (g : Quadrant → ℝ) (hg : LPPStatements.IsShapeFunction μ g) :
    (∫⁻ t, ENNReal.ofReal (max (-t) 0) ∂μ) < ∞ := by
  exact negative_mean_finite_of_upper_bound_and_horizontal_rate μ b hb (g (1, 0))
    (ae_horizontal_rate_of_shape μ g hg)

end LPPDifferentiability.FinalDraft
