/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# First moments of weak limits

Bounded continuous clips and monotone convergence supply the moment step that
follows equations (2.11) to (2.13) of Liggett (1985). These helpers use real laws.
-/

public section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace LPPDifferentiability

/-- Clip the nonnegative part at a natural level. -/
@[expose] def nonnegativeClip (m : ℕ) (x : ℝ) : ℝ := min (max x 0) m

theorem nonnegativeClip_nonneg (m : ℕ) (x : ℝ) : 0 ≤ nonnegativeClip m x :=
  le_min (le_max_right _ _) (Nat.cast_nonneg _)

theorem nonnegativeClip_le_level (m : ℕ) (x : ℝ) : nonnegativeClip m x ≤ m :=
  min_le_right _ _

theorem nonnegativeClip_le_self (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    nonnegativeClip m x ≤ x := by
  simpa only [nonnegativeClip, max_eq_left hx] using (min_le_left x (m : ℝ))

private theorem continuous_nonnegativeClip (m : ℕ) : Continuous (nonnegativeClip m) := by
  unfold nonnegativeClip
  fun_prop

private def clipTest (g : ℝ → ℝ) (hg : Continuous g) (m : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => nonnegativeClip m (g x), (continuous_nonnegativeClip m).comp hg⟩ m
    (by
      intro x y
      change dist (nonnegativeClip m (g x)) (nonnegativeClip m (g y)) ≤ m
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith [nonnegativeClip_nonneg m (g x),
        nonnegativeClip_nonneg m (g y), nonnegativeClip_le_level m (g x),
        nonnegativeClip_le_level m (g y)])

/-- The clipped test is integrable under every probability law. -/
theorem integrable_nonnegativeClip (ρ : ProbabilityMeasure ℝ) (g : ℝ → ℝ)
    (hg : Continuous g) (m : ℕ) :
    Integrable (fun x => nonnegativeClip m (g x)) (ρ : Measure ℝ) :=
  (clipTest g hg m).integrable (ρ : Measure ℝ)

private theorem tendsto_nonnegativeClip {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun m => nonnegativeClip m x) atTop (𝓝 x) := by
  obtain ⟨M, hM⟩ := exists_nat_ge x
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop M] with m hm
  have hxm : x ≤ (m : ℝ) := hM.trans (by exact_mod_cast hm)
  simp only [nonnegativeClip, max_eq_left hx, min_eq_left hxm]

/-- Weak convergence gives convergence of each bounded continuous clip. -/
theorem tendsto_integral_nonnegativeClip_of_weak
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν)) (g : ℝ → ℝ) (hg : Continuous g) (m : ℕ) :
    Tendsto (fun n => ∫ x, nonnegativeClip m (g x) ∂(μ n : Measure ℝ)) atTop
      (𝓝 (∫ x, nonnegativeClip m (g x) ∂(ν : Measure ℝ))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) (clipTest g hg m)

/-- Under one integrable nonnegative law, clip means increase to the full mean. -/
theorem tendsto_integral_nonnegativeClip (ρ : ProbabilityMeasure ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable g (ρ : Measure ℝ)) :
    Tendsto (fun m => ∫ x, nonnegativeClip m (g x) ∂(ρ : Measure ℝ)) atTop
      (𝓝 (∫ x, g x ∂(ρ : Measure ℝ))) := by
  apply integral_tendsto_of_tendsto_of_monotone
    (fun m => integrable_nonnegativeClip ρ g hg m) hgi
  · exact Eventually.of_forall fun x m k hmk =>
      min_le_min le_rfl (by exact_mod_cast hmk)
  · exact Eventually.of_forall fun x => tendsto_nonnegativeClip (hg0 x)

/-- A common nonnegative continuous moment bound survives a weak limit.
Limit integrability is proved, rather than assumed. -/
theorem integrable_nonneg_of_weak_integral_le
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν)) (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : ∀ n, Integrable g (μ n : Measure ℝ))
    (C : ℝ) (hbound : ∀ n, (∫ x, g x ∂(μ n : Measure ℝ)) ≤ C) :
    Integrable g (ν : Measure ℝ) ∧ (∫ x, g x ∂(ν : Measure ℝ)) ≤ C := by
  have hclip (m : ℕ) : (∫ x, nonnegativeClip m (g x) ∂(ν : Measure ℝ)) ≤ C := by
    apply le_of_tendsto (tendsto_integral_nonnegativeClip_of_weak μ ν hweak g hg m)
    exact Eventually.of_forall fun n =>
      (integral_mono (integrable_nonnegativeClip (μ n) g hg m) (hgi n)
        (fun x => nonnegativeClip_le_self m (hg0 x))).trans (hbound n)
  have hlin : Tendsto
      (fun m => ∫⁻ x, ENNReal.ofReal (nonnegativeClip m (g x)) ∂(ν : Measure ℝ)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure ℝ))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro m
      exact (((continuous_nonnegativeClip m).comp hg).measurable.ennreal_ofReal).aemeasurable
    · exact Eventually.of_forall fun x m k hmk => ENNReal.ofReal_le_ofReal
        (min_le_min le_rfl (by exact_mod_cast hmk))
    · exact Eventually.of_forall fun x =>
        (ENNReal.continuous_ofReal.tendsto (g x)).comp (tendsto_nonnegativeClip (hg0 x))
  have hfinite : (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure ℝ)) ≤ ENNReal.ofReal C := by
    apply le_of_tendsto hlin
    apply Eventually.of_forall
    intro m
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_nonnegativeClip ν g hg m)
      (Eventually.of_forall fun x => nonnegativeClip_nonneg m (g x))]
    exact ENNReal.ofReal_le_ofReal (hclip m)
  have hν : Integrable g (ν : Measure ℝ) :=
    (lintegral_ofReal_ne_top_iff_integrable hg.measurable.aestronglyMeasurable
      (Eventually.of_forall hg0)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfinite)
  exact ⟨hν, le_of_tendsto (tendsto_integral_nonnegativeClip ν g hg hg0 hν)
    (Eventually.of_forall hclip)⟩

/-- Uniform absolute first moments make the identity integrable under the weak limit. -/
theorem integrable_id_of_weak_abs_integral_le
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hμ : ∀ n, Integrable (fun x : ℝ => x) (μ n : Measure ℝ))
    (C : ℝ) (hbound : ∀ n, (∫ x : ℝ, |x| ∂(μ n : Measure ℝ)) ≤ C) :
    Integrable (fun x : ℝ => x) (ν : Measure ℝ) := by
  have h := (integrable_nonneg_of_weak_integral_le μ ν hweak (fun x : ℝ => |x|)
    continuous_abs abs_nonneg (fun n => (hμ n).abs) C hbound).1
  exact h.mono measurable_id.aestronglyMeasurable
    (Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, abs_abs, le_refl])

end LPPDifferentiability
