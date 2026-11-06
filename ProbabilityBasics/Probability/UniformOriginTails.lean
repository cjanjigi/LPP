/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformOriginBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Uniform positive tails on varying uniform-origin products

The strict threshold is kept, including at atoms of the common law.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- The positive part above a strict threshold. -/
@[expose] noncomputable def positiveTail (R x : ℝ) : ℝ :=
  if R < max x 0 then max x 0 else 0

theorem positiveTail_nonneg (R x : ℝ) : 0 ≤ positiveTail R x := by
  unfold positiveTail
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem positiveTail_le_pos (R x : ℝ) : positiveTail R x ≤ max x 0 := by
  unfold positiveTail
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem positiveTail_eq_zero_of_le (R x : ℝ) (h : max x 0 ≤ R) :
    positiveTail R x = 0 := by
  simp only [positiveTail, not_lt.mpr h, ite_false]

theorem positiveTail_mono (R : ℝ) : Monotone (positiveTail R) := by
  intro x y hxy
  have h := max_le_max hxy (le_refl (0 : ℝ))
  unfold positiveTail
  split_ifs with hx hy hy
  · exact h
  · exact (hy (lt_of_lt_of_le hx h)).elim
  · exact le_max_right _ _
  · exact le_rfl

theorem positiveTail_antitone (x : ℝ) : Antitone (fun R => positiveTail R x) := by
  intro R S hRS
  change (if S < max x 0 then max x 0 else 0) ≤
    (if R < max x 0 then max x 0 else 0)
  split_ifs with hS hR hR
  · exact le_rfl
  · exact (hR (lt_of_le_of_lt hRS hS)).elim
  · exact le_max_right _ _
  · exact le_rfl

theorem measurable_positiveTail (R : ℝ) : Measurable (positiveTail R) := by
  exact Measurable.ite
    (measurableSet_lt measurable_const (measurable_id.max measurable_const))
    (measurable_id.max measurable_const) measurable_const

theorem integrable_positiveTail {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (g : A → ℝ) (hg : Integrable g ν) (R : ℝ) :
    Integrable (fun a => positiveTail R (g a)) ν := by
  apply (hg.sup (integrable_zero _ _ _)).mono'
    ((measurable_positiveTail R).comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
  exact ae_of_all _ (fun a => by
    change ‖positiveTail R (g a)‖ ≤ max (g a) 0
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveTail_nonneg R (g a))]
    exact positiveTail_le_pos R (g a))

/-- Each product tail is bounded by the tail of the fixed common law. -/
theorem integral_uniformOriginIncrement_positiveTail_le {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (hg : Integrable g ν) (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (R : ℝ) (n k : ℕ) :
    (∫ p, positiveTail R (uniformOriginIncrement X n k p)
      ∂uniformOriginProduct μ n) ≤ ∫ a, positiveTail R (g a) ∂ν := by
  apply integral_uniformOriginIncrement_comp_le μ ν X Z g hdom hlaw
    (positiveTail R) (measurable_positiveTail R) (positiveTail_mono R)
    (integrable_positiveTail ν g hg R) hm
  intro j hj
  exact integrable_positiveTail μ _ ((hi (j + 1) (by omega)).sub (hi j hj)) R

/-- Dominated convergence takes place solely on the fixed common-law space. -/
theorem tendsto_integral_positiveTail {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (g : A → ℝ) (hg : Integrable g ν) :
    Tendsto (fun m : ℕ => ∫ a, positiveTail (m : ℝ) (g a) ∂ν) atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => ∫ a, positiveTail (m : ℝ) (g a) ∂ν)
      atTop (𝓝 (∫ _a, (0 : ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun a => max (g a) 0)
    · intro m
      exact (integrable_positiveTail ν g hg (m : ℝ)).aestronglyMeasurable
    · exact hg.sup (integrable_zero _ _ _)
    · intro m
      exact ae_of_all _ (fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (positiveTail_nonneg _ _)]
        exact positiveTail_le_pos _ _)
    · apply ae_of_all
      intro a
      obtain ⟨M, hM⟩ := exists_nat_gt (max (g a) 0)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop M] with m hm
      exact (positiveTail_eq_zero_of_le _ _
        (le_trans hM.le (by exact_mod_cast hm))).symm
  simpa only [integral_zero] using ht

/-- One threshold works for all window sizes and all positive coordinates. The
carriers and their measures vary explicitly with `n`. -/
theorem uniformOriginIncrement_positiveTail_uniform {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (hg : Integrable g ν) (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) :
    ∀ ε > 0, ∃ R : ℝ, 0 ≤ R ∧ ∀ S ≥ R, ∀ n k,
      (∫ p, positiveTail S (uniformOriginIncrement X n k p)
        ∂uniformOriginProduct μ n) < ε := by
  intro ε hε
  have he := (tendsto_integral_positiveTail ν g hg).eventually (gt_mem_nhds hε)
  obtain ⟨M, hM⟩ := eventually_atTop.1 he
  refine ⟨(M : ℝ), Nat.cast_nonneg M, ?_⟩
  intro S hS n k
  apply lt_of_le_of_lt
    (integral_uniformOriginIncrement_positiveTail_le μ ν X Z g hdom hlaw hg hm hi S n k)
  apply lt_of_le_of_lt _ (hM M le_rfl)
  exact integral_mono (integrable_positiveTail ν g hg S)
    (integrable_positiveTail ν g hg (M : ℝ))
    (fun a => positiveTail_antitone (g a) hS)

end LPPDifferentiability
