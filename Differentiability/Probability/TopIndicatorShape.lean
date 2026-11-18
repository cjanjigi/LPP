/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.WeakNegativeShape
public import Martin2004.Probability.BoundedExpectedUniform
public import Differentiability.Probability.TopIndicatorLaw
public import Martin2004.Probability.BoundedMarginalTails

/-!
# Shapes for bounded nonnegative laws

The top-indicator field uses one shape witness throughout the sampling theorem,
the expected-floor limit and the finite mean bounds. The weak-negative shape
result keeps these conclusions together.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- A probability law supported almost everywhere in the unit interval has
one continuous homogeneous concave shape with the uniform sampling theorem,
the expected-floor characterization and bounds at every lattice start.
All moment and tail obligations are derived from the displayed support bound. -/
theorem exists_shape_with_expected_bounds_of_ae_mem_unit_interval
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ t ∂ν, 0 ≤ t ∧ t ≤ 1) :
    ∃ g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw ν) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        Integrable (fun ω : Environment => lastPassage ω u d) (environmentLaw ν)) ∧
      (∀ x : Quadrant, 0 ≤ g x ∧ g x ≤ (x.1 : ℝ) + x.2) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        (∫ ω : Environment, lastPassage ω u d ∂environmentLaw ν) ≤
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))) := by
  have habs : ∀ᵐ t ∂ν, |t| ≤ 1 := by
    filter_upwards [hν] with t ht
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hfirst := integrable_id_of_ae_abs_le ν 1 habs
  have hpos : (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    (integrated_positive_sqrt_tail_le_of_ae_abs_le ν 1 (by norm_num) habs).trans_lt
      ENNReal.ofReal_lt_top
  have hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂ν) < ∞ := by
    refine ⟨2, by norm_num, ?_⟩
    have hz : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ (2 : ℝ)) ∂ν) = 0 := by
      calc
        _ = ∫⁻ _t : ℝ, (0 : ℝ≥0∞) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hν] with t ht
          rw [max_eq_right (neg_nonpos.mpr ht.1)]
          norm_num
        _ = 0 := lintegral_zero
    rw [hz]
    exact ENNReal.zero_lt_top
  obtain ⟨g, hg, _hunique⟩ :=
    exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail ν hneg hpos
  have hlim := hg.2.2.2.2.1
  have hmean : 0 ≤ ∫ t : ℝ, t ∂ν :=
    integral_nonneg_of_ae (hν.mono fun _ ht => ht.1)
  have hnonneg (x : Quadrant) : 0 ≤ g x := by
    apply ge_of_tendsto (hlim x)
    apply Eventually.of_forall
    intro n
    apply div_nonneg _ (Nat.cast_nonneg n)
    exact (mul_nonneg (Nat.cast_nonneg _) hmean).trans
      (integral_lastPassage_ge_path_mean ν hfirst 0 _)
  have hupper := abs_real_expected_rate_le_of_ae_abs_le ν 1 (by norm_num) habs g hlim
  refine ⟨g, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hlim, ?_, ?_, ?_⟩
  · exact fun u d => integrable_lastPassage ν hfirst u d
  · intro x
    exact ⟨hnonneg x, (le_abs_self (g x)).trans (by simpa only [one_mul] using hupper x)⟩
  · intro u d
    have htrans := integral_lastPassage_translation ν hfirst u 0 d
    rw [add_zero] at htrans
    rw [htrans]
    exact integral_lastPassage_le_real_expected_rate_of_ae_abs_le ν 1 (by norm_num) habs g hlim d

private theorem real_expected_rate_ge_path_mean
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun t : ℝ => t) ν) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw ν) / (n : ℝ)) atTop (𝓝 (g x)))
    (x : Quadrant) :
    (∫ t : ℝ, t ∂ν) * ((x.1 : ℝ) + x.2) ≤ g x := by
  have hl := (tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ)
    x.1.property x.2.property).mul_const (∫ t : ℝ, t ∂ν)
  rw [mul_comm ((x.1 : ℝ) + x.2)] at hl
  apply le_of_tendsto_of_tendsto' hl (hlim x)
  intro n
  have h := div_le_div_of_nonneg_right
    (integral_lastPassage_ge_path_mean ν hν 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)) (Nat.cast_nonneg n)
  (convert h using 1; ring)

/-- The top indicator of the environment has a shape under the iid field law. The
same witness has the expected-floor characterization, all finite passage mean
bounds and the zero conclusion at an infinite top. The marginal is only assumed
to be a probability measure. -/
theorem exists_source_top_indicator_shape (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage (topWeightIndicatorField μ ω) 0 d -
            g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
              ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        Integrable (fun ω : Environment => lastPassage (topWeightIndicatorField μ ω) u d)
          (environmentLaw μ)) ∧
      (∀ x : Quadrant, 0 ≤ g x ∧ g x ≤ (x.1 : ℝ) + x.2) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) u d ∂environmentLaw μ) ≤
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))) ∧
      (∀ x : Quadrant, (∫ t : ℝ, t ∂μ.map (topWeightIndicator μ)) * ((x.1 : ℝ) + x.2) ≤ g x) ∧
      (supportTop μ = ⊤ → g = fun _ => 0) := by
  let ν : Measure ℝ := μ.map (topWeightIndicator μ)
  have hfield : Measurable (topWeightIndicatorField μ) :=
    measurable_source_top_indicator_environment μ
  have hlaw : (environmentLaw μ).map
      (topWeightIndicatorField μ) = environmentLaw ν :=
    source_top_indicator_environmentLaw_map μ
  have hν : ∀ᵐ t ∂ν, 0 ≤ t ∧ t ≤ 1 :=
    source_top_indicator_map_ae_mem_unitInterval μ
  have habs : ∀ᵐ t ∂ν, |t| ≤ 1 := by
    filter_upwards [hν] with t ht
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hfirst := integrable_id_of_ae_abs_le ν 1 habs
  obtain ⟨g, hg⟩ := exists_shape_with_expected_bounds_of_ae_mem_unit_interval ν hν
  have hpass (u : Lattice) (d : ℕ × ℕ) :
      Integrable (fun ω : Environment => lastPassage (topWeightIndicatorField μ ω) u d)
        (environmentLaw μ) ∧
      (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) u d ∂environmentLaw μ) =
        ∫ η : Environment, lastPassage η u d ∂environmentLaw ν := by
    have hi : Integrable (fun η : Environment => lastPassage η u d)
        ((environmentLaw μ).map (topWeightIndicatorField μ)) := by
      rw [hlaw]
      exact hg.2.2.2.2.2.1 u d
    refine ⟨hi.comp_measurable hfield, ?_⟩
    have heq := integral_map hfield.aemeasurable hi.aestronglyMeasurable
    rw [hlaw] at heq
    exact heq.symm
  have hsample : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topWeightIndicatorField μ ω) 0 d -
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    have h := hg.2.2.2.1
    rw [← hlaw] at h
    exact ae_of_ae_map hfield.aemeasurable h
  have hlim (x : Quadrant) : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)) := by
    simpa only [(hpass _ _).2] using hg.2.2.2.2.1 x
  refine ⟨g, hg.1, hg.2.1, hg.2.2.1, hsample, hlim,
    (fun u d => (hpass u d).1), hg.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro u d
    rw [(hpass u d).2]
    exact hg.2.2.2.2.2.2.2 u d
  · exact real_expected_rate_ge_path_mean ν hfirst g hg.2.2.2.2.1
  · intro hM
    have hz (u : Lattice) (d : ℕ × ℕ) :
        (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) u d ∂environmentLaw μ) = 0 := by
      have hzero := source_top_indicator_environment_field_eq_zero_of_endpoint_top μ hM
      calc
        _ = ∫ _ω : Environment, (0 : ℝ) ∂environmentLaw μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun ω => by
            change lastPassage (topWeightIndicatorField μ ω) u d = 0
            rw [hzero ω, lastPassage_const, mul_zero]
        _ = 0 := by simp only [integral_zero]
    funext x
    apply tendsto_nhds_unique (hlim x)
    simpa only [hz, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end LPPDifferentiability
