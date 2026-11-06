/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Analysis.RealFloorInterpolation
public import Martin2004.Analysis.RationalInteriorExtension
public import Martin2004.Probability.MartinRationalRate
public import LPP_Foundations.Probability.PassageAxisMean

/-!
# Actual expected passage rates on the whole real quadrant

Only probability and Martin's two square-root tails are assumed. The unique
whole-quadrant witness has actual floor expectation limits, a continuous
interior restriction, exact signed axis values and the same rational rates.
No shape function is chosen, and continuity across the boundary is not
defined here.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNRat NNReal

namespace LPPDifferentiability

/-- Actual normalized floor expectations determine one function on the whole
quadrant under the probability and two square-root tail assumptions.
The interior restriction is continuous; axis values are their signed means.
The rational witness is produced by the rational-rate theorem of
`MartinRationalRate`, and every finite passage is integrable. -/
theorem exists_unique_lastPassage_real_expected_rate_of_martin_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      Continuous (fun x : QuadrantInterior => g x.val) ∧
      g 0 = 0 ∧
      (∀ s : ℝ≥0, g (s, 0) = (∫ t : ℝ, t ∂μ) * (s : ℝ)) ∧
      (∀ t : ℝ≥0, g (0, t) = (∫ s : ℝ, s ∂μ) * (t : ℝ)) ∧
      (∃ F : (ℚ≥0 × ℚ≥0) → ℝ,
        (∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0
            (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊)
            ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (F q))) ∧
        (∀ q : ℚ≥0 × ℚ≥0, g (nnratPairToQuadrant q) = F q)) ∧
      (∀ z : ℕ × ℕ, Integrable (fun ω : Environment => lastPassage ω 0 z)
        (environmentLaw μ)) := by
  classical
  let m : ℝ := ∫ t : ℝ, t ∂μ
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  obtain ⟨F, ⟨hFlim, _, hFhom, hFadd, _, _, _, hFb, _, hFi⟩, _⟩ :=
    exists_unique_lastPassage_rational_rate_of_martin_tails μ hneg hpos
  obtain ⟨G, ⟨hG, hGF⟩, _⟩ :=
    existsUnique_continuous_nnrat_rate_interior_extension F hFhom hFadd
      m (F (1, 1) - m) (fun q => (hFb q).1) (fun q => (hFb q).2)
  let g : Quadrant → ℝ := fun x =>
    if h : 0 < x.1 ∧ 0 < x.2 then G ⟨x, h⟩ else m * ((x.1 : ℝ) + x.2)
  have hgi (x : QuadrantInterior) : g x.val = G x := by
    simp only [g, dite_eq_left x.property]
  have hgx (s : ℝ≥0) : g (s, 0) = m * (s : ℝ) := by
    simp [g]
  have hgy (t : ℝ≥0) : g (0, t) = m * (t : ℝ) := by
    simp [g]
  have hmono : Monotone (fun z : ℕ × ℕ =>
      (∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) -
        ((z.1 + z.2 : ℕ) : ℝ) * m) := by
    intro z w hzw
    exact integral_lastPassage_corrected_monotone μ hμ z w hzw.1 hzw.2
  have hgLim (x : Quadrant) : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)) := by
    by_cases hx : 0 < x.1
    · by_cases hy : 0 < x.2
      · have hi := tendsto_corrected_floor_of_rational_limits
          (fun z => ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ)
          m hmono F G hG hGF hFlim ⟨x, hx, hy⟩
        rw [show g x = G ⟨x, hx, hy⟩ from hgi ⟨x, hx, hy⟩]
        exact hi
      · have hz : x.2 = 0 := le_antisymm (le_of_not_gt hy) bot_le
        have heq : x = (x.1, 0) := Prod.ext rfl hz
        rw [heq, hgx]
        have ht := (tendsto_nat_floor_mul_div_nat (x.1 : ℝ) x.1.property).mul_const m
        rw [mul_comm m]
        convert ht using 1
        funext n
        simp only [NNReal.coe_zero, mul_zero, Nat.floor_zero,
          integral_lastPassage_horizontal μ hμ]
        ring
    · have hz : x.1 = 0 := le_antisymm (le_of_not_gt hx) bot_le
      have heq : x = (0, x.2) := Prod.ext hz rfl
      rw [heq, hgy]
      have ht := (tendsto_nat_floor_mul_div_nat (x.2 : ℝ) x.2.property).mul_const m
      rw [mul_comm m]
      convert ht using 1
      funext n
      simp only [NNReal.coe_zero, mul_zero, Nat.floor_zero,
        integral_lastPassage_vertical μ hμ]
      ring
  refine ⟨g, ⟨hgLim, ?_, ?_, hgx, hgy, ⟨F, hFlim, ?_⟩, hFi⟩, ?_⟩
  · have heq : (fun x : QuadrantInterior => g x.val) = G := funext hgi
    rw [heq]
    exact hG
  · change g (0, 0) = 0
    simpa only [NNReal.coe_zero, mul_zero] using hgx 0
  · intro q
    have hcast : Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * ((nnratPairToQuadrant q).1 : ℝ)⌋₊,
            ⌊(n : ℝ) * ((nnratPairToQuadrant q).2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (F q)) := by
      simpa only [coe_nnratPairToQuadrant_fst, coe_nnratPairToQuadrant_snd] using hFlim q
    exact tendsto_nhds_unique (hgLim (nnratPairToQuadrant q)) hcast
  · intro H hH
    funext x
    exact tendsto_nhds_unique (hH.1 x) (hgLim x)

end LPPDifferentiability
