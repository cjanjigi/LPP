/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.RealExpectedTruncation
public import Martin2004.Probability.NegativeRemainderMean
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Closed-quadrant continuity under a first moment

Martin (2004), Lemma 3.6 gives relative, hence compact uniform, approximation
by the actual continuous clipped rates. This proves continuity of the same
unique actual expected-rate witness, retaining every geometry and expectation
property. No negative square-root tail is assumed.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal NNRat Uniformity

namespace LPPDifferentiability

/-- Under the genuine first moment and positive square-root tail, one
deterministic cutoff makes the actual continuous clipped rates approximate
the same actual expected rate in every direction with relative error ε.
The non-strict bound includes zero length without asserting error < 0. -/
theorem exists_clipped_real_expected_rate_relative_approximation
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ ε : ℝ, 0 < ε → ∃ L0 : ℝ, 0 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ gL : Quadrant → ℝ, Continuous gL ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (μ.map (fun t : ℝ => max (-L) (min L t)))) / (n : ℝ))
        atTop (𝓝 (gL x))) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gL x))) ∧
      (∀ x : Quadrant, |g x - gL x| ≤ ε * ((x.1 : ℝ) + x.2)) := by
  obtain ⟨C, _hC, hcompare⟩ := exists_real_expected_rate_clipping_comparison
  have hn := tendsto_integral_negative_remainder_zero hμ
  have hp : Tendsto (fun L : ℝ =>
      C * (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_martin_positive_tail_toReal_zero μ hpos).const_mul C
  intro ε hε
  obtain ⟨L0, hL0⟩ := eventually_atTop.1
    ((eventually_ge_atTop (0 : ℝ)).and
      ((hn.eventually_lt_const hε).and (hp.eventually_lt_const hε)))
  refine ⟨max 0 L0, le_max_left _ _, ?_⟩
  intro L hL
  obtain ⟨hLnonneg, hnL, hpL⟩ := hL0 L ((le_max_right _ _).trans hL)
  obtain ⟨gL, hc, hm, ho, hb⟩ := hcompare μ hμ hpos g hg L hLnonneg
  refine ⟨gL, hc, hm, ho, ?_⟩
  intro x
  have hlength : 0 ≤ (x.1 : ℝ) + x.2 := add_nonneg x.1.coe_nonneg x.2.coe_nonneg
  obtain ⟨hlo, hhi⟩ := hb x
  apply abs_le.mpr
  constructor
  · have hn' := mul_le_mul_of_nonneg_left hnL.le hlength
    linarith only [hlo, hn']
  · have hp' := mul_le_mul_of_nonneg_left hpL.le hlength
    have hhi' : g x - gL x ≤ ((x.1 : ℝ) + x.2) *
        (C * (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) := by
      nlinarith only [hhi]
    nlinarith only [hhi', hp']

/-- The relative approximation is uniform on every closed bounded length
set. Every cutoff above the one chosen works, and the approximants retain
their actual clipped-law floor expectation limits. -/
theorem exists_clipped_real_expected_rate_compact_approximation
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ L0 : ℝ, 0 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ gL : Quadrant → ℝ, Continuous gL ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (μ.map (fun t : ℝ => max (-L) (min L t)))) / (n : ℝ))
        atTop (𝓝 (gL x))) ∧
      (∀ x : Quadrant, (x.1 : ℝ) + x.2 ≤ R → |g x - gL x| < ε) := by
  have hRp : 0 < R + 1 := by linarith only [hR]
  have hδ : 0 < ε / (R + 1) := div_pos hε hRp
  obtain ⟨L0, hL0, happrox⟩ :=
    exists_clipped_real_expected_rate_relative_approximation μ hμ hpos g hg _ hδ
  refine ⟨L0, hL0, ?_⟩
  intro L hL
  obtain ⟨gL, hc, hm, _, hb⟩ := happrox L hL
  refine ⟨gL, hc, hm, ?_⟩
  intro x hx
  have hscale := div_mul_cancel₀ ε hRp.ne'
  calc
    |g x - gL x| ≤ ε / (R + 1) * ((x.1 : ℝ) + x.2) := hb x
    _ ≤ ε / (R + 1) * R := mul_le_mul_of_nonneg_left hx hδ.le
    _ < ε := by nlinarith only [hscale, hδ]

/-- Actual continuous clipped rates approximate locally uniformly, so the
actual expected rate is continuous on the entire closed quadrant. This is
the uniform approximation argument of Martin (2004), Lemma 3.6. -/
theorem continuous_real_expected_rate_of_integrable_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    Continuous g := by
  apply continuous_of_locally_uniform_approx_of_continuousAt
  intro x u hu
  obtain ⟨ε, hε, huε⟩ := Metric.mem_uniformity_dist.1 hu
  let R : ℝ := (x.1 : ℝ) + x.2 + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨L0, _hL0, happrox⟩ :=
    exists_clipped_real_expected_rate_compact_approximation μ hμ hpos g hg R ε hR hε
  obtain ⟨gL, hc, _, hb⟩ := happrox L0 le_rfl
  have hlength : Continuous (fun y : Quadrant => (y.1 : ℝ) + y.2) :=
    (NNReal.continuous_coe.comp continuous_fst).add
      (NNReal.continuous_coe.comp continuous_snd)
  refine ⟨{y : Quadrant | (y.1 : ℝ) + y.2 < R},
    (isOpen_lt hlength continuous_const).mem_nhds ?_, gL, hc.continuousAt, ?_⟩
  · change (x.1 : ℝ) + x.2 < (x.1 : ℝ) + x.2 + 1
    linarith
  · intro y hy
    apply huε
    rw [Real.dist_eq]
    exact hb y hy.le

/-- The same unique actual expected rate keeps the entire weak geometry
predicate, and is continuous on the whole closed quadrant. Only probability,
a first moment and the positive square-root tail are assumed. -/
theorem exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      (
      ((∀ x : Quadrant, Tendsto (fun n : ℕ =>
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
        (environmentLaw μ))) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x + y)) ∧
      (∀ x : Quadrant, g x.swap = g x) ∧
      (∀ (L : ℝ), 0 ≤ L → (∀ᵐ t ∂μ, |t| ≤ L) →
        ∀ x : Quadrant, |g x| ≤ L * ((x.1 : ℝ) + x.2))
      ) ∧ Continuous g := by
  obtain ⟨g, hg, hUnique⟩ :=
    exists_unique_lastPassage_real_expected_rate_geometry_of_integrable_and_positive_tail μ hμ hpos
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · exact continuous_real_expected_rate_of_integrable_and_positive_tail μ hμ hpos g hg.1.1
  · intro f hf
    exact hUnique f hf.1


end LPPDifferentiability
