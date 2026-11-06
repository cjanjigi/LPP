/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.WeakNegativeShape
public import LPP_Foundations.Probability.TranslationCylinder
public import LPP_Foundations.Probability.PassageMeasurable
public import LPP_Foundations.Model.LastPassage.Translate
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Uniform deterministic-endpoint shape probabilities

The uniform shape event at the origin gives increasing good events. Their
probabilities tend to one. Measure-preserving environment translation gives one
probability bound for all deterministic signed starts and displacements.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

private theorem exists_uniform_probability_of_ae_origin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (hg : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ → ℝ, (∀ s, 0 ≤ p s ∧ p s ≤ 1) ∧
      Tendsto p atTop (𝓝 1) ∧
      ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), 1 ≤ s →
        s ≤ ((d.1 + d.2 : ℕ) : ℝ) →
        p s ≤ (environmentLaw μ).real {ω : Environment |
          |lastPassage ω u d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)} := by
  let E : ℝ → Set Environment := fun s => {ω | ∀ d : ℕ × ℕ,
    s ≤ ((d.1 + d.2 : ℕ) : ℝ) →
      |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
        ε * ((d.1 + d.2 : ℕ) : ℝ)}
  have hmeas (s : ℝ) : MeasurableSet (E s) := by
    simp only [E, ofPred_forall]
    exact MeasurableSet.iInter fun d => MeasurableSet.iInter fun _hd =>
      measurableSet_le ((measurable_lastPassage 0 d).sub_const _).abs measurable_const
  have hmono : Monotone E := by
    intro s t hst ω hω d hd
    exact hω d (hst.trans hd)
  have hfullNat : environmentLaw μ (⋃ n : ℕ, E (n : ℝ)) = 1 := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion fun n : ℕ => hmeas (n : ℝ))).mp
    filter_upwards [hg] with ω hω
    obtain ⟨N, _hN, hbound⟩ := hω ε hε
    apply mem_iUnion.mpr
    refine ⟨N, ?_⟩
    intro d hd
    exact hbound d (by exact_mod_cast hd)
  have hfull : environmentLaw μ (⋃ s : ℝ, E s) = 1 := by
    apply le_antisymm prob_le_one
    rw [← hfullNat]
    apply measure_mono
    intro ω hω
    obtain ⟨n, hn⟩ := mem_iUnion.mp hω
    exact mem_iUnion.mpr ⟨(n : ℝ), hn⟩
  have ht : Tendsto (fun s : ℝ => environmentLaw μ (E s)) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := environmentLaw μ) hmono
    rw [hfull] at h
    exact h
  refine ⟨fun s => (environmentLaw μ).real (E s),
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩), ?_, ?_⟩
  · have h := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp ht
    simpa only [measureReal_def, Function.comp_def, ENNReal.toReal_one] using h
  · intro s u d _hs hd
    have hm : MeasurableSet {ω : Environment |
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)} :=
      measurableSet_le ((measurable_lastPassage 0 d).sub_const _).abs measurable_const
    have htrans := (measurePreserving_environment_translation μ u).measureReal_preimage
      hm.nullMeasurableSet
    simp only [preimage_ofPred_eq, lastPassage_translate, add_zero] at htrans
    rw [htrans]
    exact measureReal_mono fun ω hω => hω d hd

/-- Under the unchanged weak-negative hypotheses, the unique shape keeps its full
origin sample characterization and supplies one probability function for every
positive tolerance. Its endpoint bound is
uniform over all deterministic signed starts and natural displacements. -/
theorem exists_unique_shape_with_uniform_probability_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ p : ℝ → ℝ,
        (∀ s, 0 ≤ p s ∧ p s ≤ 1) ∧ Tendsto p atTop (𝓝 1) ∧
        ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), 1 ≤ s →
          s ≤ ((d.1 + d.2 : ℕ) : ℝ) →
          p s ≤ (environmentLaw μ).real {ω : Environment |
            |lastPassage ω u d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
              ε * ((d.1 + d.2 : ℕ) : ℝ)}) := by
  obtain ⟨g, hg, hunique⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, ?_⟩, ?_⟩
  · intro ε hε
    exact exists_uniform_probability_of_ae_origin μ g hg.2.2.2 ε hε
  · intro f hf
    exact hunique f ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

end LPPDifferentiability
