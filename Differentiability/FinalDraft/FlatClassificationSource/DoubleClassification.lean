/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.Classification
public import Differentiability.Probability.TopIndicatorLaw
public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Frozen.Analysis.UnitDirectionInterval
import all Differentiability.FinalDraft.FlatTopRates.ShapeRates
import Differentiability.Probability.FlatShiftAdapters
import Differentiability.Probability.TopIndicatorShape
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic

/-! # Applying the normalized classification to both weight laws -/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- The two separate normalized classifications identify the level set of the original
shape and the level-one set of the actual top-indicator shape. Their common expected
rate set determines the segment and the differentiability endpoints whenever it has a
real infimum. This is the two-law argument of the final differentiability paper,
Theorem `thm:flat-top`, cases `flat:a` through `flat:c`. -/
theorem top_segment_of_two_normalized_classifications
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnondegenerate : ∀ c : ℝ, μ ({c} : Set ℝ) < 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (M : ℝ) (hM : (M : EReal) = supportTop μ)
    (g : Quadrant → ℝ) (hg : LPPStatements.IsShapeFunction μ g)
    (gtop : Quadrant → ℝ)
    (hgtop : ∀ x : Quadrant,
      Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gtop x))) :
    let R := expectedHalfLineRates (bernoulliMeasure (1 : ℝ) 0
      ⟨μ.real {M}, measureReal_nonneg, measureReal_le_one⟩)
    let Uperc : Set Quadrant := {x ∈ closedUnitDirections | gtop x = 1}
    Uperc = {x ∈ closedUnitDirections | g x = M} ∧
    (∀ x ∈ closedUnitDirections, x ∉ Uperc → g x < M) ∧
    (μ {M} = 0 → Uperc = ∅) ∧
    (0 < μ {M} →
      (¬ BddBelow R → Uperc = ∅) ∧
      ∀ β : ℝ, IsGLB R β → 1 / 2 ≤ β ∧ β < 1 ∧
        Uperc = unitDirectionInterval (1 - β) β ∧
        DifferentiableAt ℝ (quadrantExtension g) (1 - β, β) ∧
        DifferentiableAt ℝ (quadrantExtension g) (β, 1 - β)) := by
  intro R Uperc
  obtain ⟨hcont, hhom, hconc, hsample⟩ := hg
  have hupper : ∀ᵐ t ∂μ, t ≤ M := by
    filter_upwards [source_ae_le_support_sSup μ] with t ht
    rw [← hM] at ht
    exact EReal.coe_le_coe_iff.mp ht
  let ν := μ.map (fun t => t + (1 - M))
  have hm : Measurable (fun t : ℝ => t + (1 - M)) := by fun_prop
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr
    inferInstance
  obtain ⟨-, -, hνle, hνone⟩ := shifted_law_environment μ M hM ν rfl
  let gb : Quadrant → ℝ := fun z => g z + (1 - M) * ((z.1 : ℝ) + z.2)
  obtain ⟨hνneg, hbcont, hbhom, hbconc, hbsample⟩ :=
    shifted_shape_of_shape μ M hupper hneg ν rfl g hcont hhom hconc
      ((LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mp hsample)
  -- The first classification applies to the shifted original weights.
  obtain ⟨hbupper, hbzero, hbpos⟩ :=
    normalized_weighted_shape_classification ν hνle (by rw [hνone]; exact hnondegenerate M)
      hνneg gb hbcont hbhom hbconc hbsample
  let p : unitInterval := ⟨μ.real {M}, measureReal_nonneg, measureReal_le_one⟩
  let κ := bernoulliMeasure (1 : ℝ) 0 p
  have hκone : κ {1} = μ {M} := by
    rw [show κ {1} = (unitInterval.toNNReal p : ENNReal) from
      bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp) (by simp),
      ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hκValues : ∀ᵐ t ∂κ, t = 1 ∨ t = 0 := by
    rw [ae_iff]
    change κ (({1} : Set ℝ) ∪ {0})ᶜ = 0
    exact bernoulliMeasure_apply_of_notMem_of_notMem p
      ((measurableSet_singleton _).union (measurableSet_singleton _)).compl (by simp) (by simp)
  have hκBox : ∀ᵐ t ∂κ, 0 ≤ t ∧ t ≤ 1 := by
    filter_upwards [hκValues] with t ht
    rcases ht with rfl | rfl <;> norm_num
  have hκneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂κ) < ∞ := by
    refine ⟨2, by norm_num, ?_⟩
    have hz : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ (2 : ℝ)) ∂κ) = 0 := by
      calc
        _ = ∫⁻ _t : ℝ, (0 : ℝ≥0∞) ∂κ := by
          apply lintegral_congr_ae
          filter_upwards [hκBox] with t ht
          rw [max_eq_right (neg_nonpos.mpr ht.1)]
          norm_num
        _ = 0 := lintegral_zero
    rw [hz]
    exact ENNReal.zero_lt_top
  obtain ⟨g', hc', hh', hcv', hshape', hlim', -, -, -⟩ :=
    exists_shape_with_expected_bounds_of_ae_mem_unit_interval κ hκBox
  have hmap : (environmentLaw μ).map (topWeightIndicatorField μ) = environmentLaw κ := by
    rw [source_top_indicator_environmentLaw_map]
    simp only [environmentLaw, (source_top_indicator_hasLaw μ).map_eq,
      supportTopAtom_eq_singleton_of_eq μ M hM, κ, p]
  have hPass (d : ℕ × ℕ) :
      (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0 d ∂environmentLaw μ) =
      ∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw κ := by
    rw [← hmap]
    symm
    exact integral_map (measurable_source_top_indicator_environment μ).aemeasurable
      (measurable_lastPassage 0 d).aestronglyMeasurable
  have hEq : gtop = g' := by
    funext x
    apply tendsto_nhds_unique (hgtop x)
    simpa only [hPass] using hlim' x
  -- The second classification applies to the law of the original indicator, whose
  -- shape is identified by its actual expected passage limits.
  obtain ⟨-, htzero, htpos⟩ := normalized_weighted_shape_classification κ (hκBox.mono fun _ h => h.2)
    (by rw [hκone]; exact hnondegenerate M) hκneg g' hc' hh' hcv' hshape'
  have hRν : expectedHalfLineRates ν = R := by
    have hReal : ν.real {1} = μ.real {M} := congrArg ENNReal.toReal hνone
    have hpEq : (⟨ν.real {1}, measureReal_nonneg, measureReal_le_one⟩ : unitInterval) = p :=
      Subtype.ext hReal
    exact (expectedHalfLineRates_eq_bernoulli_topMass ν).trans
      (congrArg (fun q : unitInterval =>
        expectedHalfLineRates (bernoulliMeasure (1 : ℝ) 0 q)) hpEq)
  have hsame (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g' (toQuadrant (t, 1 - t)) = 1 ↔ gb (toQuadrant (t, 1 - t)) = 1 := by
    by_cases h0 : μ {M} = 0
    · exact iff_of_false (ne_of_lt (htzero (hκone.trans h0) t ht))
        (ne_of_lt (hbzero (hνone.trans h0) t ht))
    have hpos : 0 < μ {M} := pos_iff_ne_zero.mpr h0
    obtain ⟨htEmpty, htInterval⟩ := htpos (by rwa [hκone])
    obtain ⟨hbEmpty, hbInterval⟩ := hbpos (by rwa [hνone])
    by_cases hB : BddBelow R
    · have hNonempty : R.Nonempty := range_nonempty _
      have hβ : IsGLB R (sInf R) := isGLB_csInf hNonempty hB
      have htβ := (htInterval (sInf R) hβ).2.2.1 t ht
      have hbβ := (hbInterval (sInf R) (hRν.symm ▸ hβ)).2.2.1 t ht
      exact htβ.trans hbβ.symm
    · exact iff_of_false (ne_of_lt (htEmpty hB t ht))
        (ne_of_lt (hbEmpty (hRν.symm ▸ hB) t ht))
  have hgb (x : Quadrant) (hx : x ∈ closedUnitDirections) : gb x = g x + (1 - M) := by
    have hLevel : (x.1 : ℝ) + x.2 = 1 := hx
    simp only [gb, hLevel, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    change (x ∈ closedUnitDirections ∧ gtop x = 1) ↔ x ∈ closedUnitDirections ∧ g x = M
    obtain h | h := em (x ∈ closedUnitDirections)
    · obtain ⟨he, ht⟩ := toQuadrant_first_of_mem_closedUnitDirections x h
      have hI := hsame (x.1 : ℝ) ht
      rw [he, hgb x h, ← hEq] at hI
      simp only [h, true_and]
      constructor
      · intro hx
        linarith [(hI.mp hx)]
      · intro hx
        apply hI.mpr
        linarith
    · simp only [h, false_and]
  · intro x hx hU
    obtain ⟨he, ht⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
    have hle := hbupper (x.1 : ℝ) ht
    rw [he, hgb x hx] at hle
    refine lt_of_le_of_ne (by linarith) fun heq => hU ⟨hx, ?_⟩
    have hI := hsame (x.1 : ℝ) ht
    rw [he, hgb x hx, ← hEq] at hI
    exact hI.mpr (by linarith)
  · intro h0
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, h1⟩
    obtain ⟨he, ht⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
    have h := htzero (hκone.trans h0) (x.1 : ℝ) ht
    rw [he, ← hEq, h1] at h
    exact lt_irrefl _ h
  · intro hpos
    obtain ⟨htEmpty, htInterval⟩ := htpos (by rwa [hκone])
    obtain ⟨-, hbInterval⟩ := hbpos (by rwa [hνone])
    refine ⟨?_, ?_⟩
    · intro hB
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, h1⟩
      obtain ⟨he, ht⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
      have h := htEmpty hB (x.1 : ℝ) ht
      rw [he, ← hEq, h1] at h
      exact lt_irrefl _ h
    · intro β hβ
      obtain ⟨hhalf, hone, htI, -, -⟩ := htInterval β hβ
      obtain ⟨-, -, -, hbRight, hbLeft⟩ := hbInterval β (hRν.symm ▸ hβ)
      have hp : 0 < β := by linarith
      have hpc : 0 < 1 - β := sub_pos.mpr hone
      refine ⟨hhalf, hone, ?_,
        (differentiableAt_quadrantExtension_add_level_iff g (1 - M) (1 - β, β) hpc hp).mp hbLeft,
        (differentiableAt_quadrantExtension_add_level_iff g (1 - M) (β, 1 - β) hp hpc).mp hbRight⟩
      ext x
      change (x ∈ closedUnitDirections ∧ gtop x = 1) ↔
        x ∈ closedUnitDirections ∧ (x.1 : ℝ) ∈ Icc (1 - β) β
      constructor
      · rintro ⟨hx, h1⟩
        obtain ⟨he, ht⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
        have hI := htI (x.1 : ℝ) ht
        rw [he, ← hEq] at hI
        exact ⟨hx, hI.mp h1⟩
      · rintro ⟨hx, hI⟩
        obtain ⟨he, ht⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
        have ht := htI (x.1 : ℝ) ht
        rw [he, ← hEq] at ht
        exact ⟨hx, ht.mpr hI⟩

end LPPDifferentiability.FinalDraft
