/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.Percolation
public import Differentiability.Probability.TopIndicatorLaw
public import LPP_Foundations.Frozen.Analysis.UnitDirectionInterval
public import LPP_Foundations.Statements.ShapeDefinitions
import Differentiability.FinalDraft.FlatClassificationSource.DoubleClassification
import Differentiability.FinalDraft.FlatTop.Trichotomy
import Differentiability.FinalDraft.FlatTopRates.SurvivalRates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Proof of the current differentiability paper's flat-top theorem. -/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability.FinalDraft.FlatTop

/-- The unit-direction interval with both bounds one half is the midpoint. -/
private theorem unitDirectionInterval_half_half :
    unitDirectionInterval (1 / 2) (1 / 2) = {((1 / 2, 1 / 2) : Quadrant)} := by
  have hhalf : (((1 / 2 : ℝ≥0) : ℝ)) = 1 / 2 := by norm_num
  ext x
  change (x ∈ closedUnitDirections ∧ 1 / 2 ≤ (x.1 : ℝ) ∧ (x.1 : ℝ) ≤ 1 / 2) ↔
    x ∈ ({((1 / 2, 1 / 2) : Quadrant)} : Set Quadrant)
  constructor
  · rintro ⟨hx, hlo, hhi⟩
    have hx₁ : (x.1 : ℝ) = 1 / 2 := le_antisymm hhi hlo
    have hl : (x.1 : ℝ) + x.2 = 1 := hx
    have hx₂ : (x.2 : ℝ) = 1 / 2 := by linarith only [hl, hx₁]
    exact mem_singleton_iff.mpr (Prod.ext (NNReal.eq (hx₁.trans hhalf.symm))
      (NNReal.eq (hx₂.trans hhalf.symm)))
  · intro hx
    rcases mem_singleton_iff.mp hx with rfl
    refine ⟨?_, hhalf.symm.le, hhalf.le⟩
    change (((1 / 2 : ℝ≥0) : ℝ) + ((1 / 2 : ℝ≥0) : ℝ)) = 1
    rw [hhalf]
    norm_num

/-- The finite support top is attained exactly on the top-indicator flat
segment. The critical density and the origin cluster's speed determine this
segment and its endpoints are differentiability points. -/
theorem flat_top
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
    let p₁ : ℝ := μ.real {M}
    let Uperc : Set Quadrant := {x ∈ closedUnitDirections | gtop x = 1}
    Uperc = {x ∈ closedUnitDirections | g x = M} ∧
    (∀ x ∈ closedUnitDirections, x ∉ Uperc → g x < M) ∧
    (p₁ < orientedSiteCriticalDensity → Uperc = ∅) ∧
    (p₁ = orientedSiteCriticalDensity →
      Uperc = {((1 / 2, 1 / 2) : Quadrant)} ∧
        DifferentiableAt ℝ (quadrantExtension g) (1 / 2, 1 / 2)) ∧
    (orientedSiteCriticalDensity < p₁ →
      0 < environmentLaw μ (orientedSiteSurvival M) ∧
      ∃ β : ℝ, 1 / 2 < β ∧ β < 1 ∧ IsOriginRightEdgeSpeed μ M β ∧
        Uperc = unitDirectionInterval (1 - β) β ∧
        DifferentiableAt ℝ (quadrantExtension g) (1 - β, β) ∧
        DifferentiableAt ℝ (quadrantExtension g) (β, 1 - β)) :=
by
  intro p₁ Uperc
  let p : unitInterval := ⟨p₁, measureReal_nonneg, measureReal_le_one⟩
  let R := expectedHalfLineRates (bernoulliMeasure (1 : ℝ) 0 p)
  obtain ⟨hsame, hgap, hzero, hpositive⟩ :=
    top_segment_of_two_normalized_classifications μ hnondegenerate hneg M hM g hg gtop hgtop
  refine ⟨hsame, hgap, ?_, ?_, ?_⟩
  · intro hp
    by_cases hatom : μ {M} = 0
    · exact hzero hatom
    obtain ⟨hempty, hinterval⟩ := hpositive (pos_iff_ne_zero.mpr hatom)
    apply hempty
    intro hBdd
    have hβ : IsGLB R (sInf R) := isGLB_csInf (range_nonempty _) hBdd
    have hβhalf : 1 / 2 ≤ sInf R := (hinterval _ hβ).1
    have hp₀ : 0 < (p : ℝ) := ENNReal.toReal_pos hatom (measure_ne_top _ _)
    exact (lt_half_of_isGLB_halfLineEdge_of_lt_criticalDensity p hp₀ hp hβ).not_ge hβhalf
  · intro hp
    have hp₀ : 0 < (p : ℝ) := by
      change 0 < p₁
      rw [hp]
      exact orientedSiteCriticalDensity_mem_Ioo.1
    have hatom : 0 < μ {M} := (ENNReal.toReal_pos_iff.mp hp₀).1
    have hβ : IsGLB R (1 / 2) := by
      let pc : unitInterval := ⟨orientedSiteCriticalDensity,
        orientedSiteCriticalDensity_mem_Ioo.1.le, orientedSiteCriticalDensity_mem_Ioo.2.le⟩
      have hpc : p = pc := Subtype.ext hp
      change IsGLB (expectedHalfLineRates (bernoulliMeasure (1 : ℝ) 0 p)) (1 / 2)
      rw [hpc]
      exact isGLB_halfLineEdge_at_criticalDensity
    obtain ⟨_, _, hInterval, hDiff, _⟩ := (hpositive hatom).2 _ hβ
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hInterval hDiff
    exact ⟨hInterval.trans unitDirectionInterval_half_half, hDiff⟩
  · intro hp
    obtain ⟨hsurv, β, _, hβ, hspeed⟩ :=
      exists_originRightEdgeSpeed_of_critical_lt_topAtom μ M hM hp
    have hp₀ : 0 < (p : ℝ) := orientedSiteCriticalDensity_mem_Ioo.1.trans hp
    have hatom : 0 < μ {M} := (ENNReal.toReal_pos_iff.mp hp₀).1
    obtain ⟨_, hone, hInterval, hLeft, hRight⟩ := (hpositive hatom).2 β hβ
    exact ⟨hsurv, β, half_lt_of_isGLB_halfLineEdge_of_criticalDensity_lt p hp hβ,
      hone, hspeed, hInterval, hLeft, hRight⟩

end LPPDifferentiability.FinalDraft.FlatTop
