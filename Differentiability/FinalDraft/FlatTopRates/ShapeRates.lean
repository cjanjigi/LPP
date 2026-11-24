/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Model.OrientedPercolation
public import Differentiability.Probability.TopIndicatorLaw
public import LPP_Foundations.Frozen.Analysis.UnitDirectionInterval
public import LPP_Foundations.Frozen.Model.LastPassage
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Differentiability.Probability.FlatShiftAdapters
import Differentiability.Probability.TopFlatSegment
import Differentiability.Probability.TopIndicatorShape
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The actual top-indicator flat segment and Bernoulli edge rates

The image of the original environment by the top-indicator field is the canonical iid
Bernoulli environment at the top atom's mass. Expected floor limits give the same shape
on both environments. This identifies the rates in the flat segment result with the
rates used for the actual origin speed.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- The finite top atom is the singleton consisting of the real support endpoint. -/
private theorem supportTopAtom_eq_singleton_of_eq (μ : Measure ℝ) (M : ℝ)
    (hM : (M : EReal) = supportTop μ) : supportTopAtom μ = {M} := by
  ext t
  change (t : EReal) = supportTop μ ↔ t ∈ ({M} : Set ℝ)
  rw [← hM, EReal.coe_eq_coe_iff, mem_singleton_iff]

/-- A unit direction is the point of the line segment with the given first coordinate. -/
private theorem toQuadrant_first_of_mem_closedUnitDirections (x : Quadrant)
    (hx : x ∈ closedUnitDirections) :
    toQuadrant ((x.1 : ℝ), 1 - (x.1 : ℝ)) = x ∧ (x.1 : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have hxSum : (x.1 : ℝ) + x.2 = 1 := hx
  have hx₂ : (x.2 : ℝ) = 1 - (x.1 : ℝ) := by linarith
  have hx₁ : (x.1 : ℝ) ≤ 1 := by linarith [x.2.property]
  refine ⟨?_, ⟨x.1.property, hx₁⟩⟩
  apply Prod.ext <;> apply NNReal.eq
  · exact Real.coe_toNNReal _ x.1.property
  · exact (Real.coe_toNNReal _ (sub_nonneg.mpr hx₁)).trans hx₂.symm

/-- The actual top-indicator shape has no flat direction when the top atom has zero mass. -/
theorem topIndicatorFlatSegment_eq_empty_of_topAtom_zero (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (M : ℝ) (hM : (M : EReal) = supportTop μ) (hzero : μ {M} = 0)
    (gtop : Quadrant → ℝ)
    (hgtop : ∀ x : Quadrant,
      Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gtop x))) :
    {x ∈ closedUnitDirections | gtop x = 1} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, htop⟩
  have hx₂ : (x.2 : ℝ) = 1 - (x.1 : ℝ) := by
    have : (x.1 : ℝ) + x.2 = 1 := hx
    linarith
  have hlim := hgtop x
  rw [hx₂, htop] at hlim
  have hpos := source_top_atom_pos_of_top_limit_pos μ (x.1 : ℝ) 1 hlim one_pos
  rw [supportTopAtom_eq_singleton_of_eq μ M hM, hzero] at hpos
  exact lt_irrefl _ hpos

/-- The original top-indicator flat segment is the interval determined by the same Bernoulli
expected half-line rates used for the origin speed. An unbounded-below rate set gives an empty
segment. -/
theorem topIndicatorFlatSegment_of_bernoulli_rates (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (M : ℝ) (hM : (M : EReal) = supportTop μ)
    (hp₀ : 0 < μ {M}) (hp₁ : μ {M} < 1) (gtop : Quadrant → ℝ)
    (hgtop : ∀ x : Quadrant,
      Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gtop x))) :
    let ν := bernoulliMeasure (1 : ℝ) 0 ⟨μ.real {M}, by simp⟩
    let R : Set ℝ := Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)
    let Uperc : Set Quadrant := {x ∈ closedUnitDirections | gtop x = 1}
    (¬ BddBelow R → Uperc = ∅) ∧
      ∀ β : ℝ, IsGLB R β → 1 / 2 ≤ β ∧ Uperc = unitDirectionInterval (1 - β) β := by
  intro ν R Uperc
  let p : unitInterval := ⟨μ.real {M}, by simp⟩
  have hν₁ : ν {1} = μ {M} := by
    rw [show ν {1} = (unitInterval.toNNReal p : ENNReal) from
      bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp) (by simp),
      ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hνValues : ∀ᵐ t ∂ν, t = 1 ∨ t = 0 := by
    rw [ae_iff]
    change ν (({1} : Set ℝ) ∪ {0})ᶜ = 0
    exact bernoulliMeasure_apply_of_notMem_of_notMem p
      ((measurableSet_singleton _).union (measurableSet_singleton _)).compl (by simp) (by simp)
  have hνBox : ∀ᵐ t ∂ν, 0 ≤ t ∧ t ≤ 1 := by
    filter_upwards [hνValues] with t ht
    rcases ht with rfl | rfl <;> norm_num
  have hFieldValues : ∀ᵐ ω ∂environmentLaw ν, ∀ z : Lattice, ω z = 1 ∨ ω z = 0 := by
    refine ae_all_iff.mpr fun z =>
      ae_of_ae_map (μ := environmentLaw ν) (p := fun t : ℝ => t = 1 ∨ t = 0)
        (measurable_environment_eval z).aemeasurable ?_
    rwa [environmentLaw_map_eval]
  have hId : ∀ᵐ ω ∂environmentLaw ν, topField ω = ω := by
    filter_upwards [hFieldValues] with ω hω
    funext z
    rcases hω z with h | h <;> simp [topField, h]
  obtain ⟨g, hcont, hhom, hconc, hsample, hlim, _, _⟩ :=
    exists_shape_with_expected_bounds_of_ae_mem_unit_interval ν hνBox
  have hmap : (environmentLaw μ).map (topWeightIndicatorField μ) = environmentLaw ν := by
    rw [source_top_indicator_environmentLaw_map]
    simp only [environmentLaw, (source_top_indicator_hasLaw μ).map_eq,
      supportTopAtom_eq_singleton_of_eq μ M hM, ν]
  have hPass (d : ℕ × ℕ) :
      (∫ ω : Environment, lastPassage (topWeightIndicatorField μ ω) 0 d ∂environmentLaw μ) =
      ∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw ν := by
    rw [← hmap]
    symm
    exact integral_map (measurable_source_top_indicator_environment μ).aemeasurable
      (measurable_lastPassage 0 d).aestronglyMeasurable
  have hEq : gtop = g := by
    funext x
    apply tendsto_nhds_unique (hgtop x)
    simpa only [hPass] using hlim x
  have htopSample : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    filter_upwards [hId, hsample] with ω hω h
    rwa [hω]
  obtain ⟨hEmpty, hInterval⟩ :=
    top_shape_flat_segment_of_expected_edge_rates ν (by rwa [hν₁])
    (by rwa [hν₁]) g hcont hhom hconc htopSample
  refine ⟨?_, ?_⟩
  · intro hUnbounded
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxg⟩
    obtain ⟨hxEq, hxI⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
    have hlt := hEmpty hUnbounded (x.1 : ℝ) hxI
    rw [hxEq, ← hEq, hxg] at hlt
    exact lt_irrefl _ hlt
  · intro β hβ
    obtain ⟨hhalf, _, hInterval⟩ := hInterval β hβ
    refine ⟨hhalf, ?_⟩
    ext x
    change (x ∈ closedUnitDirections ∧ gtop x = 1) ↔
      x ∈ closedUnitDirections ∧ (x.1 : ℝ) ∈ Icc (1 - β) β
    refine ⟨?_, ?_⟩
    · rintro ⟨hx, hgx⟩
      obtain ⟨hxEq, hxI⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
      refine ⟨hx, (hInterval _ hxI).mp ?_⟩
      rwa [hxEq, ← hEq]
    · rintro ⟨hx, hxβ⟩
      obtain ⟨hxEq, hxI⟩ := toQuadrant_first_of_mem_closedUnitDirections x hx
      have hgx := (hInterval _ hxI).mpr hxβ
      rw [hxEq, ← hEq] at hgx
      exact ⟨hx, hgx⟩

end LPPDifferentiability.FinalDraft
