/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Model.OrientedPercolation
public import Differentiability.Probability.TopIndicatorLaw
public import Differentiability.FinalDraft.FlatTopRates.RightContinuity
import all Differentiability.Probability.HalfLineEdgeDeviation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The laws of threshold indicators -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace LPPDifferentiability.FinalDraft

private theorem environmentLaw_congr (ν κ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] (h : ν = κ) :
    environmentLaw ν = environmentLaw κ := by
  subst κ
  rfl

/-- The open-site indicator of a weight at least `1 - δ`. -/
noncomputable def nearTopIndicator (δ w : ℝ) : ℝ :=
  (Ici (1 - δ)).indicator (fun _ => 1) w

/-- The Bernoulli parameter of the near-top indicators. -/
noncomputable def nearTopDensity (ν : Measure ℝ) [IsProbabilityMeasure ν] (δ : ℝ) :
    unitInterval :=
  ⟨ν.real (Ici (1 - δ)), measureReal_nonneg, measureReal_le_one⟩

/-- Thresholding each coordinate gives the iid Bernoulli environment at the threshold density. -/
theorem map_nearTopIndicator_environmentLaw (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (δ : ℝ) :
    (environmentLaw ν).map (fun ω : Environment => fun z => nearTopIndicator δ (ω z)) =
      environmentLaw (bernoulliMeasure (1 : ℝ) 0 (nearTopDensity ν δ)) := by
  have hf : Measurable (nearTopIndicator δ) := measurable_const.indicator measurableSet_Ici
  have hlaw : ν.map (nearTopIndicator δ) =
      bernoulliMeasure (1 : ℝ) 0 (nearTopDensity ν δ) :=
    (hasLaw_indicator_one_bernoulliMeasure
      (P := ν) (M := ℝ) (s := Ici (1 - δ)) measurableSet_Ici.nullMeasurableSet).map_eq
  exact (environmentLaw_map_coordinatewise ν _ hf).trans (environmentLaw_congr _ _ hlaw)

/-- A site is open in the thresholded environment exactly when its weight reaches the cutoff. -/
theorem mem_topSites_nearTopIndicator_iff (ω : Environment) (δ : ℝ) (z : Lattice) :
    z ∈ topSites (fun x => nearTopIndicator δ (ω x)) ↔ 1 - δ ≤ ω z := by
  change nearTopIndicator δ (ω z) = 1 ↔ ω z ∈ Ici (1 - δ)
  unfold nearTopIndicator
  by_cases hz : ω z ∈ Ici (1 - δ)
  · rw [indicator_of_mem hz]
    exact iff_of_true rfl hz
  · rw [indicator_of_notMem hz]
    exact iff_of_false zero_ne_one hz

/-- The density at positive deficits tending to zero decreases to the mass at one, for weights
bounded above by one almost surely. -/
theorem tendsto_nearTopDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ w ∂ν, w ≤ 1) :
    Tendsto (fun n : ℕ => nearTopDensity ν (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (⟨ν.real {1}, measureReal_nonneg, measureReal_le_one⟩ : unitInterval)) := by
  let S (n : ℕ) := Ici (1 - 1 / ((n : ℝ) + 1))
  have hS : Antitone S := by
    intro n m hnm
    apply Ici_subset_Ici.mpr
    have hd : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity)
        (by exact_mod_cast Nat.succ_le_succ hnm)
    linarith
  have hInter : (⋂ n, S n) = Ici (1 : ℝ) := by
    ext t
    rw [mem_iInter]
    constructor
    · intro ht
      change 1 ≤ t
      have hT : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
        simpa only [sub_zero] using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact le_of_tendsto hT (Eventually.of_forall ht)
    · intro ht n
      change 1 - 1 / ((n : ℝ) + 1) ≤ t
      exact (sub_le_self _ (by positivity)).trans ht
  have hLaw : ν (Ici (1 : ℝ)) = ν ({1} : Set ℝ) := by
    apply measure_congr
    filter_upwards [hle] with t ht
    change (1 ≤ t) = (t = 1)
    exact propext ⟨fun h => le_antisymm ht h, fun h => h.ge⟩
  have hT := tendsto_measure_iInter_atTop (μ := ν)
    (s := S) (fun _ => measurableSet_Ici.nullMeasurableSet) hS ⟨0, measure_ne_top _ _⟩
  rw [hInter, hLaw] at hT
  exact tendsto_subtype_rng.mpr
    ((ENNReal.tendsto_toReal (measure_ne_top ν {1})).comp hT)

/-- The expected half-line edge of a law is the edge of Bernoulli sites of the same top mass. -/
theorem integral_halfLineEdge_eq_bernoulli_topMass (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (L : ℕ) :
    (∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν) =
      ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw
        (bernoulliMeasure (1 : ℝ) 0 ⟨ν.real {1}, measureReal_nonneg, measureReal_le_one⟩) := by
  let f := ({1} : Set ℝ).indicator (fun _ => (1 : ℝ))
  let F (ω : Environment) : Environment := fun z => f (ω z)
  have hf : Measurable f := measurable_const.indicator (measurableSet_singleton _)
  have hmap := environmentLaw_map_coordinatewise ν f hf
  have hlaw : ν.map f = bernoulliMeasure (1 : ℝ) 0
      ⟨ν.real {1}, measureReal_nonneg, measureReal_le_one⟩ :=
    (hasLaw_indicator_one_bernoulliMeasure (P := ν) (M := ℝ)
      (s := ({1} : Set ℝ)) (measurableSet_singleton _).nullMeasurableSet).map_eq
  change (environmentLaw ν).map F = environmentLaw (ν.map f) at hmap
  have hmap' := hmap.trans (environmentLaw_congr _ _ hlaw)
  rw [← hmap']
  have hm : Measurable (fun ω : Environment => (halfLineEdge ω L : ℝ)) :=
    (Measurable.of_discrete (f := fun x : ℤ => (x : ℝ))).comp (measurable_halfLineEdge L)
  rw [integral_map (measurable_coordinatewise_environment_map f hf).aemeasurable
    hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hsites : topSites (F ω) = topSites ω := by
    ext z
    by_cases h : ω z = 1 <;> simp [F, f, topSites, h]
  change ((openEdge (topSites ω) antidiagHalfLine L : ℤ) : ℝ) =
    ((openEdge (topSites (F ω)) antidiagHalfLine L : ℤ) : ℝ)
  rw [hsites]

/-- A strict one-length half-line expectation bound persists at a positive near-top deficit
when the original top mass is positive. -/
theorem exists_nearTopDensity_halfLineEdge_lt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ w ∂ν, w ≤ 1) (hp : 0 < ν {1}) (L : ℕ) (b : ℝ)
    (hL : (∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν) < b) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < (nearTopDensity ν δ : ℝ) ∧
      (∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw
        (bernoulliMeasure (1 : ℝ) 0 (nearTopDensity ν δ))) < b := by
  let p : unitInterval := ⟨ν.real {1}, measureReal_nonneg, measureReal_le_one⟩
  have hpR : 0 < (p : ℝ) := ENNReal.toReal_pos hp.ne' (measure_ne_top ν {1})
  have hD : Tendsto (fun n : ℕ => nearTopDensity ν (1 / ((n : ℝ) + 1))) atTop
      (𝓝[Ici p] p) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_nearTopDensity ν hle, ?_⟩
    filter_upwards [] with n
    change ν.real {1} ≤ ν.real (Ici (1 - 1 / ((n : ℝ) + 1)))
    exact measureReal_mono (by
      intro x hx
      rw [mem_singleton_iff.mp hx]
      exact sub_le_self _ (by positivity)) (measure_ne_top _ _)
  let F (q : unitInterval) : ℝ :=
    ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 q)
  have hFc : Tendsto F (𝓝[Ici p] p) (𝓝 (F p)) :=
    continuousWithinAt_integral_halfLineEdge_bernoulli p hpR L
  have hC := hFc.comp hD
  have hFp : F p = ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν :=
    (integral_halfLineEdge_eq_bernoulli_topMass ν L).symm
  rw [hFp] at hC
  have hpq := ((tendsto_nhdsWithin_iff.mp hD).2.and
    (hC.eventually (Iio_mem_nhds hL))).exists
  obtain ⟨j, hj, hj'⟩ := hpq
  exact ⟨1 / ((j : ℝ) + 1), by positivity, lt_of_lt_of_le hpR hj, hj'⟩

end LPPDifferentiability.FinalDraft
