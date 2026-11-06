/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import ProbabilityBasics.Probability.IndependentBadCount
public import Mathlib.MeasureTheory.Measure.Real

import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.Image

/-!
# Bad-site counts in a finite family of regions

This file bounds the probability that some region of a finite family contains at least `K` bad
sites. A site is bad when its value lies strictly below `-T`. Within each region the sites are
independent, and the union bound over the regions gives the estimate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace LPPDifferentiability

private theorem measureReal_bad_site_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : ℝ) (z : Lattice) :
    (environmentLaw μ).real {ω : Environment | ω z < -T} = μ.real (Iio (-T)) := by
  have hSet : {ω : Environment | ω z < -T} =
      (fun ω : Environment => ω z) ⁻¹' Iio (-T) := by
    ext ω
    simp [Set.mem_Iio]
  rw [hSet]
  change ((environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Iio (-T))).toReal =
    (μ (Iio (-T))).toReal
  calc
    ((environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Iio (-T))).toReal =
        (((environmentLaw μ).map (fun ω : Environment => ω z)) (Iio (-T))).toReal := by
          rw [Measure.map_apply (measurable_environment_eval z) measurableSet_Iio]
    _ = μ.real (Iio (-T)) := by
      rw [environmentLaw_map_eval μ z]
      rfl

private theorem iIndep_bad_site_events_on_finset (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (T : ℝ) (S : Finset Lattice) :
    iIndepSet
      (fun z : {v : Lattice // v ∈ S} =>
        {ω : Environment | ω z.1 < -T}) (environmentLaw μ) := by
  classical
  let I := {v : Lattice // v ∈ S}
  let bad : I → Set Environment := fun z => {ω | ω z.1 < -T}
  have hCoordinates :
      iIndepFun (fun z : I => fun ω : Environment => ω z.1) (environmentLaw μ) := by
    exact (iIndepFun_environment_eval μ).precomp Subtype.val_injective
  apply (iIndepSet_iff_iIndep bad (environmentLaw μ)).2
  apply iIndep_of_iIndep_of_le hCoordinates.iIndep
  intro z
  refine MeasurableSpace.generateFrom_le fun A hA => ?_
  have hA' : A = bad z := by simpa only [Set.mem_singleton_iff] using hA
  subst A
  exact MeasurableSpace.measurableSet_comap.2
    ⟨Iio (-T), measurableSet_Iio, by
      ext ω
      simp [bad, Set.mem_Iio]⟩

private theorem bad_filter_card_eq_subtype_filter_card
    (S : Finset Lattice) (T : ℝ) (ω : Environment) :
    (S.filter (fun z => ω z < -T)).card =
      ((Finset.univ : Finset {z : Lattice // z ∈ S}).filter
        (fun z => ω z.1 < -T)).card := by
  classical
  rw [Finset.univ_eq_attach]
  simpa only [Finset.card_map, Finset.card_attach] using
    (congrArg Finset.card
      (Finset.filter_attach (fun z : Lattice => ω z < -T) S)).symm

private theorem bad_count_event_eq_subtype_count
    (S : Finset Lattice) (T : ℝ) (K : ℕ) :
    {ω : Environment | K ≤ (S.filter (fun z => ω z < -T)).card} =
      {ω : Environment | K ≤
        ((Finset.univ : Finset {z : Lattice // z ∈ S}).filter
          (fun z => ω z.1 < -T)).card} := by
  ext ω
  change (K ≤ (S.filter (fun z : Lattice => ω z < -T)).card) ↔
    K ≤ ((Finset.univ : Finset {z : Lattice // z ∈ S}).filter
      (fun z => ω z.1 < -T)).card
  exact Iff.of_eq
    (congrArg (fun n : ℕ => K ≤ n) (bad_filter_card_eq_subtype_filter_card S T ω))

private theorem measurable_and_bad_count_probability_on_finset
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (S : Finset Lattice) (K : ℕ) :
    MeasurableSet {ω : Environment | K ≤ (S.filter (fun z => ω z < -T)).card} ∧
      (environmentLaw μ).real
        {ω : Environment | K ≤ (S.filter (fun z => ω z < -T)).card} ≤
          ((S.card : ℝ) * μ.real (Iio (-T))) ^ K := by
  classical
  let I := {z : Lattice // z ∈ S}
  let bad : I → Set Environment := fun z => {ω | ω z.1 < -T}
  have hBadMeas : ∀ z : I, MeasurableSet (bad z) := by
    intro z
    exact measurableSet_lt (measurable_environment_eval z.1) measurable_const
  have hInd : iIndepSet bad (environmentLaw μ) := by
    simpa only [bad] using iIndep_bad_site_events_on_finset μ T S
  have hMeasSubtype := measurableSet_iIndepSet_badCount_ge bad hBadMeas K
  have hMarginal (z : I) :
      (environmentLaw μ).real (bad z) ≤ μ.real (Iio (-T)) := by
    change (environmentLaw μ).real {ω : Environment | ω z.1 < -T} ≤ _
    rw [measureReal_bad_site_eq μ T z.1]
  have hProbabilitySubtype :=
    measureReal_iIndepSet_badCount_ge_le_pow (environmentLaw μ) bad hBadMeas
      hInd (μ.real (Iio (-T))) measureReal_nonneg hMarginal K
  have hCard : Fintype.card I = S.card := Fintype.card_coe S
  have hEvent := bad_count_event_eq_subtype_count S T K
  have hProbabilitySubtype' := hProbabilitySubtype
  rw [hCard] at hProbabilitySubtype'
  constructor
  · rw [hEvent]
    exact hMeasSubtype
  · rw [hEvent]
    exact hProbabilitySubtype'

/-- For finite site sets `S j` (with `j ∈ J`) that each have at most `A` sites, the probability
that some set contains at least `K` sites below `-T` is at most `J.card` times
`(A * μ(Iio (-T)))^K`. Independence is used only within each site set, which follows from the
law of the environment; no independence between different sets is assumed. -/
theorem measurable_and_measureReal_exists_bad_count_ge_le
    {ι : Type*} [DecidableEq ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : ℝ) (J : Finset ι) (S : ι → Finset Lattice)
    (A K : ℕ) (hCap : ∀ j ∈ J, (S j).card ≤ A) :
    MeasurableSet {ω : Environment | ∃ j ∈ J,
      K ≤ ((S j).filter (fun z => ω z < -T)).card} ∧
      (environmentLaw μ).real {ω : Environment | ∃ j ∈ J,
        K ≤ ((S j).filter (fun z => ω z < -T)).card} ≤
          (J.card : ℝ) * ((A : ℝ) * μ.real (Iio (-T))) ^ K := by
  classical
  let badCount : ι → Set Environment := fun j =>
    {ω | K ≤ ((S j).filter (fun z => ω z < -T)).card}
  have hEvent :
      {ω : Environment | ∃ j ∈ J, K ≤ ((S j).filter (fun z => ω z < -T)).card} =
        ⋃ j ∈ J, badCount j := by
    ext ω
    simp [badCount]
  have hBadMeas (j : ι) : MeasurableSet (badCount j) :=
    (measurable_and_bad_count_probability_on_finset μ T (S j) K).1
  have hBadProbability (j : ι) (hj : j ∈ J) :
      (environmentLaw μ).real (badCount j) ≤
        ((A : ℝ) * μ.real (Iio (-T))) ^ K := by
    have hCount :=
      (measurable_and_bad_count_probability_on_finset μ T (S j) K).2
    have hCardReal : ((S j).card : ℝ) ≤ (A : ℝ) := by exact_mod_cast hCap j hj
    have hTailNonneg : 0 ≤ μ.real (Iio (-T)) := measureReal_nonneg
    have hBase := mul_le_mul_of_nonneg_right hCardReal hTailNonneg
    have hBaseNonneg : 0 ≤ ((S j).card : ℝ) * μ.real (Iio (-T)) :=
      mul_nonneg (Nat.cast_nonneg _) hTailNonneg
    calc
      (environmentLaw μ).real (badCount j) ≤
          (((S j).card : ℝ) * μ.real (Iio (-T))) ^ K := by
        simpa only [badCount] using hCount
      _ ≤ ((A : ℝ) * μ.real (Iio (-T))) ^ K :=
        pow_le_pow_left₀ hBaseNonneg hBase K
  constructor
  · rw [hEvent]
    exact Finset.measurableSet_biUnion J fun j _ => hBadMeas j
  · rw [hEvent]
    calc
      (environmentLaw μ).real (⋃ j ∈ J, badCount j) ≤
          ∑ j ∈ J, (environmentLaw μ).real (badCount j) :=
        measureReal_biUnion_finset_le J badCount
      _ ≤ ∑ _j ∈ J, ((A : ℝ) * μ.real (Iio (-T))) ^ K := by
        apply Finset.sum_le_sum
        intro j hj
        exact hBadProbability j hj
      _ = (J.card : ℝ) * ((A : ℝ) * μ.real (Iio (-T))) ^ K := by simp

end LPPDifferentiability
