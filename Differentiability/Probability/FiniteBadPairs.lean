/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite bad-pair probabilities in the environment

This file bounds the probability that some pair of distinct sites, from a finite set of pairs,
is bad at once, meaning that both values lie strictly below `-T`. The bound is the number of
pairs times the square of the one-site lower-tail probability.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace LPPDifferentiability

/-- For two distinct sites `u` and `v`, the probability that both values lie strictly below `-T`
is the square of the one-site probability. -/
theorem environmentLaw_real_bad_pair_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (u v : Lattice) (huv : u ≠ v) :
    (environmentLaw μ).real {ω : Environment | ω u < -T ∧ ω v < -T} =
      (μ.real (Iio (-T))) ^ 2 := by
  classical
  let f : Bool → Lattice := fun b => if b then v else u
  have hf : Function.Injective f := by
    intro b c h
    cases b <;> cases c <;> simp_all [f]
  let coordinates : Environment → Bool → ℝ := fun ω b => ω (f b)
  let rectangle : Set (Bool → ℝ) := Set.univ.pi (fun _ => Iio (-T))
  have hrectangle : MeasurableSet rectangle :=
    MeasurableSet.univ_pi fun _ => measurableSet_Iio
  have hcoordinates : Measurable coordinates :=
    measurable_finite_environment_coordinates f
  have hpre : coordinates ⁻¹' rectangle =
      {ω : Environment | ω u < -T ∧ ω v < -T} := by
    ext ω
    simp [coordinates, rectangle, f]
  have hlaw :
      (environmentLaw μ).map coordinates = Measure.pi (fun _ : Bool => μ) :=
    environmentLaw_map_finite_coordinates μ f hf
  have hprod :
      (Measure.pi (fun _ : Bool => μ)) rectangle =
        ∏ _b : Bool, μ (Iio (-T)) := by
    change (Measure.pi (fun _ : Bool => μ))
      (Set.univ.pi (fun _ : Bool => Iio (-T))) = _
    exact Measure.pi_pi (fun _ : Bool => μ) (fun _ => Iio (-T))
  calc
    (environmentLaw μ).real {ω : Environment | ω u < -T ∧ ω v < -T} =
        (environmentLaw μ).real (coordinates ⁻¹' rectangle) := by rw [hpre]
    _ = ((environmentLaw μ).map coordinates).real rectangle :=
      (map_measureReal_apply hcoordinates hrectangle).symm
    _ = (Measure.pi (fun _ : Bool => μ)).real rectangle := by rw [hlaw]
    _ = (μ.real (Iio (-T))) ^ 2 := by
      rw [measureReal_def, hprod]
      simp [measureReal_def]

/-- A finite union of two-site events, each saying that both values lie strictly below `-T`, is
measurable. -/
theorem measurableSet_finite_bad_pair_union
    (B : Finset (Lattice × Lattice)) (T : ℝ) :
    MeasurableSet (⋃ uv ∈ B,
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) := by
  classical
  exact Finset.measurableSet_biUnion B fun uv huv =>
    (measurableSet_lt (measurable_environment_eval uv.1) measurable_const).inter
      (measurableSet_lt (measurable_environment_eval uv.2) measurable_const)

/-- The union bound over finitely many pairs of distinct sites, using the pair law above. -/
theorem environmentLaw_real_finite_bad_pair_union_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (B : Finset (Lattice × Lattice))
    (hB : ∀ uv ∈ B, uv.1 ≠ uv.2) :
    (environmentLaw μ).real (⋃ uv ∈ B,
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) ≤
        (B.card : ℝ) * (μ.real (Iio (-T))) ^ 2 := by
  classical
  calc
    (environmentLaw μ).real
        (⋃ uv ∈ B, {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) ≤
        ∑ uv ∈ B,
          (environmentLaw μ).real {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T} :=
      measureReal_biUnion_finset_le B _
    _ ≤ ∑ _uv ∈ B, (μ.real (Iio (-T))) ^ 2 := by
      apply Finset.sum_le_sum
      intro uv huv
      exact le_of_eq (environmentLaw_real_bad_pair_probability μ T uv.1 uv.2 (hB uv huv))
    _ = (B.card : ℝ) * (μ.real (Iio (-T))) ^ 2 := by simp

/-- The event that some close pair of sites in `Q` is bad is measurable. The pairs are the ordered
pairs of distinct sites of `Q` whose `L1` distance is at most two. -/
theorem measurableSet_close_bad_pair_union
    (Q : Finset Lattice) (T : ℝ) :
    MeasurableSet (⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) := by
  classical
  exact measurableSet_finite_bad_pair_union
    ((Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
      |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2)) T

/-- The probability of the close-pair failure event is at most the number of ordered close pairs
times the square of the one-site lower-tail probability. -/
theorem environmentLaw_real_close_bad_pair_union_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (Q : Finset Lattice) (T : ℝ) :
    (environmentLaw μ).real (⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}) ≤
        (((Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
          |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2)).card : ℝ) *
          (μ.real (Iio (-T))) ^ 2 := by
  classical
  apply environmentLaw_real_finite_bad_pair_union_le
  intro uv huv
  exact (Finset.mem_filter.mp huv).2.1

end LPPDifferentiability
