/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Mathlib.Topology.Order.ProjIcc

/-!
# Bounded coordinates with the original real law

The explicit interval projection gives a probability measure on the literal
closed subtype. Its real pushforward equals the original law under its AE
bound; endpoint atoms and the degenerate interval are retained.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Clipping to the literal closed bounded subtype is measurable. -/
theorem measurable_bounded_coordinate (L : ℝ) (hL : 0 ≤ L) :
    Measurable (Set.projIcc (-L) L (neg_le_self hL)) :=
  (continuous_projIcc (a := -L) (b := L) (h := neg_le_self hL)).measurable

/-- The explicit clipped image of a probability measure is a probability measure. -/
theorem isProbabilityMeasure_bounded_coordinate_map (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L) :
    IsProbabilityMeasure (μ.map (Set.projIcc (-L) L (neg_le_self hL))) :=
  inferInstance

/-- Clipping retains the original real law when the stated marginal bound holds AE. -/
theorem bounded_coordinate_map_val (μ : Measure ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ᵐ x ∂μ, |x| ≤ L) :
    (μ.map (Set.projIcc (-L) L (neg_le_self hL))).map
        (Subtype.val : Set.Icc (-L) L → ℝ) = μ := by
  rw [Measure.map_map measurable_subtype_coe (measurable_bounded_coordinate L hL)]
  calc
    _ = μ.map (id : ℝ → ℝ) := by
      apply Measure.map_congr
      filter_upwards [hbound] with x hx
      exact congrArg Subtype.val (Set.projIcc_of_mem (neg_le_self hL) (abs_le.mp hx))
    _ = μ := Measure.map_id

/-- The actual finite bounded vector is measurable. -/
theorem measurable_finite_bounded_environment_coordinates {I : Type*}
    (L : ℝ) (hL : 0 ≤ L) (f : I → Lattice) :
    Measurable (fun ω : Environment => fun i =>
      Set.projIcc (-L) L (neg_le_self hL) (ω (f i))) :=
  measurable_pi_iff.mpr fun i =>
    (measurable_bounded_coordinate L hL).comp (measurable_environment_eval (f i))

/-- The entire actual finite bounded vector has the explicit clipped product law. -/
theorem environmentLaw_map_finite_bounded_coordinates {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (f : I → Lattice) (hf : Function.Injective f) :
    (environmentLaw μ).map (fun ω : Environment => fun i =>
      Set.projIcc (-L) L (neg_le_self hL) (ω (f i))) =
      Measure.pi (fun _ : I => μ.map (Set.projIcc (-L) L (neg_le_self hL))) :=
  environmentLaw_map_finite_coordinates_comp μ f hf _ (measurable_bounded_coordinate L hL)

/-- Actual bounded blocks have the nested product of the explicit clipped image laws. -/
theorem environmentLaw_map_finite_bounded_blocks {K : Type*} [Fintype K]
    {I : K → Type*} [∀ k, Fintype (I k)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (f : Sigma I → Lattice) (hf : Function.Injective f) :
    (environmentLaw μ).map (fun ω : Environment => fun k i =>
      Set.projIcc (-L) L (neg_le_self hL) (ω (f ⟨k, i⟩))) =
      Measure.pi (fun k => Measure.pi (fun _ : I k =>
        μ.map (Set.projIcc (-L) L (neg_le_self hL)))) :=
  environmentLaw_map_finite_blocks_comp μ f hf _ (measurable_bounded_coordinate L hL)

/-- Integrals of measurable functions of the actual bounded blocks use their actual law. -/
theorem integral_finite_bounded_environment_blocks {K : Type*} [Fintype K]
    {I : K → Type*} [∀ k, Fintype (I k)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (f : Sigma I → Lattice) (hf : Function.Injective f)
    (F : ((k : K) → I k → Set.Icc (-L) L) → ℝ) (hF : Measurable F) :
    (∫ ω, F (fun k i => Set.projIcc (-L) L (neg_le_self hL) (ω (f ⟨k, i⟩)))
      ∂environmentLaw μ) =
      ∫ x, F x ∂Measure.pi (fun k => Measure.pi (fun _ : I k =>
        μ.map (Set.projIcc (-L) L (neg_le_self hL)))) :=
  integral_finite_environment_blocks_comp μ f hf _ (measurable_bounded_coordinate L hL) F hF

end LPPDifferentiability
