/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite joint laws of the i.i.d. environment

Restriction along an injective map of sites preserves mutual independence, so a finite vector of
environment values has the product law. Dependent finite blocks are obtained by currying this
joint law, and the empty blocks are included.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- A vector of environment coordinates, indexed by `I`, is measurable. -/
theorem measurable_finite_environment_coordinates {I : Type*} (f : I → Lattice) :
    Measurable (fun ω : Environment => fun i => ω (f i)) :=
  measurable_pi_iff.mpr fun i => measurable_environment_eval (f i)

/-- A finite tuple of distinct sites has the product of the one-site marginal law `μ`. -/
theorem environmentLaw_map_finite_coordinates {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : I → Lattice)
    (hf : Function.Injective f) :
    (environmentLaw μ).map (fun ω : Environment => fun i => ω (f i)) =
      Measure.pi (fun _ : I => μ) := by
  have hi := (iIndepFun_environment_eval μ).precomp hf
  have h := hi.map_fun_eq_pi_map
    (fun i => (measurable_environment_eval (f i)).aemeasurable)
  simpa only [environmentLaw_map_eval] using h

/-- Applying a measurable map to every coordinate of a finite tuple keeps the product form of the
law. -/
theorem environmentLaw_map_finite_coordinates_comp {I E : Type*} [Fintype I]
    [MeasurableSpace E] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : I → Lattice) (hf : Function.Injective f) (c : ℝ → E) (hc : Measurable c) :
    (environmentLaw μ).map (fun ω : Environment => fun i => c (ω (f i))) =
      Measure.pi (fun _ : I => μ.map c) := by
  calc
    _ = ((environmentLaw μ).map (fun ω : Environment => fun i => ω (f i))).map
        (fun x : I → ℝ => fun i => c (x i)) := by
      exact (Measure.map_map (μ := environmentLaw μ)
        (g := fun x : I → ℝ => fun i => c (x i))
        (measurable_pi_iff.mpr fun i => hc.comp (measurable_pi_apply i))
        (measurable_finite_environment_coordinates f)).symm
    _ = _ := by
      rw [environmentLaw_map_finite_coordinates μ f hf]
      exact Measure.pi_map_pi (fun _ => hc.aemeasurable)

/-- Currying a finite product indexed by a dependent sum gives the nested product. -/
theorem map_pi_sigma_curry {K : Type*} [Fintype K] {I : K → Type*}
    [∀ k, Fintype (I k)] {E : (k : K) → I k → Type*}
    [∀ k i, MeasurableSpace (E k i)] (ν : (k : K) → (i : I k) → Measure (E k i))
    [∀ k i, IsProbabilityMeasure (ν k i)] :
    (Measure.pi (fun p : Sigma I => ν p.1 p.2)).map
        (fun x k i => x ⟨k, i⟩) =
      Measure.pi (fun k => Measure.pi (ν k)) := by
  have h := Measure.infinitePi_map_piCurry ν
  simp only [Measure.infinitePi_eq_pi] at h
  have hcurry : (MeasurableEquiv.piCurry E :
      ((p : Sigma I) → E p.1 p.2) → (k : K) → (i : I k) → E k i) =
      (fun x k i => x ⟨k, i⟩) := by
    ext x k i
    rfl
  rw [hcurry] at h
  exact h

/-- The vector of finite blocks of coordinates, indexed by a dependent sum, has the nested
product law. -/
theorem environmentLaw_map_finite_blocks_comp {K E : Type*} [Fintype K]
    {I : K → Type*} [∀ k, Fintype (I k)] [MeasurableSpace E]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : Sigma I → Lattice)
    (hf : Function.Injective f) (c : ℝ → E) (hc : Measurable c) :
    (environmentLaw μ).map (fun ω : Environment => fun k i => c (ω (f ⟨k, i⟩))) =
      Measure.pi (fun k => Measure.pi (fun _ : I k => μ.map c)) := by
  calc
    _ = ((environmentLaw μ).map (fun ω : Environment => fun p => c (ω (f p)))).map
        (fun x : Sigma I → E => fun k i => x ⟨k, i⟩) := by
      exact (Measure.map_map (μ := environmentLaw μ)
        (g := fun x : Sigma I → E => fun k i => x ⟨k, i⟩)
        (f := fun ω : Environment => fun p => c (ω (f p)))
        (measurable_pi_iff.mpr fun k =>
          measurable_pi_iff.mpr fun i => measurable_pi_apply (⟨k, i⟩ : Sigma I))
        (measurable_pi_iff.mpr fun p => hc.comp (measurable_environment_eval (f p)))).symm
    _ = _ := by
      rw [environmentLaw_map_finite_coordinates_comp μ f hf c hc]
      exact map_pi_sigma_curry (fun _ _ => μ.map c)

/-- The real block vectors themselves, and not only their one-site marginals, have the nested
law. -/
theorem environmentLaw_map_finite_blocks {K : Type*} [Fintype K]
    {I : K → Type*} [∀ k, Fintype (I k)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : Sigma I → Lattice)
    (hf : Function.Injective f) :
    (environmentLaw μ).map (fun ω : Environment => fun k i => ω (f ⟨k, i⟩)) =
      Measure.pi (fun k => Measure.pi (fun _ : I k => μ)) := by
  simpa only [id_eq, Measure.map_id] using
    environmentLaw_map_finite_blocks_comp μ f hf id measurable_id

/-- The mean of a measurable function of a finite vector of coordinates equals its mean under the
product law. -/
theorem integral_finite_environment_coordinates {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : I → Lattice)
    (hf : Function.Injective f) (F : (I → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ω, F (fun i => ω (f i)) ∂environmentLaw μ) =
      ∫ x, F x ∂Measure.pi (fun _ : I => μ) := by
  rw [← environmentLaw_map_finite_coordinates μ f hf]
  exact (integral_map_of_stronglyMeasurable
    (measurable_finite_environment_coordinates f) hF.stronglyMeasurable).symm

/-- The mean of a measurable function of mapped block vectors equals its mean under the nested
product law. -/
theorem integral_finite_environment_blocks_comp {K E : Type*} [Fintype K]
    {I : K → Type*} [∀ k, Fintype (I k)] [MeasurableSpace E]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : Sigma I → Lattice)
    (hf : Function.Injective f) (c : ℝ → E) (hc : Measurable c)
    (F : ((k : K) → I k → E) → ℝ) (hF : Measurable F) :
    (∫ ω, F (fun k i => c (ω (f ⟨k, i⟩))) ∂environmentLaw μ) =
      ∫ x, F x ∂Measure.pi (fun k => Measure.pi (fun _ : I k => μ.map c)) := by
  rw [← environmentLaw_map_finite_blocks_comp μ f hf c hc]
  exact (integral_map_of_stronglyMeasurable
    (measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun i =>
      hc.comp (measurable_environment_eval (f ⟨k, i⟩))) hF.stronglyMeasurable).symm

end LPPDifferentiability
