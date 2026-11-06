/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentLaw

/-!
# Coordinates of the environment law

Reading the weight at one site is measurable, each site has the prescribed marginal law, and
the site weights are independent under the canonical environment law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Reading the weight at a fixed site is measurable. -/
theorem measurable_environment_eval (z : Lattice) :
    Measurable (fun ω : Environment => ω z) :=
  measurable_pi_apply z

/-- Each site has the prescribed marginal law. -/
theorem environmentLaw_map_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (z : Lattice) :
    (environmentLaw μ).map (fun ω : Environment => ω z) = μ := by
  exact Measure.infinitePi_map_eval (fun _ : Lattice => μ) z

/-- The site weights under the canonical environment law are independent. -/
theorem iIndepFun_environment_eval (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    iIndepFun (fun z (ω : Environment) => ω z) (environmentLaw μ) := by
  exact iIndepFun_infinitePi (P := fun _ : Lattice => μ)
    (X := fun (_ : Lattice) (x : ℝ) => x) (fun _ => measurable_id)

end LPPDifferentiability
