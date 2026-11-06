/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Probability.CoordinateLaw

/-!
# The finite law of weights on a fixed path

The collected vertices of a fixed path are distinct, so their weights under the
canonical environment law are independent and have the common marginal law.
These statements concern a deterministic path; they do not assert that an
environment-dependent choice of path has independent weights.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The vector of weights at all collected vertices of a fixed path is measurable. -/
theorem measurable_path_collected_evals {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    Measurable (fun ω : Environment =>
      fun i : Fin (d.1 + d.2) => ω (p.vertex i.castSucc)) :=
  Measurable.of_eval fun i => measurable_environment_eval (p.vertex i.castSucc)

/-- Weights along a fixed path are independent under the canonical environment law. -/
theorem iIndepFun_path_collected_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    iIndepFun
      (fun (i : Fin (d.1 + d.2)) (ω : Environment) => ω (p.vertex i.castSucc))
      (environmentLaw μ) := by
  have hinj : Function.Injective
      (fun i : Fin (d.1 + d.2) => p.vertex i.castSucc) := by
    intro i j hij
    exact Fin.castSucc_injective _ (p.vertex_injective hij)
  exact (iIndepFun_environment_eval μ).precomp hinj

/-- The collected weight vector of a fixed path has the finite iid product law. -/
theorem environmentLaw_map_path_collected_evals (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    (environmentLaw μ).map
      (fun ω : Environment => fun i : Fin (d.1 + d.2) => ω (p.vertex i.castSucc)) =
    Measure.pi (fun _ : Fin (d.1 + d.2) => μ) := by
  calc
    (environmentLaw μ).map
        (fun ω : Environment => fun i : Fin (d.1 + d.2) =>
          ω (p.vertex i.castSucc)) =
        Measure.pi (fun i : Fin (d.1 + d.2) =>
          (environmentLaw μ).map (fun ω : Environment => ω (p.vertex i.castSucc))) := by
      exact iIndepFun.map_fun_eq_pi_map
        (fun i => (measurable_environment_eval (p.vertex i.castSucc)).aemeasurable)
        (iIndepFun_path_collected_eval μ p)
    _ = Measure.pi (fun _ : Fin (d.1 + d.2) => μ) := by
      exact congrArg (fun ν : Fin (d.1 + d.2) → Measure ℝ => Measure.pi ν)
        (funext fun i => environmentLaw_map_eval μ (p.vertex i.castSucc))

end LPPDifferentiability
