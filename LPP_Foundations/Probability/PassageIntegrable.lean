/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import LPP_Foundations.Probability.PassageMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability of finite path weights and passage times

An integrable one-site law gives integrable coordinate weights, finite path sums,
and the finite maximum that defines last passage. No sign or boundedness assumption
is needed. These lemmas assume only the explicit first-moment condition; they do
not derive it from the stronger moment conditions of the differentiability preprint.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- The canonical weight at every site is integrable under an integrable marginal law. -/
theorem integrable_environment_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (z : Lattice) :
    Integrable (fun ω : Environment => ω z) (environmentLaw μ) := by
  have hmap : Integrable (fun x : ℝ => x)
      ((environmentLaw μ).map (fun ω : Environment => ω z)) := by
    rw [environmentLaw_map_eval]
    exact hμ
  exact hmap.comp_measurable (measurable_environment_eval z)

/-- The actual terminal-excluded sum along each finite path is integrable. -/
theorem integrable_pathWeight (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    Integrable (fun ω : Environment => pathWeight ω p) (environmentLaw μ) := by
  classical
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_environment_eval μ hμ (p.vertex i.castSucc)

/-- The finite maximum over all actual paths is integrable. -/
theorem integrable_lastPassage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (u : Lattice) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment => lastPassage ω u d) (environmentLaw μ) := by
  classical
  have hsup :
      Integrable
        (Finset.univ.sup' Finset.univ_nonempty
          (fun p : Path u d => fun ω : Environment => pathWeight ω p))
        (environmentLaw μ) :=
    Finset.sup'_induction
      (p := fun f : Environment → ℝ => Integrable f (environmentLaw μ))
      Finset.univ_nonempty _
      (fun _ hf _ hg => hf.sup hg) (fun p _ => integrable_pathWeight μ hμ p)
  have heq :
      (fun ω : Environment => lastPassage ω u d) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun p : Path u d => fun ω : Environment => pathWeight ω p) := by
    funext ω
    simp [lastPassage, Finset.max'_eq_sup', Finset.sup'_image]
  rw [heq]
  exact hsup

/-- Every coordinate has the first moment of the prescribed marginal law. -/
theorem integral_environment_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (z : Lattice) :
    (∫ ω : Environment, ω z ∂environmentLaw μ) = ∫ x : ℝ, x ∂μ := by
  have hmap : Integrable (fun x : ℝ => x)
      ((environmentLaw μ).map (fun ω : Environment => ω z)) := by
    rw [environmentLaw_map_eval]
    exact hμ
  have h := integral_map (μ := environmentLaw μ)
    (measurable_environment_eval z).aemeasurable
    (f := fun x : ℝ => x) hmap.aestronglyMeasurable
  rw [environmentLaw_map_eval] at h
  exact h.symm

/-- The mean of a fixed path weight is its length times the one-site mean. -/
theorem integral_pathWeight (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    (∫ ω : Environment, pathWeight ω p ∂environmentLaw μ) =
      (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ := by
  classical
  unfold pathWeight
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_environment_eval μ hμ (p.vertex i.castSucc))]
  simp only [integral_environment_eval μ hμ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end LPPDifferentiability
