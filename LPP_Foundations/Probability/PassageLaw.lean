/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Translate
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.Stationarity

/-!
# Translation invariance of finite passage laws and means

Covariance of the actual finite path maximum and stationarity of the canonical
i.i.d. environment give translation invariance in law. Under an explicit first
moment condition, passage times are integrable and their means are invariant
and superadditive. Deriving this first moment condition from the stronger moment
assumptions of the differentiability preprint is not done here.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- Translating the starting point preserves the law of the finite passage time. -/
theorem environmentLaw_map_lastPassage_translation (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (v u : Lattice) (d : ℕ × ℕ) :
    (environmentLaw μ).map (fun ω : Environment => lastPassage ω (v + u) d) =
      (environmentLaw μ).map (fun ω : Environment => lastPassage ω u d) := by
  have htrans : Measurable (fun ω : Environment => fun z => ω (v + z)) :=
    Measurable.of_eval fun z => measurable_pi_apply (v + z)
  calc
    (environmentLaw μ).map (fun ω : Environment => lastPassage ω (v + u) d) =
        ((environmentLaw μ).map (fun ω : Environment => fun z => ω (v + z))).map
          (fun ω : Environment => lastPassage ω u d) := by
      rw [Measure.map_map (measurable_lastPassage u d) htrans]
      simp only [Function.comp_def, lastPassage_translate]
    _ = (environmentLaw μ).map (fun ω : Environment => lastPassage ω u d) := by
      rw [environmentLaw_map_translation]

/-- Finite passage means are invariant when the marginal has a finite first moment. -/
theorem integral_lastPassage_translation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (v u : Lattice) (d : ℕ × ℕ) :
    (∫ ω : Environment, lastPassage ω (v + u) d ∂environmentLaw μ) =
      ∫ ω : Environment, lastPassage ω u d ∂environmentLaw μ := by
  have htrans : Measurable (fun ω : Environment => fun z => ω (v + z)) :=
    Measurable.of_eval fun z => measurable_pi_apply (v + z)
  have hpassage : AEStronglyMeasurable (fun ω : Environment => lastPassage ω u d)
      ((environmentLaw μ).map (fun ω : Environment => fun z => ω (v + z))) := by
    rw [environmentLaw_map_translation]
    exact (integrable_lastPassage μ hμ u d).aestronglyMeasurable
  have h := integral_map htrans.aemeasurable hpassage
  rw [environmentLaw_map_translation] at h
  simpa only [lastPassage_translate] using h.symm

/-- The expected finite passage value is superadditive in nonnegative displacement. -/
theorem integral_lastPassage_superadditive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (u : Lattice) (d e : ℕ × ℕ) :
    (∫ ω : Environment, lastPassage ω u d ∂environmentLaw μ) +
        (∫ ω : Environment, lastPassage ω u e ∂environmentLaw μ) ≤
      ∫ ω : Environment, lastPassage ω u (d + e) ∂environmentLaw μ := by
  have hd := integrable_lastPassage μ hμ u d
  have he := integrable_lastPassage μ hμ (u + ((d.1 : ℤ), (d.2 : ℤ))) e
  have h := integral_mono (hd.add he) (integrable_lastPassage μ hμ u (d + e))
    (fun ω => lastPassage_superadditive ω u d e)
  have hmean := integral_lastPassage_translation μ hμ ((d.1 : ℤ), (d.2 : ℤ)) u e
  rw [add_comm ((d.1 : ℤ), (d.2 : ℤ)) u] at hmean
  change (∫ ω : Environment, lastPassage ω u d +
    lastPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e ∂environmentLaw μ) ≤ _ at h
  rw [integral_add hd he, hmean] at h
  exact h

end LPPDifferentiability
