/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Rays
public import LPP_Foundations.Probability.PassageLaw
public import LPP_Foundations.Probability.TranslationErgodic
public import Mathlib.Analysis.Subadditive

/-!
# Probability facts for actual last-passage rays

Negated finite passage values are measurable and integrable under a genuine
marginal first moment. Their expectations are subadditive, and every nonzero
natural ray uses an ergodic coordinate translation of the iid environment.
No convergence or finiteness of a limiting rate is asserted here.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- Every finite negated ray passage is measurable in the actual environment. -/
theorem measurable_neg_lastPassage_ray (a : ℕ × ℕ) (n : ℕ) :
    Measurable (fun ω : Environment => -lastPassage ω 0 (n • a)) :=
  (measurable_lastPassage 0 (n • a)).neg

/-- A genuine first moment of the marginal makes every finite ray term integrable. -/
theorem integrable_neg_lastPassage_ray (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (a : ℕ × ℕ) (n : ℕ) :
    Integrable (fun ω : Environment => -lastPassage ω 0 (n • a)) (environmentLaw μ) :=
  (integrable_lastPassage μ hμ 0 (n • a)).neg

/-- The actual means of negated finite ray passage are a subadditive sequence. -/
theorem subadditive_integral_neg_lastPassage_ray (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (a : ℕ × ℕ) :
    Subadditive (fun n : ℕ => ∫ ω : Environment,
      -lastPassage ω 0 (n • a) ∂environmentLaw μ) := by
  intro m n
  simp only [integral_neg]
  have h := neg_le_neg (integral_lastPassage_superadditive μ hμ 0 (m • a) (n • a))
  rw [← add_nsmul, neg_add] at h
  exact h

/-- Every nonzero natural direction gives the actual ergodic lattice shift. -/
theorem ergodic_environment_natRay_translation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℕ × ℕ) (ha : a ≠ 0) :
    Ergodic (fun ω : Environment => fun z => ω (((a.1 : ℤ), (a.2 : ℤ)) + z))
      (environmentLaw μ) := by
  apply ergodic_environment_translation μ
  intro h
  apply ha
  change ((a.1 : ℤ), (a.2 : ℤ)) = (0, 0) at h
  have hfst : (a.1 : ℤ) = 0 := congrArg Prod.fst h
  have hsnd : (a.2 : ℤ) = 0 := congrArg Prod.snd h
  exact Prod.ext (Int.natCast_inj.mp hfst) (Int.natCast_inj.mp hsnd)

end LPPDifferentiability
