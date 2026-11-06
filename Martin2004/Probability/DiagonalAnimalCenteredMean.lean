/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.DiagonalAnimalMean
public import Martin2004.Probability.DiagonalAnimalLaw
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Actual centered animal moments and expected rates

The centered sequence always uses the positive radius `n+1`. Translation of
actual proper intervals identifies its expectation with the even subsequence
of the origin expectations. The expected-limit theorem here is conditional
on the origin expected limit; it makes no centered almost-sure assertion.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- The actual centered maximum divided by the length of its proper interval. -/
noncomputable def diagonalAnimalCenteredRate (n : ℕ) (ω : Environment) : ℝ :=
  diagonalAnimalMaximum (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) (by omega) ω /
    (2 * (n + 1 : ℕ) : ℕ)

/-- The exact positive-radius normalization. -/
theorem diagonalAnimalCenteredRate_eq (n : ℕ) (ω : Environment) :
    diagonalAnimalCenteredRate n ω =
      diagonalAnimalMaximum (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) (by omega) ω /
        (2 * (n + 1 : ℕ) : ℕ) := rfl

/-- A finite first marginal moment gives finite moments of the actual centered
normalized maximum, with no sign restriction. -/
theorem integrable_diagonalAnimalCenteredRate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (n : ℕ) :
    Integrable (diagonalAnimalCenteredRate n) (environmentLaw μ) := by
  apply Integrable.div_const
  apply integrable_diagonalAnimalMaximum (environmentLaw μ) (fun v ω => ω v)
  intro v
  have hi : Integrable (fun x : ℝ => x)
      ((environmentLaw μ).map (fun ω : Environment => ω v)) := by
    rw [environmentLaw_map_eval]
    exact hμ
  exact hi.comp_measurable (measurable_environment_eval v)

/-- Centered and origin intervals of the same positive length have equal
normalized means, by the law of the actual translated maximum. -/
theorem integral_diagonalAnimalCenteredRate_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) :
    (∫ ω, diagonalAnimalCenteredRate n ω ∂environmentLaw μ) =
      (∫ ω : Environment,
        diagonalAnimalMaximum 0 ((2 * (n + 1 : ℕ) : ℕ) : ℤ) (by omega) ω /
          (2 * (n + 1 : ℕ) : ℕ) ∂environmentLaw μ) := by
  have hlaw := diagonalAnimalMaximum_identDistrib μ 0
    ((2 * (n + 1 : ℕ) : ℕ) : ℤ) (-((n + 1 : ℕ) : ℤ)) (by omega)
  have hleft : (0 : ℤ) + -((n + 1 : ℕ) : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
  have hright : ((2 * (n + 1 : ℕ) : ℕ) : ℤ) + -((n + 1 : ℕ) : ℤ) =
      ((n + 1 : ℕ) : ℤ) := by omega
  simp only [hleft, hright] at hlaw
  simp only [diagonalAnimalCenteredRate, integral_div]
  rw [hlaw.integral_eq]

/-- Conditional expected-rate transfer along the genuine even positive
subsequence. No pointwise centered limit is used. -/
theorem tendsto_integral_diagonalAnimalCenteredRate_of_origin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ}
    (hmean : Tendsto (fun n : ℕ => ∫ ω : Environment,
      diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
        (n + 1 : ℕ) ∂environmentLaw μ) atTop (𝓝 q)) :
    Tendsto (fun n => ∫ ω, diagonalAnimalCenteredRate n ω ∂environmentLaw μ)
      atTop (𝓝 q) := by
  have hsub : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2 * n + 1; omega) tendsto_id
  have heven := hmean.comp hsub
  have heq (n : ℕ) :
      (∫ ω, diagonalAnimalCenteredRate n ω ∂environmentLaw μ) =
      (∫ ω : Environment,
        diagonalAnimalMaximum 0 (((2 * n + 1) + 1 : ℕ) : ℤ) (by omega) ω /
          ((2 * n + 1) + 1 : ℕ) ∂environmentLaw μ) := by
    rw [integral_diagonalAnimalCenteredRate_eq]
    have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    simp only [hindex]
  exact heven.congr (fun n => (heq n).symm)

end LPPDifferentiability
