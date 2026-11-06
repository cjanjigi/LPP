/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.MartinFirstMoment
public import Martin2004.Probability.MartinNaturalShape
public import LPP_Foundations.Probability.PassageSymmetry

/-!
# Coordinate symmetry of Martin's natural passage rate

The actual expected passage limits inherit coordinate symmetry from the
finite passage laws. Applying this to the unique natural rate under Martin's
two square-root-tail assumptions preserves every property of the existing
natural-rate theorem and adds symmetry of that same witness.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace LPPDifferentiability

/-- Actual expected-ray limits for a first-moment environment have equal rates
in the two coordinate-swapped natural directions. -/
theorem martin_natural_rate_swap_of_expected_limits (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ)
    (g : (ℕ × ℕ) → ℝ)
    (hlim : ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0 (n • a)
          ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 (g a))) :
    ∀ a : ℕ × ℕ, g a.swap = g a := by
  intro a
  have hmeans :
      (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0 (n • a.swap)
          ∂environmentLaw μ) / (n : ℝ)) =
      (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0 (n • a)
          ∂environmentLaw μ) / (n : ℝ)) := by
    funext n
    have hdir : n • a.swap = (n • a).swap := by
      ext <;> simp
    rw [hdir]
    simpa using congrArg (fun x : ℝ => x / (n : ℝ))
      ((integrable_and_integral_lastPassage_swap μ hμ 0 (n • a)).2.2)
  have hlimSwap : Tendsto
      (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0 (n • a)
          ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 (g a.swap)) := by
    simpa only [hmeans] using hlim a.swap
  exact tendsto_nhds_unique hlimSwap (hlim a)

/-- Under Martin's two integrated square-root tails, the unique natural rate
from `exists_unique_lastPassage_natural_shape_of_martin_tails` is invariant
under swapping coordinates. Its existing conclusions are all retained, and
the same unique rate function witnesses the strengthened result. -/
theorem exists_unique_lastPassage_natural_shape_of_martin_tails_and_swap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : (ℕ × ℕ) → ℝ,
      ((∀ a : ℕ × ℕ,
        Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 (n • a)
            ∂environmentLaw μ) / (n : ℝ))
          atTop (𝓝 (g a)) ∧
        g a = sSup (range (fun n : ℕ =>
          (∫ ω : Environment,
            lastPassage ω 0 ((n + 1) • a) ∂environmentLaw μ) /
            ((n + 1 : ℕ) : ℝ))) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto
          (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ))
          atTop (𝓝 (g a))) ∧
        Tendsto (fun n : ℕ => ∫ ω : Environment,
          |lastPassage ω 0 (n • a) / (n : ℝ) - g a|
            ∂environmentLaw μ) atTop (𝓝 0)) ∧
      g 0 = 0 ∧
      (∀ (a : ℕ × ℕ) (k : ℕ), g (k • a) = (k : ℝ) * g a) ∧
      (∀ a b : ℕ × ℕ, g a + g b ≤ g (a + b)) ∧
      (∀ k : ℕ, g (k, 0) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ k : ℕ, g (0, k) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ a : ℕ × ℕ,
        ((a.1 + a.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤ g a ∧
        g a ≤ ((a.1 + a.2 : ℕ) : ℝ) *
          (g (1, 1) - ∫ x : ℝ, x ∂μ)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ))
        atTop (𝓝 (g a)))) ∧
      (∀ a : ℕ × ℕ, g a.swap = g a) := by
  classical
  obtain ⟨g, hg, hUnique⟩ :=
    exists_unique_lastPassage_natural_shape_of_martin_tails μ hneg hpos
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  have hlim := fun a : ℕ × ℕ => (hg.1 a).1
  have hswap := martin_natural_rate_swap_of_expected_limits μ hμ g hlim
  refine ⟨g, ⟨hg, hswap⟩, ?_⟩
  intro f hf
  exact hUnique f hf.1

end LPPDifferentiability
