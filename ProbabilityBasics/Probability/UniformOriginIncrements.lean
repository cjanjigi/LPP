/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformOrigin

/-!
# The expectation of finite uniform-origin increments

This is equation (2.9) of Liggett (1985), with window size `n + 1` and coordinate
`k + 1`. Every index of the original sequence that occurs is positive.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- The difference of Liggett (1985) at a random positive origin. Coordinate `k`
corresponds to Liggett's coordinate `k + 1`. No value of the original sequence at
zero is used. -/
@[expose] def uniformOriginIncrement {Ω : Type*} (X : ℕ → Ω → ℝ) (n k : ℕ)
    (p : Ω × Fin (n + 1)) : ℝ :=
  X (k + p.2.val + 2) p.1 - X (k + p.2.val + 1) p.1

theorem measurable_uniformOriginIncrement {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (X j)) (n k : ℕ) :
    Measurable (uniformOriginIncrement X n k) := by
  unfold uniformOriginIncrement
  apply measurable_from_prod_countable_left
  intro u
  exact (hm (k + u.val + 2) (by omega)).sub (hm (k + u.val + 1) (by omega))

theorem integrable_uniformOriginIncrement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (n k : ℕ) :
    Integrable (uniformOriginIncrement X n k) (uniformOriginProduct μ n) := by
  unfold uniformOriginIncrement
  apply integrable_uniformOrigin_family μ n
    (fun u ω => X (k + u.val + 2) ω - X (k + u.val + 1) ω)
  · intro u
    exact (hm _ (by omega)).sub (hm _ (by omega))
  · intro u
    exact (hi _ (by omega)).sub (hi _ (by omega))

private theorem sum_successive_differences (g : ℕ → ℝ) (m : ℕ) :
    (∑ u : Fin m, (g (u.val + 1) - g u.val)) = g m - g 0 := by
  induction m with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_self]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    ring

/-- The finite average in the first equality of equation (2.9) of Liggett (1985),
with finite first moments justifying every subtraction of integrals. -/
theorem integral_uniformOriginIncrement_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (n k : ℕ) :
    (∫ p, uniformOriginIncrement X n k p ∂uniformOriginProduct μ n) =
      (∑ u : Fin (n + 1), ((∫ ω, X (k + u.val + 2) ω ∂μ) -
        (∫ ω, X (k + u.val + 1) ω ∂μ))) / (n + 1 : ℝ) := by
  rw [show uniformOriginIncrement X n k =
    (fun p : Ω × Fin (n + 1) =>
      X (k + p.2.val + 2) p.1 - X (k + p.2.val + 1) p.1) from rfl]
  rw [integral_uniformOrigin_family μ n
    (fun u ω => X (k + u.val + 2) ω - X (k + u.val + 1) ω)
    (fun u => (hm _ (by omega)).sub (hm _ (by omega)))
    (fun u => (hi _ (by omega)).sub (hi _ (by omega)))]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact integral_sub (hi _ (by omega)) (hi _ (by omega))

/-- The telescoped expectation: this is equation (2.9) of Liggett (1985) after
shifting the indices, so that the window has size `n + 1` and the coordinate is
`k + 1`. -/
theorem integral_uniformOriginIncrement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (n k : ℕ) :
    (∫ p, uniformOriginIncrement X n k p ∂uniformOriginProduct μ n) =
      ((∫ ω, X (k + n + 2) ω ∂μ) - (∫ ω, X (k + 1) ω ∂μ)) / (n + 1 : ℝ) := by
  rw [integral_uniformOriginIncrement_average μ X hm hi n k]
  congr 1
  simpa only [Nat.add_assoc, Nat.zero_add, Nat.add_zero] using
    sum_successive_differences (fun j => ∫ ω, X (k + j + 1) ω ∂μ) (n + 1)

end LPPDifferentiability
