/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinPassageMean
public import Martin2004.Probability.MartinRaySymmetry

/-!
# Natural passage rates with a first negative moment

For an integrable marginal, the positive integrated square-root tail supplies
an actual finite expected passage bound. The application of Liggett (1985),
Theorem 1.10, then produces ray limits, which determine one unique natural
rate with all natural geometry and coordinate symmetry. No extension to real
directions, no continuity statement and no uniform weak-moment shape theorem
is asserted. The two-tail results keep their statements.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace LPPDifferentiability

/-- An integrable marginal and its finite positive square-root tail produce
actual expected, almost-sure and L1 ray limits, with the exact expected
supremum. The finite bound is proved internally, not assumed. -/
theorem exists_lastPassage_ray_convergence_of_integrable_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (a : ℕ × ℕ) :
    ∃ g : ℝ,
      Tendsto (fun n : ℕ =>
        (∫ ω, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
        atTop (𝓝 g) ∧
      g = sSup (range (fun n : ℕ =>
        (∫ ω, lastPassage ω 0 ((n + 1) • a) ∂environmentLaw μ) /
          ((n + 1 : ℕ) : ℝ))) ∧
      (∀ᵐ ω ∂environmentLaw μ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 g)) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |lastPassage ω 0 (n • a) / (n : ℝ) - g| ∂environmentLaw μ)
        atTop (𝓝 0) := by
  obtain ⟨C, _hC, hfinite, _hrate⟩ := exists_positive_lastPassage_mean_bound
  let I : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)
  refine exists_lastPassage_ray_convergence_of_expected_bound μ hμ a
    (C * ((a.1 + a.2 : ℕ) : ℝ) * I.toReal) ?_
  intro n _hn
  calc
    (∫ ω, lastPassage ω 0 (n • a) ∂environmentLaw μ) ≤
        C * (((n • a).1 + (n • a).2 : ℕ) : ℝ) * I.toReal :=
      (hfinite μ hμ hpos (n • a)).2
    _ = (C * ((a.1 + a.2 : ℕ) : ℝ) * I.toReal) * (n : ℝ) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        Nat.cast_add, Nat.cast_mul]
      ring

/-- One unique natural rate for the actual passage values, under a first
moment and the positive square-root tail. All limits, geometry, signed axis
values, the common almost-sure event and symmetry belong to this witness. -/
theorem exists_unique_lastPassage_natural_shape_of_integrable_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : (ℕ × ℕ) → ℝ,
      (∀ a : ℕ × ℕ,
        Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
          atTop (𝓝 (g a)) ∧
        g a = sSup (range (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 ((n + 1) • a) ∂environmentLaw μ) /
            ((n + 1 : ℕ) : ℝ))) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto
          (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a))) ∧
        Tendsto (fun n : ℕ => ∫ ω : Environment,
          |lastPassage ω 0 (n • a) / (n : ℝ) - g a| ∂environmentLaw μ)
          atTop (𝓝 0)) ∧
      g 0 = 0 ∧
      (∀ (a : ℕ × ℕ) (k : ℕ), g (k • a) = (k : ℝ) * g a) ∧
      (∀ a b : ℕ × ℕ, g a + g b ≤ g (a + b)) ∧
      (∀ k : ℕ, g (k, 0) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ k : ℕ, g (0, k) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ a : ℕ × ℕ,
        ((a.1 + a.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤ g a ∧
        g a ≤ ((a.1 + a.2 : ℕ) : ℝ) * (g (1, 1) - ∫ x : ℝ, x ∂μ)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a))) ∧
      (∀ a : ℕ × ℕ, g a.swap = g a) := by
  classical
  have hrays := fun a : ℕ × ℕ =>
    exists_lastPassage_ray_convergence_of_integrable_and_positive_tail μ hμ hpos a
  choose g hg using hrays
  have hlim := fun a : ℕ × ℕ => (hg a).1
  refine ⟨g, ?_, ?_⟩
  · refine ⟨hg, martin_ray_limit_zero μ g hlim,
      martin_ray_limit_nsmul μ g hlim,
      martin_ray_limit_superadditive μ hμ g hlim,
      martin_ray_limit_horizontal μ hμ g hlim,
      martin_ray_limit_vertical μ hμ g hlim, ?_, ?_, ?_⟩
    · intro a
      exact ⟨martin_ray_limit_ge_path_mean μ hμ g hlim a,
        martin_ray_limit_le_diagonal_mean μ hμ g hlim a⟩
    · exact ae_all_iff.mpr (fun a => (hg a).2.2.1)
    · exact martin_natural_rate_swap_of_expected_limits μ hμ g hlim
  · intro f hf
    funext a
    exact tendsto_nhds_unique (hf.1 a).1 (hlim a)

end LPPDifferentiability
