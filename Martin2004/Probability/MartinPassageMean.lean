/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.AnimalPositiveMean
public import LPP_Foundations.Model.LastPassage.AnimalComparison
public import LPP_Foundations.Probability.PassageIntegrable
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Expected passage bounds from the positive square-root tail

One universal animal constant bounds actual signed last-passage expectations.
If an actual normalized expected passage sequence has a limit, the same
constant also bounds that limit. The limit clause is conditional: this file
does not prove that a ray limit exists.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace LPPDifferentiability

/-- One positive constant bounds actual expected passage values for every
integrable marginal with finite positive square-root tail. The same constant
bounds any actual expected rate along a natural ray, conditional on convergence
of that normalized expected passage sequence. -/
theorem exists_positive_lastPassage_mean_bound :
    ∃ C : ℝ, 0 < C ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
        (_hμ : Integrable (fun x : ℝ => x) μ)
        (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
        (d : ℕ × ℕ),
        Integrable (fun ω : Environment => lastPassage ω 0 d) (environmentLaw μ) ∧
        (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
          C * ((d.1 + d.2 : ℕ) : ℝ) *
            (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
        (_hμ : Integrable (fun x : ℝ => x) μ)
        (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
        (a : ℕ × ℕ) (g : ℝ),
        Tendsto
          (fun n : ℕ =>
            (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) /
              (n : ℝ))
          atTop (𝓝 g) →
        g ≤ C * ((a.1 + a.2 : ℕ) : ℝ) *
          (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) := by
  obtain ⟨C, hC, hanimal⟩ := exists_positive_animalMaximum_mean_bound
  have hfinite :
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
        (hμ : Integrable (fun x : ℝ => x) μ)
        (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
        (d : ℕ × ℕ),
        Integrable (fun ω : Environment => lastPassage ω 0 d) (environmentLaw μ) ∧
        (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
          C * ((d.1 + d.2 : ℕ) : ℝ) *
            (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal := by
    intro μ _ hμ hpos d
    let I : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)
    have hpassage : Integrable (fun ω : Environment => lastPassage ω 0 d)
        (environmentLaw μ) := integrable_lastPassage μ hμ 0 d
    refine ⟨hpassage, ?_⟩
    by_cases hd : 0 < d.1 + d.2
    · have hn : 1 ≤ d.1 + d.2 := by omega
      have hanimalMoment := (hanimal μ (d.1 + d.2) hn).2 hpos
      calc
        (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
            ∫ ω : Environment,
              animalMaximum (d.1 + d.2) hn (fun v => max (ω v) 0)
                ∂environmentLaw μ := by
          apply integral_mono hpassage hanimalMoment.1
          intro ω
          exact lastPassage_le_animalMaximum_atOrigin ω d hd
        _ ≤ C * ((d.1 + d.2 : ℕ) : ℝ) * I.toReal := by
          simpa only [I] using hanimalMoment.2
    · have hd0 : d = (0, 0) := by
        apply Prod.ext <;> omega
      rw [hd0]
      simp only [lastPassage_zero, integral_zero, Nat.zero_add, Nat.cast_zero,
        mul_zero, zero_mul]
      exact le_rfl
  refine ⟨C, hC, hfinite, ?_⟩
  · intro μ _ hμ hpos a g hlimit
    let I : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)
    let K : ℝ := C * ((a.1 + a.2 : ℕ) : ℝ) * I.toReal
    have hterm : ∀ n : ℕ,
        (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) /
          (n : ℝ) ≤ K := by
      intro n
      by_cases hn : 0 < n
      · have hpassage := (hfinite μ hμ hpos (n • a)).2
        have hpassage' :
            (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) ≤
              C * (((n • a).1 + (n • a).2 : ℕ) : ℝ) * I.toReal := by
          simpa only [I] using hpassage
        have hscale : (((n • a).1 + (n • a).2 : ℕ) : ℝ) =
            (n : ℝ) * ((a.1 + a.2 : ℕ) : ℝ) := by
          simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
            Nat.cast_add, Nat.cast_mul]
          ring
        have hnum :
            (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) ≤
              K * (n : ℝ) := by
          calc
            _ ≤ C * (((n • a).1 + (n • a).2 : ℕ) : ℝ) * I.toReal := hpassage'
            _ = K * (n : ℝ) := by
              rw [hscale]
              dsimp [K]
              ring
        exact (div_le_iff₀ (Nat.cast_pos.mpr hn)).2 hnum
      · have hn0 : n = 0 := by omega
        subst n
        have hzero :
            (∫ ω : Environment,
              lastPassage ω 0 ((0 : ℕ) • a) ∂environmentLaw μ) = 0 := by
          have hfun :
              (fun ω : Environment => lastPassage ω 0 ((0 : ℕ) • a)) =
                fun _ : Environment => (0 : ℝ) := by
            funext ω
            rw [zero_smul]
            exact lastPassage_zero ω 0
          rw [hfun]
          exact integral_zero Environment ℝ
        rw [hzero]
        simp only [zero_div]
        dsimp [K]
        positivity
    exact le_of_tendsto' hlimit hterm

end LPPDifferentiability
