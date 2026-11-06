/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.SparseMinimumLaw
public import Martin2004.Probability.GreedyAnimalAlmostSureBound

/-!
# Four-color sparse-field animal bounds

The universal rooted-animal constant is chosen before the law and cutoff.
For each deterministic cutoff the four whole-field laws pull one event back
to the original environment, before every positive real tolerance. The common
threshold uses the absolute endpoint length, as required by the connector.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- The actual four sparse fields share one eventual bound, with one threshold
for all colors and all endpoints. The sum is the error used by the connector.
The cutoff is deterministic and precedes the original-environment AE event. -/
theorem exists_sparseMinimumField_animalMaximum_eventually_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      Integrable (fun x : ℝ => x) μ → ∀ L : ℝ, 0 ≤ L →
      ∀ᵐ ω ∂environmentLaw μ,
        ∀ η : ℝ, 0 < η → ∃ N : ℕ, 3 ≤ N ∧
          ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
            (∀ c : Fin 2 × Fin 2,
              animalMaximum (z.1 + z.2 + 3) (by omega) (sparseMinimumField L c ω) ≤
                2 * (z.1 + z.2 : ℕ) * (C * (∫ x, max (-L - x) 0 ∂μ) + η)) ∧
            (∑ c : Fin 2 × Fin 2,
              animalMaximum (z.1 + z.2 + 3) (by omega) (sparseMinimumField L c ω)) ≤
                8 * (z.1 + z.2 : ℕ) * (C * (∫ x, max (-L - x) 0 ∂μ) + η) := by
  obtain ⟨C, hC, hbound⟩ := exists_animalMaximum_limsup_and_eventually_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hμ L _hL
  have hmean : 0 ≤ ∫ x, max (-L - x) 0 ∂μ :=
    integral_nonneg (fun x => le_max_right (-L - x) 0)
  have htail := sparseMinimumLaw_sqrt_tail_eq_mean μ hμ L
  have hfinite :
      (∫⁻ t in Ioi (0 : ℝ), (sparseMinimumLaw μ L (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
    rw [htail]
    exact ENNReal.ofReal_lt_top
  have hcanonical := hbound (sparseMinimumLaw μ L) hfinite
  have hfields : ∀ c : Fin 2 × Fin 2,
      ∀ᵐ ω ∂environmentLaw μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
        animalMaximum (n + 1) (by omega) (sparseMinimumField L c ω) /
          ((n + 1 : ℕ) : ℝ) < C * (∫ x, max (-L - x) 0 ∂μ) + η := by
    intro c
    have hp : MeasurePreserving (sparseMinimumField L c)
        (environmentLaw μ) (environmentLaw (sparseMinimumLaw μ L)) :=
      ⟨measurable_sparseMinimumField L c, environmentLaw_map_sparseMinimumField μ L c⟩
    filter_upwards [hp.quasiMeasurePreserving.ae hcanonical] with ω hω
    simpa only [htail, ENNReal.toReal_ofReal hmean] using hω.2
  filter_upwards [ae_all_iff.mpr hfields] with ω hω
  intro η hη
  have hall : ∀ᶠ n : ℕ in atTop, ∀ c : Fin 2 × Fin 2,
      animalMaximum (n + 1) (by omega) (sparseMinimumField L c ω) /
        ((n + 1 : ℕ) : ℝ) < C * (∫ x, max (-L - x) 0 ∂μ) + η :=
    eventually_all.mpr (fun c => hω c η hη)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hall
  refine ⟨max K 3, le_max_right _ _, ?_⟩
  intro z hz
  have hlen : 3 ≤ z.1 + z.2 := (le_max_right K 3).trans hz
  have hfactor : 0 ≤ C * (∫ x, max (-L - x) 0 ∂μ) + η :=
    add_nonneg (mul_nonneg hC.le hmean) hη.le
  have hsize : ((z.1 + z.2 + 3 : ℕ) : ℝ) ≤ 2 * (z.1 + z.2 : ℕ) := by
    exact_mod_cast (show z.1 + z.2 + 3 ≤ 2 * (z.1 + z.2) by omega)
  have heach : ∀ c : Fin 2 × Fin 2,
      animalMaximum (z.1 + z.2 + 3) (by omega) (sparseMinimumField L c ω) ≤
        2 * (z.1 + z.2 : ℕ) * (C * (∫ x, max (-L - x) 0 ∂μ) + η) := by
    intro c
    have hr := hK (z.1 + z.2 + 2) (by omega) c
    have heq : z.1 + z.2 + 2 + 1 = z.1 + z.2 + 3 := by omega
    simp only [heq] at hr
    have hden : (0 : ℝ) < ((z.1 + z.2 + 3 : ℕ) : ℝ) := by positivity
    calc
      _ ≤ ((z.1 + z.2 + 3 : ℕ) : ℝ) *
          (C * (∫ x, max (-L - x) 0 ∂μ) + η) :=
        ((div_lt_iff₀ hden).mp hr).le.trans_eq (mul_comm _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsize hfactor
  refine ⟨heach, ?_⟩
  calc
    _ ≤ ∑ _c : Fin 2 × Fin 2,
        2 * (z.1 + z.2 : ℕ) * (C * (∫ x, max (-L - x) 0 ∂μ) + η) :=
      Finset.sum_le_sum (fun c _ => heach c)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Nat.reduceMul, nsmul_eq_mul]; ring

end LPPDifferentiability
