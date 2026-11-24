/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Truncation.Laws
import Martin2004.Probability.ExpectedPositiveClipping
import Mathlib.Tactic

/-! The finite passage comparison behind subsection `sub:ub_mom-chat` of the final
differentiability draft. The expected positive remainder is bounded by
the lattice-animal estimate of Martin (2002), Theorem 2.3. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft.Truncation

/-- The tail in the shape bound in subsection `sub:ub_mom-chat` is the ordinary integral of
the square root of the strict-tail probability. Under the paper's tail
hypothesis it is finite at every cutoff. -/
theorem upperTail_toReal_eq_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ) :
    (upperTail μ M).toReal = ∫ t in Ioi M, Real.sqrt (μ.real (Ioi t)) := by
  have htail : Antitone (fun t : ℝ => μ.real (Ioi t)) :=
    fun _ _ h => measureReal_mono (Ioi_subset_Ioi h)
  have hmeas : Measurable (fun t : ℝ => Real.sqrt (μ.real (Ioi t))) :=
    Real.continuous_sqrt.measurable.comp htail.measurable
  rw [upperTail, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg (μ.real (Ioi t)))
    hmeas.aestronglyMeasurable]
  simp_rw [ofReal_sqrt_measureReal]

/-- For the actual coupled weights, the loss in an upper-clipped passage
is nonnegative and is bounded by the passage in the positive remainder
field. This is the finite comparison used in subsection `sub:ub_mom-chat`. -/
theorem lastPassage_upperClipped_comparison (ω : Environment) (M : ℝ)
    (u : Lattice) (d : ℕ × ℕ) :
    lastPassage (upperClippedField M ω) u d ≤ lastPassage ω u d ∧
    lastPassage ω u d ≤ lastPassage (upperClippedField M ω) u d +
      lastPassage (fun z => max (ω z - M) 0) u d := by
  have hmono : lastPassage (upperClippedField M ω) u d ≤ lastPassage ω u d :=
    lastPassage_mono _ _ u d (fun z => min_le_right M (ω z))
  have hdecomp : ω = upperClippedField M ω + (fun z => max (ω z - M) 0) := by
    funext z
    change ω z = min M (ω z) + max (ω z - M) 0
    rcases le_total M (ω z) with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h), add_zero]
  refine ⟨hmono, ?_⟩
  calc
    lastPassage ω u d =
        lastPassage (upperClippedField M ω + (fun z => max (ω z - M) 0)) u d :=
      congrArg (fun η : Environment => lastPassage η u d) hdecomp
    _ ≤ _ := lastPassage_add_le _ _ u d

/-- Under the clipped law the expected passage is exactly the expected
passage of the coupled upper-clipped field on the original space.
This identifies the clipped expectations used in subsection `sub:ub_mom-chat`. -/
theorem integral_lastPassage_upperClippedLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (d : ℕ × ℕ) :
    (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw (upperClippedLaw μ M)) =
      ∫ ω : Environment, lastPassage (upperClippedField M ω) 0 d ∂environmentLaw μ := by
  have hm := measurePreserving_upperClippedField μ M
  rw [← hm.map_eq]
  exact integral_map hm.measurable.aemeasurable
    (measurable_lastPassage 0 d).aestronglyMeasurable

private theorem integrable_id_upperClippedLaw (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : LPPStatements.HasFiniteMean μ) (M : ℝ) :
    Integrable (fun t : ℝ => t) (upperClippedLaw μ M) := by
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (show Measurable (fun x : ℝ => min M x) by fun_prop).aemeasurable).2
  exact (integrable_const M).inf hμ

/-- The expected passage loss at every endpoint is at most its length
times one universal constant and the square-root tail above the cutoff.
This is the finite form of subsection `sub:ub_mom-chat`, using Martin (2002), Theorem 2.3
on the actual positive remainder law. -/
theorem exists_integral_lastPassage_upperClippedLaw_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      LPPStatements.HasFiniteMean μ →
      LPPStatements.HasSqrtUpperTail μ →
      ∀ (M : ℝ) (d : ℕ × ℕ),
        0 ≤ (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) -
          (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw (upperClippedLaw μ M)) ∧
        (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) -
          (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw (upperClippedLaw μ M)) ≤
            C * ((d.1 + d.2 : ℕ) : ℝ) * (upperTail μ M).toReal := by
  obtain ⟨C, hC, hAnimal⟩ := exists_positive_animalMaximum_mean_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hμ hpos M d
  have hi := integrable_lastPassage μ hμ 0 d
  have hc := integrable_lastPassage (upperClippedLaw μ M)
    (integrable_id_upperClippedLaw μ hμ M) 0 d
  have hm := measurePreserving_upperClippedField μ M
  have hc' : Integrable (fun ω : Environment => lastPassage (upperClippedField M ω) 0 d)
      (environmentLaw μ) := by
    rw [← hm.map_eq] at hc
    exact hc.comp_measurable hm.measurable
  let ν := μ.map (fun x : ℝ => max (x - M) 0)
  obtain ⟨hr, hrmean⟩ := positive_remainder_lastPassage_integrable_integral μ hμ M d
  have hνtail :
      (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
    change (∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (x - M) 0)) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞
    rw [positive_remainder_sqrt_tail]
    exact upperTail_lt_top μ hpos M
  -- Apply the animal bound to the actual nonnegative remainder law.
  have hrbound :
      (∫ ω : Environment, lastPassage (fun z => max (ω z - M) 0) 0 d ∂environmentLaw μ) ≤
        C * ((d.1 + d.2 : ℕ) : ℝ) * (upperTail μ M).toReal := by
    rw [hrmean]
    by_cases hd : 0 < d.1 + d.2
    · obtain ⟨hAI, hAB⟩ := (hAnimal ν (d.1 + d.2) hd).2 hνtail
      calc
        _ ≤ ∫ ω : Environment, animalMaximum (d.1 + d.2) hd (fun z => max (ω z) 0)
            ∂environmentLaw ν :=
          integral_mono (integrable_lastPassage ν (integrable_id_map_positive_remainder μ hμ M) 0 d)
            hAI (fun ω => lastPassage_le_animalMaximum_atOrigin ω d hd)
        _ ≤ _ := by simpa only [upperTail, ν, positive_remainder_sqrt_tail] using hAB
    · have he : d = (0, 0) := Prod.ext (by omega) (by omega)
      subst d
      simp only [lastPassage_zero, integral_zero, Nat.add_zero, Nat.cast_zero,
        mul_zero, zero_mul, le_refl]
  -- Integrate the two pointwise inequalities on the common environment.
  rw [integral_lastPassage_upperClippedLaw]
  have hlo := integral_mono hc' hi fun ω => (lastPassage_upperClipped_comparison ω M 0 d).1
  have hup := integral_mono hi (hc'.add hr) fun ω => (lastPassage_upperClipped_comparison ω M 0 d).2
  change (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
    ∫ ω : Environment, lastPassage (upperClippedField M ω) 0 d +
      lastPassage (fun z => max (ω z - M) 0) 0 d ∂environmentLaw μ at hup
  rw [integral_add hc' hr] at hup
  exact ⟨sub_nonneg.mpr hlo, by linarith only [hup, hrbound]⟩

end LPPDifferentiability.FinalDraft.Truncation
