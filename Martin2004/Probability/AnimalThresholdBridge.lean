/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Maximum
public import Martin2004.Probability.AnimalLayerCake
public import Martin2004.Probability.BernoulliThreshold

/-!
# Real animal maxima and strict-threshold counts

These representation identities connect the actual real animal maximum to
finite-family layer cake. The maximum uses exactly the canonical rooted,
connected animals of the specified positive size.
-/

public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- Applying `ofReal` to a finite nonnegative sum preserves its value. -/
theorem finite_sum_ofReal_eq_ofReal_sum {α : Type*} (U : Finset α) (w : α → ℝ)
    (hw : ∀ v ∈ U, 0 ≤ w v) :
    (∑ v ∈ U, ENNReal.ofReal (w v)) = ENNReal.ofReal (∑ v ∈ U, w v) := by
  exact (ENNReal.ofReal_sum_of_nonneg hw).symm

/-- Applying `ofReal` to an attained finite maximum preserves its value. -/
theorem finite_sup'_ofReal_eq_ofReal_sup' {α : Type*} (H : Finset α)
    (hH : H.Nonempty) (f : α → ℝ) :
    H.sup' hH (fun U => ENNReal.ofReal (f U)) = ENNReal.ofReal (H.sup' hH f) := by
  exact (Finset.apply_sup'_eq_sup'_comp hH ENNReal.ofReal ENNReal.ofReal_max).symm

/-- Nonnegative site sums and their finite-family maxima agree in both carriers. -/
theorem finite_sup'_sum_ofReal_eq_ofReal_sup'_sum {α : Type*}
    (H : Finset (Finset α)) (hH : H.Nonempty) (w : α → ℝ) (hw : ∀ v, 0 ≤ w v) :
    H.sup' hH (fun U => ∑ v ∈ U, ENNReal.ofReal (w v)) =
      ENNReal.ofReal (H.sup' hH (fun U => ∑ v ∈ U, w v)) := by
  calc
    _ = H.sup' hH (fun U => ENNReal.ofReal (∑ v ∈ U, w v)) := by
      apply Finset.sup'_congr hH rfl
      intro U _
      exact finite_sum_ofReal_eq_ofReal_sum U w (fun v _ => hw v)
    _ = _ := finite_sup'_ofReal_eq_ofReal_sup' H hH _

/-- The actual nonnegative real maximum is the ENNReal finite-family maximum. -/
theorem animalMaximum_ofReal_eq_sup'_sum_ofReal (n : ℕ) (hn : 1 ≤ n)
    (w : Lattice → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ENNReal.ofReal (animalMaximum n hn w) =
      (animalFamily_finite n).toFinset.sup'
        ((animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn))
        (fun U => ∑ v ∈ U, ENNReal.ofReal (w v)) := by
  exact (finite_sup'_sum_ofReal_eq_ofReal_sup'_sum _ _ w hw).symm

/-- Each strict-threshold field value is nonnegative. -/
theorem strictThresholdField_nonneg (t : ℝ) (ω : Environment) (z : Lattice) :
    0 ≤ strictThresholdField t ω z := by
  rcases strictThresholdField_zero_or_one t ω z with h | h
  · rw [h]
  · rw [h]
    norm_num

/-- The threshold count is the real threshold-field sum after `ofReal`. -/
theorem animalThresholdCount_eq_ofReal_animalWeight
    (U : Finset Lattice) (ω : Environment) (t : ℝ) :
    animalThresholdCount U ω t = ENNReal.ofReal (animalWeight (strictThresholdField t ω) U) := by
  rw [animalThresholdCount_eq_sum_strictThresholdIndicator]
  exact finite_sum_ofReal_eq_ofReal_sum U (strictThresholdField t ω)
    (fun z _ => strictThresholdField_nonneg t ω z)

/-- The strict-threshold maximum equals the actual real animal maximum
of the strict threshold field, after applying `ofReal`. -/
theorem animalThresholdMaximum_eq_ofReal_animalMaximum
    (n : ℕ) (hn : 1 ≤ n) (ω : Environment) (t : ℝ) :
    animalThresholdMaximum (animalFamily_finite n).toFinset
        ((animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn)) ω t =
      ENNReal.ofReal (animalMaximum n hn (strictThresholdField t ω)) := by
  unfold animalThresholdMaximum
  calc
    _ = (animalFamily_finite n).toFinset.sup'
        ((animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn))
        (fun U => ENNReal.ofReal (animalWeight (strictThresholdField t ω) U)) := by
      apply Finset.sup'_congr ((animalFamily_finite n).toFinset_nonempty.mpr
        (animalFamily_nonempty n hn)) rfl
      intro U _
      exact animalThresholdCount_eq_ofReal_animalWeight U ω t
    _ = _ := finite_sup'_ofReal_eq_ofReal_sup' _ _ _

/-- Nonnegative levels see the same strict threshold field after taking positive parts. -/
theorem strictThresholdField_positivePart (ω : Environment) (t : ℝ) (ht : 0 ≤ t) :
    strictThresholdField t (fun z => max (ω z) 0) = strictThresholdField t ω := by
  funext z
  exact strictThresholdIndicator_positivePart t (ω z) ht

/-- Taking positive parts preserves the threshold maximum at every nonnegative level. -/
theorem animalThresholdMaximum_positivePart (H : Finset (Finset Lattice)) (hH : H.Nonempty)
    (ω : Environment) (t : ℝ) (ht : 0 ≤ t) :
    animalThresholdMaximum H hH (fun z => max (ω z) 0) t =
      animalThresholdMaximum H hH ω t := by
  unfold animalThresholdMaximum
  apply Finset.sup'_congr hH rfl
  intro U _
  exact animalThresholdCount_positivePart U ω t ht

/-- The actual threshold-field animal maximum is unchanged by positive parts. -/
theorem animalMaximum_strictThresholdField_positivePart
    (n : ℕ) (hn : 1 ≤ n) (ω : Environment) (t : ℝ) (ht : 0 ≤ t) :
    animalMaximum n hn (strictThresholdField t (fun z => max (ω z) 0)) =
      animalMaximum n hn (strictThresholdField t ω) := by
  rw [strictThresholdField_positivePart ω t ht]

/-- The real maximum over actual animals satisfies the layer-cake bound. -/
theorem animalMaximum_ofReal_le_lintegral_thresholdMaximum
    (n : ℕ) (hn : 1 ≤ n) (w : Lattice → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ENNReal.ofReal (animalMaximum n hn w) ≤
      ∫⁻ t in Ioi (0 : ℝ),
        animalThresholdMaximum (animalFamily_finite n).toFinset
          ((animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn))
          w t ∂volume := by
  rw [animalMaximum_ofReal_eq_sup'_sum_ofReal n hn w hw]
  exact finite_animalThresholdMaximum_lintegral _ _ w hw

end LPPDifferentiability
