/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralArray
public import Martin2004.Probability.BilateralArrayIncrements
public import Martin2004.Probability.DiagonalAnimalLaw
public import LPP_Foundations.Model.Animals.DiagonalSuperadditive

/-! The canonical full proper-interval array of the actual diagonal animal
maxima. Stationarity uses the whole indexed law, not the marginals. -/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- The actual maximum array, with exactly the proper-interval carrier. -/
noncomputable def diagonalAnimalArray (ω : Environment) : BilateralArray :=
  fun p => diagonalAnimalMaximum p.val.1 p.val.2 p.property ω

@[simp] theorem diagonalAnimalArray_apply (ω : Environment) (a b : ℤ) (h : a < b) :
    diagonalAnimalArray ω ⟨(a, b), h⟩ = diagonalAnimalMaximum a b h ω := rfl

theorem measurable_diagonalAnimalArray : Measurable diagonalAnimalArray :=
  measurable_diagonalAnimalMaximum_process (fun p : BilateralInterval => p.val.1)
    (fun p => p.val.2) (fun p => p.property)

/-- Whole-array stationarity inherited from the actual indexed Q law. -/
theorem environmentLaw_map_bilateralArrayShift_diagonalAnimalArray
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (environmentLaw μ).map (bilateralArrayShift ∘ diagonalAnimalArray) =
      (environmentLaw μ).map diagonalAnimalArray :=
  environmentLaw_map_diagonalAnimalMaximum_process μ
    (fun p : BilateralInterval => p.val.1) (fun p => p.val.2) (fun p => p.property) 1

/-- The literal shift preserves the canonical actual-array law. -/
theorem measurePreserving_bilateralArrayShift_diagonalAnimalArray
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving bilateralArrayShift
      ((environmentLaw μ).map diagonalAnimalArray)
      ((environmentLaw μ).map diagonalAnimalArray) := by
  refine ⟨measurable_bilateralArrayShift, ?_⟩
  rw [Measure.map_map measurable_bilateralArrayShift measurable_diagonalAnimalArray]
  exact environmentLaw_map_bilateralArrayShift_diagonalAnimalArray μ

/-- Actual Q superadditivity supplies the conditional finite interval lemma,
even for signed environments. -/
theorem diagonalAnimalMaximum_le_sum_Ico_bilateralArrayIncrements
    (ω : Environment) (n : ℕ) (a b : ℤ) (hab : a < b)
    (ha : bilateralIncrementRoot n < a) :
    diagonalAnimalMaximum a b hab ω ≤
      ∑ t ∈ Finset.Ico a b, bilateralArrayIncrements n (diagonalAnimalArray ω) t := by
  exact interval_le_sum_Ico_bilateralArrayIncrements_of_superadditive
    (diagonalAnimalArray ω)
    (fun _ _ _ hab hbc => diagonalAnimalMaximum_superadditive hab hbc ω) n a b hab ha

/-- Nonnegative actual environments give nonnegative auxiliary increments. -/
theorem diagonalAnimalArrayIncrements_nonneg_of_forall_nonneg
    (ω : Environment) (hω : ∀ v, 0 ≤ ω v) (n : ℕ) (t : ℤ) :
    0 ≤ bilateralArrayIncrements n (diagonalAnimalArray ω) t := by
  exact bilateralArrayIncrements_nonneg_of_nonneg_superadditive (diagonalAnimalArray ω)
    (fun p => diagonalAnimalMaximum_nonneg_of_forall_nonneg
      p.val.1 p.val.2 p.property ω hω)
    (fun _ _ _ hab hbc => diagonalAnimalMaximum_superadditive hab hbc ω) n t

end LPPDifferentiability
