/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.DiagonalMaximum
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurability of the actual diagonal-family maximum. -/

@[expose] public section

namespace LPPDifferentiability

/-- The maximum over the actual diagonal family is measurable when each site
weight is measurable on the original space. -/
theorem measurable_diagonalAnimalMaximum {Ω : Type*} [MeasurableSpace Ω]
    (X : Lattice → Ω → ℝ) (hX : ∀ v, Measurable (X v))
    (m n : ℤ) (hmn : m < n) :
    Measurable
      (fun ω => diagonalAnimalMaximum m n hmn (fun v => X v ω)) := by
  classical
  let F := (diagonalAnimalFamily_finite m n).toFinset
  have hF : F.Nonempty :=
    (diagonalAnimalFamily_finite m n).toFinset_nonempty.mpr
      (diagonalAnimalFamily_nonempty m n hmn)
  have hsup : Measurable
      (F.sup' hF
        (fun s => fun ω => animalWeight (fun v => X v ω) s)) := by
    apply Finset.measurable_sup' hF
    intro s hs
    simp only [animalWeight]
    exact Finset.measurable_fun_sum s (fun v _ => hX v)
  have hmax :
      (fun ω => diagonalAnimalMaximum m n hmn (fun v => X v ω)) =
        F.sup' hF (fun s => fun ω => animalWeight (fun v => X v ω) s) := by
    funext ω
    change
      F.sup' hF (fun s => animalWeight (fun v => X v ω) s) =
        F.sup' hF (fun s => fun ω => animalWeight (fun v => X v ω) s) ω
    exact (Finset.sup'_apply hF
      (fun s => fun ω => animalWeight (fun v => X v ω) s) ω).symm
  rw [hmax]
  exact hsup

end LPPDifferentiability
