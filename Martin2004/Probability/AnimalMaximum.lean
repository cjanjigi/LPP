/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Maximum
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurability of the actual maximum from a measurable site field. -/

@[expose] public section

namespace LPPDifferentiability

/-- The maximum over the actual size-`n` animal family is measurable when each
site weight is measurable on the original probability space. -/
theorem measurable_animalMaximum {Ω : Type*} [MeasurableSpace Ω]
    (X : Lattice → Ω → ℝ) (hX : ∀ v, Measurable (X v))
    (n : ℕ) (hn : 1 ≤ n) :
    Measurable (fun ω => animalMaximum n hn (fun v => X v ω)) := by
  classical
  let F := (animalFamily_finite n).toFinset
  have hF : F.Nonempty :=
    (animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn)
  have hsup : Measurable
      (F.sup' hF (fun s => fun ω => animalWeight (fun v => X v ω) s)) := by
    apply Finset.measurable_sup' hF
    intro s hs
    simp only [animalWeight]
    exact Finset.measurable_fun_sum s (fun v _ => hX v)
  have hmax :
      (fun ω => animalMaximum n hn (fun v => X v ω)) =
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
