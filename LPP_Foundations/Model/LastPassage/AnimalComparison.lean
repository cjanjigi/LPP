/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Maximum
public import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LPP_Foundations.Model.Animals.PathSets
import LPP_Foundations.Model.LastPassage.Translate

/-! A signed passage maximum is bounded by the maximum over animals. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- At the origin, compare a maximizing path with its collected animal.
The positive part of the site field bounds every signed path weight. -/
theorem lastPassage_le_animalMaximum_atOrigin (ω : Environment) (d : ℕ × ℕ)
    (hd : 0 < d.1 + d.2) :
    lastPassage ω 0 d ≤
      animalMaximum (d.1 + d.2) (by omega) (fun z => max (ω z) 0) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω 0 d
  calc
    lastPassage ω 0 d = pathWeight ω p := hp.symm
    _ = ∑ z ∈ p.collectedSites, ω z :=
      Path.pathWeight_eq_sum_collectedSites ω p
    _ ≤ ∑ z ∈ p.collectedSites, max (ω z) 0 := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_max_left (ω z) 0
    _ = animalWeight (fun z => max (ω z) 0) p.collectedSites := rfl
    _ ≤ animalMaximum (d.1 + d.2) (by omega) (fun z => max (ω z) 0) :=
      animalWeight_le_animalMaximum (d.1 + d.2) (by omega)
        (fun z => max (ω z) 0)
        (Path.collectedSites_mem_animalFamily p hd)

/-- At any starting point, bound signed passage by the animal maximum
for the translated positive-part field. -/
theorem lastPassage_le_animalMaximum (ω : Environment) (u : Lattice)
    (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) :
    lastPassage ω u d ≤
      animalMaximum (d.1 + d.2) (by omega)
        (fun z => max (ω (u + z)) 0) := by
  calc
    lastPassage ω u d = lastPassage ω (u + (0 : Lattice)) d := by simp
    _ = lastPassage (fun z => ω (u + z)) 0 d :=
      (lastPassage_translate ω u 0 d).symm
    _ ≤ animalMaximum (d.1 + d.2) (by omega)
        (fun z => max (ω (u + z)) 0) :=
      lastPassage_le_animalMaximum_atOrigin (fun z => ω (u + z)) d hd

end LPPDifferentiability
