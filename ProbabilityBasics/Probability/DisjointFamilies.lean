/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independence of arrays indexed by disjoint sets

This file proves that two arrays made from disjoint parts of a mutually
independent family are independent. The index type and the two index sets may
be infinite, and the coordinate types may vary with the index.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics

/-- If measurable coordinates are mutually independent, then the two complete
arrays indexed by any disjoint sets of coordinates are independent. This is
the whole-array independence used in A1 and A2 of
`docs/runs/STRONG-EXISTENCE-20261111-INTAKE/COALESCENCE-20261112/NEXT-STATEMENTS.md`;
the sigma-algebra step follows Mathlib's `indep_iSup_of_disjoint`
(`Mathlib/Probability/Independence/Basic.lean:511-514`). -/
theorem indepFun_restrict_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ∀ i, Ω → β i)
    (h_indep : iIndepFun f P)
    (h_meas : ∀ i, Measurable (f i))
    (S T : Set ι) (hST : Disjoint S T) :
    IndepFun (fun ω (i : S) => f i ω) (fun ω (i : T) => f i ω) P := by
  classical
  let m : ι → MeasurableSpace Ω := fun i =>
    MeasurableSpace.comap (f i) (inferInstance : MeasurableSpace (β i))

  -- Mutual independence of the functions is independence of their coordinate sigma-algebras.
  have h_indep_spaces : iIndep m P := by
    exact (iIndepFun_iff_iIndep
      (fun i => (inferInstance : MeasurableSpace (β i))) f P).mp h_indep

  -- Measurability places every coordinate sigma-algebra inside the ambient one.
  have h_le : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := by
    intro i
    exact (h_meas i).comap_le

  -- Disjoint coordinate sets generate independent supremum sigma-algebras.
  have h_sup_indep : Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) P :=
    indep_iSup_of_disjoint h_le h_indep_spaces hST

  -- The sigma-algebra of a restricted Pi array is the supremum of its coordinates.
  have h_left_space :
      MeasurableSpace.comap (fun ω (i : S) => f i ω)
          (inferInstance : MeasurableSpace (∀ i : S, β i)) =
        ⨆ i ∈ S, m i := by
    rw [MeasurableSpace.comap_process_pi
      (fun i : S => fun ω : Ω => f i.1 ω)]
    change (⨆ i : S, m i.1) = ⨆ i ∈ S, m i
    apply le_antisymm
    · refine iSup_le fun i => ?_
      exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
    · refine iSup_le fun i => iSup_le fun hi => ?_
      exact le_iSup_of_le ⟨i, hi⟩ le_rfl

  have h_right_space :
      MeasurableSpace.comap (fun ω (i : T) => f i ω)
          (inferInstance : MeasurableSpace (∀ i : T, β i)) =
        ⨆ i ∈ T, m i := by
    rw [MeasurableSpace.comap_process_pi
      (fun i : T => fun ω : Ω => f i.1 ω)]
    change (⨆ i : T, m i.1) = ⨆ i ∈ T, m i
    apply le_antisymm
    · refine iSup_le fun i => ?_
      exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
    · refine iSup_le fun i => iSup_le fun hi => ?_
      exact le_iSup_of_le ⟨i, hi⟩ le_rfl

  -- Independence of the generated sigma-algebras is independence of the arrays.
  rw [IndepFun_iff_Indep, h_left_space, h_right_space]
  exact h_sup_indep

end ProbabilityBasics
