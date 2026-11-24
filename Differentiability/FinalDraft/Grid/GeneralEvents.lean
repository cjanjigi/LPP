/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Grid.Events
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
import LPP_Foundations.Model.Paths.Fintype
import LPP_Foundations.Probability.PassageMeasurable

/-! # Grid cell events for general weights -/

@[expose] public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- The closed block of a crossing trial, including its terminal level
(`differentiability_final_draft.tex`, the block in `eq:crossblock`). -/
def gridCrossingBlock (a w : ℝ) (I : ℤ) (l m : ℕ) (c : Lattice) : Set Lattice :=
  {z | I + (m : ℤ) ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (l : ℤ) - (m : ℤ) ∧
    |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) -
      ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * w}

/-- All the weights in a region are at most the given cap
(`differentiability_final_draft.tex`, Lemma `lem:stair-general`). -/
def gridUpperCap (Q : Set Lattice) (cap : ℝ) : Set Environment :=
  {ω | ∀ z ∈ Q, ω z ≤ cap}

/-- The crossing trial and the cap on that same block at its fixed rounded
centre (`differentiability_final_draft.tex`, `eq:heavy-cross`). -/
def gridCappedTrial (a G K : ℝ) (I h : ℤ) (l m j w : ℕ) (ν : Fin (j ^ 2)) :
    Set Environment :=
  let centre := coarseCrossingCentre a h w I m (ν.val + 1)
  gridCrossingTrial a G K w I l m centre ∩ gridUpperCap (gridCrossingBlock a w I l m centre) w

/-- At a coarse scale at least one fixed capped trial succeeds. At a fine
scale the cell condition is the whole space
(Appendix B, Remark `rk:good-general` and item `ch:prob`). -/
noncomputable def generalGridCellGood (a G K cstar : ℝ) (I h : ℤ) (l j w : ℕ) :
    Set Environment :=
  if 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ) then
    ⋃ ν : Fin (j ^ 2), gridCappedTrial a G K I h l ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊ j w ν
  else univ

/-- The cell conditions at all scales, levels and bins in the grid
(Appendix B, equations `eq:Gdef` and item `ch:prob`). -/
def generalGridCellsGood (a G K cstar A R : ℝ) (k J mk : ℕ) : Set Environment :=
  {ω | ∀ j : ℕ, J ≤ j → j ≤ ⌈((mk : ℝ) - 1) / 4⌉₊ →
    ∀ I : ℤ, ((2 ^ (mk - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ mk →
    ∀ h : ℤ, (∃ ρ : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ ρ ∧
      ρ < ((h : ℝ) + 1) * 2 ^ (k - j) ∧ |ρ| ≤ R * 2 ^ k) →
    ω ∈ generalGridCellGood a G K cstar I h (2 ^ (mk - 4 * j - 1)) j (2 ^ (k - j))}

/-- The region cap for `E_hv` and each block cap is measurable
(`differentiability_final_draft.tex`, Lemma `lem:stair-general`). -/
theorem measurableSet_gridUpperCap (Q : Set Lattice) (cap : ℝ) :
    MeasurableSet (gridUpperCap Q cap) := by
  have heq : gridUpperCap Q cap = ⋂ z : Q, {ω : Environment | ω z ≤ cap} := by
    ext ω
    simp only [gridUpperCap, mem_ofPred_eq, mem_iInter, Subtype.forall]
  rw [heq]
  exact MeasurableSet.iInter fun z => measurableSet_le (measurable_pi_apply z.val) measurable_const

/-- The translated crossing trial is measurable
(`differentiability_final_draft.tex`, `eq:crossblock` and `success55`). -/
theorem measurableSet_gridCrossingTrial (a G K w : ℝ) (I : ℤ) (l m : ℕ) (c : Lattice) :
    MeasurableSet (gridCrossingTrial a G K w I l m c) := by
  let index := {s : Σ u : Lattice, Σ d : ℕ × ℕ, Path u d |
    s.1.1 + s.1.2 = I + (m : ℤ) ∧ s.2.1.1 + s.2.1.2 = l - 2 * m ∧
    ∀ i, |(1 - a) * ((s.2.2.vertex i).1 : ℝ) - a * ((s.2.2.vertex i).2 : ℝ) -
      ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * w}
  have heq : gridCrossingTrial a G K w I l m c = ⋃ s : index,
      {ω : Environment | G * ((l - 2 * m : ℕ) : ℝ) - K * w < pathWeight ω s.val.2.2} := by
    ext ω
    simp only [gridCrossingTrial, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨u, d, x, hu, hd, hx, hw⟩
      exact ⟨⟨⟨u, d, x⟩, hu, hd, hx⟩, hw⟩
    · rintro ⟨⟨⟨u, d, x⟩, hu, hd, hx⟩, hw⟩
      exact ⟨u, d, x, hu, hd, hx, hw⟩
  rw [heq]
  exact MeasurableSet.iUnion fun s => measurableSet_lt measurable_const (measurable_pathWeight s.val.2.2)

/-- Each capped crossing trial is measurable
(`differentiability_final_draft.tex`, `eq:heavy-cross`). -/
theorem measurableSet_gridCappedTrial (a G K : ℝ) (I h : ℤ) (l m j w : ℕ)
    (ν : Fin (j ^ 2)) : MeasurableSet (gridCappedTrial a G K I h l m j w ν) := by
  unfold gridCappedTrial
  exact (measurableSet_gridCrossingTrial a G K w I l m _).inter (measurableSet_gridUpperCap _ w)

/-- The general-weight good event at each grid cell is measurable
(Appendix B item `ch:prob`). -/
theorem measurableSet_generalGridCellGood (a G K cstar : ℝ) (I h : ℤ) (l j w : ℕ) :
    MeasurableSet (generalGridCellGood a G K cstar I h l j w) := by
  unfold generalGridCellGood
  split_ifs
  · exact MeasurableSet.iUnion fun ν => measurableSet_gridCappedTrial a G K I h l _ j w ν
  · exact MeasurableSet.univ

/-- The intersection of the general-weight cell conditions is measurable
(Appendix B, equations `eq:Gdef` and item `ch:prob`). -/
theorem measurableSet_generalGridCellsGood (a G K cstar A R : ℝ) (k J mk : ℕ) :
    MeasurableSet (generalGridCellsGood a G K cstar A R k J mk) := by
  classical
  let scales := {j : ℕ // J ≤ j ∧ j ≤ ⌈((mk : ℝ) - 1) / 4⌉₊}
  let levels (j : scales) := {I : ℤ // ((2 ^ (mk - 4 * j.val - 1) : ℕ) : ℤ) ∣ I ∧
    |(I : ℝ)| ≤ (A + 4) * 2 ^ mk}
  let bins (j : scales) := {h : ℤ // ∃ ρ : ℝ, (h : ℝ) * 2 ^ (k - j.val) ≤ ρ ∧
    ρ < ((h : ℝ) + 1) * 2 ^ (k - j.val) ∧ |ρ| ≤ R * 2 ^ k}
  have heq : generalGridCellsGood a G K cstar A R k J mk =
      ⋂ j : scales, ⋂ I : levels j, ⋂ h : bins j,
        generalGridCellGood a G K cstar I.val h.val (2 ^ (mk - 4 * j.val - 1))
          j.val (2 ^ (k - j.val)) := by
    ext ω
    simp only [generalGridCellsGood, mem_ofPred_eq, mem_iInter]
    constructor
    · intro hω j I h
      exact hω j.val j.property.1 j.property.2 I.val I.property.1 I.property.2 h.val h.property
    · intro hω j hj hj' I hI hI' h hh
      exact hω ⟨j, hj, hj'⟩ ⟨I, hI, hI'⟩ ⟨h, hh⟩
  rw [heq]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun I =>
    MeasurableSet.iInter fun h => measurableSet_generalGridCellGood a G K cstar I.val h.val _ _ _

end LPPDifferentiability
