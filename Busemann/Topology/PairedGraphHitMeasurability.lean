/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.PairedSkorokhodPathBorelSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Measurability of graph-hit events in the paired-path topology. -/

@[expose] public section
open MeasureTheory
open scoped Topology
namespace LPP.Busemann

/-- A closed set is hit on a Borel event for the ordered-pair graph topology. -/
private theorem measurableSet_pairedPathOrderGraph_hit_closed
    (S : Set ℝ) (J : Type*) (F : Set (SqueezedState J × SqueezedState J))
    (hF : IsClosed F) :
    MeasurableSet {f : PairedSkorokhodPath S J |
      (pairedPathOrderGraph S J f ∩ F).Nonempty} := by
  classical
  -- The graph-contained-in-the-open-complement condition is an upper generator.
  have hUpperGenerator :
      {f : PairedSkorokhodPath S J |
        pairedPathOrderGraph S J f ⊆ Fᶜ} ∈ pairedGraphVietorisGenerators S J := by
    unfold pairedGraphVietorisGenerators
    apply Set.mem_union_left
    exact ⟨Fᶜ, hF.isOpen_compl, rfl⟩
  -- A generator is open in the topology it generates.
  have hUpperOpen : IsOpen {f : PairedSkorokhodPath S J |
      pairedPathOrderGraph S J f ⊆ Fᶜ} := by
    change IsOpen[TopologicalSpace.generateFrom (pairedGraphVietorisGenerators S J)] _
    exact TopologicalSpace.isOpen_generateFrom_of_mem hUpperGenerator
  -- Open sets are Borel in the paired path Borel space.
  have hUpperMeasurable : MeasurableSet {f : PairedSkorokhodPath S J |
      pairedPathOrderGraph S J f ⊆ Fᶜ} := hUpperOpen.measurableSet
  -- The complement of the upper condition says exactly that the graph hits F.
  have hHitEq :
      {f : PairedSkorokhodPath S J |
        (pairedPathOrderGraph S J f ∩ F).Nonempty} =
      {f : PairedSkorokhodPath S J |
        pairedPathOrderGraph S J f ⊆ Fᶜ}ᶜ := by
    ext f
    change (pairedPathOrderGraph S J f ∩ F).Nonempty ↔
      ¬ pairedPathOrderGraph S J f ⊆ Fᶜ
    constructor
    · rintro ⟨x, hxGraph, hxF⟩ hSubset
      have hxNotF : x ∉ F := (Set.mem_compl_iff F x).mp (hSubset hxGraph)
      exact hxNotF hxF
    · intro hNotSubset
      obtain ⟨x, hxGraph, hxNotComplement⟩ := Set.not_subset.mp hNotSubset
      have hxF : x ∈ F := by
        by_contra hxNotF
        exact hxNotComplement ((Set.mem_compl_iff F x).mpr hxNotF)
      exact ⟨x, hxGraph, hxF⟩
  rw [hHitEq]
  exact hUpperMeasurable.compl

/-- Hitting a countable union of closed sets is Borel for the actual ordered-pair
graph topology. This formalizes the closed-hit step from the generators in
`Busemann/Frozen/StrongExistence/Definitions/PairedGraphVietorisGenerators.lean:11`. -/
theorem measurableSet_pairedPathOrderGraph_hit_fsigma
    (S : Set ℝ) (J : Type*)
    (B : Set (SqueezedState J × SqueezedState J))
    (hB : ∃ F : ℕ → Set (SqueezedState J × SqueezedState J),
      (∀ n, IsClosed (F n)) ∧ B = ⋃ n, F n) :
    MeasurableSet {f : PairedSkorokhodPath S J |
      (pairedPathOrderGraph S J f ∩ B).Nonempty} := by
  classical
  obtain ⟨F, hClosed, hB_eq⟩ := hB
  rw [hB_eq]
  -- A graph hits a countable union exactly when it hits one term.
  have hEventEq :
      {f : PairedSkorokhodPath S J |
        (pairedPathOrderGraph S J f ∩ (⋃ n, F n)).Nonempty} =
      ⋃ n, {f : PairedSkorokhodPath S J |
        (pairedPathOrderGraph S J f ∩ F n).Nonempty} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hxGraph, hxUnion⟩
      obtain ⟨n, hxTerm⟩ := Set.mem_iUnion.mp hxUnion
      exact ⟨n, x, hxGraph, hxTerm⟩
    · rintro ⟨n, x, hxGraph, hxTerm⟩
      exact ⟨x, hxGraph, Set.mem_iUnion.mpr ⟨n, hxTerm⟩⟩
  rw [hEventEq]
  -- Each closed hit is Borel, so their countable union is Borel.
  exact MeasurableSet.iUnion fun n =>
    measurableSet_pairedPathOrderGraph_hit_closed S J (F n) (hClosed n)

end LPP.Busemann
