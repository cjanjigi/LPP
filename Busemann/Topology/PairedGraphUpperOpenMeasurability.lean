/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Topology.ClosedInnerExhaustion
public import Busemann.Topology.PairedGraphOpenHitMeasurability

/-! Measurability of upper containment for the literal paired order graph. -/

@[expose] public section
open MeasureTheory
namespace LPP.Busemann

/-- Containment of the literal compact ordered graph in an open set is
measurable under the selected sampled-evaluation sigma algebra. -/
theorem measurableSet_pairedPathOrderGraph_subset_open_of_sidedSamples
    (S : Set ℝ) (J : Type*) [Countable J] (hS : IsClosed S)
    (D : Set {v : ℝ // v ∈ S}) (hD : D.Countable)
    (hside : ∀ t : {v : ℝ // v ∈ S}, t ∉ D →
      t ∈ closure (D ∩ Set.Iio t) ∧
      t ∈ closure (D ∩ Set.Ioi t))
    (U : Set (SqueezedState J × SqueezedState J)) (hU : IsOpen U) :
    @MeasurableSet (PairedSkorokhodPath S J)
      (MeasurableSpace.generateFrom
        {A : Set (PairedSkorokhodPath S J) |
          ∃ s : {v : ℝ // v ∈ S}, s ∈ D ∧
            ∃ j : J, ∃ V : Set ℝ, IsOpen V ∧
              (A = {f | evalMinus f s j ∈ V} ∨
               A = {f | evalPlus f s j ∈ V})})
      {f : PairedSkorokhodPath S J |
        pairedPathOrderGraph S J f ⊆ U} := by
  classical
  have _hS : IsClosed S := hS

  -- This is the exact sampled-evaluation sigma in the parent theorem.
  let : MeasurableSpace (PairedSkorokhodPath S J) :=
    MeasurableSpace.generateFrom
      {A : Set (PairedSkorokhodPath S J) |
        ∃ s : {v : ℝ // v ∈ S}, s ∈ D ∧
          ∃ j : J, ∃ V : Set ℝ, IsOpen V ∧
            (A = {f | evalMinus f s j ∈ V} ∨
             A = {f | evalPlus f s j ∈ V})}

  -- Countable J gives a pseudometric on the actual state-pair space.
  have hPseudoJ : TopologicalSpace.PseudoMetrizableSpace (J → ℝ) := inferInstance
  have hPseudoReal : TopologicalSpace.PseudoMetrizableSpace ℝ := inferInstance
  have hPseudoAmbient : TopologicalSpace.PseudoMetrizableSpace (ℝ × (J → ℝ)) :=
    @TopologicalSpace.pseudoMetrizableSpace_prod ℝ (J → ℝ)
      inferInstance inferInstance hPseudoReal hPseudoJ
  have hInducing : Topology.IsInducing (squeezedStateEmbedding J) :=
    Topology.IsInducing.induced (squeezedStateEmbedding J)
  have hPseudoState : TopologicalSpace.PseudoMetrizableSpace (SqueezedState J) :=
    @Topology.IsInducing.pseudoMetrizableSpace
      (SqueezedState J) (ℝ × (J → ℝ)) inferInstance inferInstance hPseudoAmbient
      (squeezedStateEmbedding J) hInducing
  have hPseudoPair :
      TopologicalSpace.PseudoMetrizableSpace (SqueezedState J × SqueezedState J) :=
    @TopologicalSpace.pseudoMetrizableSpace_prod (SqueezedState J) (SqueezedState J)
      inferInstance inferInstance hPseudoState hPseudoState
  let : TopologicalSpace.PseudoMetrizableSpace
      (SqueezedState J × SqueezedState J) := hPseudoPair

  -- Fix the exhaustion for U before considering any path.
  obtain ⟨F, hFclosed, hFsubset, _, _, hCompactCapture⟩ :=
    exists_closed_inner_exhaustion_of_isOpen hU

  have hGraphCompact (f : PairedSkorokhodPath S J) :
      IsCompact (pairedPathOrderGraph S J f) := f.2

  have hGraphSubsetIff (f : PairedSkorokhodPath S J) :
      pairedPathOrderGraph S J f ⊆ U ↔
        ∃ n, pairedPathOrderGraph S J f ⊆ F n := by
    constructor
    · intro hGraphSubsetU
      exact hCompactCapture _ (hGraphCompact f) hGraphSubsetU
    · rintro ⟨n, hGraphSubsetFn⟩
      exact hGraphSubsetFn.trans (hFsubset n)

  have hSubsetFnEventEq (n : ℕ) :
      {f : PairedSkorokhodPath S J | pairedPathOrderGraph S J f ⊆ F n} =
        {f : PairedSkorokhodPath S J |
          (pairedPathOrderGraph S J f ∩ (F n)ᶜ).Nonempty}ᶜ := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · intro hSubset hHit
      rcases hHit with ⟨z, hzGraph, hzComplement⟩
      exact hzComplement (hSubset hzGraph)
    · intro hNoHit z hzGraph
      by_contra hzNotFn
      exact hNoHit ⟨z, hzGraph, hzNotFn⟩

  have hSubsetFnMeasurable (n : ℕ) :
      MeasurableSet
        {f : PairedSkorokhodPath S J | pairedPathOrderGraph S J f ⊆ F n} := by
    rw [hSubsetFnEventEq n]
    have hComplementOpen : IsOpen ((F n)ᶜ) := (hFclosed n).isOpen_compl
    have hComplementHitMeasurable :
        MeasurableSet
          {f : PairedSkorokhodPath S J |
            (pairedPathOrderGraph S J f ∩ (F n)ᶜ).Nonempty} :=
      measurableSet_pairedPathOrderGraph_hit_open_of_sidedSamples
        S J hS D hD hside (F n)ᶜ hComplementOpen
    exact hComplementHitMeasurable.compl

  have hUpperUnion :
      {f : PairedSkorokhodPath S J | pairedPathOrderGraph S J f ⊆ U} =
        ⋃ n, {f : PairedSkorokhodPath S J |
          pairedPathOrderGraph S J f ⊆ F n} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact hGraphSubsetIff f

  rw [hUpperUnion]
  exact MeasurableSet.iUnion hSubsetFnMeasurable

end LPP.Busemann
