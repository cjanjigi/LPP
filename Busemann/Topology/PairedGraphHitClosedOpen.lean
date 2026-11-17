/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Topology.PairedGraphHitMeasurability

/-! A closed set restricted to an open part of the ordered-pair graph still
has a Borel hit event, by writing the open part as a countable union of closed
sets. -/

@[expose] public section
open MeasureTheory
namespace LPP.Busemann

/-- The ordered-pair graph hitting a closed set inside an open set is Borel.
This extends the countable closed-hit result in
`Busemann/Topology/PairedGraphHitMeasurability.lean:60`. -/
theorem measurableSet_pairedPathOrderGraph_hit_closed_inter_open
    (S : Set ℝ) (J : Type*) [Countable J]
    (F O : Set (SqueezedState J × SqueezedState J))
    (hF : IsClosed F) (hO : IsOpen O) :
    MeasurableSet {f : PairedSkorokhodPath S J |
      (pairedPathOrderGraph S J f ∩ (F ∩ O)).Nonempty} := by
  classical
  -- Countably many state coordinates give a pseudometric on the actual pair space.
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

  -- Pseudometrizability makes the pair space perfectly normal, so Oᶜ is Gδ.
  have hOcomplementClosed : IsClosed (Oᶜ) := hO.isClosed_compl
  have hOcomplementGDelta : IsGδ (Oᶜ) := hOcomplementClosed.isGδ
  obtain ⟨U, hUopen, hOcomplementEq⟩ := hOcomplementGDelta.eq_iInter_nat
  have hOeq : O = ⋃ n, (U n)ᶜ := by
    calc
      O = (Oᶜ)ᶜ := by simp
      _ = (⋂ n, U n)ᶜ := by rw [hOcomplementEq]
      _ = ⋃ n, (U n)ᶜ := Set.compl_iInter U

  -- Intersecting each closed complement with F gives closed terms for F ∩ O.
  have hFOisFsigma :
      ∃ G : ℕ → Set (SqueezedState J × SqueezedState J),
        (∀ n, IsClosed (G n)) ∧ F ∩ O = ⋃ n, G n := by
    refine ⟨fun n => F ∩ (U n)ᶜ, ?_, ?_⟩
    · intro n
      exact hF.inter (hUopen n).isClosed_compl
    · rw [hOeq, Set.inter_iUnion]

  -- The existing Fσ result applies to the same graph and Borel carrier.
  exact measurableSet_pairedPathOrderGraph_hit_fsigma S J (F ∩ O) hFOisFsigma

end LPP.Busemann
