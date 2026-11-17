/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.ConditionalPositive
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! Conditional positivity for finite intersections of events. -/

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics

/-- Positive conditional expectations for all singleton events imply positive
conditional expectations for their finite intersections, with the conditioning
field decreasing as the finite set grows. This is the finite-block induction
used in GRS, arXiv:1510.00860v1, Appendix A, lines 1466–1468. -/
theorem ae_condExp_indicator_finset_pos
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure[mΩ] Ω) [IsFiniteMeasure P]
    (m : Finset ι → MeasurableSpace Ω)
    (hm : ∀ V, m V ≤ mΩ)
    (hmono : ∀ U V, U ⊆ V → m V ≤ m U)
    (E : ι → Set Ω)
    (hE : ∀ i, @MeasurableSet Ω mΩ (E i))
    (hOutside : ∀ i j, i ≠ j → @MeasurableSet Ω (m {i}) (E j))
    (hSingle : ∀ i, ∀ᵐ ω ∂P, 0 < (MeasureTheory.condExp (m {i}) P
      ((E i).indicator fun _ : Ω => (1 : ℝ))) ω) :
    ∀ V : Finset ι, ∀ᵐ ω ∂P,
      0 < (MeasureTheory.condExp (m V) P
        ((⋂ i ∈ V, E i).indicator fun _ : Ω => (1 : ℝ))) ω := by
  classical
  let : MeasurableSpace Ω := mΩ
  let good : Finset ι → Set Ω := fun V => ⋂ i ∈ V, E i

  -- Every finite intersection is measurable in the original ambient field.
  have hgood_ambient (V : Finset ι) : @MeasurableSet Ω mΩ (good V) := by
    exact Finset.measurableSet_biInter V (fun i _ => hE i)

  -- The event criterion turns each singleton hypothesis into an
  -- intersection statement for every event in its singleton field.
  have hsingle_criterion (i : ι) (H : Set Ω)
      (hH : MeasurableSet[m {i}] H) (hHpos : 0 < P H) :
      0 < P (E i ∩ H) :=
    (ae_condExp_indicator_pos_iff P (m {i}) (hm {i}) (E i) (hE i)).mp
      (hSingle i) H hH hHpos

  -- Prove the finite-intersection event criterion by induction on the block.
  have hgood_criterion : ∀ V : Finset ι, ∀ H : Set Ω,
      MeasurableSet[m V] H → 0 < P H → 0 < P (good V ∩ H) := by
    intro V
    induction V using Finset.induction_on with
    | empty =>
        intro H _hH hHpos
        simpa [good] using hHpos
    | @insert i V hi ih =>
        intro H hHinsert hHpos
        have hVsubset : V ⊆ insert i V := by
          intro j hj
          simp only [Finset.mem_insert]
          exact Or.inr hj
        have hSingletonSubset : ({i} : Finset ι) ⊆ insert i V := by
          intro j hj
          simp only [Finset.mem_singleton] at hj
          subst j
          exact Finset.mem_insert_self _ _

        -- Nesting makes the positive conditioning event measurable in each
        -- of the two smaller fields used at this induction step.
        have hH_V : MeasurableSet[m V] H :=
          hmono V (insert i V) hVsubset H hHinsert
        have hH_single : MeasurableSet[m {i}] H :=
          hmono {i} (insert i V) hSingletonSubset H hHinsert
        have hgoodV_pos : 0 < P (good V ∩ H) := ih H hH_V hHpos

        -- The old block event is measurable in the new singleton field by
        -- the off-diagonal assumptions.
        have hgoodV_single : @MeasurableSet Ω (m {i}) (good V) := by
          let : MeasurableSpace Ω := m {i}
          exact Finset.measurableSet_biInter V fun j hj =>
            hOutside i j (by
              intro hij
              subst j
              exact False.elim (hi hj))
        have hintersection_single :
            @MeasurableSet Ω (m {i}) (good V ∩ H) := by
          let : MeasurableSpace Ω := m {i}
          exact hgoodV_single.inter hH_single

        -- Apply singleton positivity to the old block intersected with H.
        have hinsert_pos : 0 < P (E i ∩ (good V ∩ H)) :=
          hsingle_criterion i (good V ∩ H) hintersection_single hgoodV_pos
        have hgood_insert : good (insert i V) = E i ∩ good V := by
          ext ω
          simp [good]
        simpa [hgood_insert, Set.inter_assoc] using hinsert_pos

  -- The criterion converts the event statement back to conditional
  -- positivity for each finite block.
  intro V
  have hpositive :=
    (ae_condExp_indicator_pos_iff P (m V) (hm V) (good V) (hgood_ambient V)).mpr
      (hgood_criterion V)
  simpa [good] using hpositive

end ProbabilityBasics
