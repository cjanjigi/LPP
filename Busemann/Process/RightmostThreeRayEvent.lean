/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.RightmostCocyclePath
public import Mathlib.Dynamics.Ergodic.Conservative
import Busemann.Process.RightmostPathCovariance
import Busemann.Process.RightmostPathInterlacing
import Lean.Elab.Tactic.Omega

/-! Stationary recurrence produces the actual three-ray event of Appendix A. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability

namespace LPP.Busemann

/-- Recurrence of a positive normalized pair event produces three actual
rightmost rays, retaining both occurrences of the original event. Covariance
is required only almost surely; the output event removes its exceptional set.
Georgiou, Rassoul-Agha, and Seppäläinen, arXiv:1510.00860v1, Appendix A,
lines 1534–1551. -/
theorem exists_positive_three_ray_event_of_recurrence
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hZero : ∀ ω : Ω, T 0 ω = ω)
    (hAdd : ∀ z w : Lattice, ∀ ω : Ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (m : ℕ) (hm : 0 < m)
    (A : Set Ω) (hA : MeasurableSet A) (hPositive : 0 < P A)
    (hDisjoint : ∀ ω ∈ A, ∀ r s : ℕ,
      rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
        rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s)
    (hEastZero : ∀ ω ∈ A,
      rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0))
    (hEastM : ∀ ω ∈ A,
      rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
        (1, (m : ℤ))) :
    ∃ i : ℕ, m < i ∧ ∃ E : Set Ω,
      MeasurableSet E ∧ 0 < P E ∧
      E ⊆ A ∩ (T (0, (i : ℤ))) ⁻¹' A ∧
      ∀ ω ∈ E,
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
            rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) r ≠
            rightmostCocyclePath (fun x y => B x y ω)
              (0, ((i + m : ℕ) : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω)
          (0, ((i + m : ℕ) : ℤ)) = (1, ((i + m : ℕ) : ℤ)) := by
  -- Coordinate sections come from the cocycle's joint measurability.
  have hMeas (x y : Lattice) : Measurable (B x y) := by
    have hSection : Measurable (fun ω : Ω => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.comp hSection

  -- The one-step north shift iterates to the literal lattice action.
  have hIterate (n : ℕ) (ω : Ω) :
      (T (0, 1))^[n] ω = T (0, (n : ℤ)) ω := by
    induction n with
    | zero =>
        have hOrigin : ((0, 0) : Lattice) = (0 : Lattice) := by
          apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero]
        simpa only [Function.iterate_zero_apply, Nat.cast_zero, hOrigin] using (hZero ω).symm
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        have hVector : ((0, ((n + 1 : ℕ) : ℤ)) : Lattice) =
            (0, 1) + (0, (n : ℤ)) := by
          apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add,
            Nat.cast_one] <;> omega
        rw [hVector, hAdd]

  -- Finite-measure recurrence needs preservation, not ergodicity.
  obtain ⟨i, hmi, hOverlap⟩ :=
    (hShift (0, 1)).conservative.exists_gt_measure_inter_ne_zero
      hA.nullMeasurableSet (ne_of_gt hPositive) m
  have hIterateFun : (T (0, 1))^[i] = T (0, (i : ℤ)) :=
    funext (hIterate i)
  rw [hIterateFun] at hOverlap
  let z : Lattice := (0, (i : ℤ))
  let F : Set Ω := A ∩ (T z) ⁻¹' A
  have hFMeas : MeasurableSet F := hA.inter (hA.preimage (hShift z).measurable)
  have hFPositive : 0 < P F := bot_lt_iff_ne_bot.mpr hOverlap

  -- A countable intersection makes covariance pointwise on one measurable full set.
  let G : Set Ω := {ω | ∀ x y : Lattice,
    B (x + z) (y + z) ω = B x y (T z ω)}
  have hGMeas : MeasurableSet G := by
    simp only [G, Set.ofPred_forall]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      measurableSet_eq_fun (hMeas (x + z) (y + z))
        ((hMeas x y).comp (hShift z).measurable)
  have hGAE : ∀ᵐ ω ∂P, ω ∈ G :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr fun y => hB.2.1 x y z
  let E : Set Ω := G ∩ F
  have hEMeas : MeasurableSet E := hGMeas.inter hFMeas
  have hEPositive : 0 < P E := by
    have hMeasure : P E = P F := Measure.measure_inter_eq_of_ae hGAE
    rw [hMeasure]
    exact hFPositive

  refine ⟨i, hmi, E, hEMeas, hEPositive, ?_, ?_⟩
  · intro ω hω
    exact hω.2
  · intro ω hω
    have hOriginal : ω ∈ A := hω.2.1
    have hShifted : T z ω ∈ A := hω.2.2
    let C : Lattice → Lattice → ℝ := fun x y => B x y ω
    let D : Lattice → Lattice → ℝ := fun x y => B x y (T z ω)
    have hCov : ∀ x y : Lattice, D x y = C (x + z) (y + z) :=
      fun x y => (hω.1 x y).symm
    have hTranslate (x : Lattice) (n : ℕ) :
        rightmostCocyclePath D x n + z = rightmostCocyclePath C (x + z) n :=
      rightmostCocyclePath_translate C D z hCov x n
    have hStartM : ((0, (m : ℤ)) : Lattice) + z =
        (0, ((i + m : ℕ) : ℤ)) := by
      apply Prod.ext <;> simp only [z, Prod.fst_add, Prod.snd_add, Nat.cast_add] <;>
        omega

    -- The translated pair is disjoint at every pair of local times.
    have hUpperPair : ∀ r s : ℕ,
        rightmostCocyclePath C (0, (i : ℤ)) r ≠
          rightmostCocyclePath C (0, ((i + m : ℕ) : ℤ)) s := by
      intro r s hMeet
      apply hDisjoint (T z ω) hShifted r s
      have hLower : rightmostCocyclePath D 0 r + z =
          rightmostCocyclePath C (0, (i : ℤ)) r := by
        simpa only [zero_add] using hTranslate 0 r
      have hUpper : rightmostCocyclePath D (0, (m : ℤ)) s + z =
          rightmostCocyclePath C (0, ((i + m : ℕ) : ℤ)) s := by
        simpa only [hStartM] using hTranslate (0, (m : ℤ)) s
      exact add_right_cancel (hLower.trans (hMeet.trans hUpper.symm))
    have hMiddleUpper : ∀ r s : ℕ,
        rightmostCocyclePath C (0, (m : ℤ)) r ≠
          rightmostCocyclePath C (0, ((i + m : ℕ) : ℤ)) s :=
      rightmostCocyclePath_disjoint_lower_of_vertical_pair C m i (i + m)
        hmi (by omega) hUpperPair

    -- The shifted upper start keeps the actual east successor.
    have hEastUpper : rightmostCocycleSuccessor C
        (0, ((i + m : ℕ) : ℤ)) = (1, ((i + m : ℕ) : ℤ)) := by
      have hSuccessor := rightmostCocycleSuccessor_translate C D z hCov (0, (m : ℤ))
      have hEastD : rightmostCocycleSuccessor D (0, (m : ℤ)) = (1, (m : ℤ)) :=
        hEastM (T z ω) hShifted
      rw [hStartM, hEastD] at hSuccessor
      calc
        rightmostCocycleSuccessor C (0, ((i + m : ℕ) : ℤ)) =
            (1, (m : ℤ)) + z := hSuccessor.symm
        _ = (1, ((i + m : ℕ) : ℤ)) := by
          apply Prod.ext <;> simp only [z, Prod.fst_add, Prod.snd_add, Nat.cast_add] <;>
            omega
    exact ⟨hDisjoint ω hOriginal, hMiddleUpper, hEastZero ω hOriginal, hEastUpper⟩

end LPP.Busemann
