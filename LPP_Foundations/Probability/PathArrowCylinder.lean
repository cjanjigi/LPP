/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.StepCode
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ProductMeasure
import LPP_Foundations.Model.Paths.Geometry
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-! The probability that one sitewise uniform arrow field follows a fixed actual path. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

namespace LPPDifferentiability

/-- A common sitewise continuous-uniform arrow field follows a prescribed actual
path with probability equal to the product of its east thresholds and north
complements. This is the cylinder calculation for JR1810.03580v3, Appendix A.1;
it does not assert a Gibbs or Markov law. -/
theorem uniform_arrow_path_cylinder (a : Lattice → unitInterval) (x : Lattice)
    (d : ℕ × ℕ) (p : Path x d) :
    let Q : Measure (Lattice → unitInterval) :=
      Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
    let A : (Lattice → unitInterval) → Lattice → Lattice := fun θ y =>
      if θ y < a y then y + (1, 0) else y + (0, 1)
    let Gamma : Set (Lattice → unitInterval) :=
      {θ | ∀ j : Fin (d.1 + d.2 + 1), ((A θ)^[j.val]) x = p.vertex j}
    MeasurableSet Gamma ∧ Q Gamma = ENNReal.ofReal
      (∏ j : Fin (d.1 + d.2), if stepCode p j then
        ((a (p.vertex j.castSucc)) : ℝ) else 1 - ((a (p.vertex j.castSucc)) : ℝ)) := by
  classical
  let Q : Measure (Lattice → unitInterval) :=
    Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
  let A : (Lattice → unitInterval) → Lattice → Lattice := fun θ y =>
    if θ y < a y then y + (1, 0) else y + (0, 1)
  let Gamma : Set (Lattice → unitInterval) :=
    {θ | ∀ j : Fin (d.1 + d.2 + 1), ((A θ)^[j.val]) x = p.vertex j}
  change MeasurableSet Gamma ∧ Q Gamma = _
  let S : Fin (d.1 + d.2) → Set unitInterval := fun j =>
    if stepCode p j = true then Set.Iio (a (p.vertex j.castSucc))
    else Set.Ici (a (p.vertex j.castSucc))
  let C : Set (Lattice → unitInterval) :=
    ⋂ j : Fin (d.1 + d.2), (fun θ => θ (p.vertex j.castSucc)) ⁻¹' S j

  -- At a prescribed departure, the actual step code gives precisely the arrow condition.
  have hlocal (j : Fin (d.1 + d.2)) (θ : Lattice → unitInterval) :
      θ (p.vertex j.castSucc) ∈ S j ↔ A θ (p.vertex j.castSucc) = p.vertex j.succ := by
    by_cases hc : stepCode p j = true
    · have he : p.vertex j.succ = p.vertex j.castSucc + (1, 0) :=
        of_decide_eq_true hc
      simp only [S, hc, ite_true, Set.mem_Iio, A]
      rw [he]
      constructor
      · intro ht
        rw [ite_eq_left ht]
      · intro harrow
        by_contra ht
        rw [ite_eq_right ht] at harrow
        have hcoord := congrArg Prod.fst harrow
        change (p.vertex j.castSucc).1 + 0 = (p.vertex j.castSucc).1 + 1 at hcoord
        omega
    · have he : ¬ p.vertex j.succ = p.vertex j.castSucc + (1, 0) := by
        intro he
        exact hc (decide_eq_true he)
      have hn := (p.step j).resolve_left he
      dsimp only [S]
      rw [ite_eq_right hc]
      change a (p.vertex j.castSucc) ≤ θ (p.vertex j.castSucc) ↔ _
      dsimp only [A]
      rw [hn]
      constructor
      · intro ht
        rw [ite_eq_right (not_lt.mpr ht)]
      · intro harrow
        by_contra ht
        rw [ite_eq_left (lt_of_not_ge ht)] at harrow
        have hcoord := congrArg Prod.fst harrow
        change (p.vertex j.castSucc).1 + 1 = (p.vertex j.castSucc).1 + 0 at hcoord
        omega

  -- Full orbit agreement is equivalent to the intersection of those fixed coordinate events.
  have hGamma : Gamma = C := by
    ext θ
    change (∀ j : Fin (d.1 + d.2 + 1), ((A θ)^[j.val]) x = p.vertex j) ↔ _
    simp only [C, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro horbit j
      apply (hlocal j θ).2
      rw [← horbit j.castSucc, ← horbit j.succ]
      exact (Function.iterate_succ_apply' (A θ) j.val x).symm
    · intro hcoords i
      induction i using Fin.induction with
      | zero => simpa only [Fin.val_zero, Function.iterate_zero, id_eq] using p.start.symm
      | succ j ih =>
          rw [Fin.val_succ, Function.iterate_succ_apply']
          have ih' : ((A θ)^[j.val]) x = p.vertex j.castSucc := ih
          rw [ih']
          exact (hlocal j θ).1 (hcoords j)

  have hS (j : Fin (d.1 + d.2)) : MeasurableSet (S j) := by
    dsimp only [S]
    split_ifs
    · exact measurableSet_Iio
    · exact measurableSet_Ici
  have hC : MeasurableSet C := by
    exact MeasurableSet.iInter (fun j => (hS j).preimage (measurable_pi_apply _))

  -- Fixed actual departure sites are distinct, so the product coordinates remain independent.
  have hinj : Function.Injective (fun j : Fin (d.1 + d.2) => p.vertex j.castSucc) := by
    intro i j hij
    have hcast := p.vertex_injective hij
    apply Fin.ext
    exact congrArg (fun t : Fin (d.1 + d.2 + 1) => t.val) hcast
  have hbase : iIndepFun (fun (y : Lattice) (θ : Lattice → unitInterval) => θ y) Q :=
    iIndepFun_infinitePi (X := fun (_ : Lattice) (u : unitInterval) => u)
      (fun _ => measurable_id)
  have hind : iIndepFun
      (fun (j : Fin (d.1 + d.2)) (θ : Lattice → unitInterval) => θ (p.vertex j.castSucc)) Q :=
    iIndepFun.precomp hinj hbase
  have hproduct : Q C =
      ∏ j : Fin (d.1 + d.2), Q ((fun θ => θ (p.vertex j.castSucc)) ⁻¹' S j) := by
    simpa only [C, Finset.mem_univ, Set.iInter_true] using
      hind.measure_inter_preimage_eq_mul Finset.univ (fun j _ => hS j)

  -- Each selected coordinate has genuine continuous-uniform interval mass.
  have hmass (j : Fin (d.1 + d.2)) :
      Q ((fun θ => θ (p.vertex j.castSucc)) ⁻¹' S j) =
        ENNReal.ofReal (if stepCode p j then
          ((a (p.vertex j.castSucc)) : ℝ) else 1 - ((a (p.vertex j.castSucc)) : ℝ)) := by
    have hmap : Q.map (fun θ => θ (p.vertex j.castSucc)) = (volume : Measure unitInterval) :=
      Measure.infinitePi_map_eval (fun _ : Lattice => (volume : Measure unitInterval))
        (p.vertex j.castSucc)
    calc
      _ = (volume : Measure unitInterval) (S j) := by
        rw [← hmap]
        exact (Measure.map_apply (measurable_pi_apply (p.vertex j.castSucc)) (hS j)).symm
      _ = _ := by
        by_cases hc : stepCode p j = true
        · simp [S, hc, unitInterval.volume_Iio]
        · simp [S, hc, unitInterval.volume_Ici]
  have hnonneg (j : Fin (d.1 + d.2)) :
      0 ≤ if stepCode p j then ((a (p.vertex j.castSucc)) : ℝ)
        else 1 - ((a (p.vertex j.castSucc)) : ℝ) := by
    split_ifs
    · exact (a (p.vertex j.castSucc)).property.1
    · exact sub_nonneg.mpr (a (p.vertex j.castSucc)).property.2
  constructor
  · rw [hGamma]
    exact hC
  · rw [hGamma, hproduct]
    simp_rw [hmass]
    exact (ENNReal.ofReal_prod_of_nonneg (fun j _ => hnonneg j)).symm

end LPPDifferentiability
