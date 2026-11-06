/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.ExcessBlockResidues
public import LPP_Foundations.Probability.Stationarity
import Mathlib.Tactic

/-!
# Excess sums over finite boxes

This file shows that the excess sum over a finite box is measurable, that translating the box
does not change the law of this sum, and that the sums over the boxes of one residue class are
mutually independent.
-/

public section
open MeasureTheory ProbabilityTheory
namespace LPPDifferentiability

/-- A finite sum of coordinate excesses is measurable. -/
theorem measurable_excess_box_sum (Q : Finset Lattice) (M : ℝ) :
    Measurable (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0) := by
  exact Finset.measurable_sum Q (fun z _ =>
    ((measurable_environment_eval z).sub_const M).max measurable_const)

/-- Translating the finite box `Q` by `v` does not change the law of its excess sum. -/
theorem excess_box_sum_map_translation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Q : Finset Lattice) (M : ℝ) (v : Lattice) :
    (environmentLaw μ).map (fun ω : Environment =>
      ∑ z ∈ Q.map ⟨fun w => v+w, fun _ _ h => add_left_cancel h⟩,
        max (ω z-M) 0) =
      (environmentLaw μ).map (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0) := by
  classical
  simp only [Finset.sum_map]
  change (environmentLaw μ).map (fun ω : Environment => ∑ z ∈ Q, max (ω (v+z)-M) 0) = _
  have heq : (fun ω : Environment => ∑ z ∈ Q, max (ω (v+z)-M) 0) =
      (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0) ∘
        (fun ω : Environment => fun z => ω (v+z)) := rfl
  rw [heq, ← Measure.map_map (measurable_excess_box_sum Q M)
    (measurable_pi_iff.mpr fun z => measurable_environment_eval (v+z)),
    environmentLaw_map_translation]

/-- For one residue class (fixed `α` and `β`), the excess sums over the translated boxes
are mutually independent. -/
theorem iIndepFun_excess_residue_sums (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a s M : ℝ) (m : ℕ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1)
    (hs : 3 ≤ s) (hm : 1 ≤ m) (α : Fin 4) (β : Fin 10) :
    let v : ℤ × ℤ → Lattice := fun d =>
      let p := 4*d.1+(α.val:ℤ)
      let h := 10*d.2+(β.val:ℤ)
      let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
      (j,p*m-j)
    iIndepFun (fun d (ω : Environment) =>
      ∑ z ∈ Q.map ⟨fun w => v d+w, fun _ _ h => add_left_cancel h⟩,
        max (ω z-M) 0) (environmentLaw μ) := by
  classical
  let v : ℤ × ℤ → Lattice := fun d =>
    let p := 4*d.1+(α.val:ℤ)
    let h := 10*d.2+(β.val:ℤ)
    let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
    (j,p*m-j)
  change iIndepFun (fun d (ω : Environment) =>
    ∑ z ∈ Q.map ⟨fun w => v d+w, fun _ _ h => add_left_cancel h⟩,
      max (ω z-M) 0) (environmentLaw μ)
  have hdis := excess_residue_boxes_pairwise a s m Q hQ hs hm α β
  let f : (ℤ × ℤ) × {z : Lattice // z ∈ Q} → Lattice := fun t => v t.1+t.2.val
  have hf : Function.Injective f := by
    rintro ⟨i,q⟩ ⟨j,r⟩ heq
    by_cases hij : i=j
    · subst j
      have hqr : q=r := Subtype.ext (add_left_cancel heq)
      subst r
      rfl
    · exfalso
      apply Finset.disjoint_left.mp (hdis hij)
      · exact Finset.mem_map.mpr ⟨q.val,q.property,rfl⟩
      · exact Finset.mem_map.mpr ⟨r.val,r.property,heq.symm⟩
  have hflat : (environmentLaw μ).map (fun ω : Environment => fun t => ω (f t)) =
      Measure.infinitePi (fun _ : (ℤ × ℤ) × {z : Lattice // z ∈ Q} => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Lattice => μ) hf
  have hblocks : (environmentLaw μ).map
      (fun ω : Environment => fun i : ℤ × ℤ => fun q : {z : Lattice // z ∈ Q} =>
        ω (v i+q.val)) =
      Measure.infinitePi (fun _ : ℤ × ℤ =>
        Measure.infinitePi (fun _ : {z : Lattice // z ∈ Q} => μ)) := by
    calc
      _ = ((environmentLaw μ).map (fun ω : Environment => fun t => ω (f t))).map
          (MeasurableEquiv.curry (ℤ × ℤ) {z : Lattice // z ∈ Q} ℝ) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = _ := by
        rw [hflat]
        exact Measure.infinitePi_map_curry (fun _ _ => μ)
  have hmargin (i : ℤ × ℤ) : (environmentLaw μ).map
      (fun ω : Environment => fun q : {z : Lattice // z ∈ Q} => ω (v i+q.val)) =
      Measure.infinitePi (fun _ : {z : Lattice // z ∈ Q} => μ) := by
    apply Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Lattice => μ)
    intro q r h
    exact Subtype.ext (add_left_cancel h)
  have hi : iIndepFun (fun i (ω : Environment) =>
      fun q : {z : Lattice // z ∈ Q} => ω (v i+q.val)) (environmentLaw μ) := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop),hblocks]
    simp_rw [hmargin]
  have hsum : Measurable (fun x : {z : Lattice // z ∈ Q} → ℝ =>
      ∑ q, max (x q-M) 0) := by
    apply Finset.measurable_sum
    intro q _
    have hq : Measurable (fun x : {z : Lattice // z ∈ Q} → ℝ => x q) := measurable_pi_apply q
    exact (hq.sub measurable_const).max measurable_const
  have hcomp := hi.comp (fun _ => fun x : {z : Lattice // z ∈ Q} → ℝ =>
    ∑ q, max (x q-M) 0) (fun _ => hsum)
  simp only [Finset.sum_map]
  change iIndepFun (fun d (ω : Environment) => ∑ z ∈ Q, max (ω (v d+z)-M) 0) (environmentLaw μ)
  change iIndepFun (fun i (ω : Environment) => ∑ q : {z : Lattice // z ∈ Q}, max (ω (v i+q.val)-M) 0) (environmentLaw μ) at hcomp
  have heq : (fun i (ω : Environment) => ∑ q : {z : Lattice // z ∈ Q}, max (ω (v i+q.val)-M) 0) =
      (fun i (ω : Environment) => ∑ z ∈ Q, max (ω (v i+z)-M) 0) := by
    funext i ω
    exact Finset.sum_coe_sort Q (fun z => max (ω (v i+z)-M) 0)
  rw [heq] at hcomp
  exact hcomp

/-- There is a finite box `Q` with the two cardinality bounds, such that every translate of `Q`
has the same excess-sum law as `Q`, and the sums over the boxes of each of the forty residue
classes are mutually independent. -/
theorem exists_excess_block_iid_classes (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a s M : ℝ) (m : ℕ) (hs : 3 ≤ s) (hm : 1 ≤ m) (hms : (m:ℝ) ≤ s^3) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
        |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1) ∧
      (Q.card:ℝ) ≤ (3*(m:ℝ)+1)*(8*s+3) ∧
      (3*(m:ℝ)+1)*(8*s+3) ≤ 44*s^4 ∧
      (∀ b : ℤ × ℤ,
        let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
        let v : Lattice := (j,b.1*m-j)
        let B := Q.map ⟨fun w => v+w, fun _ _ h => add_left_cancel h⟩
        Measurable (fun ω : Environment => ∑ z ∈ B, max (ω z-M) 0) ∧
        (environmentLaw μ).map (fun ω : Environment => ∑ z ∈ B, max (ω z-M) 0) =
          (environmentLaw μ).map (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0)) ∧
      (∀ (α : Fin 4) (β : Fin 10),
        let v : ℤ × ℤ → Lattice := fun d =>
          let p := 4*d.1+(α.val:ℤ)
          let h := 10*d.2+(β.val:ℤ)
          let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
          (j,p*m-j)
        iIndepFun (fun d (ω : Environment) =>
          ∑ z ∈ Q.map ⟨fun w => v d+w, fun _ _ h => add_left_cancel h⟩,
            max (ω z-M) 0) (environmentLaw μ)) := by
  obtain ⟨Q,hQ,hcard,hbound⟩ := exists_excess_block_base a s m hs hms
  refine ⟨Q,hQ,hcard,hbound,?_,?_⟩
  · intro b
    exact ⟨measurable_excess_box_sum _ M,excess_box_sum_map_translation μ Q M _⟩
  · intro α β
    exact iIndepFun_excess_residue_sums μ a s M m Q hQ hs hm α β

end LPPDifferentiability
end
