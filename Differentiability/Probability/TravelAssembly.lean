/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.FloorSegmentShape
public import Differentiability.Model.Paths.FloorSegmentConcat
public import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Algebra.BigOperators.Fin

/-!
# Weight and tube bounds along a floor partition

Concatenate the pieces in the proof of Lemma 3.1 of the differentiability
preprint. The resulting path satisfies both the weight estimate and the
real `l1` distance bound, on one measurable event.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set
open scoped BigOperators NNReal

namespace LPPDifferentiability

/-- Existence over the finite actual path type is a measurable event. -/
theorem measurableSet_exists_path_weight_property (u : Lattice) (d : ℕ × ℕ)
    (r : ℝ) (P : Lattice → Prop) :
    MeasurableSet {ω : Environment | ∃ q : Path u d,
      r ≤ pathWeight ω q ∧ ∀ i, P (q.vertex i)} := by
  classical
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun q =>
    (measurableSet_le measurable_const (measurable_pathWeight q)).inter
      (MeasurableSet.const _)

/-- A single constant is chosen before every displacement and floor partition.
On the piece weight event, one actual concatenated path has both conclusions. -/
theorem exists_floorSegment_travel_assembly_constant
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r+t=1 →
      (r:ℝ)*g x+(t:ℝ)*g y ≤ g (r • x+t • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z)=(c:ℝ)*g z)
    (a theta : ℝ) (ha0 : 0<a) (ha1 : a<1)
    (htheta : 0<theta) (hinterior : theta<min a (1-a)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (B : ℕ), 1 ≤ B →
      ∀ (s η δ : ℝ) (u : Lattice) (d : ℕ × ℕ),
      |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)| ≤
        (min a (1-a)-theta)*((d.1:ℝ)+(d.2:ℝ)) →
      theta/2*(((d.1:ℝ)+(d.2:ℝ))/(B:ℝ)) ≥
        2+2*(min a (1-a)-theta/2) →
      2*L*(B:ℝ) ≤ η*s/2 →
      ((d.1+d.2:ℕ):ℝ)/(B:ℝ)+4 ≤ δ*s →
      let k : ℕ → ℕ × ℕ := fun j => (j*d.1/B,j*d.2/B)
      let Δ : Fin B → ℕ × ℕ := fun j =>
        ((k (j.val+1)).1-(k j.val).1,(k (j.val+1)).2-(k j.val).2)
      let U : Fin B → Lattice := fun j =>
        u + (((k j.val).1 : ℤ),((k j.val).2 : ℤ))
      ∀ (ω : Environment) (paths : (j : Fin B) → Path (U j) (Δ j)),
      (∀ j, g (((Δ j).1:ℝ≥0),((Δ j).2:ℝ≥0))-η*s/(2*(B:ℝ)) ≤
        pathWeight ω (paths j)) →
      ∃ q : Path u d, g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s ≤ pathWeight ω q ∧
        ∀ i, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
          |((q.vertex i).1:ℝ)-((u.1:ℝ)+t*(d.1:ℝ))|+
          |((q.vertex i).2:ℝ)-((u.2:ℝ)+t*(d.2:ℝ))| ≤ δ*s := by
  obtain ⟨L,hL,hshape⟩ := floorSegment_shape_sum g hgcont hgconc hhom
    a theta ha0 ha1 htheta hinterior
  refine ⟨L,hL,?_⟩
  intro B hB s η δ u d hd hcut hloss htube k Δ U ω paths hp
  let P : Lattice → Prop := fun v => ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    |(v.1:ℝ)-((u.1:ℝ)+t*(d.1:ℝ))|+
    |(v.2:ℝ)-((u.2:ℝ)+t*(d.2:ℝ))| ≤ δ*s
  have hP (j : Fin B) (i : Fin ((Δ j).1+(Δ j).2+1)) :
      P ((paths j).vertex i) := by
    obtain ⟨ht0,ht1⟩ := floorSegment_parameter B j.val hB (Nat.le_of_lt j.isLt)
    exact ⟨(j.val:ℝ)/(B:ℝ),ht0,ht1,
      (floorSegment_path_vertex_distance u d B j.val hB j.isLt (paths j) i).trans htube⟩
  obtain ⟨q,hw,_hend,hq⟩ := floorSegment_exists_concat ω u d B hB P paths hP
  refine ⟨q,?_,hq⟩
  have hsum := (hshape d B hB hd hcut).2
  have hsum' : g ((d.1:ℝ≥0),(d.2:ℝ≥0))-2*L*(B:ℝ) ≤
      ∑ j : Fin B, g (((Δ j).1:ℝ≥0),((Δ j).2:ℝ≥0)) := by
    let f : ℕ → ℝ := fun j =>
      g ((((k (j+1)).1-(k j).1:ℕ):ℝ≥0),(((k (j+1)).2-(k j).2:ℕ):ℝ≥0))
    change g ((d.1:ℝ≥0),(d.2:ℝ≥0))-2*L*(B:ℝ) ≤ ∑ j ∈ Finset.range B, f j at hsum
    change g ((d.1:ℝ≥0),(d.2:ℝ≥0))-2*L*(B:ℝ) ≤ ∑ j : Fin B, f j.val
    rw [Fin.sum_univ_eq_sum_range f B]
    exact hsum
  have hpSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  rw [Finset.sum_sub_distrib] at hpSum
  have hcancel : (∑ _j : Fin B, η*s/(2*(B:ℝ))) = η*s/2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt (show 0<(B:ℝ) by exact_mod_cast (show 0<B by omega))]
  rw [hcancel, ← hw] at hpSum
  linarith only [hsum',hpSum,hloss]

end LPPDifferentiability
