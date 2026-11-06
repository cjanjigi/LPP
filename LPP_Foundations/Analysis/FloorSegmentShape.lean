/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.FloorSegmentShapeGeometry
public import LPP_Foundations.Analysis.HomogeneousShapeLipschitz
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shape sum over a floor partition

The deterministic shape sum used in the proof of Lemma 3.1 of the differentiability preprint.
One constant serves every floor partition that satisfies the scalar cutoff.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open scoped BigOperators NNReal

namespace LPPDifferentiability

/-- One Lipschitz witness works for every floor partition satisfying
exactly the scalar cutoff. No sign assumption on the shape is needed. -/
theorem floorSegment_shape_sum
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r+s=1 →
      (r:ℝ)*g x+(s:ℝ)*g y ≤ g (r • x+s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z)=(c:ℝ)*g z)
    (a theta : ℝ) (ha0 : 0<a) (ha1 : a<1)
    (htheta : 0<theta) (hinterior : theta<min a (1-a)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (d : ℕ × ℕ) (B : ℕ), 1 ≤ B →
      |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)| ≤
        (min a (1-a)-theta)*((d.1:ℝ)+(d.2:ℝ)) →
      theta/2*(((d.1:ℝ)+(d.2:ℝ))/(B:ℝ)) ≥
        2+2*(min a (1-a)-theta/2) →
      let k : ℕ → ℕ × ℕ := fun n => (n*d.1/B,n*d.2/B)
      let Δ : ℕ → ℕ × ℕ := fun n =>
        ((k (n+1)).1-(k n).1,(k (n+1)).2-(k n).2)
      (∀ j < B,
        g ((1/(B:ℝ≥0)) • ((d.1:ℝ≥0),(d.2:ℝ≥0)))-2*L ≤
          g (((Δ j).1:ℝ≥0),((Δ j).2:ℝ≥0))) ∧
      (∑ j ∈ Finset.range B, g (((Δ j).1:ℝ≥0),((Δ j).2:ℝ≥0))) ≥
        g ((d.1:ℝ≥0),(d.2:ℝ≥0))-2*L*(B:ℝ) := by
  obtain ⟨L,hL,hLip⟩ := quadrant_homogeneous_shape_lipschitz_on_adapted_cone
    g hgcont hgconc hhom a (theta/2) ha0 ha1 (by linarith) (by linarith)
  refine ⟨L,hL,?_⟩
  intro d B hB hd hcut k Δ
  have hb : 0 < (B:ℝ) := by exact_mod_cast (show 0<B by omega)
  let z : Quadrant := ((d.1:ℝ≥0),(d.2:ℝ≥0))
  let w : Quadrant := (1/(B:ℝ≥0)) • z
  have hw1 : (w.1:ℝ)=(d.1:ℝ)/(B:ℝ) := by
    simp [w,z,div_eq_mul_inv,mul_comm]
  have hw2 : (w.2:ℝ)=(d.2:ℝ)/(B:ℝ) := by
    simp [w,z,div_eq_mul_inv,mul_comm]
  have hscaled := adapted_cone_div a theta (d.1:ℝ) (d.2:ℝ) (B:ℝ) hb hd
  have hwcone : |(1-a)*(w.1:ℝ)-a*(w.2:ℝ)| ≤
      (min a (1-a)-theta/2)*((w.1:ℝ)+(w.2:ℝ)) := by
    rw [hw1,hw2]
    have hn : 0 ≤ (d.1:ℝ)/(B:ℝ)+(d.2:ℝ)/(B:ℝ) := by positivity
    nlinarith
  have hpiece (j : ℕ) :
      g w-2*L ≤ g (((Δ j).1:ℝ≥0),((Δ j).2:ℝ≥0)) := by
    have hcone := floorSegment_increment_interior a theta ha0 ha1 htheta
      hinterior d B j hB hd hcut
    have herr := (floorSegment_increment_bounds d B j hB).1
    let v : Quadrant := (((Δ j).1:ℝ≥0),((Δ j).2:ℝ≥0))
    have hvcone : |(1-a)*(v.1:ℝ)-a*(v.2:ℝ)| ≤
        (min a (1-a)-theta/2)*((v.1:ℝ)+(v.2:ℝ)) := by
      exact hcone.2
    have hlip := hLip v w ⟨hvcone,hwcone⟩
    rw [hw1,hw2] at hlip
    have herr' : |(v.1:ℝ)-(d.1:ℝ)/(B:ℝ)|+
      |(v.2:ℝ)-(d.2:ℝ)/(B:ℝ)| ≤ 2 := herr
    have hbound := mul_le_mul_of_nonneg_left herr' (show 0≤L by linarith)
    have hlow := (abs_le.mp (hlip.trans hbound)).1
    dsimp only [v] at hlow
    linarith
  have hsum := Finset.sum_le_sum (s:=Finset.range B)
    (fun j _ => hpiece j)
  have hhomw : g w = (1/(B:ℝ))*g z := by
    simpa only [w,NNReal.coe_div,NNReal.coe_one,NNReal.coe_natCast] using
      hhom (1/(B:ℝ≥0)) z
  have hcancel : (B:ℝ)*g w=g z := by
    rw [hhomw]
    field_simp
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  change (B:ℝ)*(g w-2*L) ≤ _ at hsum
  constructor
  · intro j _
    exact hpiece j
  · change _ ≥ g z-2*L*(B:ℝ)
    nlinarith

end LPPDifferentiability
