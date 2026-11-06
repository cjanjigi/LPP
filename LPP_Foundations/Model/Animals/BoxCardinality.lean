/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Closed integer boxes and the cardinality bound for a finite family of them. -/

@[expose] public section

namespace LPPDifferentiability

/-- The closed sup-norm box of natural radius `r` centered at `v` in the integer plane. -/
def integerBox (v : ℤ × ℤ) (r : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (v.1 - (r : ℤ)) (v.1 + (r : ℤ)) ×ˢ
    Finset.Icc (v.2 - (r : ℤ)) (v.2 + (r : ℤ))

/-- Box membership is the pair of coordinatewise integer distance bounds. -/
theorem mem_integerBox_iff (v z : ℤ × ℤ) (r : ℕ) :
    z ∈ integerBox v r ↔
      |z.1 - v.1| ≤ (r : ℤ) ∧ |z.2 - v.2| ≤ (r : ℤ) := by
  simp only [integerBox, Finset.mem_product, Finset.mem_Icc, abs_le]
  omega

/-- Every integer box has exactly `(2r + 1)^2` points, for every center. -/
theorem integerBox_card (v : ℤ × ℤ) (r : ℕ) :
    (integerBox v r).card = (2 * r + 1) ^ 2 := by
  have hinterval (a : ℤ) :
      (Finset.Icc (a - (r : ℤ)) (a + (r : ℤ))).card = 2 * r + 1 := by
    have hcast :
        ((Finset.Icc (a - (r : ℤ)) (a + (r : ℤ))).card : ℤ) =
          2 * (r : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (a := a - (r : ℤ)) (b := a + (r : ℤ))
        (h := by omega)]
      omega
    exact_mod_cast hcast
  rw [integerBox, Finset.card_product, hinterval v.1, hinterval v.2, pow_two]

/-- The union of `m` boxes is bounded by the sum of their individual cardinalities. -/
theorem integerBox_family_union_card_le (m : ℕ)
    (centers : Fin m → ℤ × ℤ) (r : ℕ) :
    ((Finset.univ : Finset (Fin m)).biUnion
        (fun i => integerBox (centers i) r)).card ≤ m * (2 * r + 1) ^ 2 := by
  calc
    ((Finset.univ : Finset (Fin m)).biUnion
        (fun i => integerBox (centers i) r)).card ≤
        ∑ i ∈ (Finset.univ : Finset (Fin m)),
          (integerBox (centers i) r).card := Finset.card_biUnion_le
    _ = (Finset.univ : Finset (Fin m)).card * (2 * r + 1) ^ 2 := by
      apply Finset.sum_const_nat
      intro i hi
      exact integerBox_card (centers i) r
    _ = m * (2 * r + 1) ^ 2 := by simp

/-- At radius `2l`, each planar covering box contributes `(4l + 1)^2` points. -/
theorem integerBox_scaledCover_union_card_le (q l : ℕ)
    (centers : Fin (q + 1) → ℤ × ℤ) :
    ((Finset.univ : Finset (Fin (q + 1))).biUnion
        (fun i => integerBox (centers i) (2 * l))).card ≤
      (q + 1) * (4 * l + 1) ^ 2 := by
  calc
    ((Finset.univ : Finset (Fin (q + 1))).biUnion
        (fun i => integerBox (centers i) (2 * l))).card ≤
        (q + 1) * (2 * (2 * l) + 1) ^ 2 :=
          integerBox_family_union_card_le (q + 1) centers (2 * l)
    _ = (q + 1) * (4 * l + 1) ^ 2 :=
      congrArg (fun n : ℕ => (q + 1) * n ^ 2) (by omega)

/-- A zero-radius box is exactly its center, including at negative coordinates. -/
theorem integerBox_zero_radius (v : ℤ × ℤ) : integerBox v 0 = {v} := by
  ext z
  simp only [mem_integerBox_iff, Finset.mem_singleton, Prod.ext_iff, abs_le]
  omega

/-- A negative center has the same exact box cardinality as every other center. -/
theorem integerBox_negative_center_card :
    (integerBox ((-2 : ℤ), -5) 1).card = 9 := by
  rw [integerBox_card]
  norm_num

/-- The union of an empty indexed family of boxes is empty. -/
theorem integerBox_empty_family_card (r : ℕ) :
    ((Finset.univ : Finset (Fin 0)).biUnion
        (fun i : Fin 0 => integerBox (Fin.elim0 i) r)).card = 0 := by
  simp

/-- Two radius-one boxes with adjacent centers overlap at the origin. -/
theorem integerBox_adjacent_boxes_overlap :
    ((0 : ℤ), 0) ∈ integerBox ((0 : ℤ), 0) 1 ∧
      ((0 : ℤ), 0) ∈ integerBox ((1 : ℤ), 0) 1 := by
  constructor
  · apply (mem_integerBox_iff ((0 : ℤ), 0) ((0 : ℤ), 0) 1).2
    norm_num
  · apply (mem_integerBox_iff ((1 : ℤ), 0) ((0 : ℤ), 0) 1).2
    norm_num

/-- The union bound applies to an indexed family with overlapping members. -/
theorem integerBox_overlapping_family_card_le :
    ((Finset.univ : Finset (Fin 2)).biUnion
        (fun i : Fin 2 =>
          integerBox (if i = 0 then ((0 : ℤ), 0) else (1, 0)) 1)).card ≤ 18 := by
  simpa using
    integerBox_family_union_card_le 2
      (fun i : Fin 2 => if i = 0 then ((0 : ℤ), 0) else (1, 0)) 1

end LPPDifferentiability
