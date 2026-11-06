/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Real `l1` control for segments with attached endpoints. -/

@[expose] public section

namespace LPPDifferentiability

theorem realL1Distance_triangle (x y z : ℝ × ℝ) :
    (|x.1 - z.1| + |x.2 - z.2|) ≤ (|x.1 - y.1| + |x.2 - y.2|) + (|y.1 - z.1| + |y.2 - z.2|) := by
  have h₁ : |x.1 - z.1| ≤ |x.1 - y.1| + |y.1 - z.1| := by
    calc
      |x.1 - z.1| = |(x.1 - y.1) + (y.1 - z.1)| := by congr 1; ring
      _ ≤ |x.1 - y.1| + |y.1 - z.1| := abs_add_le _ _
  have h₂ : |x.2 - z.2| ≤ |x.2 - y.2| + |y.2 - z.2| := by
    calc
      |x.2 - z.2| = |(x.2 - y.2) + (y.2 - z.2)| := by congr 1; ring
      _ ≤ |x.2 - y.2| + |y.2 - z.2| := abs_add_le _ _
  linarith

theorem realL1Distance_comm (x y : ℝ × ℝ) :
    (|x.1 - y.1| + |x.2 - y.2|) = (|y.1 - x.1| + |y.2 - x.2|) := by
  congr 1
  · calc
      |x.1 - y.1| = |-(x.1 - y.1)| := (abs_neg _).symm
      _ = |y.1 - x.1| := by congr 1; ring
  · calc
      |x.2 - y.2| = |-(x.2 - y.2)| := (abs_neg _).symm
      _ = |y.2 - x.2| := by congr 1; ring

theorem real_attachment_segment_l1_le
    (u uHat vHat v : ℝ × ℝ) (m t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : (|uHat.1 - u.1| + |uHat.2 - u.2|) ≤ m)
    (hv : (|vHat.1 - v.1| + |vHat.2 - v.2|) ≤ m) :
    (|((1 - t) * uHat.1 + t * vHat.1) - ((1 - t) * u.1 + t * v.1)| + |((1 - t) * uHat.2 + t * vHat.2) - ((1 - t) * u.2 + t * v.2)|) ≤ m := by
  have h₁ :
      |((1 - t) * uHat.1 + t * vHat.1) - ((1 - t) * u.1 + t * v.1)| ≤
        (1 - t) * |uHat.1 - u.1| + t * |vHat.1 - v.1| := by
    have hdiff :
        ((1 - t) * uHat.1 + t * vHat.1) - ((1 - t) * u.1 + t * v.1) =
          (1 - t) * (uHat.1 - u.1) + t * (vHat.1 - v.1) := by ring
    calc
      |((1 - t) * uHat.1 + t * vHat.1) - ((1 - t) * u.1 + t * v.1)| =
          |(1 - t) * (uHat.1 - u.1) + t * (vHat.1 - v.1)| := by rw [hdiff]
      _ ≤ |(1 - t) * (uHat.1 - u.1)| + |t * (vHat.1 - v.1)| := abs_add_le _ _
      _ = |1 - t| * |uHat.1 - u.1| + |t| * |vHat.1 - v.1| := by
        rw [abs_mul, abs_mul]
      _ = (1 - t) * |uHat.1 - u.1| + t * |vHat.1 - v.1| := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg ht0]
  have h₂ :
      |((1 - t) * uHat.2 + t * vHat.2) - ((1 - t) * u.2 + t * v.2)| ≤
        (1 - t) * |uHat.2 - u.2| + t * |vHat.2 - v.2| := by
    have hdiff :
        ((1 - t) * uHat.2 + t * vHat.2) - ((1 - t) * u.2 + t * v.2) =
          (1 - t) * (uHat.2 - u.2) + t * (vHat.2 - v.2) := by ring
    calc
      |((1 - t) * uHat.2 + t * vHat.2) - ((1 - t) * u.2 + t * v.2)| =
          |(1 - t) * (uHat.2 - u.2) + t * (vHat.2 - v.2)| := by rw [hdiff]
      _ ≤ |(1 - t) * (uHat.2 - u.2)| + |t * (vHat.2 - v.2)| := abs_add_le _ _
      _ = |1 - t| * |uHat.2 - u.2| + |t| * |vHat.2 - v.2| := by
        rw [abs_mul, abs_mul]
      _ = (1 - t) * |uHat.2 - u.2| + t * |vHat.2 - v.2| := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg ht0]
  have hweights :
      (1 - t) * (|uHat.1 - u.1| + |uHat.2 - u.2|) + t * (|vHat.1 - v.1| + |vHat.2 - v.2|) ≤ m := by
    calc
      (1 - t) * (|uHat.1 - u.1| + |uHat.2 - u.2|) + t * (|vHat.1 - v.1| + |vHat.2 - v.2|) ≤
          (1 - t) * m + t * m := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hu (by linarith))
              (mul_le_mul_of_nonneg_left hv ht0)
      _ = m := by ring
  calc
    |((1 - t) * uHat.1 + t * vHat.1) - ((1 - t) * u.1 + t * v.1)| +
        |((1 - t) * uHat.2 + t * vHat.2) - ((1 - t) * u.2 + t * v.2)| ≤
      ((1 - t) * |uHat.1 - u.1| + t * |vHat.1 - v.1|) +
        ((1 - t) * |uHat.2 - u.2| + t * |vHat.2 - v.2|) := add_le_add h₁ h₂
    _ = (1 - t) * (|uHat.1 - u.1| + |uHat.2 - u.2|) +
        t * (|vHat.1 - v.1| + |vHat.2 - v.2|) := by ring
    _ ≤ m := hweights

/-- At each shared interpolation parameter, the two segments are at real
`l1` distance at most the common endpoint attachment bound. -/
theorem lattice_attachment_segment_l1_le
    (u uHat vHat v : Lattice) (m t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : (|(uHat.1 : ℝ) - (u.1 : ℝ)| + |(uHat.2 : ℝ) - (u.2 : ℝ)|) ≤ m)
    (hv : (|(vHat.1 : ℝ) - (v.1 : ℝ)| + |(vHat.2 : ℝ) - (v.2 : ℝ)|) ≤ m) :
    (|((1 - t) * (uHat.1 : ℝ) + t * (vHat.1 : ℝ)) - ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ))| + |((1 - t) * (uHat.2 : ℝ) + t * (vHat.2 : ℝ)) - ((1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))|) ≤ m := by
  exact real_attachment_segment_l1_le
    ((u.1 : ℝ), (u.2 : ℝ)) ((uHat.1 : ℝ), (uHat.2 : ℝ))
    ((vHat.1 : ℝ), (vHat.2 : ℝ)) ((v.1 : ℝ), (v.2 : ℝ)) m t ht0 ht1 hu hv

/-- A point close to the hatted segment transfers to the original segment at
the very same interpolation parameter. -/
theorem realPoint_attachment_segment_transfer
    (x : ℝ × ℝ) (u uHat vHat v : Lattice) (r m t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : (|x.1 - ((1 - t) * (uHat.1 : ℝ) + t * (vHat.1 : ℝ))| + |x.2 - ((1 - t) * (uHat.2 : ℝ) + t * (vHat.2 : ℝ))|) ≤ r)
    (hu : (|(uHat.1 : ℝ) - (u.1 : ℝ)| + |(uHat.2 : ℝ) - (u.2 : ℝ)|) ≤ m)
    (hv : (|(vHat.1 : ℝ) - (v.1 : ℝ)| + |(vHat.2 : ℝ) - (v.2 : ℝ)|) ≤ m) :
    (|x.1 - ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ))| + |x.2 - ((1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))|) ≤ r + m := by
  have hsegments := lattice_attachment_segment_l1_le u uHat vHat v m t ht0 ht1 hu hv
  calc
    (|x.1 - ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ))| + |x.2 - ((1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))|) ≤
        (|x.1 - ((1 - t) * (uHat.1 : ℝ) + t * (vHat.1 : ℝ))| + |x.2 - ((1 - t) * (uHat.2 : ℝ) + t * (vHat.2 : ℝ))|) +
          (|((1 - t) * (uHat.1 : ℝ) + t * (vHat.1 : ℝ)) - ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ))| + |((1 - t) * (uHat.2 : ℝ) + t * (vHat.2 : ℝ)) - ((1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))|) :=
      realL1Distance_triangle x
        ((1 - t) * (uHat.1 : ℝ) + t * (vHat.1 : ℝ),
          (1 - t) * (uHat.2 : ℝ) + t * (vHat.2 : ℝ))
        ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ),
          (1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))
    _ ≤ r + m := add_le_add hx hsegments

/-- A segment-nearness witness transfers without changing its parameter. -/
theorem realPoint_attachment_segment_transfer_exists
    (x : ℝ × ℝ) (u uHat vHat v : Lattice) (r m : ℝ)
    (hnear : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      (|x.1 - ((1 - t) * (uHat.1 : ℝ) + t * (vHat.1 : ℝ))| + |x.2 - ((1 - t) * (uHat.2 : ℝ) + t * (vHat.2 : ℝ))|) ≤ r)
    (hu : (|(uHat.1 : ℝ) - (u.1 : ℝ)| + |(uHat.2 : ℝ) - (u.2 : ℝ)|) ≤ m)
    (hv : (|(vHat.1 : ℝ) - (v.1 : ℝ)| + |(vHat.2 : ℝ) - (v.2 : ℝ)|) ≤ m) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      (|x.1 - ((1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ))| + |x.2 - ((1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ))|) ≤ r + m := by
  rcases hnear with ⟨t, ht0, ht1, hx⟩
  exact ⟨t, ht0, ht1,
    realPoint_attachment_segment_transfer x u uHat vHat v r m t ht0 ht1 hx hu hv⟩

end LPPDifferentiability

end
