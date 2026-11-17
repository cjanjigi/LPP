/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Analysis.ConcaveProfileSlopes
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Tactic

/-! A finite concave profile is differentiable densely in its interior. -/

@[expose] public section
open Set

/-- Every nonempty subinterval of `(0,1)` contains a differentiability point
of a concave real profile. This is the dense-barrier input in GRS
arXiv:1510.00860v1, proof of Theorem 2.1(i). -/
theorem exists_differentiableAt_of_concaveOn_Icc
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Icc 0 1) f)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ x : ℝ, x ∈ Ioo a b ∧ DifferentiableAt ℝ f x := by
  classical
  let bad : Set ℝ := {x | x ∈ Ioo (0 : ℝ) 1 ∧ ¬ DifferentiableAt ℝ f x}
  let gap (x : ℝ) : Set ℝ :=
    Ioo (derivWithin f (Ioi x) x) (derivWithin f (Iio x) x)
  have hinterior {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : x ∈ interior (Icc (0 : ℝ) 1) := by
    simpa only [interior_Icc] using hx
  have hgap (x : ℝ) (hx : x ∈ bad) :
      derivWithin f (Ioi x) x < derivWithin f (Iio x) x := by
    have hi := hinterior hx.1
    have hle := hf.rightDeriv_le_leftDeriv_of_mem_interior hi
    have hne : derivWithin f (Iio x) x ≠ derivWithin f (Ioi x) x := by
      intro heq
      exact hx.2 ((hf.differentiableAt_iff_leftDeriv_eq_rightDeriv_of_mem_interior hi).2 heq)
    exact lt_of_le_of_ne hle (Ne.symm hne)
  have hcross {x y : ℝ} (hx : x ∈ bad) (hy : y ∈ bad) (hxy : x < y) :
      derivWithin f (Iio y) y ≤ derivWithin f (Ioi x) x := by
    have hxS : x ∈ Icc (0 : ℝ) 1 := interior_subset (hinterior hx.1)
    have hyS : y ∈ Icc (0 : ℝ) 1 := interior_subset (hinterior hy.1)
    calc
      derivWithin f (Iio y) y ≤ slope f x y :=
        hf.leftDeriv_le_slope hxS hyS hxy
          (hf.hasDerivWithinAt_leftDeriv_of_mem_interior (hinterior hy.1)).differentiableWithinAt
      _ ≤ derivWithin f (Ioi x) x :=
        hf.slope_le_rightDeriv hxS hyS hxy
          (hf.hasDerivWithinAt_rightDeriv_of_mem_interior (hinterior hx.1)).differentiableWithinAt
  have hdisjoint : bad.PairwiseDisjoint gap := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hzx' : derivWithin f (Ioi x) x < z ∧ z < derivWithin f (Iio x) x := hzx
    have hzy' : derivWithin f (Ioi y) y < z ∧ z < derivWithin f (Iio y) y := hzy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have h := hcross hx hy hlt
      linarith
    · have h := hcross hy hx hgt
      linarith
  have hcount : bad.Countable := hdisjoint.countable_of_isOpen
    (fun _ _ => isOpen_Ioo) (fun x hx => nonempty_Ioo.mpr (hgap x hx))
  have hdense : Dense badᶜ := hcount.dense_compl ℝ
  have hnonempty : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
  obtain ⟨x, hxnot, hx⟩ := hdense.exists_mem_open isOpen_Ioo hnonempty
  refine ⟨x, hx, ?_⟩
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  by_contra hnot
  exact hxnot ⟨hx01, hnot⟩
