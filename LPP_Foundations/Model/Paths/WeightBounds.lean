/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! Deterministic bounds for signed weights on finite directed paths. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Path weight is additive in the environment. -/
theorem pathWeight_add (ω η : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    pathWeight (ω + η) p = pathWeight ω p + pathWeight η p := by
  simp [pathWeight, Finset.sum_add_distrib]

/-- A constant environment contributes its value at each collected vertex. -/
theorem pathWeight_const (c : ℝ) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    pathWeight (fun _ : Lattice => c) p = ((d.1 + d.2 : ℕ) : ℝ) * c := by
  simp [pathWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Increasing every site weight can only increase the weight of a fixed path. -/
theorem pathWeight_mono (ω η : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (h : ∀ z, ω z ≤ η z) :
    pathWeight ω p ≤ pathWeight η p := by
  unfold pathWeight
  exact Finset.sum_le_sum fun i _ => h (p.vertex i.castSucc)

/-- A pointwise upper bound gives the corresponding path-weight bound. -/
theorem pathWeight_le_const (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (c : ℝ) (h : ∀ z, ω z ≤ c) :
    pathWeight ω p ≤ ((d.1 + d.2 : ℕ) : ℝ) * c := by
  calc
    pathWeight ω p ≤ pathWeight (fun _ : Lattice => c) p :=
      pathWeight_mono ω (fun _ : Lattice => c) p h
    _ = ((d.1 + d.2 : ℕ) : ℝ) * c := pathWeight_const c p

/-- A pointwise lower bound gives the corresponding path-weight bound. -/
theorem const_le_pathWeight (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (c : ℝ) (h : ∀ z, c ≤ ω z) :
    ((d.1 + d.2 : ℕ) : ℝ) * c ≤ pathWeight ω p := by
  calc
    ((d.1 + d.2 : ℕ) : ℝ) * c = pathWeight (fun _ : Lattice => c) p :=
      (pathWeight_const c p).symm
    _ ≤ pathWeight ω p := pathWeight_mono (fun _ : Lattice => c) ω p h

/-- Uniform absolute bounds on site weights give an absolute bound on path weight. -/
theorem pathWeight_abs_le (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (B : ℝ) (h : ∀ z, |ω z| ≤ B) :
    |pathWeight ω p| ≤ ((d.1 + d.2 : ℕ) : ℝ) * B := by
  have hupper : ∀ z, ω z ≤ B := fun z => (abs_le.mp (h z)).2
  have hlower : ∀ z, -B ≤ ω z := fun z => (abs_le.mp (h z)).1
  have hupper' := pathWeight_le_const ω p B hupper
  have hlower' := const_le_pathWeight ω p (-B) hlower
  apply abs_le.mpr
  constructor
  · calc
      -(((d.1 + d.2 : ℕ) : ℝ) * B) = ((d.1 + d.2 : ℕ) : ℝ) * (-B) := by ring
      _ ≤ pathWeight ω p := hlower'
  · exact hupper'

/-- Negating all site weights negates the weight of each path. -/
theorem pathWeight_neg (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) : pathWeight (-ω) p = -pathWeight ω p := by
  simp [pathWeight]

/-- Subtracting environments subtracts their path weights. -/
theorem pathWeight_sub (ω η : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) : pathWeight (ω - η) p = pathWeight ω p - pathWeight η p := by
  have henv : ω - η = ω + -η := by
    funext z
    rfl
  rw [henv, pathWeight_add, pathWeight_neg]
  rfl

/-- Pointwise perturbation bounds control the change in the weight of each path. -/
theorem pathWeight_sub_abs_le (ω η : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (B : ℝ) (h : ∀ z, |ω z - η z| ≤ B) :
    |pathWeight ω p - pathWeight η p| ≤ ((d.1 + d.2 : ℕ) : ℝ) * B := by
  have hdiff : ∀ z, |(ω - η) z| ≤ B := by
    intro z
    change |ω z - η z| ≤ B
    exact h z
  have hweight := pathWeight_abs_le (ω - η) p B hdiff
  rw [pathWeight_sub] at hweight
  exact hweight

end LPPDifferentiability
