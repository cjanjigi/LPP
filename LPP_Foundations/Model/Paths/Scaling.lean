/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact scalar scaling of finite path weights. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Scaling every site weight scales the weight of each path by the same real factor. -/
theorem pathWeight_smul (a : ℝ) (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    pathWeight (a • ω) p = a * pathWeight ω p := by
  simp only [pathWeight, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]

end LPPDifferentiability
