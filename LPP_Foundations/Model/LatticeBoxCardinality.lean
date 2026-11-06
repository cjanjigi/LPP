/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Exact cardinality of a translated integer coordinate box. -/

@[expose] public section

namespace LPPDifferentiability

/-- A signed integer lattice box with coordinate radius `k` has `(2*k+1)^2` sites. -/
theorem lattice_box_cardinality (v : Lattice) (k : ℕ) :
    (Finset.Icc (v.1 - (k : ℤ)) (v.1 + (k : ℤ)) ×ˢ
      Finset.Icc (v.2 - (k : ℤ)) (v.2 + (k : ℤ))).card = (2 * k + 1) ^ 2 := by
  have hinterval (a : ℤ) :
      (Finset.Icc (a - (k : ℤ)) (a + (k : ℤ))).card = 2 * k + 1 := by
    have hcast :
        ((Finset.Icc (a - (k : ℤ)) (a + (k : ℤ))).card : ℤ) =
          2 * (k : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (a := a - (k : ℤ)) (b := a + (k : ℤ))
        (h := by omega)]
      omega
    exact_mod_cast hcast
  rw [Finset.card_product, hinterval, hinterval, Nat.pow_two]

end LPPDifferentiability

end
