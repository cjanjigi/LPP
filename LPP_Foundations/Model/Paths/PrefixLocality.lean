/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Split

/-! Locality of the weight collected along an actual path prefix. -/

@[expose] public section

open scoped BigOperators
open LPPDifferentiability

namespace LPP

/-- Agreement before a split gives the same prefix weight.

This follows the terminal-excluded indexing of `Path.prefixPath` in
`LPP_Foundations/Model/Paths/Split.lean`. -/
theorem pathWeight_prefix_eq_of_eq_before
    (ω η : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : LPPDifferentiability.Path u d) (k : Fin (d.1 + d.2 + 1))
    (h : ∀ i : Fin (d.1 + d.2), i.val < k.val →
      ω (p.vertex i.castSucc) = η (p.vertex i.castSucc)) :
    pathWeight ω (p.prefixPath k) = pathWeight η (p.prefixPath k) := by
  unfold pathWeight
  apply Finset.sum_congr rfl
  intro i _
  have hPrefixLength := p.splitDisplacement_length k
  have hiBefore : i.val < k.val := by
    rw [← hPrefixLength]
    exact i.isLt
  have hiOriginal : i.val < d.1 + d.2 :=
    Nat.lt_of_lt_of_le hiBefore (Nat.le_of_lt_succ k.isLt)
  let iOrig : Fin (d.1 + d.2) := ⟨i.val, hiOriginal⟩
  have hVertex : (p.prefixPath k).vertex i.castSucc =
      p.vertex iOrig.castSucc := by
    change p.vertex
        (⟨i.val, Nat.lt_succ_of_lt hiOriginal⟩ : Fin (d.1 + d.2 + 1)) =
      p.vertex iOrig.castSucc
    apply congrArg p.vertex
    apply Fin.ext
    rfl
  calc
    ω ((p.prefixPath k).vertex i.castSucc) =
        ω (p.vertex iOrig.castSucc) := by rw [hVertex]
    _ = η (p.vertex iOrig.castSucc) := h iOrig hiBefore
    _ = η ((p.prefixPath k).vertex i.castSucc) := by rw [hVertex]

end LPP
