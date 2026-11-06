/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
public import LPP_Foundations.Model.Paths.Concat
import Mathlib.Algebra.BigOperators.Fin

/-! Exact additivity for path weights that omit their terminal vertex. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Omitting terminal vertices makes concatenation exactly additive. -/
theorem pathWeight_concat (ω : Environment) {u : Lattice} {d e : ℕ × ℕ}
    (p : Path u d) (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e) :
    pathWeight ω (p.concat q) = pathWeight ω p + pathWeight ω q := by
  have hlen : (d + e).1 + (d + e).2 = (d.1 + d.2) + (e.1 + e.2) := by
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  unfold pathWeight
  rw [← Fin.sum_congr' _ hlen.symm, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg ω (p.concat_vertex_left q i.castSucc)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg ω (p.concat_vertex_right q i.castSucc)

end LPPDifferentiability
