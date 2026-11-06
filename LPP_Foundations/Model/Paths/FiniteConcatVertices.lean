/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.FiniteConcat

/-! Common vertex properties transfer along the actual finite concatenation. -/

public section

open scoped BigOperators

namespace LPPDifferentiability.Path

/-- The same path has the exact weight, terminal, and common vertex property. -/
theorem exists_concat_finite_property (ω : Environment) {B : ℕ} (hB : 1 ≤ B)
    (u : Fin (B + 1) → Lattice) (d : Fin B → ℕ × ℕ)
    (hjoin : ∀ j, u j.succ = u j.castSucc +
      (((d j).1 : ℤ), ((d j).2 : ℤ)))
    (p : ∀ j, Path (u j.castSucc) (d j))
    (P : Lattice → Prop)
    (hP : ∀ j (k : Fin ((d j).1 + (d j).2 + 1)), P ((p j).vertex k)) :
    ∃ q : Path (u ((⟨0, by omega⟩ : Fin B).castSucc)) (∑ j : Fin B, d j),
      pathWeight ω q = ∑ j : Fin B, pathWeight ω (p j) ∧
      q.vertex (Fin.last ((∑ j : Fin B, d j).1 + (∑ j : Fin B, d j).2)) =
        u (Fin.last B) ∧
      (∀ i : Fin ((∑ j : Fin B, d j).1 + (∑ j : Fin B, d j).2 + 1),
        ∃ j : Fin B, ∃ k : Fin ((d j).1 + (d j).2 + 1),
          q.vertex i = (p j).vertex k) ∧
      ∀ i, P (q.vertex i) := by
  obtain ⟨q, hw, ht, hv⟩ := exists_concat_finite ω hB u d hjoin p
  refine ⟨q, hw, ht, hv, ?_⟩
  intro i
  obtain ⟨j, k, hk⟩ := hv i
  rw [hk]
  exact hP j k

end LPPDifferentiability.Path
