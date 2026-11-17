/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.LastPassage.OptimalSplit
import LPP_Foundations.Model.LastPassage.Inclusive

/-! Outgoing recurrences for terminal-omitting last passage, in the finite construction
of JR1810.03580v3. -/

@[expose] public section

namespace LPPDifferentiability

/-- An interior passage splits at its first step, as in the finite construction. -/
theorem lastPassage_outgoing_succ_succ (ω : Environment) (u : Lattice) (a b : ℕ) :
    lastPassage ω u (a + 1, b + 1) =
      ω u + max (lastPassage ω (u + (1, 0)) (a, b + 1))
        (lastPassage ω (u + (0, 1)) (a + 1, b)) := by
  apply le_antisymm
  · let k : Fin ((a + 1, b + 1).1 + (a + 1, b + 1).2 + 1) := ⟨1, by simp⟩
    obtain ⟨d, _, hlen, hsplit⟩ := exists_lastPassage_eq_split ω u (a + 1, b + 1) k
    have hc : d = (1, 0) ∨ d = (0, 1) := by
      have h : d.1 + d.2 = 1 := hlen
      rcases (show (d.1 = 1 ∧ d.2 = 0) ∨ (d.1 = 0 ∧ d.2 = 1) by omega) with h | h
      · exact Or.inl (Prod.ext h.1 h.2)
      · exact Or.inr (Prod.ext h.1 h.2)
    rcases hc with h | h
    · rw [h] at hsplit
      simp only [lastPassage_horizontal_one, Nat.cast_one, Nat.cast_zero,
        Prod.mk_sub_mk, Nat.add_sub_cancel_right, Nat.sub_zero] at hsplit
      rw [hsplit]
      exact add_le_add_right (le_max_left _ _) _
    · rw [h] at hsplit
      simp only [lastPassage_vertical_one, Nat.cast_one, Nat.cast_zero,
        Prod.mk_sub_mk, Nat.add_sub_cancel_right, Nat.sub_zero] at hsplit
      rw [hsplit]
      exact add_le_add_right (le_max_right _ _) _
  · rw [add_max]
    apply max_le
    · have h := lastPassage_superadditive ω u (1, 0) (a, b + 1)
      simpa [lastPassage_horizontal_one, Prod.mk_add_mk, Nat.add_comm] using h
    · have h := lastPassage_superadditive ω u (0, 1) (a + 1, b)
      simpa [lastPassage_vertical_one, Prod.mk_add_mk, Nat.add_comm] using h

/-- A horizontal passage splits at its first step, as in the finite construction. -/
theorem lastPassage_outgoing_horizontal_succ (ω : Environment) (u : Lattice) (n : ℕ) :
    lastPassage ω u (n + 1, 0) = ω u + lastPassage ω (u + (1, 0)) (n, 0) := by
  apply le_antisymm
  · let k : Fin ((n + 1, 0).1 + (n + 1, 0).2 + 1) := ⟨1, by simp⟩
    obtain ⟨d, hd, hlen, hsplit⟩ := exists_lastPassage_eq_split ω u (n + 1, 0) k
    have h : d = (1, 0) := by
      have hs : d.1 + d.2 = 1 := hlen
      have h2 : d.2 ≤ 0 := hd.2
      apply Prod.ext <;> simp_all
    rw [h] at hsplit
    simpa [lastPassage_horizontal_one, Prod.mk_sub_mk] using hsplit.le
  · have h := lastPassage_superadditive ω u (1, 0) (n, 0)
    simpa [lastPassage_horizontal_one, Prod.mk_add_mk, Nat.add_comm] using h

/-- A vertical passage splits at its first step, as in the finite construction. -/
theorem lastPassage_outgoing_vertical_succ (ω : Environment) (u : Lattice) (n : ℕ) :
    lastPassage ω u (0, n + 1) = ω u + lastPassage ω (u + (0, 1)) (0, n) := by
  apply le_antisymm
  · let k : Fin ((0, n + 1).1 + (0, n + 1).2 + 1) := ⟨1, by simp⟩
    obtain ⟨d, hd, hlen, hsplit⟩ := exists_lastPassage_eq_split ω u (0, n + 1) k
    have h : d = (0, 1) := by
      have hs : d.1 + d.2 = 1 := hlen
      have h1 : d.1 ≤ 0 := hd.1
      apply Prod.ext <;> simp_all
    rw [h] at hsplit
    simpa [lastPassage_vertical_one, Prod.mk_sub_mk] using hsplit.le
  · have h := lastPassage_superadditive ω u (0, 1) (0, n)
    simpa [lastPassage_vertical_one, Prod.mk_add_mk, Nat.add_comm] using h

end LPPDifferentiability
