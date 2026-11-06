/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Split
public import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Tactic.Linarith

/-! Actual segments of a maximizing path are maximizing, and each local time
admits an exact last-passage decomposition through one intermediate vertex. -/

@[expose] public section

namespace LPPDifferentiability

/-- Each actual segment of a maximizing path attains its own passage maximum. -/
theorem Path.maximizing_segments (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (hp : pathWeight ω p = lastPassage ω u d)
    (k : Fin (d.1 + d.2 + 1)) :
    pathWeight ω (p.prefixPath k) = lastPassage ω u (p.splitDisplacement k) ∧
    pathWeight ω (p.suffix k) =
      lastPassage ω (p.vertex k) (d - p.splitDisplacement k) := by
  have hprefix := pathWeight_le_lastPassage ω (p.prefixPath k)
  have hsuffix := pathWeight_le_lastPassage ω (p.suffix k)
  have hsplit := pathWeight_split ω p k
  have hconcat := lastPassage_superadditive ω u
    (p.splitDisplacement k) (d - p.splitDisplacement k)
  rw [p.splitDisplacement_add_sub k, ← p.split_vertex k] at hconcat
  constructor <;> linarith only [hp, hprefix, hsuffix, hsplit, hconcat]

/-- The actual split vertex of a maximizing path gives exact passage additivity. -/
theorem Path.lastPassage_eq_split_of_maximizing (ω : Environment)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (hp : pathWeight ω p = lastPassage ω u d)
    (k : Fin (d.1 + d.2 + 1)) :
    lastPassage ω u d = lastPassage ω u (p.splitDisplacement k) +
      lastPassage ω
        (u + (((p.splitDisplacement k).1 : ℤ), ((p.splitDisplacement k).2 : ℤ)))
        (d - p.splitDisplacement k) := by
  obtain ⟨hprefix, hsuffix⟩ := p.maximizing_segments ω hp k
  calc
    lastPassage ω u d = pathWeight ω p := hp.symm
    _ = pathWeight ω (p.prefixPath k) + pathWeight ω (p.suffix k) :=
      pathWeight_split ω p k
    _ = lastPassage ω u (p.splitDisplacement k) +
        lastPassage ω (p.vertex k) (d - p.splitDisplacement k) := by
      rw [hprefix, hsuffix]
    _ = _ := by rw [p.split_vertex k]

/-- Every local time has one intermediate displacement giving exact passage decomposition. -/
theorem exists_lastPassage_eq_split (ω : Environment) (u : Lattice) (d : ℕ × ℕ)
    (k : Fin (d.1 + d.2 + 1)) :
    ∃ a : ℕ × ℕ, a ≤ d ∧ a.1 + a.2 = k.val ∧
      lastPassage ω u d = lastPassage ω u a +
        lastPassage ω (u + ((a.1 : ℤ), (a.2 : ℤ))) (d - a) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
  exact ⟨p.splitDisplacement k, p.splitDisplacement_le k,
    p.splitDisplacement_length k, p.lastPassage_eq_split_of_maximizing ω hp k⟩

end LPPDifferentiability
