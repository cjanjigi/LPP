/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Level
public import Mathlib.Order.Fin.Basic

/-! Up-right paths have distinct vertices and stay in their endpoint rectangle. -/

@[expose] public section

namespace LPPDifferentiability

/-- Distinct local times have distinct absolute levels and hence distinct vertices. -/
theorem Path.vertex_injective {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Function.Injective p.vertex := by
  intro i j hij
  have hi := p.level i
  have hj := p.level j
  rw [hij] at hi
  apply Fin.ext
  omega

/-- The first coordinate never decreases along an up-right path. -/
theorem Path.fst_monotone {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Monotone (fun i => (p.vertex i).1) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  rcases p.step i with h | h
  · rw [h]
    simp only [Prod.fst_add]
    omega
  · rw [h]
    simp only [Prod.fst_add]
    omega

/-- The second coordinate never decreases along an up-right path. -/
theorem Path.snd_monotone {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Monotone (fun i => (p.vertex i).2) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  rcases p.step i with h | h
  · rw [h]
    simp only [Prod.snd_add]
    omega
  · rw [h]
    simp only [Prod.snd_add]
    omega

/-- Every vertex lies in the closed coordinatewise interval between the endpoints. -/
theorem Path.vertex_mem_Icc {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (i : Fin (d.1 + d.2 + 1)) :
    p.vertex i ∈ Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))) := by
  have h₁ := p.fst_monotone (Fin.zero_le i)
  have h₂ := p.snd_monotone (Fin.zero_le i)
  have h₃ := p.fst_monotone (Fin.le_last i)
  have h₄ := p.snd_monotone (Fin.le_last i)
  dsimp only at h₁ h₂ h₃ h₄
  rw [p.start] at h₁ h₂
  rw [p.finish] at h₃ h₄
  exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩

end LPPDifferentiability
