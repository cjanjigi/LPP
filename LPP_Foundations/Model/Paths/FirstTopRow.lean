/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Split
import Mathlib.Data.Finset.Max

/-! Finite-path first visits to the top row. -/

@[expose] public section

namespace LPPDifferentiability
namespace Path

/-- Every up-right path has a first vertex on its endpoint's top row, and the
split there has the full vertical displacement (GRS 1510.00859v2, Section 5.2,
equation (6.8)). -/
theorem exists_first_top_row_vertex
    {u : Lattice} {d : ℕ × ℕ} (p : LPPDifferentiability.Path u d) :
    ∃ j : Fin (d.1 + d.2 + 1),
      (p.vertex j).2 = u.2 + (d.2 : ℤ) ∧
      (∀ i : Fin (d.1 + d.2 + 1), i < j →
        (p.vertex i).2 < u.2 + (d.2 : ℤ)) ∧
      (p.splitDisplacement j).2 = d.2 := by
  let topIndices : Finset (Fin (d.1 + d.2 + 1)) :=
    Finset.univ.filter fun i => (p.vertex i).2 = u.2 + (d.2 : ℤ)
  -- The actual terminal vertex lies on the top row by `Path.finish`.
  have terminal_mem : Fin.last (d.1 + d.2) ∈ topIndices := by
    simp only [topIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [p.finish]
    rfl
  have topIndices_nonempty : topIndices.Nonempty :=
    ⟨Fin.last (d.1 + d.2), terminal_mem⟩
  -- The minimum is taken over the original `Fin` indices of this path.
  let j : Fin (d.1 + d.2 + 1) := topIndices.min' topIndices_nonempty
  have j_mem : j ∈ topIndices := by
    dsimp only [j]
    exact Finset.min'_mem topIndices topIndices_nonempty
  have j_on_top : (p.vertex j).2 = u.2 + (d.2 : ℤ) := by
    simpa only [topIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      using j_mem
  refine ⟨j, j_on_top, ?_, ?_⟩
  · intro i hij
    -- Any earlier top-row index would contradict the minimum property.
    have i_not_on_top : (p.vertex i).2 ≠ u.2 + (d.2 : ℤ) := by
      intro hi_top
      have i_mem : i ∈ topIndices := by
        simpa only [topIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          using hi_top
      have j_le_i : j ≤ i := by
        dsimp only [j]
        exact Finset.min'_le topIndices i i_mem
      omega
    -- The endpoint rectangle bounds every vertex above by the top row.
    have i_le_top : (p.vertex i).2 ≤ u.2 + (d.2 : ℤ) := by
      have h := (p.vertex_mem_Icc i).2.2
      simpa only [Prod.snd_add] using h
    omega
  · -- The split-coordinate identity turns the top-row equality into `d.2`.
    have hsplit := p.splitDisplacement_snd_cast j
    rw [j_on_top] at hsplit
    omega

end Path
end LPPDifferentiability
