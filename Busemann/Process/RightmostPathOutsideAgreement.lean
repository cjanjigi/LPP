/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Process.RightmostPaths
import Lean.Elab.Tactic.Omega

/-! Agreement of rightmost cocycle paths inside an upper orthant.

This is the finite north-tail preservation step in Appendix A.4 of the cited
paper. The proof uses only the rightmost successor and its two unit
steps.
-/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- If two cocycles agree on every outgoing edge in an upper orthant, their
rightmost paths from any point in that orthant agree at every finite time.
Georgiou, Rassoul-Agha, and Seppäläinen, *Geodesics and the competition
interface for the corner growth model*, Appendix A.4, lines 1594–1599. -/
theorem rightmostCocyclePath_eq_of_upper_orthant_edge_eq
    (C D : Lattice → Lattice → ℝ) (a u : Lattice) (hau : a ≤ u)
    (hEdges : ∀ y : Lattice, a ≤ y → ∀ e : Fin 2,
      D y (y + finiteEdgeStep e) = C y (y + finiteEdgeStep e)) :
    ∀ n : ℕ, rightmostCocyclePath D u n = rightmostCocyclePath C u n := by
  -- Unfold one iterate to expose the east-or-north successor step.
  have path_step (B : Lattice → Lattice → ℝ) (z : Lattice) (n : ℕ) :
      rightmostCocyclePath B z (n + 1) = rightmostCocyclePath B z n + (1, 0) ∨
      rightmostCocyclePath B z (n + 1) = rightmostCocyclePath B z n + (0, 1) := by
    simpa [rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step B (rightmostCocyclePath B z n)

  -- Since every step increases one coordinate, the path stays above its start.
  have path_in_upper_orthant (B : Lattice → Lattice → ℝ) :
      ∀ n : ℕ, a ≤ rightmostCocyclePath B u n := by
    intro n
    induction n with
    | zero => simpa [rightmostCocyclePath] using hau
    | succ n ih =>
        rcases path_step B u n with hEast | hNorth
        · rw [hEast]
          rcases Prod.le_def.mp ih with ⟨ha1, ha2⟩
          change a.1 ≤ (rightmostCocyclePath B u n).1 + 1 ∧
            a.2 ≤ (rightmostCocyclePath B u n).2 + 0
          exact ⟨by omega, by omega⟩
        · rw [hNorth]
          rcases Prod.le_def.mp ih with ⟨ha1, ha2⟩
          change a.1 ≤ (rightmostCocyclePath B u n).1 + 0 ∧
            a.2 ≤ (rightmostCocyclePath B u n).2 + 1
          exact ⟨by omega, by omega⟩

  -- Agreement of both increments preserves the successor's tie-breaking choice.
  have successor_eq (y : Lattice) (hy : a ≤ y) :
      rightmostCocycleSuccessor D y = rightmostCocycleSuccessor C y := by
    have hEast : D y (y + (1, 0)) = C y (y + (1, 0)) := by
      simpa [finiteEdgeStep] using hEdges y hy (0 : Fin 2)
    have hNorth : D y (y + (0, 1)) = C y (y + (0, 1)) := by
      simpa [finiteEdgeStep] using hEdges y hy (1 : Fin 2)
    simp [rightmostCocycleSuccessor, hEast, hNorth]

  -- The paths start together; at each step their common vertex is in the orthant.
  intro n
  induction n with
  | zero => simp [rightmostCocyclePath]
  | succ n ih =>
      calc
        rightmostCocyclePath D u (n + 1) =
            rightmostCocycleSuccessor D (rightmostCocyclePath D u n) := by
          simp [rightmostCocyclePath, Function.iterate_succ_apply']
        _ = rightmostCocycleSuccessor D (rightmostCocyclePath C u n) := by rw [ih]
        _ = rightmostCocycleSuccessor C (rightmostCocyclePath C u n) :=
          successor_eq (rightmostCocyclePath C u n) (path_in_upper_orthant C n)
        _ = rightmostCocyclePath C u (n + 1) := by
          simp [rightmostCocyclePath, Function.iterate_succ_apply']

end LPP.Busemann
