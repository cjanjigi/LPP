/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The two finite edge sums around an active unit square agree, by cancellation
of the endpoint potentials in the finite construction (JR1810.03580v3). -/
theorem finiteBusemannEdge_square (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) (hn : x.1 + x.2 + 1 < n) (i j : Fin 2) :
    finiteBusemannEdge ω h x n i +
        finiteBusemannEdge ω h (x + finiteEdgeStep i) n j =
      finiteBusemannEdge ω h x n j +
        finiteBusemannEdge ω h (x + finiteEdgeStep j) n i := by
  have hsource : x.1 + x.2 < n := by omega
  have hstep (k : Fin 2) :
      x.1 + (finiteEdgeStep k).1 + (x.2 + (finiteEdgeStep k).2) < n := by
    have hlevel :
        x.1 + (finiteEdgeStep k).1 + (x.2 + (finiteEdgeStep k).2) =
          x.1 + x.2 + 1 := by
      simp [finiteEdgeStep]
      split_ifs <;> omega
    omega
  have hi := hstep i
  have hj := hstep j
  have hterminal :
      x + finiteEdgeStep i + finiteEdgeStep j =
        x + finiteEdgeStep j + finiteEdgeStep i := by
    calc
      x + finiteEdgeStep i + finiteEdgeStep j =
          x + (finiteEdgeStep i + finiteEdgeStep j) := by rw [add_assoc]
      _ = x + (finiteEdgeStep j + finiteEdgeStep i) :=
        congrArg (fun y : Lattice => x + y) (add_comm _ _)
      _ = x + finiteEdgeStep j + finiteEdgeStep i := by rw [← add_assoc]
  have hbase_i :
      finiteBusemannEdge ω h x n i =
        (finiteTiltedPotential ω h x n).toReal -
          (finiteTiltedPotential ω h (x + finiteEdgeStep i) n).toReal -
          finiteTiltCoordinate h i := by
    simp [finiteBusemannEdge, hsource]
  have hmiddle_i :
      finiteBusemannEdge ω h (x + finiteEdgeStep i) n j =
        (finiteTiltedPotential ω h (x + finiteEdgeStep i) n).toReal -
          (finiteTiltedPotential ω h (x + finiteEdgeStep i + finiteEdgeStep j) n).toReal -
          finiteTiltCoordinate h j := by
    simp [finiteBusemannEdge, hi]
  have hbase_j :
      finiteBusemannEdge ω h x n j =
        (finiteTiltedPotential ω h x n).toReal -
          (finiteTiltedPotential ω h (x + finiteEdgeStep j) n).toReal -
          finiteTiltCoordinate h j := by
    simp [finiteBusemannEdge, hsource]
  have hmiddle_j :
      finiteBusemannEdge ω h (x + finiteEdgeStep j) n i =
        (finiteTiltedPotential ω h (x + finiteEdgeStep j) n).toReal -
          (finiteTiltedPotential ω h (x + finiteEdgeStep j + finiteEdgeStep i) n).toReal -
          finiteTiltCoordinate h i := by
    simp [finiteBusemannEdge, hj]
  rw [hbase_i, hmiddle_i, hbase_j, hmiddle_j, hterminal]
  ring

end LPP.Busemann
