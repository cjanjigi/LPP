/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge
import Busemann.Finite.DynamicProgramming
import Mathlib.Tactic.Linarith

/-! # Recovery at every active horizon of the actual finite construction -/

public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The minimum outgoing actual finite Busemann edge recovers the starting
weight at every active horizon, for arbitrary signed weights. This is
JR1810.03580v3 (4.14). -/
theorem finiteBusemannEdge_min_of_active
    (ω : Environment) (h : ℝ × ℝ) (x : Lattice) (n : ℤ) (hx : x.1 + x.2 < n) :
    min (finiteBusemannEdge ω h x n 0) (finiteBusemannEdge ω h x n 1) = ω x := by
  let P : ℝ := (finiteTiltedPotential ω h x n).toReal
  let R : ℝ := (finiteTiltedPotential ω h (x + (1, 0)) n).toReal
  let U : ℝ := (finiteTiltedPotential ω h (x + (0, 1)) n).toReal
  have hzero : finiteBusemannEdge ω h x n 0 = P - R - h.1 := by
    simp only [finiteBusemannEdge, dite_eq_left hx, finiteEdgeStep, finiteTiltCoordinate,
      Fin.val_zero, ite_true, P, R]
  have hone : finiteBusemannEdge ω h x n 1 = P - U - h.2 := by
    simp only [finiteBusemannEdge, dite_eq_left hx, finiteEdgeStep, finiteTiltCoordinate,
      Fin.val_one, one_ne_zero, ite_false, P, U]
  have hdp : P = ω x + max (h.1 + R) (h.2 + U) :=
    finiteTiltedPotential_toReal_outgoing ω h x n hx
  rw [hzero, hone]
  -- Whichever tilted child attains the maximum gives the recovering edge.
  rcases le_total (h.1 + R) (h.2 + U) with hle | hle
  · rw [max_eq_right hle] at hdp
    have hsecond : P - U - h.2 = ω x := by linarith only [hdp]
    have hfirst : ω x ≤ P - R - h.1 := by linarith only [hdp, hle]
    rw [hsecond, min_eq_right hfirst]
  · rw [max_eq_left hle] at hdp
    have hfirst : P - R - h.1 = ω x := by linarith only [hdp]
    have hsecond : ω x ≤ P - U - h.2 := by linarith only [hdp, hle]
    rw [hfirst, min_eq_left hsecond]

end LPP.Busemann
