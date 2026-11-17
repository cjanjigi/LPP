/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.PathTotalCalibration
public import Busemann.Frozen.Definitions.RightmostCocycleSuccessor
import LPP_Foundations.Model.Paths.WeightBounds
import LPP_Foundations.Model.RecoveryAntidiagonal
import Mathlib.Tactic

/-! Calibration transfer and the fixed east-tie contradiction. -/

@[expose] public section

open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- A chosen north edge cannot coexist with calibration of the east edge
under the same recovering cocycle, because ties choose east. -/
theorem rightmost_north_step_conflicts_east_calibration
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hrec : recovers_environment ω C) (z : Lattice)
    (hNorth : rightmostCocycleSuccessor C z = z + ((0 : ℤ), (1 : ℤ)))
    (hEastCal : C z (z + ((1 : ℤ), (0 : ℤ))) = ω z) : False := by
  have hNotEast :
      ¬ C z (z + ((1 : ℤ), (0 : ℤ))) ≤
        C z (z + ((0 : ℤ), (1 : ℤ))) := by
    intro hEast
    have hChooseEast :
        rightmostCocycleSuccessor C z = z + ((1 : ℤ), (0 : ℤ)) := by
      simp [rightmostCocycleSuccessor, hEast]
    have hxy := congrArg Prod.fst (hChooseEast.symm.trans hNorth)
    simp at hxy
  have hNorthStrict :
      C z (z + ((0 : ℤ), (1 : ℤ))) <
        C z (z + ((1 : ℤ), (0 : ℤ))) :=
    lt_of_not_ge hNotEast
  have hMin :
      min (C z (z + ((1 : ℤ), (0 : ℤ))))
        (C z (z + ((0 : ℤ), (1 : ℤ)))) =
          C z (z + ((1 : ℤ), (0 : ℤ))) := by
    calc
      _ = ω z := hrec z
      _ = C z (z + ((1 : ℤ), (0 : ℤ))) := hEastCal.symm
  have hEastLeNorth :
      C z (z + ((1 : ℤ), (0 : ℤ))) ≤
        C z (z + ((0 : ℤ), (1 : ℤ))) := by
    calc
      C z (z + ((1 : ℤ), (0 : ℤ))) =
          min (C z (z + ((1 : ℤ), (0 : ℤ))))
            (C z (z + ((0 : ℤ), (1 : ℤ)))) := hMin.symm
      _ ≤ C z (z + ((0 : ℤ), (1 : ℤ))) := min_le_right _ _
  exact (not_le_of_gt hNorthStrict) hEastLeNorth

end LPP.Busemann
