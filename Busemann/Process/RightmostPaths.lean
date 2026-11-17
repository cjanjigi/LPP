/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.RightmostCocyclePath
public import Busemann.Process.ArrowCalibration

/-! Finite path and weight facts for the rightmost cocycle path. -/

@[expose] public section
open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- The successor takes exactly one east or north step.
Strong Existence, lines 423–427. -/
theorem rightmostCocycleSuccessor_step
    (C : Lattice → Lattice → ℝ) (x : Lattice) :
    rightmostCocycleSuccessor C x = x + ((1 : ℤ), (0 : ℤ)) ∨
      rightmostCocycleSuccessor C x = x + ((0 : ℤ), (1 : ℤ)) := by
  classical
  by_cases h : C x (x + ((1 : ℤ), (0 : ℤ))) ≤
      C x (x + ((0 : ℤ), (1 : ℤ)))
  · left
    simp [rightmostCocycleSuccessor, h]
  · right
    simp [rightmostCocycleSuccessor, h]

/-- Pointwise recovery calibrates the edge chosen by the rightmost successor,
including its east choice when the two increments tie.
Strong Existence, lines 423–427. -/
theorem rightmostCocycleSuccessor_calibrated
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hrec : recovers_environment ω C) (x : Lattice) :
    C x (rightmostCocycleSuccessor C x) = ω x := by
  classical
  by_cases h : C x (x + ((1 : ℤ), (0 : ℤ))) ≤
      C x (x + ((0 : ℤ), (1 : ℤ)))
  · have hleft :
        min (C x (x + ((1 : ℤ), (0 : ℤ))))
            (C x (x + ((0 : ℤ), (1 : ℤ)))) =
          C x (x + ((1 : ℤ), (0 : ℤ))) := min_eq_left h
    calc
      C x (rightmostCocycleSuccessor C x) =
          C x (x + ((1 : ℤ), (0 : ℤ))) := by
        simp [rightmostCocycleSuccessor, h]
      _ = min (C x (x + ((1 : ℤ), (0 : ℤ))))
            (C x (x + ((0 : ℤ), (1 : ℤ)))) := hleft.symm
      _ = ω x := hrec x
  · have hvertical :
        C x (x + ((0 : ℤ), (1 : ℤ))) ≤
          C x (x + ((1 : ℤ), (0 : ℤ))) :=
      le_of_lt (not_le.mp h)
    have hright :
        min (C x (x + ((1 : ℤ), (0 : ℤ))))
            (C x (x + ((0 : ℤ), (1 : ℤ)))) =
          C x (x + ((0 : ℤ), (1 : ℤ))) := min_eq_right hvertical
    calc
      C x (rightmostCocycleSuccessor C x) =
          C x (x + ((0 : ℤ), (1 : ℤ))) := by
        simp [rightmostCocycleSuccessor, h]
      _ = min (C x (x + ((1 : ℤ), (0 : ℤ))))
            (C x (x + ((0 : ℤ), (1 : ℤ)))) := hright.symm
      _ = ω x := hrec x

/-- Every finite prefix of the rightmost path is calibrated and
maximizes last passage, with one path carrying its full iterate trace and
potential weight. GRS, arXiv:1510.00860v1, Appendix A, lines 1481–1489;
Strong Existence, lines 430–438. -/
theorem exists_rightmostCocyclePath_prefix
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (N : ℕ) :
    ∃ q : Sigma (fun k : Fin (N + 1) =>
      LPPDifferentiability.Path x (k.val, N - k.val)),
      (∀ j : ℕ, ∀ hj : j < q.1.val + (N - q.1.val) + 1,
        q.2.vertex ⟨j, hj⟩ = rightmostCocyclePath C x j) ∧
        pathWeight ω q.2 = C x (rightmostCocyclePath C x N) ∧
        pathWeight ω q.2 =
          lastPassage ω x (q.1.val, N - q.1.val) := by
  have hstep : ∀ z,
      rightmostCocycleSuccessor C z = z + ((1 : ℤ), (0 : ℤ)) ∨
        rightmostCocycleSuccessor C z = z + ((0 : ℤ), (1 : ℤ)) :=
    rightmostCocycleSuccessor_step C
  have hcal : ∀ z,
      C z (rightmostCocycleSuccessor C z) = ω z :=
    rightmostCocycleSuccessor_calibrated ω C hrec
  simpa only [rightmostCocyclePath] using
    (exists_calibrated_arrow_iterate_path ω C hC hrec
      (rightmostCocycleSuccessor C) hstep hcal x N)

end LPP.Busemann
