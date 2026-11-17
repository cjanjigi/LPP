/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CalibratedPaths
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Total path weight equals the additive endpoint potential exactly when every
collected step is calibrated. -/

@[expose] public section

open LPPDifferentiability LPP.Busemann
open scoped BigOperators

namespace LPP.Busemann

/-- A path's collected weight equals its additive endpoint potential if and
only if every collected edge increment is calibrated by the site weight.
This is the finite equality case in the recovery argument of GRS
arXiv:1510.00860v1, Appendix A, proof of A.5. -/
theorem pathWeight_eq_cocycle_iff_calibrated
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ)
    (p : LPPDifferentiability.Path x d) :
    pathWeight ω p = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) ↔
      ∀ k : Fin (d.1 + d.2),
        C (p.vertex k.castSucc) (p.vertex k.succ) =
          ω (p.vertex k.castSucc) := by
  classical
  constructor
  · intro htotal
    let n : ℕ := d.1 + d.2
    let v : Fin (n + 1) → Lattice := fun i => p.vertex i
    have hstart : v 0 = x := by
      dsimp [v]
      exact p.start
    have hfinish :
        v (Fin.last n) = x + ((d.1 : ℤ), (d.2 : ℤ)) := by
      dsimp [v, n]
      exact p.finish
    change ∀ a b c : Lattice, C a b + C b c = C a c at hC
    change ∀ z : Lattice,
      min (C z (z + ((1 : ℤ), (0 : ℤ))))
        (C z (z + ((0 : ℤ), (1 : ℤ)))) = ω z at hrec

    have hEast (z : Lattice) :
        ω z ≤ C z (z + ((1 : ℤ), (0 : ℤ))) := by
      calc
        ω z = min (C z (z + ((1 : ℤ), (0 : ℤ))))
          (C z (z + ((0 : ℤ), (1 : ℤ)))) := (hrec z).symm
        _ ≤ C z (z + ((1 : ℤ), (0 : ℤ))) := min_le_left _ _
    have hNorth (z : Lattice) :
        ω z ≤ C z (z + ((0 : ℤ), (1 : ℤ))) := by
      calc
        ω z = min (C z (z + ((1 : ℤ), (0 : ℤ))))
          (C z (z + ((0 : ℤ), (1 : ℤ)))) := (hrec z).symm
        _ ≤ C z (z + ((0 : ℤ), (1 : ℤ))) := min_le_right _ _

    let defect : Fin n → ℝ := fun i =>
      C (v i.castSucc) (v i.succ) - ω (v i.castSucc)
    have hdefect_nonneg (i : Fin n) : 0 ≤ defect i := by
      change 0 ≤ C (p.vertex i.castSucc) (p.vertex i.succ) -
        ω (p.vertex i.castSucc)
      rcases p.step i with hstep | hstep
      · rw [hstep]
        exact sub_nonneg.mpr (hEast (p.vertex i.castSucc))
      · rw [hstep]
        exact sub_nonneg.mpr (hNorth (p.vertex i.castSucc))

    have hWeight :
        pathWeight ω p = ∑ i : Fin n, ω (v i.castSucc) := rfl
    have hPotential :
        (∑ i : Fin n, C (v i.castSucc) (v i.succ)) =
          C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
      calc
        _ = C (v 0) (v (Fin.last n)) :=
          LPP.finite_edge_potential_telescope n C hC v
        _ = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
          rw [hstart, hfinish]
    have hdefect_sum : (∑ i : Fin n, defect i) = 0 := by
      calc
        _ = (∑ i : Fin n, C (v i.castSucc) (v i.succ)) -
              pathWeight ω p := by
          rw [Finset.sum_sub_distrib, ← hWeight]
        _ = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) - pathWeight ω p := by
          rw [hPotential]
        _ = 0 := by
          rw [htotal]
          exact sub_self _
    have hdefect_zero :
        ∀ i : Fin n, defect i = 0 := by
      have hzero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => hdefect_nonneg i)).mp hdefect_sum
      intro i
      exact hzero i (Finset.mem_univ i)
    intro k
    have hk := hdefect_zero k
    exact sub_eq_zero.mp hk
  · intro hcal
    exact (calibrated_path_weight_eq_and_maximizing
      ω C hC hrec x d p hcal).1

end LPP.Busemann
