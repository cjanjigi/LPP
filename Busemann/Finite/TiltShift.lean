/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Finite.PartitionRecursion
public import Busemann.Frozen.Definitions.FiniteTiltCoordinate
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Common shifts of both tilt coordinates for the actual finite path sum. -/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- Adding the same constant to both tilt coordinates factors the actual
finite path partition, shifts its log free energy, and cancels from normalized
edge differences. This is the finite tilt comparison in JR
arXiv:1810.03580v3, Appendix A.1. -/
theorem finite_tilted_partition_equal_tilt_shift
    (ω : Environment) (h : ℝ × ℝ) (c β : ℝ) (hβ : 0 < β) :
    let Z : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y =>
      ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
        Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
          u.2 * ((n - k.val : ℕ) : ℝ)))
    let F : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y => Real.log (Z u n y) / β
    let hprime : ℝ × ℝ := (h.1 + c, h.2 + c)
    (∀ n y, Z hprime n y = Real.exp (β * c * (n : ℝ)) * Z h n y) ∧
      (∀ n y, F hprime n y = F h n y + c * (n : ℝ)) ∧
      (∀ N x i,
        F hprime (N + 1) x - F hprime N (x + finiteEdgeStep i) -
            finiteTiltCoordinate hprime i =
          F h (N + 1) x - F h N (x + finiteEdgeStep i) -
            finiteTiltCoordinate h i) := by
  classical
  let Z : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y =>
    ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
      Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
        u.2 * ((n - k.val : ℕ) : ℝ)))
  let F : (ℝ × ℝ) → ℕ → Lattice → ℝ := fun u n y => Real.log (Z u n y) / β
  let hprime : ℝ × ℝ := (h.1 + c, h.2 + c)
  change (∀ n y, Z hprime n y = Real.exp (β * c * (n : ℝ)) * Z h n y) ∧
      (∀ n y, F hprime n y = F h n y + c * (n : ℝ)) ∧
      (∀ N x i,
        F hprime (N + 1) x - F hprime N (x + finiteEdgeStep i) -
            finiteTiltCoordinate hprime i =
          F h (N + 1) x - F h N (x + finiteEdgeStep i) -
            finiteTiltCoordinate h i)
  have hcount (n : ℕ) (k : Fin (n + 1)) :
      (k.val : ℝ) + ((n - k.val : ℕ) : ℝ) = (n : ℝ) := by
    have hk : k.val + (n - k.val) = n := by omega
    exact_mod_cast hk
  have hpartition (u : ℝ × ℝ) (n : ℕ) (y : Lattice) :
      Z (u.1 + c, u.2 + c) n y = Real.exp (β * c * (n : ℝ)) * Z u n y := by
    dsimp only [Z]
    calc
      (∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
          Real.exp (β * (pathWeight ω p + (u.1 + c) * (k.val : ℝ) +
            (u.2 + c) * ((n - k.val : ℕ) : ℝ)))) =
        ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
          Real.exp (β * c * (n : ℝ)) *
            Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
              u.2 * ((n - k.val : ℕ) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro p hp
        have henergy :
            β * (pathWeight ω p + (u.1 + c) * (k.val : ℝ) +
              (u.2 + c) * ((n - k.val : ℕ) : ℝ)) =
              β * c * (n : ℝ) +
                β * (pathWeight ω p + u.1 * (k.val : ℝ) +
                  u.2 * ((n - k.val : ℕ) : ℝ)) := by
          rw [← hcount n k]
          ring
        rw [henergy, Real.exp_add]
      _ = Real.exp (β * c * (n : ℝ)) *
          (∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
            Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
              u.2 * ((n - k.val : ℕ) : ℝ)))) := by
        calc
          (∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
              Real.exp (β * c * (n : ℝ)) *
                Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
                  u.2 * ((n - k.val : ℕ) : ℝ)))) =
            ∑ k : Fin (n + 1), Real.exp (β * c * (n : ℝ)) *
              (∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
                Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
                  u.2 * ((n - k.val : ℕ) : ℝ)))) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact (Finset.mul_sum Finset.univ
              (fun p : LPPDifferentiability.Path y (k.val, n - k.val) =>
                Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
                  u.2 * ((n - k.val : ℕ) : ℝ)))) (Real.exp (β * c * (n : ℝ)))).symm
          _ = Real.exp (β * c * (n : ℝ)) *
              (∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
                Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
                  u.2 * ((n - k.val : ℕ) : ℝ)))) :=
            (Finset.mul_sum Finset.univ
              (fun k : Fin (n + 1) =>
                ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
                  Real.exp (β * (pathWeight ω p + u.1 * (k.val : ℝ) +
                    u.2 * ((n - k.val : ℕ) : ℝ)))) (Real.exp (β * c * (n : ℝ)))).symm
  have hpositive (u : ℝ × ℝ) (n : ℕ) (y : Lattice) : 0 < Z u n y := by
    have hpos := (finite_tilted_partition_zero_pos_succ ω u β hβ n y).2.1
    exact hpos
  have hfree (n : ℕ) (y : Lattice) :
      F hprime n y = F h n y + c * (n : ℝ) := by
    change Real.log (Z hprime n y) / β = Real.log (Z h n y) / β + c * (n : ℝ)
    calc
      Real.log (Z hprime n y) / β =
          Real.log (Real.exp (β * c * (n : ℝ)) * Z h n y) / β := by
        rw [hpartition]
      _ = (β * c * (n : ℝ) + Real.log (Z h n y)) / β := by
        rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (hpositive h n y)), Real.log_exp]
      _ = Real.log (Z h n y) / β + c * (n : ℝ) := by
        field_simp [ne_of_gt hβ]
        ring
  have hcoordinate (i : Fin 2) :
      finiteTiltCoordinate hprime i = finiteTiltCoordinate h i + c := by
    fin_cases i <;> simp [finiteTiltCoordinate, hprime]
  refine ⟨?_, ?_, ?_⟩
  · intro n y
    exact hpartition h n y
  · intro n y
    exact hfree n y
  · intro N x i
    rw [hfree (N + 1) x, hfree N (x + finiteEdgeStep i), hcoordinate i]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

end LPP.Busemann
