/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
public import LPP_Foundations.Model.Paths.Fintype
public import LPP_Foundations.Model.Paths.Nonempty
public import ProbabilityBasics.Analysis.FiniteLogSumExp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! The derivative of the actual finite tilted path partition. -/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- The derivative of the actual normalized log partition is the
partition-weighted east-step count; see JR1810.03580v3, proof of Lemma 4.11. -/
theorem hasDerivAt_finite_tilted_partition_east_count
    (ω : Environment) (h : ℝ × ℝ) (β : ℝ) (hβ : 0 < β) (N : ℕ) (x : Lattice) :
    let Z : ℝ → ℝ := fun t =>
      ∑ k : Fin (N + 1), ∑ p : LPPDifferentiability.Path x (k.val, N - k.val),
        Real.exp (β * (pathWeight ω p + (h.1 + t) * (k.val : ℝ) +
          h.2 * ((N - k.val : ℕ) : ℝ)))
    let M : ℝ := (∑ k : Fin (N + 1),
      ∑ p : LPPDifferentiability.Path x (k.val, N - k.val),
        (k.val : ℝ) * Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
          h.2 * ((N - k.val : ℕ) : ℝ)))) / Z 0
    HasDerivAt (fun t : ℝ => Real.log (Z t) / β) M 0 := by
  classical
  let Z : ℝ → ℝ := fun t =>
    ∑ k : Fin (N + 1), ∑ p : LPPDifferentiability.Path x (k.val, N - k.val),
      Real.exp (β * (pathWeight ω p + (h.1 + t) * (k.val : ℝ) +
        h.2 * ((N - k.val : ℕ) : ℝ)))
  let M : ℝ := (∑ k : Fin (N + 1),
    ∑ p : LPPDifferentiability.Path x (k.val, N - k.val),
      (k.val : ℝ) * Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
        h.2 * ((N - k.val : ℕ) : ℝ)))) / Z 0
  change HasDerivAt (fun t : ℝ => Real.log (Z t) / β) M 0
  let I := Σ k : Fin (N + 1), LPPDifferentiability.Path x (k.val, N - k.val)
  let k0 : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
  let : Nonempty I := ⟨⟨k0, Classical.choice (inferInstance :
    Nonempty (LPPDifferentiability.Path x (k0.val, N - k0.val)))⟩⟩
  let a : I → ℝ := fun q => pathWeight ω q.2 + h.1 * (q.1.val : ℝ) +
    h.2 * ((N - q.1.val : ℕ) : ℝ)
  let d : I → ℝ := fun q => (q.1.val : ℝ)
  have hZ (t : ℝ) : (∑ q : I, Real.exp (β * (a q + t * d q))) = Z t := by
    rw [Fintype.sum_sigma]
    dsimp only [Z, a, d]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    congr 2
    ring
  have hNumerator : (∑ q : I, d q * Real.exp (β * (a q + 0 * d q))) =
      ∑ k : Fin (N + 1), ∑ p : LPPDifferentiability.Path x (k.val, N - k.val),
        (k.val : ℝ) * Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
          h.2 * ((N - k.val : ℕ) : ℝ))) := by
    rw [Fintype.sum_sigma]
    simp only [a, d, zero_mul, add_zero]
  have hfun : (fun t : ℝ => β⁻¹ * Real.log (∑ q : I, Real.exp (β * (a q + t * d q)))) =
      (fun t : ℝ => Real.log (Z t) / β) := by
    funext t
    rw [hZ]
    rw [div_eq_mul_inv, mul_comm]
  have hderiv := ProbabilityBasics.hasDerivAt_log_sum_exp_affine β hβ a d 0
  rw [hfun, hNumerator, hZ 0] at hderiv
  exact hderiv

end LPP.Busemann
