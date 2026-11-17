/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Derivatives of finite sums of exponentials -/

public section

namespace ProbabilityBasics

/-- The derivative of a logarithmic finite exponential sum with affine terms is the
weighted average of their slopes. This is the finite calculus step in Janjigian,
Rassoul-Agha, and Seppäläinen, arXiv:1810.03580v3, Appendix A.1, proof of Lemma 4.11. -/
theorem hasDerivAt_log_sum_exp_affine {idx : Type*} [Fintype idx] [Nonempty idx]
    (beta : ℝ) (hbeta : 0 < beta) (a d : idx → ℝ) (t0 : ℝ) :
    HasDerivAt
      (fun t : ℝ => beta⁻¹ * Real.log (∑ j : idx, Real.exp (beta * (a j + t * d j))))
      ((∑ j : idx, d j * Real.exp (beta * (a j + t0 * d j))) /
        (∑ j : idx, Real.exp (beta * (a j + t0 * d j)))) t0 := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta
  let Z : ℝ → ℝ := fun t => ∑ j : idx, Real.exp (beta * (a j + t * d j))

  -- Differentiate each affine exponential term by the chain rule.
  have hZ : HasDerivAt Z
      (∑ j : idx, Real.exp (beta * (a j + t0 * d j)) * (beta * d j)) t0 := by
    dsimp [Z]
    apply HasDerivAt.fun_sum
    intro j _hj
    have hId : HasDerivAt (fun t : ℝ => t) 1 t0 := hasDerivAt_id' t0
    have hSlope : HasDerivAt (fun t : ℝ => t * d j) (1 * d j) t0 :=
      hId.mul_const (d j)
    have hAffine : HasDerivAt (fun t : ℝ => a j + t * d j) (1 * d j) t0 :=
      hSlope.const_add (a j)
    have hExponent : HasDerivAt (fun t : ℝ => beta * (a j + t * d j))
        (beta * d j) t0 := by
      simpa only [one_mul] using hAffine.const_mul beta
    exact hExponent.exp

  -- Positivity of the finite exponential sum permits differentiating its logarithm.
  have hsum_pos : 0 < ∑ j : idx, Real.exp (beta * (a j + t0 * d j)) := by
    exact Finset.sum_pos (fun j _hj => Real.exp_pos _) Finset.univ_nonempty
  have hZpos : 0 < Z t0 := by
    simpa only [Z] using hsum_pos
  have hlog : HasDerivAt (fun t : ℝ => Real.log (Z t))
      ((∑ j : idx, Real.exp (beta * (a j + t0 * d j)) * (beta * d j)) / Z t0) t0 :=
    hZ.log (ne_of_gt hZpos)
  have hscaled := hlog.const_mul beta⁻¹

  -- Factor beta from the numerator and cancel it with the outside beta inverse.
  have hfactor :
      (∑ j : idx, Real.exp (beta * (a j + t0 * d j)) * (beta * d j)) =
        beta * (∑ j : idx, d j * Real.exp (beta * (a j + t0 * d j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hweighted :
      beta⁻¹ *
          ((∑ j : idx, Real.exp (beta * (a j + t0 * d j)) * (beta * d j)) /
            (∑ j : idx, Real.exp (beta * (a j + t0 * d j)))) =
        (∑ j : idx, d j * Real.exp (beta * (a j + t0 * d j))) /
          (∑ j : idx, Real.exp (beta * (a j + t0 * d j))) := by
    calc
      beta⁻¹ *
          ((∑ j : idx, Real.exp (beta * (a j + t0 * d j)) * (beta * d j)) /
            (∑ j : idx, Real.exp (beta * (a j + t0 * d j)))) =
          beta⁻¹ *
            (beta *
              ((∑ j : idx, d j * Real.exp (beta * (a j + t0 * d j))) /
                (∑ j : idx, Real.exp (beta * (a j + t0 * d j))))) := by
        rw [hfactor, mul_div_assoc]
      _ = (beta⁻¹ * beta) *
            ((∑ j : idx, d j * Real.exp (beta * (a j + t0 * d j))) /
              (∑ j : idx, Real.exp (beta * (a j + t0 * d j)))) := by rw [mul_assoc]
      _ = (∑ j : idx, d j * Real.exp (beta * (a j + t0 * d j))) /
            (∑ j : idx, Real.exp (beta * (a j + t0 * d j))) := by simp [hbeta_ne]
  simpa only [Z, hweighted] using hscaled

end ProbabilityBasics
