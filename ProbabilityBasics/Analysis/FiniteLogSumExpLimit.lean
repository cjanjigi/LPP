/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Order.Field

/-!
# Finite log-sum-exp limit

For finitely many real energies, the normalized logarithm of their exponential sum
converges to the largest energy as the real parameter tends to infinity.
-/

public section

open Filter
open scoped BigOperators

namespace ProbabilityBasics

private theorem finite_log_sum_exp_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    Finset.univ.sup' Finset.univ_nonempty a ≤
        β⁻¹ * Real.log (∑ j : ι, Real.exp (β * a j)) ∧
      β⁻¹ * Real.log (∑ j : ι, Real.exp (β * a j)) ≤
        Finset.univ.sup' Finset.univ_nonempty a +
          Real.log (Fintype.card ι : ℝ) * β⁻¹ := by
  classical
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty a
  let Z : ℝ := ∑ j : ι, Real.exp (β * a j)
  change M ≤ β⁻¹ * Real.log Z ∧
    β⁻¹ * Real.log Z ≤ M + Real.log (Fintype.card ι : ℝ) * β⁻¹
  have hmax (j : ι) : a j ≤ M := by
    dsimp [M]
    exact Finset.le_sup' a (Finset.mem_univ j)
  obtain ⟨i, hi, hMi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty a
  have hsum_lower : Real.exp (β * M) ≤ Z := by
    dsimp [Z, M]
    rw [hMi]
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos (β * a j)).le) hi
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hsum_lower
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsum_upper : Z ≤ (Fintype.card ι : ℝ) * Real.exp (β * M) := by
    calc
      Z = ∑ j : ι, Real.exp (β * a j) := rfl
      _ ≤ ∑ j : ι, Real.exp (β * M) := by
        apply Finset.sum_le_sum
        intro j _
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (hmax j) hβ.le
      _ = (Fintype.card ι : ℝ) * Real.exp (β * M) := by simp
  have hlog_lower : β * M ≤ Real.log Z := by
    calc
      β * M = Real.log (Real.exp (β * M)) := (Real.log_exp _).symm
      _ ≤ Real.log Z := Real.log_le_log (Real.exp_pos _) hsum_lower
  have hlog_upper : Real.log Z ≤ Real.log (Fintype.card ι : ℝ) + β * M := by
    calc
      Real.log Z ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (β * M)) :=
        Real.log_le_log hZpos hsum_upper
      _ = Real.log (Fintype.card ι : ℝ) + β * M := by
        rw [Real.log_mul (ne_of_gt hcard_pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hcancel : β⁻¹ * (β * M) = M := by
    rw [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
  constructor
  · calc
      M = β⁻¹ * (β * M) := hcancel.symm
      _ ≤ β⁻¹ * Real.log Z :=
        mul_le_mul_of_nonneg_left hlog_lower (inv_nonneg.mpr hβ.le)
  · calc
      β⁻¹ * Real.log Z ≤ β⁻¹ * (Real.log (Fintype.card ι : ℝ) + β * M) :=
        mul_le_mul_of_nonneg_left hlog_upper (inv_nonneg.mpr hβ.le)
      _ = M + Real.log (Fintype.card ι : ℝ) * β⁻¹ := by
        calc
          β⁻¹ * (Real.log (Fintype.card ι : ℝ) + β * M) =
              β⁻¹ * Real.log (Fintype.card ι : ℝ) + β⁻¹ * (β * M) := by rw [mul_add]
          _ = β⁻¹ * Real.log (Fintype.card ι : ℝ) + M := by rw [hcancel]
          _ = M + Real.log (Fintype.card ι : ℝ) * β⁻¹ := by rw [add_comm, mul_comm]

/-- For finitely many real energies, the normalized logarithm of their exponential sum
converges to the largest energy as the real parameter tends to infinity. This is the finite estimate
step in Lemma 4.11, Appendix A.1, of JR1810.03580v3. -/
theorem tendsto_log_sum_exp_div_atTop {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) :
    Tendsto
      (fun β : ℝ => β⁻¹ * Real.log (∑ j : ι, Real.exp (β * a j)))
      atTop (nhds (Finset.univ.sup' Finset.univ_nonempty a)) := by
  classical
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty a
  change Tendsto
    (fun β : ℝ => β⁻¹ * Real.log (∑ j : ι, Real.exp (β * a j)))
    atTop (nhds M)
  have herror : Tendsto
      (fun β : ℝ => Real.log (Fintype.card ι : ℝ) * β⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul (Real.log (Fintype.card ι : ℝ)) tendsto_inv_atTop_zero
  have hconstant : Tendsto (fun _ : ℝ => M) atTop (nhds M) := tendsto_const_nhds
  have hupper : Tendsto
      (fun β : ℝ => M + Real.log (Fintype.card ι : ℝ) * β⁻¹) atTop (nhds M) := by
    simpa only [add_zero] using hconstant.add herror
  refine Filter.Tendsto.squeeze' hconstant hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact (finite_log_sum_exp_bounds a hβ).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact (finite_log_sum_exp_bounds a hβ).2

end ProbabilityBasics
