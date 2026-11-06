/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended-real limits under vanishing real perturbations

The upper and lower limits may be plus or minus infinity.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- A real perturbation tending to zero preserves the extended-real upper limit. -/
theorem limsup_coe_eq_of_tendsto_sub_zero {u v : ℕ → ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    limsup (fun n => (u n : EReal)) atTop =
      limsup (fun n => (v n : EReal)) atTop := by
  have he : Tendsto (fun n => ((u n - v n : ℝ) : EReal)) atTop (𝓝 0) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr h
  have hs : limsup (fun n => ((u n - v n : ℝ) : EReal)) atTop = 0 := he.limsup_eq
  have hi : liminf (fun n => ((u n - v n : ℝ) : EReal)) atTop = 0 := he.liminf_eq
  have hid : (fun n => (u n : EReal)) =
      (fun n => (v n : EReal)) + (fun n => ((u n - v n : ℝ) : EReal)) := by
    funext n
    simp only [Pi.add_apply, ← EReal.coe_add, add_sub_cancel]
  rw [hid]
  apply le_antisymm
  · simpa only [hs, add_zero] using EReal.limsup_add_le
      (u := fun n => (v n : EReal))
      (v := fun n => ((u n - v n : ℝ) : EReal))
      (f := atTop) (Or.inr (by rw [hs]; exact EReal.zero_ne_top))
      (Or.inr (by rw [hs]; exact EReal.zero_ne_bot))
  · simpa only [hi, add_zero] using EReal.le_limsup_add
      (u := fun n => (v n : EReal))
      (v := fun n => ((u n - v n : ℝ) : EReal)) (f := atTop)

/-- A real perturbation tending to zero preserves the extended-real lower limit. -/
theorem liminf_coe_eq_of_tendsto_sub_zero {u v : ℕ → ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    liminf (fun n => (u n : EReal)) atTop =
      liminf (fun n => (v n : EReal)) atTop := by
  have hn : Tendsto (fun n => -u n - -v n) atTop (𝓝 0) := by
    simpa only [neg_sub_neg, neg_sub, neg_zero] using h.neg
  have heq := limsup_coe_eq_of_tendsto_sub_zero hn
  have hneg : -(liminf (fun n => (u n : EReal)) atTop) =
      -(liminf (fun n => (v n : EReal)) atTop) := by
    simpa only [EReal.coe_neg, ← Pi.neg_def, EReal.limsup_neg] using heq
  exact neg_injective hneg

end LPPDifferentiability
