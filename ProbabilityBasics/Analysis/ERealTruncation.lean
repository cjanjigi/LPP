/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Finite truncations of nonnegative extended reals

The finite truncations used in the nonnegative upper-limit step of Keane and
Petersen (arXiv:math/0608251, page 250). No finiteness of the untruncated
extended real is required.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability
namespace ERealTruncation

/-- Nonnegative extended reals, including positive infinity. -/
abbrev Nonnegative := {u : EReal // 0 ≤ u}

/-- Finite real truncation at a finite nonnegative level. -/
@[expose] noncomputable def trunc (u : Nonnegative) (r : NNReal) : ℝ :=
  (min u.val (r : ℝ)).toReal

theorem min_nonneg (u : Nonnegative) (r : NNReal) :
    0 ≤ min u.val ((r : ℝ) : EReal) :=
  le_min u.property (EReal.coe_nonneg.mpr r.property)

theorem min_ne_top (u : Nonnegative) (r : NNReal) :
    min u.val ((r : ℝ) : EReal) ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (min_le_right _ _)

theorem min_ne_bot (u : Nonnegative) (r : NNReal) :
    min u.val ((r : ℝ) : EReal) ≠ ⊥ :=
  ne_bot_of_le_ne_bot EReal.zero_ne_bot (min_nonneg u r)

@[simp] theorem coe_trunc (u : Nonnegative) (r : NNReal) :
    (trunc u r : EReal) = min u.val ((r : ℝ) : EReal) :=
  EReal.coe_toReal (min_ne_top u r) (min_ne_bot u r)

theorem trunc_nonneg (u : Nonnegative) (r : NNReal) : 0 ≤ trunc u r :=
  EReal.toReal_nonneg (min_nonneg u r)

theorem trunc_le (u : Nonnegative) (r : NNReal) : trunc u r ≤ r := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_trunc]
  exact min_le_right _ _

@[simp] theorem trunc_coe (a r : NNReal) :
    trunc ⟨(a : ℝ), EReal.coe_nonneg.mpr a.property⟩ r = min (a : ℝ) (r : ℝ) := by
  apply EReal.coe_injective
  rw [coe_trunc, EReal.coe_strictMono.monotone.map_min]

@[simp] theorem trunc_top (r : NNReal) : trunc ⟨⊤, le_top⟩ r = r := by
  apply EReal.coe_injective
  simp only [coe_trunc, min_eq_right (le_top : ((r : ℝ) : EReal) ≤ ⊤)]

@[simp] theorem trunc_zero (u : Nonnegative) : trunc u 0 = 0 := by
  apply EReal.coe_injective
  simp only [coe_trunc, NNReal.coe_zero, EReal.coe_zero, min_eq_right u.property]

@[simp] theorem trunc_zero_left (r : NNReal) : trunc ⟨0, le_rfl⟩ r = 0 := by
  apply EReal.coe_injective
  rw [coe_trunc]
  change min (0 : EReal) ((r : ℝ) : EReal) = 0
  exact min_eq_left (EReal.coe_nonneg.mpr r.property)

/-- Continuity holds on the entire public carrier, including at positive infinity. -/
theorem continuous_trunc (r : NNReal) : Continuous (fun u : Nonnegative => trunc u r) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact (EReal.tendsto_toReal (min_ne_top u r) (min_ne_bot u r)).comp
    ((continuous_subtype_val.min continuous_const).continuousAt)

theorem measurable_trunc (r : NNReal) : Measurable (fun u : Nonnegative => trunc u r) :=
  (continuous_trunc r).measurable

/-- Composition with an everywhere nonnegative measurable extended-real function. -/
theorem measurable_trunc_comp {α : Type*} [MeasurableSpace α] {f : α → EReal}
    (hf : Measurable f) (h : ∀ x, 0 ≤ f x) (r : NNReal) :
    Measurable (fun x => trunc ⟨f x, h x⟩ r) :=
  (measurable_trunc r).comp (hf.subtype_mk (h := h))

/-- The positive integer level indexed by `n` is `n+1`. -/
@[expose] def level (n : ℕ) : NNReal := ⟨(n : ℝ) + 1, by positivity⟩

theorem monotone_trunc_level (u : Nonnegative) : Monotone (fun n => trunc u (level n)) := by
  intro m n hmn
  apply EReal.coe_le_coe_iff.mp
  rw [coe_trunc, coe_trunc]
  apply min_le_min_left
  apply EReal.coe_le_coe_iff.mpr
  change (m : ℝ) + 1 ≤ (n : ℝ) + 1
  exact add_le_add (Nat.cast_le.mpr hmn : (m : ℝ) ≤ (n : ℝ)) (le_rfl : (1 : ℝ) ≤ 1)

/-- Coerced real truncations converge even when the extended-real argument is infinite. -/
theorem tendsto_coe_trunc_level (u : Nonnegative) :
    Tendsto (fun n => (trunc u (level n) : EReal)) atTop (𝓝 u.val) := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : EReal)) atTop (𝓝 ⊤) :=
    EReal.tendsto_coe_atTop.comp hr
  simp_rw [coe_trunc]
  change Tendsto (fun n : ℕ => min u.val (((n : ℝ) + 1 : ℝ) : EReal)) atTop (𝓝 u.val)
  have hu : Tendsto (fun _ : ℕ => u.val) atTop (𝓝 u.val) := tendsto_const_nhds
  simpa only [min_top_right] using hu.min he

/-- The shifted truncation is strictly below the original extended real. -/
theorem threshold_lt (u : Nonnegative) (n : ℕ) :
    ((trunc u (level n) - 1 / ((n : ℝ) + 1) : ℝ) : EReal) < u.val := by
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hs : trunc u (level n) - 1 / ((n : ℝ) + 1) < trunc u (level n) :=
    sub_lt_self _ hp
  exact (EReal.coe_lt_coe hs).trans_le (by rw [coe_trunc]; exact min_le_left _ _)

end ERealTruncation
end LPPDifferentiability
