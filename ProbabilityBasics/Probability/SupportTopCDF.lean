/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith

/-!
# The support endpoint and the closed CDF

The endpoint considered here is the `EReal` supremum of the measure support.
The helper arguments below justify the positive open upper tail and the conull
partition below the endpoint or at its atom. They apply to real probability
laws, including laws with atoms and unbounded support.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace LPPDifferentiability

/-- The upper endpoint of the support, with `+∞` allowed. -/
@[expose] noncomputable def supportTop (μ : Measure ℝ) : EReal :=
  sSup ((fun t : ℝ => (t : EReal)) '' μ.support)

/-- The real weights equal to the upper endpoint of the support. -/
@[expose] noncomputable def supportTopAtom (μ : Measure ℝ) : Set ℝ :=
  {t | (t : EReal) = supportTop μ}

/-- A real probability law has nonempty existing Mathlib support. -/
theorem source_support_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.support.Nonempty :=
  μ.nonempty_support (NeZero.ne μ)

/-- The top of the support is never minus infinity. -/
theorem source_support_sSup_ne_bot (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    supportTop μ ≠ ⊥ := by
  obtain ⟨t, ht⟩ := source_support_nonempty μ
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot t)
    (le_sSup (mem_image_of_mem (fun t : ℝ => (t : EReal)) ht))

/-- Positive open upper-tail mass is equivalent to lying strictly below the
top of the support. -/
theorem source_upper_tail_pos_iff_lt_support_sSup (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (t : ℝ) :
    0 < μ (Ioi t) ↔ (t : EReal) < supportTop μ := by
  constructor
  · intro h
    obtain ⟨s, hst, hs⟩ := μ.nonempty_inter_support_of_pos h
    exact lt_sSup_iff.mpr ⟨(s : EReal), mem_image_of_mem _ hs,
      EReal.coe_lt_coe hst⟩
  · intro h
    obtain ⟨_, ⟨s, hs, rfl⟩, hts⟩ := lt_sSup_iff.mp h
    exact (Measure.mem_support_iff_forall s).mp hs (Ioi t)
      (isOpen_Ioi.mem_nhds (EReal.coe_lt_coe_iff.mp hts))

/-- The closed CDF is below one exactly below the source support endpoint. -/
theorem source_cdf_lt_one_iff_lt_support_sSup (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (t : ℝ) :
    μ.real (Iic t) < 1 ↔ (t : EReal) < supportTop μ := by
  rw [← source_upper_tail_pos_iff_lt_support_sSup μ t]
  have hc : μ.real (Ioi t) = 1 - μ.real (Iic t) := by
    simpa only [compl_Iic] using probReal_compl_eq_one_sub (μ := μ) measurableSet_Iic
  have hp : 0 < μ.real (Ioi t) ↔ 0 < μ (Ioi t) :=
    by
      constructor
      · intro h
        exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff (μ := μ) (s := Ioi t)).mp h.ne')
      · intro h
        exact ENNReal.toReal_pos h.ne' (measure_ne_top _ _)
  rw [← hp, hc]
  exact sub_pos.symm

/-- Conull support bounds real samples by the literal extended endpoint. -/
theorem source_ae_le_support_sSup (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ t : ℝ ∂μ, (t : EReal) ≤ supportTop μ := by
  filter_upwards [μ.support_mem_ae] with t ht
  exact le_sSup (mem_image_of_mem (fun s : ℝ => (s : EReal)) ht)

/-- One conull set partitions into the below-endpoint part and the actual
extended-real equality event. -/
theorem source_ae_lt_or_eq_support_sSup (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ t : ℝ ∂μ, (t : EReal) < supportTop μ ∨ (t : EReal) = supportTop μ := by
  filter_upwards [source_ae_le_support_sSup μ] with t ht
  exact lt_or_eq_of_le ht

/-- The source partition has null complement. -/
theorem source_measure_compl_below_or_top_eq_zero (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    μ ({t : ℝ | (t : EReal) < supportTop μ} ∪ supportTopAtom μ)ᶜ = 0 :=
  source_ae_lt_or_eq_support_sSup μ

/-- When the source endpoint is plus infinity, its real equality event is empty. -/
theorem source_top_atom_eq_empty_of_support_sSup_eq_top (μ : Measure ℝ)
    (hM : supportTop μ = ⊤) :
    supportTopAtom μ = ∅ := by
  ext t
  simp only [supportTopAtom, mem_ofPred_eq, hM, EReal.coe_ne_top, mem_empty_iff_false]

end LPPDifferentiability
