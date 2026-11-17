/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.CoalescingTilt
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Separation.Hausdorff

/-! Pointwise finite limits and order for the literal sided tilt sequences. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- The literal sampled sequences have finite real limits and retain the
opposite-side order at every actual coalescing tilt. This is the deterministic
edge step for Strong Existence, lines 1194–1221. -/
theorem canonical_H_scalar_raw_limits_and_order
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (D : Set (CoalescingTilt μ))
    (left right : CoalescingTilt μ → ℕ → CoalescingTilt μ)
    (hSequences : ∀ h : CoalescingTilt μ,
      (h ∈ D → left h = (fun _ => h) ∧ right h = (fun _ => h)) ∧
      (h ∉ D →
        (∀ n, left h n ∈ D ∧ (left h n).val.1 < h.val.1) ∧
        StrictMono (fun n => (left h n).val.1) ∧
        Tendsto (left h) atTop (𝓝 h) ∧
        (∀ n, right h n ∈ D ∧ h.val.1 < (right h n).val.1) ∧
        StrictAnti (fun n => (right h n).val.1) ∧
        Tendsto (right h) atTop (𝓝 h)))
    (f : CoalescingTilt μ → ℝ)
    (hOrder : ∀ a b : CoalescingTilt μ, a ∈ D → b ∈ D →
      a.val.1 < b.val.1 → f b ≤ f a) :
    (∀ h : CoalescingTilt μ,
      Tendsto (fun n => f (left h n)) atTop
        (𝓝 (limUnder atTop (fun n => f (left h n)))) ∧
      Tendsto (fun n => f (right h n)) atTop
        (𝓝 (limUnder atTop (fun n => f (right h n))))) ∧
    (∀ h : CoalescingTilt μ,
      limUnder atTop (fun n => f (right h n)) ≤
        limUnder atTop (fun n => f (left h n))) ∧
    (∀ h k : CoalescingTilt μ, h.val.1 < k.val.1 →
      limUnder atTop (fun n => f (left k n)) ≤
        limUnder atTop (fun n => f (right h n))) := by
  classical
  have left_mem (h : CoalescingTilt μ) (n : ℕ) : left h n ∈ D := by
    rcases hSequences h with ⟨hOn, hOff⟩
    by_cases hh : h ∈ D
    · rw [(hOn hh).1]
      exact hh
    · rcases hOff hh with ⟨hLeft, _, _, _, _, _⟩
      exact (hLeft n).1
  have right_mem (h : CoalescingTilt μ) (n : ℕ) : right h n ∈ D := by
    rcases hSequences h with ⟨hOn, hOff⟩
    by_cases hh : h ∈ D
    · rw [(hOn hh).2]
      exact hh
    · rcases hOff hh with ⟨_, _, _, hRight, _, _⟩
      exact (hRight n).1
  have left_coordinate_tendsto (h : CoalescingTilt μ) :
      Tendsto (fun n => (left h n).val.1) atTop (𝓝 h.val.1) := by
    rcases hSequences h with ⟨hOn, hOff⟩
    by_cases hh : h ∈ D
    · rw [(hOn hh).1]
      exact tendsto_const_nhds
    · rcases hOff hh with ⟨_, _, hLeftTendsto, _, _, _⟩
      exact ((continuous_fst.comp continuous_subtype_val).tendsto h).comp hLeftTendsto
  have right_coordinate_tendsto (h : CoalescingTilt μ) :
      Tendsto (fun n => (right h n).val.1) atTop (𝓝 h.val.1) := by
    rcases hSequences h with ⟨hOn, hOff⟩
    by_cases hh : h ∈ D
    · rw [(hOn hh).2]
      exact tendsto_const_nhds
    · rcases hOff hh with ⟨_, _, _, _, _, hRightTendsto⟩
      exact ((continuous_fst.comp continuous_subtype_val).tendsto h).comp hRightTendsto
  have left_finite_limit (h : CoalescingTilt μ) :
      Tendsto (fun n => f (left h n)) atTop
        (𝓝 (limUnder atTop (fun n => f (left h n)))) := by
    rcases hSequences h with ⟨hOn, hOff⟩
    by_cases hh : h ∈ D
    · have hConstant : Tendsto (fun n => f (left h n)) atTop (𝓝 (f h)) := by
        rw [(hOn hh).1]
        exact tendsto_const_nhds
      rw [hConstant.limUnder_eq]
      exact hConstant
    · rcases hOff hh with ⟨hLeft, hLeftStrict, _, hRight, _, _⟩
      have hLeftAntitone : Antitone (fun n => f (left h n)) := by
        intro n m hnm
        by_cases hEq : n = m
        · subst m
          exact le_rfl
        · have hlt : n < m := lt_of_le_of_ne hnm hEq
          exact hOrder (left h n) (left h m) (hLeft n).1 (hLeft m).1
            (hLeftStrict hlt)
      have hLeftLower (n : ℕ) : f (right h 0) ≤ f (left h n) := by
        exact hOrder (left h n) (right h 0) (hLeft n).1 (hRight 0).1
          (lt_trans (hLeft n).2 (hRight 0).2)
      rcases tendsto_atTop_of_antitone hLeftAntitone with hAtBot | ⟨l, hLimit⟩
      · obtain ⟨n, hn⟩ :=
          (tendsto_atBot.1 hAtBot (f (right h 0) - 1)).exists
        linarith only [hn, hLeftLower n]
      · have hLimitValue : limUnder atTop (fun n => f (left h n)) = l :=
          hLimit.limUnder_eq
        rw [hLimitValue]
        exact hLimit
  have right_finite_limit (h : CoalescingTilt μ) :
      Tendsto (fun n => f (right h n)) atTop
        (𝓝 (limUnder atTop (fun n => f (right h n)))) := by
    rcases hSequences h with ⟨hOn, hOff⟩
    by_cases hh : h ∈ D
    · have hConstant : Tendsto (fun n => f (right h n)) atTop (𝓝 (f h)) := by
        rw [(hOn hh).2]
        exact tendsto_const_nhds
      rw [hConstant.limUnder_eq]
      exact hConstant
    · rcases hOff hh with ⟨hLeft, _, _, hRight, hRightStrict, _⟩
      have hRightMonotone : Monotone (fun n => f (right h n)) := by
        intro n m hnm
        by_cases hEq : n = m
        · subst m
          exact le_rfl
        · have hlt : n < m := lt_of_le_of_ne hnm hEq
          exact hOrder (right h m) (right h n) (hRight m).1 (hRight n).1
            (hRightStrict hlt)
      have hRightUpper (n : ℕ) : f (right h n) ≤ f (left h 0) := by
        exact hOrder (left h 0) (right h n) (hLeft 0).1 (hRight n).1
          (lt_trans (hLeft 0).2 (hRight n).2)
      rcases tendsto_atTop_of_monotone hRightMonotone with hAtTop | ⟨l, hLimit⟩
      · obtain ⟨n, hn⟩ :=
          (tendsto_atTop.1 hAtTop (f (left h 0) + 1)).exists
        linarith only [hn, hRightUpper n]
      · have hLimitValue : limUnder atTop (fun n => f (right h n)) = l :=
          hLimit.limUnder_eq
        rw [hLimitValue]
        exact hLimit
  have within_order (h : CoalescingTilt μ) (n : ℕ) :
      f (right h n) ≤ f (left h n) := by
    rcases hSequences h with ⟨hOn, hOff⟩
    by_cases hh : h ∈ D
    · rw [(hOn hh).1, (hOn hh).2]
    · rcases hOff hh with ⟨hLeft, _, _, hRight, _, _⟩
      exact hOrder (left h n) (right h n) (hLeft n).1 (hRight n).1
        (lt_trans (hLeft n).2 (hRight n).2)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact ⟨left_finite_limit h, right_finite_limit h⟩
  · intro h
    exact le_of_tendsto_of_tendsto' (right_finite_limit h) (left_finite_limit h)
      (within_order h)
  · intro h k hlt
    obtain ⟨c, hhc, hck⟩ := exists_between hlt
    have hRightEventually : ∀ᶠ n in atTop, (right h n).val.1 < c :=
      (tendsto_order.1 (right_coordinate_tendsto h)).2 c hhc
    have hLeftEventually : ∀ᶠ n in atTop, c < (left k n).val.1 :=
      (tendsto_order.1 (left_coordinate_tendsto k)).1 c hck
    have hPointwiseEventually : ∀ᶠ n in atTop, f (left k n) ≤ f (right h n) := by
      filter_upwards [hRightEventually, hLeftEventually] with n hRight hLeft
      exact hOrder (right h n) (left k n) (right_mem h n) (left_mem k n)
        (lt_trans hRight hLeft)
    exact le_of_tendsto_of_tendsto (left_finite_limit k) (right_finite_limit h)
      hPointwiseEventually

end LPP.Busemann
