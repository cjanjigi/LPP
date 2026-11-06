/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The equality set of a symmetric concave profile

A continuous concave profile on the unit interval, bounded above by one and
symmetric about its midpoint, has either no points at height one or one
closed interval of such points. If the value at the right endpoint is below
one, the right endpoint of this interval is the unique parameter describing
it.
-/

public section

open Set

namespace LPPDifferentiability

/-- The height-one set of a symmetric concave profile on `[0, 1]` is empty or
is a closed interval with a unique right endpoint in `[1/2, 1)`. -/
theorem symmetric_flat_interval
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hconc : ConcaveOn ℝ (Icc 0 1) f)
    (hupper : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ 1)
    (hsymmetric : ∀ t ∈ Icc (0 : ℝ) 1, f (1 - t) = f t)
    (hendpoint : f (1 : ℝ) < 1) :
    (∀ t ∈ Icc (0 : ℝ) 1, f t < 1) ∨
      ∃! b : ℝ,
        1 / 2 ≤ b ∧ b < 1 ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            (f t = 1 ↔ t ∈ Icc (1 - b) b) := by
  classical
  let E : Set ℝ := Icc (0 : ℝ) 1 ∩ f ⁻¹' ({1} : Set ℝ)
  have hEiff (t : ℝ) : t ∈ E ↔ t ∈ Icc (0 : ℝ) 1 ∧ f t = 1 := by
    simp [E]
  have hEclosed : IsClosed E := by
    simpa [E] using
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hEcompact : IsCompact E :=
    isCompact_Icc.of_isClosed_subset hEclosed (by
      intro t ht
      exact (hEiff t).mp ht |>.1)
  by_cases hEempty : E = ∅
  · left
    intro t ht
    have hnot : f t ≠ 1 := by
      intro hEq
      have htE : t ∈ E := (hEiff t).2 ⟨ht, hEq⟩
      rw [hEempty] at htE
      simp at htE
    exact lt_of_le_of_ne (hupper t ht) hnot
  · right
    have hEnonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hEempty
    obtain ⟨b, hbE, hbMax⟩ := hEcompact.exists_isMaxOn hEnonempty continuousOn_id
    have hbMax' (t : ℝ) (ht : t ∈ E) : t ≤ b := by
      simpa using hbMax ht
    have hbData : b ∈ Icc (0 : ℝ) 1 ∧ f b = 1 := (hEiff b).mp hbE
    have hOneNot : (1 : ℝ) ∉ E := by
      intro hOne
      have hOneData := (hEiff 1).mp hOne
      linarith
    have hbLtOne : b < 1 := by
      by_contra hnot
      have hbEqOne : b = 1 := le_antisymm hbData.1.2 (le_of_not_gt hnot)
      subst b
      exact hOneNot hbE
    have hMirrorInterval : 1 - b ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hbData.1.1, hbData.1.2]
    have hMirrorValue : f (1 - b) = 1 := by
      rw [hsymmetric b hbData.1]
      exact hbData.2
    have hMirrorE : 1 - b ∈ E :=
      (hEiff (1 - b)).2 ⟨hMirrorInterval, hMirrorValue⟩
    have hbLower : 1 / 2 ≤ b := by
      have h := hbMax' (1 - b) hMirrorE
      linarith
    have hCharacterization : ∀ t ∈ Icc (0 : ℝ) 1,
        (f t = 1 ↔ t ∈ Icc (1 - b) b) := by
      intro t ht
      constructor
      · intro htValue
        have htE : t ∈ E := (hEiff t).2 ⟨ht, htValue⟩
        have htUpper : t ≤ b := hbMax' t htE
        have hMirrorTInterval : 1 - t ∈ Icc (0 : ℝ) 1 := by
          constructor <;> linarith [ht.1, ht.2]
        have hMirrorTValue : f (1 - t) = 1 := by
          rw [hsymmetric t ht]
          exact htValue
        have hMirrorTE : 1 - t ∈ E :=
          (hEiff (1 - t)).2 ⟨hMirrorTInterval, hMirrorTValue⟩
        have htLower : 1 - t ≤ b := hbMax' (1 - t) hMirrorTE
        exact ⟨by linarith, htUpper⟩
      · intro htInterval
        have hLeftInterval : 1 - b ∈ Icc (0 : ℝ) 1 := by
          constructor <;> linarith [hbData.1.1, hbData.1.2]
        have hLower : 1 ≤ f t := by
          have hmin := hconc.min_le_of_mem_Icc hLeftInterval hbData.1 htInterval
          rw [hMirrorValue, hbData.2] at hmin
          simpa using hmin
        exact le_antisymm (hupper t ht) hLower
    refine ⟨b, ⟨hbLower, hbLtOne, hCharacterization⟩, ?_⟩
    intro c hc
    have hbLeC : b ≤ c := by
      have hInterval := (hc.2.2 b hbData.1).mp hbData.2
      exact hInterval.2
    have hcInterval : c ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hc.1, hc.2.1]
    have hcInItsOwnInterval : c ∈ Icc (1 - c) c := by
      constructor <;> linarith [hc.1]
    have hcValue : f c = 1 := (hc.2.2 c hcInterval).mpr hcInItsOwnInterval
    have hcE : c ∈ E := (hEiff c).2 ⟨hcInterval, hcValue⟩
    exact le_antisymm (hbMax' c hcE) hbLeC

