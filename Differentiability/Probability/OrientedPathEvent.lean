/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.OrientedCompactness
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Basic.Countable.Basic

/-!
# Measurability of the infinite good oriented path event

The infinite-path event is a countable intersection of countable unions of
finite all-good path events.
-/

public section

namespace LPPDifferentiability

/-- An infinite all-good oriented path exists exactly when every length has
an actual finite all-good oriented path. -/
theorem exists_infinite_good_oriented_path_iff_forall_finite_good_oriented_paths
    {Ω : Type*} (G : ℕ × ℕ → Set Ω) (ω : Ω) :
    (∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
      (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
      ∀ i, ω ∈ G (v i)) ↔
    ∀ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i, ω ∈ G (q i) := by
  constructor
  · rintro ⟨v, hzero, hstep, hgood⟩ n
    refine ⟨fun i => v i.val, ?_, ?_, ?_⟩
    · change v 0 = (0, 0)
      exact hzero
    · intro i
      simpa using hstep i.val
    · intro i
      exact hgood i.val
  · intro hfinite
    apply exists_infinite_good_oriented_path {x | ω ∈ G x}
    intro n
    obtain ⟨q, hzero, hstep, hgood⟩ := hfinite n
    exact ⟨q, hzero, hstep, hgood⟩

/-- The exact infinite all-good oriented path event is measurable whenever
each site event is measurable. -/
theorem measurableSet_exists_infinite_good_oriented_path
    {Ω : Type*} [MeasurableSpace Ω] (G : ℕ × ℕ → Set Ω)
    (hG : ∀ x, MeasurableSet (G x)) :
    MeasurableSet
      {ω : Ω | ∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
        (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
        ∀ i, ω ∈ G (v i)} := by
  classical
  have hfinite (n : ℕ) :
      MeasurableSet
        {ω : Ω | ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧
          (∀ i : Fin n,
            q i.succ = q i.castSucc + (1, 0) ∨
              q i.succ = q i.castSucc + (0, 1)) ∧
          ∀ i, ω ∈ G (q i)} := by
    have hUnion :
        {ω : Ω | ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧
          (∀ i : Fin n,
            q i.succ = q i.castSucc + (1, 0) ∨
              q i.succ = q i.castSucc + (0, 1)) ∧
          ∀ i, ω ∈ G (q i)} =
          ⋃ q : Fin (n + 1) → ℕ × ℕ,
            {ω : Ω | q 0 = (0, 0) ∧
              (∀ i : Fin n,
                q i.succ = q i.castSucc + (1, 0) ∨
                  q i.succ = q i.castSucc + (0, 1)) ∧
              ∀ i, ω ∈ G (q i)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hUnion]
    exact MeasurableSet.iUnion fun q => by
      by_cases hzero : q 0 = (0, 0)
      · by_cases hstep : ∀ i : Fin n,
          q i.succ = q i.castSucc + (1, 0) ∨
            q i.succ = q i.castSucc + (0, 1)
        · simpa [hzero, hstep] using
            (show MeasurableSet
              {ω : Ω | ∀ i : Fin (n + 1), ω ∈ G (q i)} from by
                have hsites :
                    {ω : Ω | ∀ i : Fin (n + 1), ω ∈ G (q i)} =
                      ⋂ i : Fin (n + 1), G (q i) := by
                  ext ω
                  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
                rw [hsites]
                exact MeasurableSet.iInter fun i => hG (q i))
        · have hempty :
              {ω : Ω | q 0 = (0, 0) ∧
                (∀ i : Fin n,
                  q i.succ = q i.castSucc + (1, 0) ∨
                    q i.succ = q i.castSucc + (0, 1)) ∧
                ∀ i, ω ∈ G (q i)} = ∅ := by
            ext ω
            simp [hzero, hstep]
          rw [hempty]
          exact MeasurableSet.empty
      · have hempty :
            {ω : Ω | q 0 = (0, 0) ∧
              (∀ i : Fin n,
                q i.succ = q i.castSucc + (1, 0) ∨
                  q i.succ = q i.castSucc + (0, 1)) ∧
              ∀ i, ω ∈ G (q i)} = ∅ := by
          ext ω
          simp [hzero]
        rw [hempty]
        exact MeasurableSet.empty
  have hEvent :
      {ω : Ω | ∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
        (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
        ∀ i, ω ∈ G (v i)} =
      {ω : Ω | ∀ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
        q 0 = (0, 0) ∧
        (∀ i : Fin n,
          q i.succ = q i.castSucc + (1, 0) ∨
            q i.succ = q i.castSucc + (0, 1)) ∧
        ∀ i, ω ∈ G (q i)} := by
    ext ω
    exact exists_infinite_good_oriented_path_iff_forall_finite_good_oriented_paths
      G ω
  rw [hEvent]
  have hInter :
      {ω : Ω | ∀ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
        q 0 = (0, 0) ∧
        (∀ i : Fin n,
          q i.succ = q i.castSucc + (1, 0) ∨
            q i.succ = q i.castSucc + (0, 1)) ∧
        ∀ i, ω ∈ G (q i)} =
      ⋂ n : ℕ,
        {ω : Ω | ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧
          (∀ i : Fin n,
            q i.succ = q i.castSucc + (1, 0) ∨
              q i.succ = q i.castSucc + (0, 1)) ∧
          ∀ i, ω ∈ G (q i)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hInter]
  exact MeasurableSet.iInter hfinite

end LPPDifferentiability
