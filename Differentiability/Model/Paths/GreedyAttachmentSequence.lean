/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.GreedyAttachmentDeviation
public import LPP_Foundations.Frozen.Model.Path
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! The literal preferred/forced recursive attachment sequence. -/

@[expose] public section
namespace LPPDifferentiability
namespace GreedyAttachment
open scoped Classical

/-- First-coordinate deviation from the interpolated segment at local level i. -/
def deviation (u : Lattice) (q : ℝ) (i : ℕ) (x : Lattice) : ℝ :=
  (x.1 : ℝ) - (u.1 : ℝ) - (i : ℝ) * q

/-- On a tie, the first of the two next sites is chosen. -/
noncomputable def preferred (u : Lattice) (q : ℝ) (i : ℕ) (x : Lattice) : Lattice :=
  if |deviation u q i x + (1 - q)| ≤ |deviation u q i x + (1 - q) - 1|
  then x + (1, 0) else x + (0, 1)

/-- The other of the two actual next sites. -/
noncomputable def alternate (u : Lattice) (q : ℝ) (i : ℕ) (x : Lattice) : Lattice :=
  if |deviation u q i x + (1 - q)| ≤ |deviation u q i x + (1 - q) - 1|
  then x + (0, 1) else x + (1, 0)

/-- The total recursive source algorithm, without a stopping convention. -/
noncomputable def vertex (u : Lattice) (q : ℝ) (V : Set Lattice) : ℕ → Lattice :=
  fun n => Nat.rec u (fun i x =>
    if preferred u q i x ∈ V then alternate u q i x else preferred u q i x) n

/-- A step is forced exactly when its actual preferred site is bad. -/
def forced (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) : Prop :=
  preferred u q i (vertex u q V i) ∈ V

/-- Count the actual forced indices strictly before i. -/
noncomputable def forcedCount (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) : ℕ :=
  ((Finset.range i).filter (forced u q V)).card

@[simp] theorem vertex_zero (u : Lattice) (q : ℝ) (V : Set Lattice) :
    vertex u q V 0 = u := rfl

theorem vertex_succ (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) :
    vertex u q V (i + 1) = if forced u q V i then
      alternate u q i (vertex u q V i) else preferred u q i (vertex u q V i) := by
  classical
  rfl

@[simp] theorem forcedCount_zero (u : Lattice) (q : ℝ) (V : Set Lattice) :
    forcedCount u q V 0 = 0 := by
  classical
  simp only [forcedCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty]

theorem forcedCount_succ (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) :
    forcedCount u q V (i + 1) = forcedCount u q V i + if forced u q V i then 1 else 0 := by
  classical
  simp only [forcedCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : forced u q V i
  · simp only [h, ↓reduceIte]
    rw [Finset.card_insert_of_notMem (by simp), Nat.add_comm]
  · simp only [h, ↓reduceIte, Nat.add_zero]

theorem step (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) :
    vertex u q V (i + 1) = vertex u q V i + (1, 0) ∨
    vertex u q V (i + 1) = vertex u q V i + (0, 1) := by
  classical
  rw [vertex_succ]
  unfold preferred alternate
  split_ifs <;> simp

theorem level (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) :
    (vertex u q V i).1 + (vertex u q V i).2 = u.1 + u.2 + (i : ℤ) := by
  induction i with
  | zero => simp only [vertex_zero, Nat.cast_zero, add_zero]
  | succ i ih =>
    rcases step u q V i with h | h <;> rw [h] <;>
      simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> omega

theorem start_le (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) :
    u ≤ vertex u q V i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    rcases step u q V i with h | h <;> rw [h] <;>
      exact ⟨by dsimp only [Prod.fst_add]; omega,
        by dsimp only [Prod.snd_add]; omega⟩

theorem deviation_step (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ) :
    deviation u q (i + 1) (vertex u q V (i + 1)) =
      if |deviation u q i (vertex u q V i) + (1 - q)| ≤
          |deviation u q i (vertex u q V i) + (1 - q) - 1| then
        if forced u q V i then deviation u q i (vertex u q V i) + (1 - q) - 1
        else deviation u q i (vertex u q V i) + (1 - q)
      else
        if forced u q V i then deviation u q i (vertex u q V i) + (1 - q)
        else deviation u q i (vertex u q V i) + (1 - q) - 1 := by
  classical
  rw [vertex_succ]
  unfold preferred alternate
  split_ifs <;>
    simp only [deviation, Prod.fst_add, Int.cast_add, Int.cast_one, Int.cast_zero,
      Nat.cast_add, Nat.cast_one] <;> ring

theorem deviation_bound (u : Lattice) (q : ℝ) (V : Set Lattice)
    (hq₁ : 1 / 4 ≤ q) (hq₂ : q ≤ 3 / 4) (i : ℕ) :
    |deviation u q i (vertex u q V i)| ≤ 1 + (forcedCount u q V i : ℝ) := by
  classical
  exact greedy_attachment_deviation_bound_of_recurrence (1 - q)
    (by linarith) (by linarith) (forced u q V)
    (fun j => deviation u q j (vertex u q V j)) (forcedCount u q V)
    (by simp only [vertex_zero, deviation, Nat.cast_zero, zero_mul, sub_self])
    (forcedCount_zero u q V) (deviation_step u q V) (forcedCount_succ u q V) i

theorem candidate_level (u x : Lattice) (q : ℝ) (i : ℕ) :
    (preferred u q i x).1 + (preferred u q i x).2 = x.1 + x.2 + 1 := by
  unfold preferred
  split_ifs <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem preferred_injective (u : Lattice) (q : ℝ) (V : Set Lattice) :
    Function.Injective (fun i => preferred u q i (vertex u q V i)) := by
  intro i j h
  have hi := candidate_level u (vertex u q V i) q i
  have hj := candidate_level u (vertex u q V j) q j
  change preferred u q i (vertex u q V i) = preferred u q j (vertex u q V j) at h
  rw [h] at hi
  have li := level u q V i
  have lj := level u q V j
  omega

theorem candidate_deviation (u x : Lattice) (q : ℝ) (i : ℕ) :
    deviation u q (i + 1) (preferred u q i x) =
      if |deviation u q i x + (1 - q)| ≤ |deviation u q i x + (1 - q) - 1|
      then deviation u q i x + (1 - q) else deviation u q i x + (1 - q) - 1 := by
  unfold preferred
  split_ifs <;>
    simp only [deviation, Prod.fst_add, Int.cast_add, Int.cast_one, Int.cast_zero,
      Nat.cast_add, Nat.cast_one] <;> ring

theorem preferred_deviation_le (u : Lattice) (q : ℝ) (V : Set Lattice)
    (hq₁ : 1 / 4 ≤ q) (hq₂ : q ≤ 3 / 4) (i : ℕ) :
    |deviation u q (i + 1) (preferred u q i (vertex u q V i))| ≤
      1 + (forcedCount u q V i : ℝ) := by
  rw [candidate_deviation]
  have hb := deviation_bound u q V hq₁ hq₂ i
  have hs := greedy_attachment_preferred_step_abs_le
    (deviation u q i (vertex u q V i)) (1 - q)
    (show (1 / 4 : ℝ) ≤ 1 - q by linarith)
    (show 1 - q ≤ (3 / 4 : ℝ) by linarith)
  have hm : max 1 (|deviation u q i (vertex u q V i)| - 1 / 4) ≤
      1 + (forcedCount u q V i : ℝ) := by
    have hfnonneg : (0 : ℝ) ≤ (forcedCount u q V i : ℝ) := Nat.cast_nonneg _
    apply max_le <;> linarith only [hb, hfnonneg]
  split_ifs with h
  · rw [min_eq_left h] at hs
    exact hs.trans hm
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))] at hs
    exact hs.trans hm

/-- The literal tube deviation equals the transverse deviation at the same level. -/
theorem transverse_deviation_eq (u x : Lattice) (q a : ℝ) (i : ℕ)
    (hlevel : x.1 + x.2 = u.1 + u.2 + (i : ℤ)) :
    ((1 - a) * (x.1 : ℝ) - a * (x.2 : ℝ)) -
      (((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) + (i : ℝ) * (q - a)) =
      deviation u q i x := by
  have h : (x.1 : ℝ) + (x.2 : ℝ) = (u.1 : ℝ) + (u.2 : ℝ) + (i : ℝ) := by
    exact_mod_cast hlevel
  unfold deviation
  linear_combination -a * h

end GreedyAttachment
end LPPDifferentiability
