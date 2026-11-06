/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Inclusive
import Mathlib.Tactic.Linarith

/-! The exit-point bound for inclusive passage times from the origin. A path to
`(m + 1, n + 1)` leaves the two axes either from the bottom row, by stepping up from
`(k + 1, 0)`, or from the left column, by stepping right from `(0, l + 1)`. The proof is
an induction on the corner, using the last-step recursion and one-step extensions of
the bulk piece. This bound is used to compare stationary passage times with bulk passage times. -/

@[expose] public section

namespace LPPDifferentiability

/-- The exit-point bound for the corner `(m + 1, n + 1)`, as one statement to induct on.
It is the statement of `inclusivePassage_le_exit`. -/
private def ExitBound (ω : Environment) (m n : ℕ) : Prop :=
  (∃ k : ℕ, k ≤ m ∧ inclusivePassage ω 0 (m + 1, n + 1) ≤
      inclusivePassage ω 0 (k + 1, 0) +
        inclusivePassage ω (((k : ℤ) + 1, 1) : Lattice) (m - k, n)) ∨
    (∃ l : ℕ, l ≤ n ∧ inclusivePassage ω 0 (m + 1, n + 1) ≤
      inclusivePassage ω 0 (0, l + 1) +
        inclusivePassage ω ((1, (l : ℤ) + 1) : Lattice) (m, n - l))

/-- The inclusive passage time over zero displacement is the weight of the vertex. -/
private theorem inclusivePassage_zero_displacement (ω : Environment) (u : Lattice) :
    inclusivePassage ω u (0, 0) = ω u := by
  unfold inclusivePassage
  rw [lastPassage_zero, zero_add]
  exact congrArg ω (by ext <;> simp)

/-- One more upward step: the inclusive passage time to a vertex, plus the weight of
the vertex just above it, is at most the inclusive passage time to that upper vertex. -/
private theorem inclusivePassage_extend_up (ω : Environment) (u : Lattice) (a b : ℕ) :
    inclusivePassage ω u (a, b) + ω (u + ((a : ℤ), ((b + 1 : ℕ) : ℤ))) ≤
      inclusivePassage ω u (a, b + 1) := by
  have hs : lastPassage ω u (a, b) + ω (u + ((a : ℤ), (b : ℤ))) ≤
      lastPassage ω u (a, b + 1) := by
    have h := lastPassage_superadditive ω u (a, b) (0, 1)
    rw [lastPassage_vertical_one] at h
    exact h
  show lastPassage ω u (a, b) + ω (u + ((a : ℤ), (b : ℤ))) +
      ω (u + ((a : ℤ), ((b + 1 : ℕ) : ℤ))) ≤
    lastPassage ω u (a, b + 1) + ω (u + ((a : ℤ), ((b + 1 : ℕ) : ℤ)))
  linarith

/-- One more rightward step: the inclusive passage time to a vertex, plus the weight of
the vertex just to its right, is at most the inclusive passage time to that right vertex. -/
private theorem inclusivePassage_extend_right (ω : Environment) (u : Lattice) (a b : ℕ) :
    inclusivePassage ω u (a, b) + ω (u + (((a + 1 : ℕ) : ℤ), (b : ℤ))) ≤
      inclusivePassage ω u (a + 1, b) := by
  have hs : lastPassage ω u (a, b) + ω (u + ((a : ℤ), (b : ℤ))) ≤
      lastPassage ω u (a + 1, b) := by
    have h := lastPassage_superadditive ω u (a, b) (1, 0)
    rw [lastPassage_horizontal_one] at h
    exact h
  show lastPassage ω u (a, b) + ω (u + ((a : ℤ), (b : ℤ))) +
      ω (u + (((a + 1 : ℕ) : ℤ), (b : ℤ))) ≤
    lastPassage ω u (a + 1, b) + ω (u + (((a + 1 : ℕ) : ℤ), (b : ℤ)))
  linarith

/-- Last-step recursion at the origin. The inclusive passage time to
`(m + 1, n + 1)` is at most the end weight plus the inclusive passage time to the
left neighbour or to the lower neighbour. -/
private theorem inclusivePassage_corner_cases (ω : Environment) (m n : ℕ) :
    inclusivePassage ω 0 (m + 1, n + 1) ≤
        ω (0 + (((m + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) +
          inclusivePassage ω 0 (m, n + 1) ∨
    inclusivePassage ω 0 (m + 1, n + 1) ≤
        ω (0 + (((m + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) +
          inclusivePassage ω 0 (m + 1, n) := by
  have hrec : lastPassage ω 0 (m + 1, n + 1) =
      max (inclusivePassage ω 0 (m, n + 1)) (inclusivePassage ω 0 (m + 1, n)) :=
    lastPassage_succ_succ ω 0 (m, n)
  have hsplit : inclusivePassage ω 0 (m + 1, n + 1) =
      lastPassage ω 0 (m + 1, n + 1) +
        ω (0 + (((m + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) := rfl
  rcases le_total (inclusivePassage ω 0 (m, n + 1))
      (inclusivePassage ω 0 (m + 1, n)) with h | h
  · right
    rw [hsplit, hrec, max_eq_right h]
    exact (add_comm _ _).le
  · left
    rw [hsplit, hrec, max_eq_left h]
    exact (add_comm _ _).le

/-- Left predecessor on the left column: the exit is the top of the column read so far,
and the bulk piece is the single vertex to the right of it. -/
private theorem exitBound_of_left_column (ω : Environment) (n : ℕ)
    (h : inclusivePassage ω 0 (0 + 1, n + 1) ≤
      ω (0 + ((((0 + 1 : ℕ)) : ℤ), ((n + 1 : ℕ) : ℤ))) + inclusivePassage ω 0 (0, n + 1)) :
    ExitBound ω 0 n := by
  unfold ExitBound
  right
  refine ⟨n, le_rfl, ?_⟩
  have hpt : ((0 : Lattice) + ((((0 + 1 : ℕ)) : ℤ), ((n + 1 : ℕ) : ℤ))) =
      ((1, (n : ℤ) + 1) : Lattice) := by
    apply Prod.ext <;> simp
  have hw := congrArg ω hpt
  rw [Nat.sub_self, inclusivePassage_zero_displacement]
  linarith

/-- Lower predecessor on the bottom row: the exit is the last column read so far, and
the bulk piece is the single vertex above it. -/
private theorem exitBound_of_below_row (ω : Environment) (m : ℕ)
    (h : inclusivePassage ω 0 (m + 1, 0 + 1) ≤
      ω (0 + (((m + 1 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ))) + inclusivePassage ω 0 (m + 1, 0)) :
    ExitBound ω m 0 := by
  unfold ExitBound
  left
  refine ⟨m, le_rfl, ?_⟩
  have hpt : ((0 : Lattice) + (((m + 1 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ))) =
      (((m : ℤ) + 1, 1) : Lattice) := by
    apply Prod.ext <;> simp
  have hw := congrArg ω hpt
  rw [Nat.sub_self, inclusivePassage_zero_displacement]
  linarith

/-- Lower predecessor above the bottom row: keep the exit of the shorter column and
extend its bulk piece by one upward step. -/
private theorem exitBound_of_below_succ (ω : Environment) (m n : ℕ)
    (ih : ExitBound ω m n)
    (h : inclusivePassage ω 0 (m + 1, n + 1 + 1) ≤
      ω (0 + (((m + 1 : ℕ) : ℤ), ((n + 1 + 1 : ℕ) : ℤ))) +
        inclusivePassage ω 0 (m + 1, n + 1)) :
    ExitBound ω m (n + 1) := by
  unfold ExitBound at ih ⊢
  rcases ih with ⟨k, hk, hbound⟩ | ⟨l, hl, hbound⟩
  · left
    refine ⟨k, hk, ?_⟩
    have hext := inclusivePassage_extend_up ω (((k : ℤ) + 1, 1) : Lattice) (m - k) n
    have hpt : ((0 : Lattice) + (((m + 1 : ℕ) : ℤ), ((n + 1 + 1 : ℕ) : ℤ))) =
        (((k : ℤ) + 1, 1) : Lattice) + (((m - k : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)) := by
      apply Prod.ext <;> simp <;> omega
    have hw := congrArg ω hpt
    linarith
  · right
    refine ⟨l, by omega, ?_⟩
    have hext := inclusivePassage_extend_up ω ((1, (l : ℤ) + 1) : Lattice) m (n - l)
    have hsub : n + 1 - l = n - l + 1 := by omega
    have hpt : ((0 : Lattice) + (((m + 1 : ℕ) : ℤ), ((n + 1 + 1 : ℕ) : ℤ))) =
        ((1, (l : ℤ) + 1) : Lattice) + ((m : ℤ), ((n - l + 1 : ℕ) : ℤ)) := by
      apply Prod.ext <;> simp <;> omega
    have hw := congrArg ω hpt
    rw [hsub]
    linarith

/-- Left predecessor with a positive column index: keep the exit of the narrower strip
and extend its bulk piece by one rightward step. -/
private theorem exitBound_of_left_step (ω : Environment) (m n : ℕ)
    (ih : ExitBound ω m n)
    (h : inclusivePassage ω 0 (m + 1 + 1, n + 1) ≤
      ω (0 + (((m + 1 + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) +
        inclusivePassage ω 0 (m + 1, n + 1)) :
    ExitBound ω (m + 1) n := by
  unfold ExitBound at ih ⊢
  rcases ih with ⟨k, hk, hbound⟩ | ⟨l, hl, hbound⟩
  · left
    refine ⟨k, by omega, ?_⟩
    have hext := inclusivePassage_extend_right ω (((k : ℤ) + 1, 1) : Lattice) (m - k) n
    have hsub : m + 1 - k = m - k + 1 := by omega
    have hpt : ((0 : Lattice) + (((m + 1 + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) =
        (((k : ℤ) + 1, 1) : Lattice) + (((m - k + 1 : ℕ) : ℤ), (n : ℤ)) := by
      apply Prod.ext <;> simp <;> omega
    have hw := congrArg ω hpt
    rw [hsub]
    linarith
  · right
    refine ⟨l, hl, ?_⟩
    have hext := inclusivePassage_extend_right ω ((1, (l : ℤ) + 1) : Lattice) m (n - l)
    have hpt : ((0 : Lattice) + (((m + 1 + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) =
        ((1, (l : ℤ) + 1) : Lattice) + (((m + 1 : ℕ) : ℤ), ((n - l : ℕ) : ℤ)) := by
      apply Prod.ext <;> simp <;> omega
    have hw := congrArg ω hpt
    linarith

/-- The exit-point bound for every corner, by induction on the two coordinates. -/
private theorem exitBound_all (ω : Environment) (m n : ℕ) : ExitBound ω m n := by
  induction m generalizing n with
  | zero =>
    induction n with
    | zero =>
      rcases inclusivePassage_corner_cases ω 0 0 with h | h
      · exact exitBound_of_left_column ω 0 h
      · exact exitBound_of_below_row ω 0 h
    | succ n ihn =>
      rcases inclusivePassage_corner_cases ω 0 (n + 1) with h | h
      · exact exitBound_of_left_column ω (n + 1) h
      · exact exitBound_of_below_succ ω 0 n ihn h
  | succ m ihm =>
    induction n with
    | zero =>
      rcases inclusivePassage_corner_cases ω (m + 1) 0 with h | h
      · exact exitBound_of_left_step ω m 0 (ihm 0) h
      · exact exitBound_of_below_row ω (m + 1) h
    | succ n ihn =>
      rcases inclusivePassage_corner_cases ω (m + 1) (n + 1) with h | h
      · exact exitBound_of_left_step ω m (n + 1) (ihm (n + 1)) h
      · exact exitBound_of_below_succ ω (m + 1) n ihn h

/-- Exit-point bound. A path from the origin to `(m + 1, n + 1)` leaves the axes either
from the bottom row, by stepping up from `(k + 1, 0)` with `k ≤ m`, or from the left
column, by stepping right from `(0, l + 1)` with `l ≤ n`. So the inclusive passage time
is at most the axis piece to the exit plus the passage time through the bulk from the
vertex just beyond the exit. No sign condition on the weights is needed. -/
theorem inclusivePassage_le_exit (ω : Environment) (m n : ℕ) :
    (∃ k : ℕ, k ≤ m ∧ inclusivePassage ω 0 (m + 1, n + 1) ≤
      inclusivePassage ω 0 (k + 1, 0) +
        inclusivePassage ω (((k : ℤ) + 1, 1) : Lattice) (m - k, n)) ∨
    (∃ l : ℕ, l ≤ n ∧ inclusivePassage ω 0 (m + 1, n + 1) ≤
      inclusivePassage ω 0 (0, l + 1) +
        inclusivePassage ω ((1, (l : ℤ) + 1) : Lattice) (m, n - l)) :=
  exitBound_all ω m n

end LPPDifferentiability
