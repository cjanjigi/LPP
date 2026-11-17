/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Monotone.Basic

/-! First crossings of vertical and horizontal boundaries by up-right rays. -/

@[expose] public section

open Filter LPPDifferentiability

namespace LPPDifferentiability

private theorem up_right_path_step_bounds
    (p : ℕ → Lattice)
    (hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1))
    (n : ℕ) :
    ((p n).1 ≤ (p (n + 1)).1 ∧ (p (n + 1)).1 ≤ (p n).1 + 1) ∧
      ((p n).2 ≤ (p (n + 1)).2 ∧ (p (n + 1)).2 ≤ (p n).2 + 1) := by
  rcases hp n with h | h <;>
    simp only [h, Prod.fst_add, Prod.snd_add] <;> omega

/-- A ray whose first coordinate escapes has a final east step from `x=M`.
Every later vertex lies strictly to its right, and its height bounds every
vertex that still lies on that vertical line. This is the east-boundary step
in GRS, arXiv:1510.00860v1, Appendix A.3/A.4, lines 1517–1587. -/
theorem up_right_path_last_east_departure
    (p : ℕ → Lattice)
    (hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1))
    (hEscape : Tendsto (fun n => (p n).1) atTop atTop)
    (M : ℤ) (hStart : (p 0).1 ≤ M) :
    ∃ n : ℕ, (p n).1 = M ∧ p (n + 1) = p n + (1, 0) ∧
      (∀ t : ℕ, n < t → M < (p t).1) ∧
      (∀ t : ℕ, (p t).1 = M → (p t).2 ≤ (p n).2) := by
  classical
  have hSteps (n : ℕ) := up_right_path_step_bounds p hp n
  have hXmono : Monotone (fun n => (p n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    exact (hSteps n).1.1
  have hYmono : Monotone (fun n => (p n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    exact (hSteps n).2.1

  -- Coordinate escape gives a crossing time; Nat.find selects the first one.
  have hex : ∃ k : ℕ, M < (p k).1 := by
    rcases (hEscape.eventually_gt_atTop M).exists with ⟨k, hk⟩
    exact ⟨k, hk⟩
  let k : ℕ := Nat.find hex
  have hCross : M < (p k).1 := Nat.find_spec hex
  have hkPos : 0 < k := by
    by_contra hnot
    have hkZero : k = 0 := by omega
    have hAtZero : M < (p 0).1 := by simpa only [hkZero] using hCross
    exact (not_lt_of_ge hStart) hAtZero
  have hPrevIndex : k - 1 + 1 = k := by omega

  -- The vertex before the first crossing is still on or left of `M`.
  have hPrevNot : ¬ M < (p (k - 1)).1 := Nat.find_min hex (by omega)
  have hPrevBound : (p (k - 1)).1 ≤ M := by omega
  have hPreviousStep := hp (k - 1)
  rw [hPrevIndex] at hPreviousStep

  -- A one-unit crossing forces equality with `M` and an east step.
  have hLast : (p (k - 1)).1 = M ∧ p k = p (k - 1) + (1, 0) := by
    rcases hPreviousStep with hEast | hNorth
    · have hXStep : (p k).1 = (p (k - 1)).1 + 1 := by
        rw [hEast]
        simp only [Prod.fst_add]
      rw [hXStep] at hCross
      constructor
      · omega
      · exact hEast
    · have hXStep : (p k).1 = (p (k - 1)).1 := by
        rw [hNorth]
        simp only [Prod.fst_add, add_zero]
      rw [hXStep] at hCross
      omega

  refine ⟨k - 1, hLast.1, ?_, ?_, ?_⟩
  · simpa only [hPrevIndex] using hLast.2
  · intro t hnt
    have hkt : k ≤ t := by omega
    have hMono : (p k).1 ≤ (p t).1 := hXmono hkt
    omega
  · intro t hOnBoundary
    have ht : t ≤ k - 1 := by
      by_contra hnot
      have hkt : k ≤ t := by omega
      have hMono : (p k).1 ≤ (p t).1 := hXmono hkt
      omega
    exact hYmono ht

/-- A ray whose second coordinate escapes first reaches height `M` by a north
step, with every earlier vertex strictly below that height. This is the
north-boundary hit used in GRS, arXiv:1510.00860v1, Appendix A.3/A.4,
lines 1517–1587. -/
theorem up_right_path_first_north_arrival
    (p : ℕ → Lattice)
    (hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1))
    (hEscape : Tendsto (fun n => (p n).2) atTop atTop)
    (M : ℤ) (hStart : (p 0).2 < M) :
    ∃ n : ℕ, 0 < n ∧ (p n).2 = M ∧
      p n = p (n - 1) + (0, 1) ∧
      (∀ t : ℕ, t < n → (p t).2 < M) := by
  classical
  have hex : ∃ k : ℕ, M ≤ (p k).2 := by
    rcases (hEscape.eventually_gt_atTop M).exists with ⟨k, hk⟩
    exact ⟨k, le_of_lt hk⟩
  let k : ℕ := Nat.find hex
  have hArriveBound : M ≤ (p k).2 := Nat.find_spec hex
  have hkPos : 0 < k := by
    by_contra hnot
    have hkZero : k = 0 := by omega
    have hAtZero : M ≤ (p 0).2 := by simpa only [hkZero] using hArriveBound
    exact (not_le_of_gt hStart) hAtZero
  have hPrevIndex : k - 1 + 1 = k := by omega

  -- Minimality leaves the predecessor strictly below `M`.
  have hPrevNot : ¬ M ≤ (p (k - 1)).2 := Nat.find_min hex (by omega)
  have hPrevHeight : (p (k - 1)).2 < M := by omega
  have hPreviousStep := hp (k - 1)
  rw [hPrevIndex] at hPreviousStep

  -- The east step cannot cross the height, so the first crossing is north.
  have hNorth : p k = p (k - 1) + (0, 1) := by
    rcases hPreviousStep with hEast | hNorth
    · have hYStep : (p k).2 = (p (k - 1)).2 := by
        rw [hEast]
        simp only [Prod.snd_add, add_zero]
      rw [hYStep] at hArriveBound
      omega
    · exact hNorth
  have hArrive : (p k).2 = M := by
    have hYStep : (p k).2 = (p (k - 1)).2 + 1 := by
      rw [hNorth]
      simp only [Prod.snd_add]
    omega

  refine ⟨k, hkPos, hArrive, hNorth, ?_⟩
  intro t ht
  have hBeforeNot : ¬ M ≤ (p t).2 := Nat.find_min hex ht
  omega

end LPPDifferentiability
