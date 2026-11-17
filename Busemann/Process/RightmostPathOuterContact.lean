/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathVerticalOrder
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! An outer-path contact prevents a later meeting with the preserved middle tail. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem outer_contact_path_restart
    (C : Lattice → Lattice → ℝ) (x : Lattice) (m n : ℕ) :
    rightmostCocyclePath C (rightmostCocyclePath C x m) n =
      rightmostCocyclePath C x (m + n) := by
  change (rightmostCocycleSuccessor C)^[n] ((rightmostCocycleSuccessor C)^[m] x) =
    (rightmostCocycleSuccessor C)^[m + n] x
  rw [Nat.add_comm m n, Function.iterate_add_apply]

private theorem outer_contact_path_level
    (C : Lattice → Lattice → ℝ) (x : Lattice) (n : ℕ) :
    (rightmostCocyclePath C x n).1 + (rightmostCocyclePath C x n).2 =
      x.1 + x.2 + (n : ℤ) := by
  induction n with
  | zero =>
      simp only [rightmostCocyclePath, Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n ih =>
      have hStep :
          rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (1, 0) ∨
          rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (0, 1) := by
        simpa only [rightmostCocyclePath, Function.iterate_succ_apply'] using
          rightmostCocycleSuccessor_step C (rightmostCocyclePath C x n)
      rcases hStep with h | h <;>
        simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega

/-- A modified ray that meets the preserved middle north tail cannot have
touched either old outer ray at any earlier time, including the meeting time.
This is the all-vertex barrier obstruction in GRS, arXiv:1510.00860v1,
Appendix A.4, lines 1616–1625. The start may have any signed absolute level. -/
theorem rightmostCocyclePath_prefix_avoids_outer_of_meets_middle
    (C D : Lattice → Lattice → ℝ)
    (m ell : ℕ) (hm : 0 < m) (hmell : m < ell)
    (M1 M2 a1 a2 : ℤ) (hTop : (ell : ℤ) < M2) (nL nM nU : ℕ)
    (hNorthL : rightmostCocyclePath C 0 nL = (M1, M2))
    (hNorthM : rightmostCocyclePath C (0, (m : ℤ)) nM = (a2, M2))
    (hNorthU : rightmostCocyclePath C (0, (ell : ℤ)) nU = (a1, M2))
    (hDisjointLM : ∀ r s : ℕ, rightmostCocyclePath C 0 r ≠
      rightmostCocyclePath C (0, (m : ℤ)) s)
    (hDisjointMU : ∀ r s : ℕ, rightmostCocyclePath C (0, (m : ℤ)) r ≠
      rightmostCocyclePath C (0, (ell : ℤ)) s)
    (hMiddleTail : ∀ r : ℕ, rightmostCocyclePath D (a2, M2) r =
      rightmostCocyclePath C (a2, M2) r)
    (hLowerBarrier : ∀ r s : ℕ,
      (rightmostCocyclePath D (rightmostCocyclePath C 0 r) s).2 ≤
        (rightmostCocyclePath C (rightmostCocyclePath C 0 r) s).2)
    (hUpperBarrier : ∀ r s : ℕ,
      (rightmostCocyclePath C (rightmostCocyclePath C (0, (ell : ℤ)) r) s).2 ≤
        (rightmostCocyclePath D (rightmostCocyclePath C (0, (ell : ℤ)) r) s).2)
    (v : Lattice) (N k : ℕ)
    (hMeet : rightmostCocyclePath D v N = rightmostCocyclePath D (a2, M2) k) :
    ∀ t : ℕ, t ≤ N → ∀ r : ℕ,
      rightmostCocyclePath D v t ≠ rightmostCocyclePath C 0 r ∧
      rightmostCocyclePath D v t ≠ rightmostCocyclePath C (0, (ell : ℤ)) r := by
  -- The joint theorem derives both strict orders from the physical source data.
  obtain ⟨hLM, hMU, _⟩ := rightmostCocyclePath_height_order_and_north_hit_order
    C m ell hm hmell M1 M2 a1 a2 hTop nL nM nU
    hNorthL hNorthM hNorthU hDisjointLM hDisjointMU
  -- Identify the alleged meeting with the actual old middle trace.
  have hOldMiddle : rightmostCocyclePath D v N =
      rightmostCocyclePath C (0, (m : ℤ)) (nM + k) := by
    calc
      rightmostCocyclePath D v N = rightmostCocyclePath D (a2, M2) k := hMeet
      _ = rightmostCocyclePath C (a2, M2) k := hMiddleTail k
      _ = rightmostCocyclePath C (rightmostCocyclePath C (0, (m : ℤ)) nM) k := by
        rw [hNorthM]
      _ = rightmostCocyclePath C (0, (m : ℤ)) (nM + k) :=
        outer_contact_path_restart C (0, (m : ℤ)) nM k
  intro t ht r
  constructor
  · intro hContact
    -- Restart D at the alleged lower contact and run the actual remaining time.
    have hContinuation :
        rightmostCocyclePath D (rightmostCocyclePath C 0 r) (N - t) =
          rightmostCocyclePath C (0, (m : ℤ)) (nM + k) := by
      rw [← hContact, outer_contact_path_restart, Nat.add_sub_of_le ht, hOldMiddle]
    -- Equal site levels give the exact old lower index at the meeting.
    have hIndex : r + (N - t) = m + (nM + k) := by
      have hNewLevel := outer_contact_path_level D (rightmostCocyclePath C 0 r) (N - t)
      have hLowerLevel := outer_contact_path_level C 0 r
      have hMiddleLevel := outer_contact_path_level C (0, (m : ℤ)) (nM + k)
      rw [hContinuation] at hNewLevel
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hLowerLevel hMiddleLevel
      omega
    have hMiddleIndex : r + (N - t) - m = nM + k := by omega
    have hOldOrder := hLM (r + (N - t)) (by omega)
    rw [hMiddleIndex] at hOldOrder
    -- A.5 places the meeting below that lower vertex, contrary to strict old order.
    have hBarrier := hLowerBarrier r (N - t)
    rw [hContinuation, outer_contact_path_restart] at hBarrier
    exact (not_lt_of_ge hBarrier) hOldOrder
  · intro hContact
    -- The upper contact uses the same remaining time, with its different starting level.
    have hContinuation :
        rightmostCocyclePath D (rightmostCocyclePath C (0, (ell : ℤ)) r) (N - t) =
          rightmostCocyclePath C (0, (m : ℤ)) (nM + k) := by
      rw [← hContact, outer_contact_path_restart, Nat.add_sub_of_le ht, hOldMiddle]
    have hIndex : ell + (r + (N - t)) = m + (nM + k) := by
      have hNewLevel := outer_contact_path_level D
        (rightmostCocyclePath C (0, (ell : ℤ)) r) (N - t)
      have hUpperLevel := outer_contact_path_level C (0, (ell : ℤ)) r
      have hMiddleLevel := outer_contact_path_level C (0, (m : ℤ)) (nM + k)
      rw [hContinuation] at hNewLevel
      simp only [zero_add] at hUpperLevel hMiddleLevel
      omega
    have hMiddleIndex : ell + (r + (N - t)) - m = nM + k := by omega
    have hUpperIndex : ell + (r + (N - t)) - ell = r + (N - t) := by omega
    have hOldOrder := hMU (ell + (r + (N - t))) (by omega)
    rw [hMiddleIndex, hUpperIndex] at hOldOrder
    -- Here A.5 places the meeting above the upper vertex; strict old order puts it below.
    have hBarrier := hUpperBarrier r (N - t)
    rw [outer_contact_path_restart, hContinuation] at hBarrier
    exact (not_lt_of_ge hBarrier) hOldOrder

end LPP.Busemann
