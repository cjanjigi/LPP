/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LatticeRayCrossingBalance
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Position and length bounds conditional on the literal discrete ray sum. -/

@[expose] public section

namespace LPPDifferentiability

private theorem fin_sequence_upper_bound {m : ℕ} (f : Fin (m + 1) → ℤ)
    (h : ∀ k : Fin m, f k.succ ≤ f k.castSucc + 1)
    (i j : Fin (m + 1)) (hij : i ≤ j) :
    f j ≤ f i + ((j.val - i.val : ℕ) : ℤ) := by
  revert i
  induction j using Fin.induction with
  | zero =>
    intro i hij
    change i.val ≤ 0 at hij
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      omega
    subst i
    simp only [Nat.sub_self, Nat.cast_zero, add_zero, le_refl]
  | succ j ih =>
    intro i hij
    by_cases hi : i = j.succ
    · subst i
      simp only [Nat.sub_self, Nat.cast_zero, add_zero, le_refl]
    · have hij' : i ≤ j.castSucc := by
        change i.val ≤ j.val
        have hne := Fin.val_ne_of_ne hi
        change i.val ≠ j.val + 1 at hne
        change i.val ≤ j.val + 1 at hij
        omega
      have hb := ih i hij'
      have hs := h j
      have hcast : (((j.succ).val - i.val : ℕ) : ℤ) =
          (((j.castSucc).val - i.val : ℕ) : ℤ) + 1 := by
        have hnat : (j.succ).val - i.val = (j.castSucc).val - i.val + 1 := by
          change i.val ≤ j.val at hij'
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        rw [hnat, Nat.cast_add, Nat.cast_one]
      omega

/-- Any two actual vertices differ by at most the walk length in either coordinate. -/
theorem lattice_walk_coordinate_difference_bounds
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (i j : Fin (m + 1)) :
    |(v i).1 - (v j).1| ≤ (m : ℤ) ∧ |(v i).2 - (v j).2| ≤ (m : ℤ) := by
  have hcoord (k : Fin m) :
      (-1 ≤ (v k.succ).1 - (v k.castSucc).1 ∧
        (v k.succ).1 - (v k.castSucc).1 ≤ 1) ∧
      (-1 ≤ (v k.succ).2 - (v k.castSucc).2 ∧
        (v k.succ).2 - (v k.castSucc).2 ≤ 1) := by
    rcases hstep k with h | h | h | h <;>
      have hx := congrArg Prod.fst h <;>
      have hy := congrArg Prod.snd h <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hx hy <;> omega
  have hscalar (f : Fin (m + 1) → ℤ)
      (hf : ∀ k : Fin m, -1 ≤ f k.succ - f k.castSucc ∧
        f k.succ - f k.castSucc ≤ 1) : |f i - f j| ≤ (m : ℤ) := by
    have hforward := fin_sequence_upper_bound f (fun k => by have hk := hf k; omega)
    have hbackward := fin_sequence_upper_bound (fun k => -f k)
      (fun k => by have hk := hf k; omega)
    have hi := i.isLt
    have hj := j.isLt
    by_cases hij : i ≤ j
    · have h₁ := hforward i j hij
      have h₂ := hbackward i j hij
      have hlength : ((j.val - i.val : ℕ) : ℤ) ≤ (m : ℤ) := by
        exact_mod_cast (show j.val - i.val ≤ m by omega)
      rw [abs_le]
      constructor <;> omega
    · have hji : j ≤ i := le_of_not_ge hij
      have h₁ := hforward j i hji
      have h₂ := hbackward j i hji
      have hlength : ((i.val - j.val : ℕ) : ℤ) ≤ (m : ℤ) := by
        exact_mod_cast (show i.val - j.val ≤ m by omega)
      rw [abs_le]
      constructor <;> omega
  exact ⟨hscalar (fun k => (v k).1) (fun k => (hcoord k).1),
    hscalar (fun k => (v k).2) (fun k => (hcoord k).2)⟩

/-- The actual vertices lie in the safe box with `(m+2)^2` integer sites. -/
theorem lattice_walk_vertex_bounds_of_ray_sum_ne_zero
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (hnonneg : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2)
    (hindex : (∑ i : Fin m,
      if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
      then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
      then -1 else 0) ≠ 0) :
    ∀ i, 0 ≤ (v i).1 ∧ (v i).1 ≤ (m : ℤ) + 1 ∧
      0 ≤ (v i).2 ∧ (v i).2 ≤ (m : ℤ) + 1 := by
  obtain ⟨j, hj⟩ :=
    exists_origin_vertex_of_ray_sum_ne_zero m v hclosed hstep hnonneg hindex
  intro i
  obtain ⟨hx, hy⟩ := lattice_walk_coordinate_difference_bounds m v hstep i j
  rw [hj] at hx hy
  simp only [sub_zero] at hx hy
  obtain ⟨hx₀, hy₀⟩ := hnonneg i
  have hx' := (abs_le.mp hx).2
  have hy' := (abs_le.mp hy).2
  exact ⟨hx₀, by omega, hy₀, by omega⟩

/-- Nonzero literal ray sum excludes the empty walk and two-step backtracking. -/
theorem four_le_length_of_ray_sum_ne_zero
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (hindex : (∑ i : Fin m,
      if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
      then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
      then -1 else 0) ≠ 0) : 4 ≤ m := by
  classical
  have hcount := (closed_lattice_walk_direction_balance m v hclosed hstep).2.2
  by_contra hm
  have hsmall : m = 0 ∨ m = 2 := by omega
  rcases hsmall with rfl | rfl
  · simp only [Fin.sum_univ_zero] at hindex
    exact hindex rfl
  · have hclose : v (2 : Fin 3) = v (0 : Fin 3) := hclosed.symm
    have hxy : (v (0 : Fin 3)).2 ≠ (v (1 : Fin 3)).2 →
        (v (0 : Fin 3)).1 = (v (1 : Fin 3)).1 := by
      rcases hstep (0 : Fin 2) with h | h | h | h <;>
        have hx := congrArg Prod.fst h <;>
        have hy := congrArg Prod.snd h <;>
        simp only [Prod.fst_sub, Prod.snd_sub] at hx hy <;>
        norm_num at hx hy <;> omega
    apply hindex
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceFinMk, add_zero]
    change ((if (v (0 : Fin 3)).2 = 0 ∧ (v (1 : Fin 3)).2 = 1 ∧
        1 ≤ (v (0 : Fin 3)).1 then (1 : ℤ)
      else if (v (0 : Fin 3)).2 = 1 ∧ (v (1 : Fin 3)).2 = 0 ∧
        1 ≤ (v (0 : Fin 3)).1 then -1 else 0) +
      (if (v (1 : Fin 3)).2 = 0 ∧ (v (2 : Fin 3)).2 = 1 ∧
        1 ≤ (v (1 : Fin 3)).1 then (1 : ℤ)
      else if (v (1 : Fin 3)).2 = 1 ∧ (v (2 : Fin 3)).2 = 0 ∧
        1 ≤ (v (1 : Fin 3)).1 then -1 else 0)) = 0
    rw [hclose]
    by_cases hy : (v (0 : Fin 3)).2 = (v (1 : Fin 3)).2
    · rw [hy]
      split_ifs <;> omega
    · have hx := hxy hy
      rw [hx]
      split_ifs <;> omega

end LPPDifferentiability
