/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.LevelNet
import Mathlib.Tactic

/-! Finite lattice nets on signed levels, with the source interval coverage. -/

public section

namespace LPPDifferentiability

/-- Ordinary existence of the source finite net. Every coordinate, gap,
endpoint and interval conclusion concerns the same actual lattice family. -/
theorem exists_level_net (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (m : ℕ) (hm : 1 ≤ min a (1 - a) * m / 4)
    (I : ℤ) (A B : ℝ) (hwidth : (m : ℝ) ≤ B - A) :
    ∃ (M : ℕ) (v : Fin (M + 1) → Lattice),
      1 ≤ M ∧ Function.Injective v ∧
      (∀ j, (v j).1 + (v j).2 = I ∧
        A ≤ (1-a) * (v j).1 - a * (v j).2 ∧
        (1-a) * (v j).1 - a * (v j).2 ≤ B) ∧
      (∀ (j : ℕ) (hj : j < M),
        min a (1-a) * m / 4 ≤
          ((1-a) * (v ⟨j+1, by omega⟩).1 - a * (v ⟨j+1, by omega⟩).2) -
          ((1-a) * (v ⟨j, by omega⟩).1 - a * (v ⟨j, by omega⟩).2) ∧
        ((1-a) * (v ⟨j+1, by omega⟩).1 - a * (v ⟨j+1, by omega⟩).2) -
          ((1-a) * (v ⟨j, by omega⟩).1 - a * (v ⟨j, by omega⟩).2) ≤
          min a (1-a) * m / 2) ∧
      (∀ j, ((1-a) * (v j).1 - a * (v j).2 ≤ A + min a (1-a) * m / 2 ↔
        j.val = 0)) ∧
      (∀ j, (B - min a (1-a) * m / 2 ≤ (1-a) * (v j).1 - a * (v j).2 ↔
        j.val = M)) ∧
      ((1-a) * (v ⟨0, by omega⟩).1 - a * (v ⟨0, by omega⟩).2 ≤
        A + min a (1-a) * m / 2) ∧
      (B - min a (1-a) * m / 2 ≤
        (1-a) * (v ⟨M, by omega⟩).1 - a * (v ⟨M, by omega⟩).2) ∧
      (M + 1 : ℝ) < 4 * (B-A) / (min a (1-a) * m) ∧
      (∀ γ : ℝ, A ≤ γ → γ + m ≤ B →
        ∃ j, γ ≤ (1-a) * (v j).1 - a * (v j).2 ∧
          (1-a) * (v j).1 - a * (v j).2 ≤ γ + m) := by
  let t : ℝ := min a (1-a) * m / 4
  have ht : 1 ≤ t := hm
  have htheta : min a (1-a) ≤ (1/2 : ℝ) := by
    have h₁ := min_le_left a (1-a)
    have h₂ := min_le_right a (1-a)
    linarith
  have htheta_pos : 0 < min a (1-a) := lt_min ha (by linarith)
  have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm8 : 8 * t ≤ (m : ℝ) := by
    dsimp [t]
    nlinarith only [mul_le_mul_of_nonneg_right htheta hmnonneg]
  obtain ⟨M, p, q, hM, hqlo, hqhi, hfirstA, hfirst, hsecond,
    hlast, hlastB, hbefore, hcard⟩ :=
    exists_integer_level_grid t A B (a * I) ht (hm8.trans hwidth)
  let v : Fin (M+1) → Lattice := fun j =>
    (p + (j.val : ℤ) * q, I - (p + (j.val : ℤ) * q))
  let x : Fin (M+1) → ℝ := fun j => (p : ℝ) + j.val * (q : ℝ) - a * I
  have hr (j : Fin (M+1)) : (1-a) * (v j).1 - a * (v j).2 = x j := by
    dsimp [v, x]
    push_cast
    ring
  have hqpos : 0 < (q : ℝ) := by linarith
  have hx0 : x ⟨0, by omega⟩ = (p : ℝ) - a * I := by simp only [x, Nat.cast_zero, zero_mul, add_zero]
  have hxM : x ⟨M, by omega⟩ = (p : ℝ) + M * (q : ℝ) - a * I := rfl
  have hgap (j : ℕ) (hj : j < M) :
      x ⟨j+1, by omega⟩ - x ⟨j, by omega⟩ = (q : ℝ) := by
    dsimp [x]
    push_cast
    ring
  have hinj : Function.Injective v := by
    intro i j hij
    have hxij : x i = x j := by rw [← hr i, ← hr j, hij]
    have hval : (i.val : ℝ) = j.val := by
      dsimp [x] at hxij
      nlinarith only [hxij, hqpos]
    apply Fin.ext
    exact_mod_cast hval
  have hleft (j : Fin (M+1)) : x j ≤ A + 2*t ↔ j.val = 0 := by
    constructor
    · intro hj
      by_contra hn
      have hj1 : (1 : ℝ) ≤ j.val := by exact_mod_cast (show 1 ≤ j.val by omega)
      have hmul := mul_le_mul_of_nonneg_right hj1 hqpos.le
      dsimp [x] at hj
      linarith
    · intro hj
      dsimp [x]
      rw [hj]
      simpa only [Nat.cast_zero, zero_mul, add_zero] using hfirst
  have hright (j : Fin (M+1)) : B-2*t ≤ x j ↔ j.val = M := by
    constructor
    · intro hj
      by_contra hn
      have hjM : j.val < M := by omega
      have := hbefore j.val hjM
      change x j < B-2*t at this
      linarith
    · intro hj
      dsimp [x]
      rw [hj]
      exact hlast
  refine ⟨M, v, hM, hinj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · dsimp [v]
      omega
    · rw [hr]
      have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
      have := mul_nonneg hj0 hqpos.le
      dsimp [x]
      linarith
    · rw [hr]
      have hjM : (j.val : ℝ) ≤ M := by exact_mod_cast (show j.val ≤ M by omega)
      have := mul_le_mul_of_nonneg_right hjM hqpos.le
      dsimp [x]
      linarith
  · intro j hj
    rw [hr, hr, hgap j hj]
    constructor
    · exact hqlo
    · dsimp [t] at hqhi
      linarith
  · intro j
    rw [hr]
    have heq : min a (1-a) * m / 2 = 2*t := by dsimp [t]; ring
    rw [heq]
    exact hleft j
  · intro j
    rw [hr]
    have heq : min a (1-a) * m / 2 = 2*t := by dsimp [t]; ring
    rw [heq]
    exact hright j
  · rw [hr, hx0]
    dsimp [t] at hfirst
    linarith
  · rw [hr, hxM]
    dsimp [t] at hlast
    linarith
  · convert hcard using 1
    dsimp [t]
    rw [div_div_eq_mul_div]
    ring
  · intro γ hγA hγB
    let L := max γ (A+2*t)
    let U := min (γ+m) (B-2*t)
    have hlen : L + 2*t ≤ U := by
      dsimp [L, U]
      apply le_min
      · rcases le_total γ (A+2*t) with h | h
        · rw [max_eq_right h]
          linarith
        · rw [max_eq_left h]
          linarith
      · rcases le_total γ (A+2*t) with h | h
        · rw [max_eq_right h]
          linarith
        · rw [max_eq_left h]
          linarith
    obtain ⟨j, hjL, hjU⟩ := finite_grid_interval_coverage M x L U (2*t) (by linarith) hlen
      (by rw [hx0]; exact hfirst.trans (le_max_right _ _))
      ((min_le_right _ _).trans (by rw [hxM]; exact hlast))
      (by intro j hj; rw [hgap j hj]; exact hqhi)
    refine ⟨j, ?_, ?_⟩
    · rw [hr]
      exact (le_max_left _ _).trans hjL
    · rw [hr]
      exact hjU.trans (min_le_left _ _)

end LPPDifferentiability
