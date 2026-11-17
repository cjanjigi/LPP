/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! A strict finite boundary detour for arbitrary real weights. -/

@[expose] public section
open scoped BigOperators

namespace LPPDifferentiability

/-- If the collected weights away from the entry are at most `K`, while the
vertical boundary has a strict excess and the horizontal boundary has weights
at least `K`, the vertical-then-horizontal route has greater weight. Its
trace is the actual path used in the finite detour in GRS, arXiv:1510.00860v1,
Appendix A.4, lines 1616–1632 and 1673–1687. -/
theorem exists_vertical_then_horizontal_strict_detour
    (ω : LPPDifferentiability.Environment) (u : LPPDifferentiability.Lattice)
    (a b : ℕ) (ha : 0 < a) (_hb : 0 < b)
    (K : ℝ) (p : LPPDifferentiability.Path u (b, a))
    (hInterior : ∀ i : Fin (b + a), 0 < i.val →
      ω (p.vertex i.castSucc) ≤ K)
    (hWest : ((a - 1 : ℕ) : ℝ) * K <
      ∑ r : Fin (a - 1), ω (u + ((0 : ℤ), ((r.val + 1 : ℕ) : ℤ))))
    (hNorth : ∀ i : Fin b, K ≤ ω (u + (Int.ofNat i.val, Int.ofNat a))) :
    ∃ q : LPPDifferentiability.Path u (b, a),
      (∀ i : Fin (b + a + 1), i.val ≤ a →
        q.vertex i = u + ((0 : ℤ), (i.val : ℤ))) ∧
      (∀ i : Fin (b + a + 1), a ≤ i.val →
        q.vertex i = u + (((i.val - a : ℕ) : ℤ), (a : ℤ))) ∧
      LPPDifferentiability.pathWeight ω p < LPPDifferentiability.pathWeight ω q := by
  cases a with
  | zero => omega
  | succ a =>
    let q : Path u (b, a + 1) := {
      vertex := fun i => (u.1 + ((i.val - (a + 1) : ℕ) : ℤ),
        u.2 + ((min i.val (a + 1) : ℕ) : ℤ))
      start := by simp
      finish := by
        apply Prod.ext <;> simp
      step := by
        intro i
        by_cases h : i.val < a + 1
        · right
          apply Prod.ext
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.fst_add]
            rw [Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega)]
            simp
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.snd_add]
            rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
            simp only [Nat.cast_add, Nat.cast_one]
            omega
        · left
          apply Prod.ext
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.fst_add]
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            simp only [Nat.cast_add, Nat.cast_one]
            omega
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.snd_add]
            rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
            simp }
    have hvertical (i : Fin (b + (a + 1) + 1)) (hi : i.val ≤ a + 1) :
        q.vertex i = u + ((0 : ℤ), (i.val : ℤ)) := by
      apply Prod.ext
      · simp [q, Nat.sub_eq_zero_of_le hi]
      · simp [q, Nat.min_eq_left hi]
    have hhorizontal (i : Fin (b + (a + 1) + 1)) (hi : a + 1 ≤ i.val) :
        q.vertex i = u + (((i.val - (a + 1) : ℕ) : ℤ), ((a + 1 : ℕ) : ℤ)) := by
      apply Prod.ext
      · simp [q]
      · simp [q, Nat.min_eq_right hi]
    refine ⟨q, hvertical, hhorizontal, ?_⟩
    have hlen : b + (a + 1) = (a + b) + 1 := by omega
    let tail (r : Path u (b, a + 1)) (i : Fin (a + b)) : ℝ :=
      ω (r.vertex ((i.succ.cast hlen.symm).castSucc))
    have hsplit (r : Path u (b, a + 1)) :
        pathWeight ω r = ω u + ∑ i : Fin (a + b), tail r i := by
      unfold pathWeight
      rw [← Fin.sum_congr' _ hlen.symm, Fin.sum_univ_succ]
      congr 1
      · simpa using congrArg ω r.start
    have hupper : (∑ i : Fin (a + b), tail p i) ≤ ((a + b : ℕ) : ℝ) * K := by
      calc
        _ ≤ ∑ _i : Fin (a + b), K := by
          apply Finset.sum_le_sum
          intro i _
          apply hInterior
          simp
        _ = ((a + b : ℕ) : ℝ) * K := by simp
    have hwest : (∑ i : Fin a, tail q (Fin.castAdd b i)) =
        ∑ i : Fin a, ω (u + ((0 : ℤ), ((i.val + 1 : ℕ) : ℤ))) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [tail]
      have ht := hvertical ((Fin.castAdd b i).succ.cast hlen.symm |>.castSucc) (by simp)
      simpa using congrArg ω ht
    have hnorth : (∑ i : Fin b, tail q (Fin.natAdd a i)) =
        ∑ i : Fin b, ω (u + ((i.val : ℤ), ((a + 1 : ℕ) : ℤ))) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [tail]
      have ht := hhorizontal ((Fin.natAdd a i).succ.cast hlen.symm |>.castSucc) (by simp)
      simpa using congrArg ω ht
    have hnorthbound : ((b : ℕ) : ℝ) * K ≤
        ∑ i : Fin b, ω (u + ((i.val : ℤ), ((a + 1 : ℕ) : ℤ))) := by
      calc
        _ = ∑ _i : Fin b, K := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => hNorth i
    have hlower : ((a + b : ℕ) : ℝ) * K < ∑ i : Fin (a + b), tail q i := by
      rw [Fin.sum_univ_add, hwest, hnorth]
      simp only [Nat.succ_sub_one] at hWest
      have hcast : ((a + b : ℕ) : ℝ) * K = (a : ℝ) * K + (b : ℝ) * K := by
        push_cast
        ring
      rw [hcast]
      exact add_lt_add_of_lt_of_le hWest hnorthbound
    rw [hsplit p, hsplit q]
    linarith

end LPPDifferentiability
