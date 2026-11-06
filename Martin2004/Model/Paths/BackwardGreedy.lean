/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.Paths.Split
public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.Animals.Extension
public import LPP_Foundations.Model.Animals.Maximum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Backward greedy directed paths

Construct a directed path by choosing a predecessor of minimum cost, with the left predecessor
selected on ties. Bound its terminal-excluded negative-part weight by cutoff and remainder charges.

## Main results

- `exists_backwardGreedyPath`: construction with the backward greedy rule.
- `exists_backwardGreedyPath_charge`: the finite cutoff and remainder bound.
-/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

private theorem exists_snoc_relation {u : Lattice} {d : ℕ × ℕ}
    (R : Lattice → Lattice → Prop) (p : Path u d)
    (hp : ∀ i : Fin (d.1 + d.2), R (p.vertex i.castSucc) (p.vertex i.succ))
    (e : ℕ × ℕ) (he : e.1 + e.2 = 1)
    (hlast : R (u + ((d.1 : ℤ), (d.2 : ℤ)))
      (u + (((d + e).1 : ℤ), ((d + e).2 : ℤ)))) :
    ∃ q : Path u (d + e),
      ∀ i : Fin ((d + e).1 + (d + e).2),
        R (q.vertex i.castSucc) (q.vertex i.succ) := by
  let s := horizontalFirst (u + ((d.1 : ℤ), (d.2 : ℤ))) e
  refine ⟨p.concat s, ?_⟩
  intro i
  by_cases hi : i.val < d.1 + d.2
  · have hl := p.concat_vertex_left s (⟨i.val, by omega⟩ : Fin (d.1 + d.2 + 1))
    have hr := p.concat_vertex_left s (⟨i.val + 1, by omega⟩ : Fin (d.1 + d.2 + 1))
    exact (hl.symm ▸ hr.symm ▸ hp ⟨i.val, hi⟩)
  · have hiv : i.val = d.1 + d.2 := by
      have hh := i.isLt
      simp only [Prod.fst_add, Prod.snd_add] at hh
      omega
    have hl := p.concat_vertex_left s (Fin.last (d.1 + d.2))
    have hr := (p.concat s).finish
    have hli : i.castSucc = (⟨d.1 + d.2, by
        simp only [Prod.fst_add, Prod.snd_add]
        omega⟩ : Fin ((d + e).1 + (d + e).2 + 1)) := Fin.ext hiv
    have hri : i.succ = Fin.last ((d + e).1 + (d + e).2) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last, Prod.fst_add, Prod.snd_add]
      omega
    simp only [Fin.val_last] at hl
    rw [hli, hri, hl, hr, p.finish]
    exact hlast

/-- There is an actual up-right path with the backward greedy rule at every
current site strictly above both starting coordinates. Boundary steps form
the initial straight segment. The left predecessor is selected on ties. -/
theorem exists_backwardGreedyPath (Y : Environment) (u : Lattice) (d : ℕ × ℕ) :
    ∃ p : Path u d, ∀ i : Fin (d.1 + d.2),
      u.1 < (p.vertex i.succ).1 → u.2 < (p.vertex i.succ).2 →
      p.vertex i.castSucc =
        if Y (p.vertex i.succ - (1, 0)) ≤ Y (p.vertex i.succ - (0, 1)) then
          p.vertex i.succ - (1, 0) else p.vertex i.succ - (0, 1) := by
  let R : Lattice → Lattice → Prop := fun a v =>
    u.1 < v.1 → u.2 < v.2 →
      a = if Y (v - (1, 0)) ≤ Y (v - (0, 1)) then
        v - (1, 0) else v - (0, 1)
  suffices h : ∀ n : ℕ, ∀ a b : ℕ, a + b = n →
      ∃ p : Path u (a, b), ∀ i : Fin (a + b), R (p.vertex i.castSucc) (p.vertex i.succ) by
    exact h (d.1 + d.2) d.1 d.2 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab
    cases a with
    | zero =>
      refine ⟨horizontalFirst u (0, b), ?_⟩
      intro i hfst
      change u.1 < u.1 + (min i.succ.val 0 : ℕ) at hfst
      simp only [Nat.min_zero, Nat.cast_zero, add_zero, lt_self_iff_false] at hfst
    | succ a =>
      cases b with
      | zero =>
        refine ⟨horizontalFirst u (a + 1, 0), ?_⟩
        intro i _ hsnd
        change u.2 < u.2 + (i.succ.val - (a + 1) : ℕ) at hsnd
        have hi := i.isLt
        simp only [Nat.add_zero] at hi
        rw [Nat.sub_eq_zero_of_le (by simp only [Fin.val_succ]; omega)] at hsnd
        simp only [Nat.cast_zero, add_zero, lt_self_iff_false] at hsnd
      | succ b =>
        let v : Lattice := u + (((a + 1 : ℕ) : ℤ), ((b + 1 : ℕ) : ℤ))
        by_cases hchoice : Y (v - (1, 0)) ≤ Y (v - (0, 1))
        · obtain ⟨p, hp⟩ := ih (a + (b + 1)) (by omega) a (b + 1) rfl
          have hlast : R (u + ((a : ℤ), ((b + 1 : ℕ) : ℤ)))
              (u + ((((a, b + 1) + (1, 0)).1 : ℤ),
                (((a, b + 1) + (1, 0)).2 : ℤ))) := by
            intro _ _
            change u + ((a : ℤ), ((b + 1 : ℕ) : ℤ)) =
              if Y (v - (1, 0)) ≤ Y (v - (0, 1)) then v - (1, 0) else v - (0, 1)
            rw [ite_eq_left hchoice]
            apply Prod.ext <;> simp only [v, Prod.fst_add, Prod.snd_add,
              Prod.fst_sub, Prod.snd_sub, Nat.cast_add, Nat.cast_one] <;> omega
          simpa only [Prod.mk_add_mk, Nat.add_zero, Nat.add_one] using
            exists_snoc_relation R p hp (1, 0) rfl hlast
        · obtain ⟨p, hp⟩ := ih ((a + 1) + b) (by omega) (a + 1) b rfl
          have hlast : R (u + (((a + 1 : ℕ) : ℤ), (b : ℤ)))
              (u + ((((a + 1, b) + (0, 1)).1 : ℤ),
                (((a + 1, b) + (0, 1)).2 : ℤ))) := by
            intro _ _
            change u + (((a + 1 : ℕ) : ℤ), (b : ℤ)) =
              if Y (v - (1, 0)) ≤ Y (v - (0, 1)) then v - (1, 0) else v - (0, 1)
            rw [ite_eq_right hchoice]
            apply Prod.ext <;> simp only [v, Prod.fst_add, Prod.snd_add,
              Prod.fst_sub, Prod.snd_sub, Nat.cast_add, Nat.cast_one] <;> omega
          simpa only [Prod.mk_add_mk, Nat.add_zero, Nat.add_one] using
            exists_snoc_relation R p hp (0, 1) rfl hlast

/-- The chosen negative part is exactly the minimum of the alternatives. -/
theorem backwardGreedy_negativePart_eq_min (ω : Environment) (v : Lattice) :
    max (-ω (if max (-ω (v - (1, 0))) 0 ≤ max (-ω (v - (0, 1))) 0 then
        v - (1, 0) else v - (0, 1))) 0 =
      min (max (-ω (v - (1, 0))) 0) (max (-ω (v - (0, 1))) 0) := by
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

/-- One negative part is bounded by the cutoff and its actual remainder. -/
theorem negativePart_le_cutoff_add_remainder (x L : ℝ) (hL : 0 ≤ L) :
    max (-x) 0 ≤ L + max (-L - x) 0 := by
  apply max_le
  · have h := le_max_left (-L - x) 0
    linarith only [h]
  · have h := le_max_right (-L - x) 0
    exact add_nonneg hL h

/-- Pointwise greedy charges use the actual two-predecessor minimum. -/
theorem backwardGreedy_negativePart_le_cutoff_min (ω : Environment) (v : Lattice)
    (L : ℝ) (hL : 0 ≤ L) :
    max (-ω (if max (-ω (v - (1, 0))) 0 ≤ max (-ω (v - (0, 1))) 0 then
        v - (1, 0) else v - (0, 1))) 0 ≤
      L + min (max (-L - ω (v - (1, 0))) 0)
        (max (-L - ω (v - (0, 1))) 0) := by
  rw [backwardGreedy_negativePart_eq_min]
  calc
    min (max (-ω (v - (1, 0))) 0) (max (-ω (v - (0, 1))) 0) ≤
        min (L + max (-L - ω (v - (1, 0))) 0)
          (L + max (-L - ω (v - (0, 1))) 0) :=
      min_le_min (negativePart_le_cutoff_add_remainder _ L hL)
        (negativePart_le_cutoff_add_remainder _ L hL)
    _ = L + min (max (-L - ω (v - (1, 0))) 0)
        (max (-L - ω (v - (0, 1))) 0) := min_add_add_left _ _ _

/-- A produced finite connector has exact terminal-excluded charges. The
boundary summands are its straight initial segment; every other summand is
the actual greedy minimum at the later vertex of that step. -/
theorem exists_backwardGreedyPath_charge (ω : Environment) (u : Lattice)
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ p : Path u d,
      (∀ i : Fin (d.1 + d.2),
        u.1 < (p.vertex i.succ).1 → u.2 < (p.vertex i.succ).2 →
        p.vertex i.castSucc =
          if max (-ω (p.vertex i.succ - (1, 0))) 0 ≤
              max (-ω (p.vertex i.succ - (0, 1))) 0 then
            p.vertex i.succ - (1, 0) else p.vertex i.succ - (0, 1)) ∧
      pathWeight (fun v => max (-ω v) 0) p ≤
        (d.1 + d.2 : ℕ) * L +
          ∑ i : Fin (d.1 + d.2),
            if u.1 < (p.vertex i.succ).1 ∧ u.2 < (p.vertex i.succ).2 then
              min (max (-L - ω (p.vertex i.succ - (1, 0))) 0)
                (max (-L - ω (p.vertex i.succ - (0, 1))) 0)
            else max (-ω (p.vertex i.castSucc)) 0 := by
  obtain ⟨p, hp⟩ := exists_backwardGreedyPath (fun v => max (-ω v) 0) u d
  refine ⟨p, hp, ?_⟩
  calc
    pathWeight (fun v => max (-ω v) 0) p ≤
        ∑ i : Fin (d.1 + d.2), (L +
          if u.1 < (p.vertex i.succ).1 ∧ u.2 < (p.vertex i.succ).2 then
            min (max (-L - ω (p.vertex i.succ - (1, 0))) 0)
              (max (-L - ω (p.vertex i.succ - (0, 1))) 0)
          else max (-ω (p.vertex i.castSucc)) 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : u.1 < (p.vertex i.succ).1 ∧ u.2 < (p.vertex i.succ).2
      · rw [ite_eq_left hi, hp i hi.1 hi.2]
        exact backwardGreedy_negativePart_le_cutoff_min ω (p.vertex i.succ) L hL
      · rw [ite_eq_right hi]
        exact le_add_of_nonneg_left hL
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end LPPDifferentiability
