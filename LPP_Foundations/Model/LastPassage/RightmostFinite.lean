/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Model.Paths.Fintype
import LPP_Foundations.Model.Paths.Translate
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! A finite tie-breaking argument for a greatest maximizing up-right path. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

private theorem path_first_step_bounds {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (i : Fin (d.1 + d.2)) :
    (p.vertex i.castSucc).1 ≤ (p.vertex i.succ).1 ∧
      (p.vertex i.succ).1 ≤ (p.vertex i.castSucc).1 + 1 := by
  rcases p.step i with h | h
  · have h₁ := congrArg Prod.fst h
    simp only [Prod.fst_add] at h₁
    constructor <;> omega
  · have h₁ := congrArg Prod.fst h
    simp only [Prod.fst_add] at h₁
    constructor <;> omega

private theorem max_step_bounds {a b a' b' : ℤ}
    (ha : a ≤ a') (ha' : a' ≤ a + 1)
    (hb : b ≤ b') (hb' : b' ≤ b + 1) :
    max a b ≤ max a' b' ∧ max a' b' ≤ max a b + 1 := by
  constructor
  · apply max_le
    · exact le_trans ha (le_max_left a' b')
    · exact le_trans hb (le_max_right a' b')
  · have h₁ : a' ≤ max a b + 1 := by omega
    have h₂ : b' ≤ max a b + 1 := by omega
    exact max_le h₁ h₂

private theorem min_step_bounds {a b a' b' : ℤ}
    (ha : a ≤ a') (ha' : a' ≤ a + 1)
    (hb : b ≤ b') (hb' : b' ≤ b + 1) :
    min a b ≤ min a' b' ∧ min a' b' ≤ min a b + 1 := by
  constructor
  · apply le_min
    · exact le_trans (min_le_left a b) ha
    · exact le_trans (min_le_right a b) hb
  · rcases le_total a b with hab | hba
    · rw [min_eq_left hab]
      exact le_trans (min_le_left a' b') ha'
    · rw [min_eq_right hba]
      exact le_trans (min_le_right a' b') hb'

private def southeastVertex {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) (i : Fin (d.1 + d.2 + 1)) : Lattice :=
  (max (p.vertex i).1 (q.vertex i).1,
    u.1 + u.2 + (i.val : ℤ) - max (p.vertex i).1 (q.vertex i).1)

private def northwestVertex {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) (i : Fin (d.1 + d.2 + 1)) : Lattice :=
  (min (p.vertex i).1 (q.vertex i).1,
    u.1 + u.2 + (i.val : ℤ) - min (p.vertex i).1 (q.vertex i).1)

private theorem southeastVertex_level {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) (i : Fin (d.1 + d.2 + 1)) :
    (southeastVertex p q i).1 + (southeastVertex p q i).2 =
      u.1 + u.2 + (i.val : ℤ) := by
  simp only [southeastVertex]
  omega

private theorem northwestVertex_level {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) (i : Fin (d.1 + d.2 + 1)) :
    (northwestVertex p q i).1 + (northwestVertex p q i).2 =
      u.1 + u.2 + (i.val : ℤ) := by
  simp only [northwestVertex]
  omega

private def southeastPath {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) : Path u d where
  vertex := southeastVertex p q
  start := by
    simp [southeastVertex, p.start, q.start]
  finish := by
    apply Prod.ext
    · have hp := congrArg Prod.fst p.finish
      have hq := congrArg Prod.fst q.finish
      simp only [Prod.fst_add] at hp hq
      change max (p.vertex (Fin.last (d.1 + d.2))).1
          (q.vertex (Fin.last (d.1 + d.2))).1 =
        (u + ((d.1 : ℤ), (d.2 : ℤ))).1
      rw [hp, hq]
      simp only [max_self, Prod.fst_add]
    · have hp₁ := congrArg Prod.fst p.finish
      have hp₂ := congrArg Prod.snd p.finish
      have hq₁ := congrArg Prod.fst q.finish
      simp only [Prod.fst_add, Prod.snd_add] at hp₁ hp₂ hq₁
      have hlevel := p.level (Fin.last (d.1 + d.2))
      rw [hp₁, hp₂] at hlevel
      change u.1 + u.2 + ((Fin.last (d.1 + d.2)).val : ℤ) -
          max (p.vertex (Fin.last (d.1 + d.2))).1
            (q.vertex (Fin.last (d.1 + d.2))).1 =
        (u + ((d.1 : ℤ), (d.2 : ℤ))).2
      rw [hp₁, hq₁]
      simp only [max_self, Prod.snd_add, Fin.val_last, Nat.cast_add] at hlevel ⊢
      omega
  step i := by
    have hp := path_first_step_bounds p i
    have hq := path_first_step_bounds q i
    have hx := max_step_bounds hp.1 hp.2 hq.1 hq.2
    have htime : (i.succ.val : ℤ) = (i.castSucc.val : ℤ) + 1 := by simp
    have hchoice :
        max (p.vertex i.succ).1 (q.vertex i.succ).1 =
            max (p.vertex i.castSucc).1 (q.vertex i.castSucc).1 ∨
          max (p.vertex i.succ).1 (q.vertex i.succ).1 =
            max (p.vertex i.castSucc).1 (q.vertex i.castSucc).1 + 1 := by
      omega
    rcases hchoice with hzero | hone
    · right
      apply Prod.ext
      · simpa only [southeastVertex, Prod.fst_add, add_zero] using hzero
      · simp only [southeastVertex, Prod.snd_add, Fin.val_succ,
          Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        omega
    · left
      apply Prod.ext
      · simpa only [southeastVertex, Prod.fst_add] using hone
      · simp only [southeastVertex, Prod.snd_add, Fin.val_succ,
          Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        omega

private def northwestPath {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) : Path u d where
  vertex := northwestVertex p q
  start := by
    simp [northwestVertex, p.start, q.start]
  finish := by
    apply Prod.ext
    · have hp := congrArg Prod.fst p.finish
      have hq := congrArg Prod.fst q.finish
      simp only [Prod.fst_add] at hp hq
      change min (p.vertex (Fin.last (d.1 + d.2))).1
          (q.vertex (Fin.last (d.1 + d.2))).1 =
        (u + ((d.1 : ℤ), (d.2 : ℤ))).1
      rw [hp, hq]
      simp only [min_self, Prod.fst_add]
    · have hp₁ := congrArg Prod.fst p.finish
      have hp₂ := congrArg Prod.snd p.finish
      have hq₁ := congrArg Prod.fst q.finish
      simp only [Prod.fst_add, Prod.snd_add] at hp₁ hp₂ hq₁
      have hlevel := p.level (Fin.last (d.1 + d.2))
      rw [hp₁, hp₂] at hlevel
      change u.1 + u.2 + ((Fin.last (d.1 + d.2)).val : ℤ) -
          min (p.vertex (Fin.last (d.1 + d.2))).1
            (q.vertex (Fin.last (d.1 + d.2))).1 =
        (u + ((d.1 : ℤ), (d.2 : ℤ))).2
      rw [hp₁, hq₁]
      simp only [min_self, Prod.snd_add, Fin.val_last, Nat.cast_add] at hlevel ⊢
      omega
  step i := by
    have hp := path_first_step_bounds p i
    have hq := path_first_step_bounds q i
    have hx := min_step_bounds hp.1 hp.2 hq.1 hq.2
    have htime : (i.succ.val : ℤ) = (i.castSucc.val : ℤ) + 1 := by simp
    have hchoice :
        min (p.vertex i.succ).1 (q.vertex i.succ).1 =
            min (p.vertex i.castSucc).1 (q.vertex i.castSucc).1 ∨
          min (p.vertex i.succ).1 (q.vertex i.succ).1 =
            min (p.vertex i.castSucc).1 (q.vertex i.castSucc).1 + 1 := by
      omega
    rcases hchoice with hzero | hone
    · right
      apply Prod.ext
      · simpa only [northwestVertex, Prod.fst_add, add_zero] using hzero
      · simp only [northwestVertex, Prod.snd_add, Fin.val_succ,
          Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        omega
    · left
      apply Prod.ext
      · simpa only [northwestVertex, Prod.fst_add] using hone
      · simp only [northwestVertex, Prod.snd_add, Fin.val_succ,
          Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        omega

private theorem vertex_eq_of_first_and_level {x y : Lattice} {l : ℤ}
    (hfirst : x.1 = y.1) (hx : x.1 + x.2 = l) (hy : y.1 + y.2 = l) :
    x = y := by
  apply Prod.ext
  · exact hfirst
  · omega

private theorem southeast_northwest_vertices_swap {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) (i : Fin (d.1 + d.2 + 1)) :
    (southeastVertex p q i = p.vertex i ∧ northwestVertex p q i = q.vertex i) ∨
      (southeastVertex p q i = q.vertex i ∧ northwestVertex p q i = p.vertex i) := by
  rcases le_total (p.vertex i).1 (q.vertex i).1 with h | h
  · right
    have hmax : max (p.vertex i).1 (q.vertex i).1 = (q.vertex i).1 := max_eq_right h
    have hmin : min (p.vertex i).1 (q.vertex i).1 = (p.vertex i).1 := min_eq_left h
    constructor
    · apply vertex_eq_of_first_and_level
      · simpa only [southeastVertex] using hmax
      · exact southeastVertex_level p q i
      · exact q.level i
    · apply vertex_eq_of_first_and_level
      · simpa only [northwestVertex] using hmin
      · exact northwestVertex_level p q i
      · exact p.level i
  · left
    have hmax : max (p.vertex i).1 (q.vertex i).1 = (p.vertex i).1 := max_eq_left h
    have hmin : min (p.vertex i).1 (q.vertex i).1 = (q.vertex i).1 := min_eq_right h
    constructor
    · apply vertex_eq_of_first_and_level
      · simpa only [southeastVertex] using hmax
      · exact southeastVertex_level p q i
      · exact p.level i
    · apply vertex_eq_of_first_and_level
      · simpa only [northwestVertex] using hmin
      · exact northwestVertex_level p q i
      · exact q.level i

private theorem envelope_weights_sum (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p q : Path u d) :
    pathWeight ω (southeastPath p q) + pathWeight ω (northwestPath p q) =
      pathWeight ω p + pathWeight ω q := by
  classical
  simp only [pathWeight]
  calc
    (∑ i : Fin (d.1 + d.2), ω ((southeastPath p q).vertex i.castSucc)) +
        ∑ i : Fin (d.1 + d.2), ω ((northwestPath p q).vertex i.castSucc) =
      ∑ i : Fin (d.1 + d.2),
        (ω ((southeastPath p q).vertex i.castSucc) +
          ω ((northwestPath p q).vertex i.castSucc)) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin (d.1 + d.2),
        (ω (p.vertex i.castSucc) + ω (q.vertex i.castSucc)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases southeast_northwest_vertices_swap p q i.castSucc with h | h
          · simp only [southeastPath, northwestPath]
            simp [h.1, h.2]
          · simp only [southeastPath, northwestPath]
            simp [h.1, h.2, add_comm]
    _ = (∑ i : Fin (d.1 + d.2), ω (p.vertex i.castSucc)) +
        ∑ i : Fin (d.1 + d.2), ω (q.vertex i.castSucc) := by
          rw [Finset.sum_add_distrib]

private def firstCoordinateScore {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) : ℤ :=
  ∑ i : Fin (d.1 + d.2 + 1), (p.vertex i).1

/-- A maximizing path can be chosen to lie weakly to the right of every maximizing path.
This fills the finite-path omission cited in the source at lines 187–195 and 732. -/
theorem exists_unique_rightmost_maximizing_path
    (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    ∃! p : Path u d,
      pathWeight ω p = lastPassage ω u d ∧
      ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
        ∀ i : Fin (d.1 + d.2 + 1), (q.vertex i).1 ≤ (p.vertex i).1 := by
  classical
  let maximizingPaths : Finset (Path u d) :=
    Finset.univ.filter fun r => pathWeight ω r = lastPassage ω u d
  obtain ⟨p₀, hp₀⟩ := exists_pathWeight_eq_lastPassage ω u d
  have hp₀Mem : p₀ ∈ maximizingPaths := by
    simp [maximizingPaths, hp₀]
  obtain ⟨p, hpMem, hscoreMax⟩ :=
    maximizingPaths.exists_max_image firstCoordinateScore ⟨p₀, hp₀Mem⟩
  have hpWeight : pathWeight ω p = lastPassage ω u d := by
    simpa [maximizingPaths] using hpMem
  have hdom : ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
      ∀ i : Fin (d.1 + d.2 + 1), (q.vertex i).1 ≤ (p.vertex i).1 := by
    intro q hq i
    by_contra hnot
    have hstrict : (p.vertex i).1 < (q.vertex i).1 := lt_of_not_ge hnot
    have hsum := envelope_weights_sum ω p q
    have hseUpper := pathWeight_le_lastPassage ω (southeastPath p q)
    have hnwUpper := pathWeight_le_lastPassage ω (northwestPath p q)
    rw [hpWeight, hq] at hsum
    have hseWeight : pathWeight ω (southeastPath p q) = lastPassage ω u d := by
      linarith
    have hseMem : southeastPath p q ∈ maximizingPaths := by
      simp [maximizingPaths, hseWeight]
    have hscoreStrict : firstCoordinateScore p < firstCoordinateScore (southeastPath p q) := by
      unfold firstCoordinateScore
      apply Finset.sum_lt_sum
      · intro j hj
        exact le_max_left (p.vertex j).1 (q.vertex j).1
      · exact ⟨i, Finset.mem_univ i,
          lt_of_lt_of_le hstrict (le_max_right (p.vertex i).1 (q.vertex i).1)⟩
    exact (not_lt_of_ge (hscoreMax (southeastPath p q) hseMem)) hscoreStrict
  refine ⟨p, ⟨hpWeight, hdom⟩, ?_⟩
  intro q hq
  rcases hq with ⟨hqWeight, hqdom⟩
  apply Path.ext
  intro i
  apply Prod.ext
  · exact le_antisymm (hdom q hqWeight i) (hqdom p hpWeight i)
  · have hfirst := le_antisymm (hdom q hqWeight i) (hqdom p hpWeight i)
    have hpLevel := p.level i
    have hqLevel := q.level i
    omega

end LPPDifferentiability
