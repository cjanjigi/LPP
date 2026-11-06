/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GreedyAttachmentRectangle
public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Model.Paths.Geometry
import Mathlib.Tactic

/-! The actual greedy prefix followed by the source horizontal-first box phase. -/

@[expose] public section
namespace LPPDifferentiability
namespace GreedyAttachment
open scoped Classical

private theorem splice_sequence (u : Lattice) (d e : ℕ × ℕ) (n : ℕ)
    (x : ℕ → Lattice) (V : Set Lattice)
    (hx0 : x 0 = u)
    (hxstep : ∀ i, x (i + 1) = x i + (1, 0) ∨ x (i + 1) = x i + (0, 1))
    (q : Path (x n) e) (hlen : n + (e.1 + e.2) = d.1 + d.2)
    (hend : x n + ((e.1 : ℤ), (e.2 : ℤ)) = u + ((d.1 : ℤ), (d.2 : ℤ)))
    (hxgood : ∀ i ≤ n, x i ∉ V)
    (hqgood : ∀ j, q.vertex j ∉ V) :
    ∃ p : Path u d,
      (∀ (i : ℕ) (hi : i ≤ n),
        p.vertex ⟨i, by omega⟩ = x i) ∧
      (∀ j, p.vertex j ∉ V) := by
  have hn : n ≤ d.1 + d.2 := by omega
  let v : Fin (d.1 + d.2 + 1) → Lattice := fun i =>
    if h : i.val < n then x i.val
    else q.vertex ⟨i.val - n, by have hi := i.isLt; omega⟩
  have hleft (i : ℕ) (hi : i ≤ n) : v ⟨i, by omega⟩ = x i := by
    dsimp only [v]
    split_ifs with h
    · rfl
    · have hin : i = n := by omega
      subst i
      convert q.start using 1
      congr 1
      apply Fin.ext
      exact Nat.sub_self n
  have hright (j : Fin (e.1 + e.2 + 1)) :
      v ⟨n + j.val, by have hj := j.isLt; omega⟩ = q.vertex j := by
    dsimp only [v]
    rw [dite_eq_right (by omega)]
    congr 1
    apply Fin.ext
    exact Nat.add_sub_cancel_left n j.val
  let p : Path u d := {
    vertex := v
    start := (hleft 0 (Nat.zero_le n)).trans hx0
    finish := by
      have he : (Fin.last (d.1 + d.2) : Fin (d.1 + d.2 + 1)) =
          ⟨n + (Fin.last (e.1 + e.2)).val, by simp only [Fin.val_last]; omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [he, hright]
      exact q.finish.trans hend
    step := by
      intro i
      by_cases hi : i.val < n
      · have hl := hleft i.val (by omega)
        have hr := hleft (i.val + 1) (by omega)
        change v i.succ = v i.castSucc + (1, 0) ∨ v i.succ = v i.castSucc + (0, 1)
        rw [show v i.castSucc = x i.val from hl,
          show v i.succ = x (i.val + 1) from hr]
        exact hxstep i.val
      · let j : Fin (e.1 + e.2) := ⟨i.val - n, by have hi' := i.isLt; omega⟩
        have hl : v i.castSucc = q.vertex j.castSucc := by
          convert hright j.castSucc using 1
          congr 1
          apply Fin.ext
          dsimp only [j, Fin.val_castSucc]
          omega
        have hr : v i.succ = q.vertex j.succ := by
          convert hright j.succ using 1
          congr 1
          apply Fin.ext
          dsimp only [j, Fin.val_succ]
          omega
        change v i.succ = v i.castSucc + (1, 0) ∨ v i.succ = v i.castSucc + (0, 1)
        rw [hl, hr]
        exact q.step j }
  refine ⟨p, hleft, ?_⟩
  intro i
  change v i ∉ V
  by_cases hi : i.val ≤ n
  · have hvi : v i = x i.val := hleft i.val hi
    rw [hvi]
    exact hxgood i.val hi
  · let j : Fin (e.1 + e.2 + 1) := ⟨i.val - n, by have hi' := i.isLt; omega⟩
    have hvj : v i = q.vertex j := by
      convert hright j using 1
      congr 1
      apply Fin.ext
      dsimp only [j]
      omega
    rw [hvj]
    exact hqgood j

/-- Construct the source's actual greedy/box attachment. Every vertex of the
same returned Path, including its terminal vertex, is good. The hypotheses
are precisely the local geometric consequences of E1, E2 and E3 (Section B.2 of the
differentiability preprint). -/
theorem exists_bad_avoiding_attachment (u : Lattice) (d : ℕ × ℕ)
    (V : Set Lattice) (K : ℕ) (hK : 2 ≤ K) (hm : 4 * K + 4 ≤ d.1 + d.2)
    (hq₁ : 1 / 4 ≤ (d.1 : ℝ) / (d.1 + d.2 : ℕ))
    (hq₂ : (d.1 : ℝ) / (d.1 + d.2 : ℕ) ≤ 3 / 4) (hu : u ∉ V)
    (hsep : ∀ z ∈ Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))),
      ∀ w ∈ Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))),
      z ∈ V → w ∈ V → z ≠ w →
      ¬ (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)| ≤ 2))
    (hbox : ∀ z ∈ Set.Icc
      (u + ((d.1 : ℤ), (d.2 : ℤ)) - (((4 * K + 4 : ℕ) : ℤ), ((4 * K + 4 : ℕ) : ℤ)))
      (u + ((d.1 : ℤ), (d.2 : ℤ))), z ∉ V)
    (hbad : ((Finset.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ)))).filter (fun z => z ∈ V ∧
      |(z.1 : ℝ) - (u.1 : ℝ) - (((z.1 + z.2 - (u.1 + u.2) : ℤ) : ℝ)) *
        ((d.1 : ℝ) / (d.1 + d.2 : ℕ))| ≤ (K : ℝ) + 2)).card < K) :
    ∃ p : Path u d,
      (∀ (i : ℕ) (hi : i ≤ d.1 + d.2 - (4 * K + 4)),
        p.vertex ⟨i, by omega⟩ =
          vertex u ((d.1 : ℝ) / (d.1 + d.2 : ℕ)) V i) ∧
      p.vertex (Fin.last (d.1 + d.2)) = u + ((d.1 : ℤ), (d.2 : ℤ)) ∧
      (∀ i, p.vertex i ∉ V) := by
  let n := d.1 + d.2 - (4 * K + 4)
  let q : ℝ := (d.1 : ℝ) / (d.1 + d.2 : ℕ)
  let x := vertex u q V
  let t := u + ((d.1 : ℤ), (d.2 : ℤ))
  have hphase := greedy_phase u d V K hK hm hq₁ hq₂ hu hsep hbad
  obtain ⟨hr, hf, _hg⟩ := hphase n le_rfl
  have hn : n ≤ d.1 + d.2 := Nat.sub_le _ _
  obtain ⟨haPos, hbPos⟩ := remaining_positive u d V K n hm hq₁ hq₂ le_rfl hr hf
  change 1 ≤ (t.1 - (x n).1).toNat at haPos
  change 1 ≤ (t.2 - (x n).2).toNat at hbPos
  let a := (t.1 - (x n).1).toNat
  let b := (t.2 - (x n).2).toNat
  have ha : (a : ℤ) = t.1 - (x n).1 := Int.toNat_of_nonneg (by omega)
  have hb : (b : ℤ) = t.2 - (x n).2 := Int.toNat_of_nonneg (by omega)
  have hl := level u q V n
  have hab : a + b = 4 * K + 4 := by
    dsimp only [t] at ha hb
    simp only [Prod.fst_add, Prod.snd_add] at ha hb
    dsimp only [x] at ha hb
    omega
  have hend : x n + ((a : ℤ), (b : ℤ)) = t := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  let tail := horizontalFirst (x n) (a, b)
  have htail : ∀ j, tail.vertex j ∉ V := by
    intro j
    apply hbox
    obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := tail.vertex_mem_Icc j
    change x n + ((a : ℤ), (b : ℤ)) = t at hend
    rw [hend] at h₃ h₄
    refine ⟨⟨?_, ?_⟩, ⟨h₃, h₄⟩⟩
    · change t.1 - ((4 * K + 4 : ℕ) : ℤ) ≤ (tail.vertex j).1
      omega
    · change t.2 - ((4 * K + 4 : ℕ) : ℤ) ≤ (tail.vertex j).2
      omega
  obtain ⟨p, hp, hgood⟩ := splice_sequence u d (a, b) n x V
    (vertex_zero u q V) (step u q V) tail (by dsimp only; omega) hend
    (fun i hi => (hphase i hi).2.2) htail
  exact ⟨p, hp, p.finish, hgood⟩

end GreedyAttachment
end LPPDifferentiability
