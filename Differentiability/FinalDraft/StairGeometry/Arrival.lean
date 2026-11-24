/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.StairGeometry.Deterministic
import Differentiability.Model.Paths.GridCoarseGeneralPieces
import LPP_Foundations.Model.Paths.Concat
import Mathlib.Tactic

/-! The arrival path is the actual join of the greedy prefix and the horizontal-first tail. -/

public section

namespace LPPDifferentiability.StairGeometry

/-- Clause (iii), the prescribed arrival path to the given target exists, avoids very bad
sites in its collected vertices, and lies in the stated transverse band. -/
theorem arrival_path (ω : Environment) (T a : ℝ) (K₁ K₃ : ℕ) (Q : Set Lattice)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hE : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q)
    (z v : Lattice) (hzQ : z ∈ Q) (hz : z ∉ forwardTrapped ω T)
    (h₁ : z.1 ≤ v.1) (h₂ : z.2 ≤ v.2) :
    let L := arrivalBoxSize (slopeCutoff a) K₁ K₃
    let n := (v.1 - z.1 + (v.2 - z.2)).toNat
    let q := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
    let x := forwardGreedy ω T z hz q
    L ≤ n → slopeCutoff a ≤ q → q ≤ 1 - slopeCutoff a → boxFree ω T L v →
    (∀ y : Lattice, z.1 + z.2 ≤ y.1 + y.2 → y.1 + y.2 ≤ v.1 + v.2 →
      |GreedyAttachment.deviation z q (y.1 + y.2 - (z.1 + z.2)).toNat y| ≤ (deviationBound K₁ K₃ : ℝ) →
        y ∈ Q) →
    let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
    let tail := horizontalFirst (x (n - L)) e
    ∃ (d : ℕ × ℕ) (p : Path z d),
      z + ((d.1 : ℤ), (d.2 : ℤ)) = v ∧ d.1 + d.2 = n ∧
      (∀ i : Fin (d.1 + d.2 + 1), i.val ≤ n - L → p.vertex i = x i.val) ∧
      (∀ (j : Fin (e.1 + e.2 + 1)) (i : Fin (d.1 + d.2 + 1)),
        i.val = n - L + j.val → p.vertex i = tail.vertex j ∧
          v.1 - (L : ℤ) ≤ (p.vertex i).1 ∧ (p.vertex i).1 ≤ v.1 ∧
          v.2 - (L : ℤ) ≤ (p.vertex i).2 ∧ (p.vertex i).2 ≤ v.2) ∧
      (∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (p.vertex i)) ∧
      (∀ i : Fin (d.1 + d.2 + 1),
        |GreedyAttachment.deviation z q i.val (p.vertex i)| ≤ (deviationBound K₁ K₃ : ℝ) + (L : ℝ)) := by
  intro L n q x hLn hq₁ hq₂ hbox hmargin e tail
  obtain ⟨hx₁, hx₂, he, hprefix, hgood, hgoodTail, hdev⟩ :=
    arrival_pieces ω T a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ hE z v hzQ hz h₁ h₂ hLn hq₁ hq₂ hbox hmargin
  change (x (n - L)).1 ≤ v.1 at hx₁
  change (x (n - L)).2 ≤ v.2 at hx₂
  change e.1 + e.2 = L at he
  have hex := exists_path_of_seq x (n - L)
    (fun i _ => GreedyAttachment.step z q (forwardTrapped ω T) i)
  have hxzero : x 0 = z := GreedyAttachment.vertex_zero z q (forwardTrapped ω T)
  rw [hxzero] at hex
  obtain ⟨b, p, hend, hlen, hvertices, _⟩ := hex
  let pTail := horizontalFirst (z + ((b.1 : ℤ), (b.2 : ℤ))) e
  have htail (j : Fin (e.1 + e.2 + 1)) : pTail.vertex j = tail.vertex j := by
    change (horizontalFirst (z + ((b.1 : ℤ), (b.2 : ℤ))) e).vertex j = _
    rw [hend]
  have he₁ : (e.1 : ℤ) = v.1 - (x (n - L)).1 := by
    change ((v.1 - (x (n - L)).1).toNat : ℤ) = _
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hx₁)
  have he₂ : (e.2 : ℤ) = v.2 - (x (n - L)).2 := by
    change ((v.2 - (x (n - L)).2).toNat : ℤ) = _
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hx₂)
  have hfinish : z + (((b + e).1 : ℤ), ((b + e).2 : ℤ)) = v := by
    have hleft : z.1 + (b.1 : ℤ) = (x (n - L)).1 := congrArg Prod.fst hend
    have hright : z.2 + (b.2 : ℤ) = (x (n - L)).2 := congrArg Prod.snd hend
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> omega
  have hlen' : (b + e).1 + (b + e).2 = n := by
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  let r := p.concat pTail
  have hleft (i : Fin ((b + e).1 + (b + e).2 + 1)) (hi : i.val ≤ n - L) : r.vertex i = x i.val := by
    let j : Fin (b.1 + b.2 + 1) := ⟨i.val, by omega⟩
    exact (Path.concat_vertex_left p pTail j).trans (hvertices j)
  have hright (j : Fin (e.1 + e.2 + 1)) (i : Fin ((b + e).1 + (b + e).2 + 1))
      (hi : i.val = n - L + j.val) : r.vertex i = tail.vertex j := by
    have hi' : i = ⟨b.1 + b.2 + j.val, by
        simp only [Prod.fst_add, Prod.snd_add]
        have hj := j.isLt
        omega⟩ := Fin.ext (by show i.val = b.1 + b.2 + j.val; omega)
    rw [hi']
    exact (Path.concat_vertex_right p pTail j).trans (htail j)
  refine ⟨b + e, r, hfinish, hlen', hleft, ?_, ?_, ?_⟩
  · intro j i hi
    refine ⟨hright j i hi, ?_⟩
    rw [hright j i hi]
    have hfst : (tail.vertex j).1 = (x (n - L)).1 + (min j.val e.1 : ℕ) := rfl
    have hsnd : (tail.vertex j).2 = (x (n - L)).2 + (j.val - e.1 : ℕ) := rfl
    rw [hfst, hsnd]
    have hj := j.isLt
    rcases le_total j.val e.1 with hj₁ | hj₂
    · rw [Nat.min_eq_left hj₁]
      omega
    · rw [Nat.min_eq_right hj₂]
      omega
  · intro i hi
    by_cases hil : i.val < n - L
    · rw [hleft i hil.le]
      exact hgood i.val hil
    · let j : Fin (e.1 + e.2 + 1) := ⟨i.val - (n - L), by omega⟩
      rw [hright j i (by dsimp [j]; omega)]
      exact hgoodTail j (by change i.val - (n - L) < e.1 + e.2; omega)
  · intro i
    by_cases hil : i.val ≤ n - L
    · rw [hleft i hil]
      exact (hprefix i.val hil).2.trans (le_add_of_nonneg_right (Nat.cast_nonneg L))
    · let j : Fin (e.1 + e.2 + 1) := ⟨i.val - (n - L), by have := i.isLt; omega⟩
      have hidx : i.val = n - L + j.val := by dsimp [j]; omega
      rw [hright j i hidx]
      simpa only [hidx] using hdev j

end LPPDifferentiability.StairGeometry
