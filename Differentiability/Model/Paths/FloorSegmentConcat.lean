/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.FloorSegment
public import LPP_Foundations.Model.Paths.FiniteConcatVertices
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi

/-! Actual finite concatenation along the literal floor chain. -/

public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Natural floor increments telescope, including when some pieces are zero. -/
theorem floorSegment_sum_increments (d : ℕ × ℕ) (B : ℕ) (hB : 1 ≤ B) :
    let k : ℕ → ℕ × ℕ := fun j => (j*d.1/B,j*d.2/B)
    let Δ : Fin B → ℕ × ℕ := fun j =>
      ((k (j.val+1)).1-(k j.val).1,(k (j.val+1)).2-(k j.val).2)
    (∑ j, Δ j) = d := by
  intro k Δ
  have hm (n : ℕ) : Monotone (fun j => j*n/B) :=
    fun _ _ hij => Nat.div_le_div_right (Nat.mul_le_mul_right n hij)
  have hs (n : ℕ) : (∑ j : Fin B, ((j.val+1)*n/B-j.val*n/B)) = n := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j+1)*n/B-j*n/B) B]
    have ht := Finset.sum_range_tsub (hm n) B
    simpa only [Nat.zero_mul, Nat.zero_div, Nat.sub_zero,
      Nat.mul_div_cancel_left _ (show 0 < B by omega)] using ht
  apply Prod.ext
  · simpa only [Prod.fst_sum, Δ, k] using hs d.1
  · simpa only [Prod.snd_sum, Δ, k] using hs d.2

/-- The same concatenated path has the exact weight and every piece vertex
property. Compatibility and the displacement are derived from actual floors. -/
theorem floorSegment_exists_concat (ω : Environment) (u : Lattice)
    (d : ℕ × ℕ) (B : ℕ) (hB : 1 ≤ B)
    (P : Lattice → Prop) :
    let k : ℕ → ℕ × ℕ := fun j => (j*d.1/B,j*d.2/B)
    let Δ : Fin B → ℕ × ℕ := fun j =>
      ((k (j.val+1)).1-(k j.val).1,(k (j.val+1)).2-(k j.val).2)
    let U : Fin B → Lattice := fun j =>
      u + (((k j.val).1 : ℤ),((k j.val).2 : ℤ))
    ∀ paths : (j : Fin B) → Path (U j) (Δ j),
      (∀ j (i : Fin ((Δ j).1+(Δ j).2+1)), P ((paths j).vertex i)) →
      ∃ q : Path u d,
        pathWeight ω q = ∑ j, pathWeight ω (paths j) ∧
        q.vertex (Fin.last (d.1+d.2)) = u + ((d.1 : ℤ),(d.2 : ℤ)) ∧
        ∀ i, P (q.vertex i) := by
  intro k Δ U paths hP
  let V : Fin (B+1) → Lattice := fun j =>
    u + (((k j.val).1 : ℤ),((k j.val).2 : ℤ))
  have hjoin (j : Fin B) :
      V j.succ = V j.castSucc + (((Δ j).1 : ℤ),((Δ j).2 : ℤ)) :=
    (floorSegment_increment u d B j.val hB).symm
  have hs : (∑ j, Δ j) = d := floorSegment_sum_increments d B hB
  have hstart : V ((⟨0, by omega⟩ : Fin B).castSucc) = u := by
    simpa only [V, Fin.val_castSucc, Fin.val_mk] using
      (floorSegment_endpoints u d B hB).1
  have hend : V (Fin.last B) = u + ((d.1 : ℤ),(d.2 : ℤ)) :=
    (floorSegment_endpoints u d B hB).2
  obtain ⟨q, hw, ht, _hv, hp⟩ :=
    Path.exists_concat_finite_property ω hB V Δ hjoin paths P hP
  have hex : ∃ q : Path (V ((⟨0, by omega⟩ : Fin B).castSucc)) (∑ j, Δ j),
      pathWeight ω q = ∑ j, pathWeight ω (paths j) ∧
      q.vertex (Fin.last ((∑ j, Δ j).1+(∑ j, Δ j).2)) =
        u + ((d.1 : ℤ),(d.2 : ℤ)) ∧ ∀ i, P (q.vertex i) :=
    ⟨q, hw, ht.trans hend, hp⟩
  rw [hstart, hs] at hex
  exact hex

end LPPDifferentiability
