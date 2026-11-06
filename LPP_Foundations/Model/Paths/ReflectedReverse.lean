/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Path
public import Mathlib.Data.Set.Operations

/-! Reversing and reflecting an actual finite up-right path. -/

@[expose] public section

namespace LPPDifferentiability
namespace Path

private theorem neg_add_endpoint_cancel (a b : Lattice) :
    -(a + b) + b = -a := by
  apply Prod.ext
  · change -(a.1 + b.1) + b.1 = -a.1
    rw [Int.neg_add]
    exact Int.neg_add_cancel_right (-a.1) b.1
  · change -(a.2 + b.2) + b.2 = -a.2
    rw [Int.neg_add]
    exact Int.neg_add_cancel_right (-a.2) b.2

/-- Reflecting every vertex and reversing its index gives an ordinary up-right
path from the reflected endpoint back to the reflected start. -/
theorem exists_reflected_reverse {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    ∃ q : Path (-(u + ((d.1 : ℤ), (d.2 : ℤ)))) d,
      ∀ i : Fin (d.1 + d.2 + 1), q.vertex i = -(p.vertex i.rev) := by
  refine ⟨{
    vertex := fun i => -(p.vertex i.rev)
    start := by simp only [Fin.rev_zero, p.finish]
    finish := by
      simp only [Fin.rev_last, p.start]
      exact (neg_add_endpoint_cancel u ((d.1 : ℤ), (d.2 : ℤ))).symm
    step := by
      intro i
      simp only [Fin.rev_succ, Fin.rev_castSucc]
      rcases p.step i.rev with h | h
      · left
        rw [h]
        exact (neg_add_endpoint_cancel _ _).symm
      · right
        rw [h]
        exact (neg_add_endpoint_cancel _ _).symm
  }, ?_⟩
  intro i
  rfl

/-- The same reflected reverse path avoids the reflected image of any set of
bad vertices avoided by the original path. -/
theorem exists_reflected_reverse_avoiding_image {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (V : Set Lattice)
    (hV : ∀ i : Fin (d.1 + d.2 + 1), p.vertex i ∉ V) :
    ∃ q : Path (-(u + ((d.1 : ℤ), (d.2 : ℤ)))) d,
      (∀ i, q.vertex i = -(p.vertex i.rev)) ∧
      (∀ i, q.vertex i ∉ V.image Neg.neg) := by
  obtain ⟨q, hq⟩ := p.exists_reflected_reverse
  refine ⟨q, hq, ?_⟩
  intro i hmem
  obtain ⟨v, hv, hqi⟩ := (Set.mem_image Neg.neg V (q.vertex i)).mp hmem
  have hp : p.vertex i.rev = v := by
    have hneg : -(p.vertex i.rev) = -v := by
      calc
        -(p.vertex i.rev) = q.vertex i := (hq i).symm
        _ = -v := hqi.symm
    have hfst : -(p.vertex i.rev).1 = -v.1 := by
      change (-(p.vertex i.rev)).1 = (-v).1
      exact congrArg Prod.fst hneg
    have hsnd : -(p.vertex i.rev).2 = -v.2 := by
      change (-(p.vertex i.rev)).2 = (-v).2
      exact congrArg Prod.snd hneg
    exact Prod.ext ((Int.neg_inj).mp hfst) ((Int.neg_inj).mp hsnd)
  exact hV i.rev (by rw [hp]; exact hv)

/-- Every vertex of the same reflected reverse path belongs to the reflected
image of any region containing every vertex of the original path. -/
theorem exists_reflected_reverse_mem_image {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (R : Set Lattice)
    (hR : ∀ i : Fin (d.1 + d.2 + 1), p.vertex i ∈ R) :
    ∃ q : Path (-(u + ((d.1 : ℤ), (d.2 : ℤ)))) d,
      (∀ i, q.vertex i = -(p.vertex i.rev)) ∧
      (∀ i, q.vertex i ∈ R.image Neg.neg) := by
  obtain ⟨q, hq⟩ := p.exists_reflected_reverse
  refine ⟨q, hq, ?_⟩
  intro i
  rw [hq i]
  exact Set.mem_image_of_mem Neg.neg (hR i.rev)

end Path
end LPPDifferentiability
