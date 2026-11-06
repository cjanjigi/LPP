/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Traversal
public import LPP_Foundations.Model.Animals.CoarseWalk
public import LPP_Foundations.Model.Animals.BoxCardinality

/-! Martin's covering lemma for lattice animals in the integer plane.

This is Lemma 2.1 of Martin (2002), which restates Lemma 1 of Cox, Gandolfi, Griffin
and Kesten (1993). The proof here is a separate reconstruction, not a copy of the
proof of Cox et al.
-/

public section

namespace LPPDifferentiability

/-- Every finite connected animal containing zero has Martin's coarse cover.
The same finite union satisfies the planar box-cardinality bound. -/
theorem exists_animal_cover (s : Finset Lattice) (hs : IsConnectedAnimal s)
    (hzero : (0 : Lattice) ∈ s) (l : ℕ) (hl : 1 ≤ l) (hln : l ≤ s.card) :
    ∃ u : Fin ((2 * s.card / l) + 1) → Lattice,
      u 0 = 0 ∧
      (∀ i : Fin (2 * s.card / l),
        |(u i.succ).1 - (u i.castSucc).1| ≤ 1 ∧
        |(u i.succ).2 - (u i.castSucc).2| ≤ 1) ∧
      s ⊆ ((Finset.univ : Finset (Fin ((2 * s.card / l) + 1))).biUnion
        (fun i => integerBox ((l : ℤ) * (u i).1, (l : ℤ) * (u i).2) (2 * l))) ∧
      ((Finset.univ : Finset (Fin ((2 * s.card / l) + 1))).biUnion
        (fun i => integerBox ((l : ℤ) * (u i).1, (l : ℤ) * (u i).2) (2 * l))).card ≤
          ((2 * s.card / l) + 1) * (4 * l + 1) ^ 2 := by
  obtain ⟨w, hw0, hstep, hvisit, _⟩ := exists_padded_animal_walk s hs hzero
  obtain ⟨u, hu0, hustep, hucover⟩ := exists_coarse_walk_cover l s.card hl hln w hw0
    (fun t _ => hstep t)
  refine ⟨u, hu0, hustep, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht, htz⟩ := hvisit z hz
    obtain ⟨i, hi⟩ := hucover t ht
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply (mem_integerBox_iff _ _ _).2
    simpa only [htz, Nat.cast_mul, Nat.cast_ofNat] using hi
  · exact integerBox_scaledCover_union_card_le (2 * s.card / l) l
      (fun i => ((l : ℤ) * (u i).1, (l : ℤ) * (u i).2))

end LPPDifferentiability
