/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.PathSets
public import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Data.Finset.Prod

/-! The animal family in Martin's planar diagonal process. The family has a
terminal-excluded up-right path as a member when `m < n`. -/

@[expose] public section

namespace LPPDifferentiability

/-- Martin's planar family for `Q(m,n)`, before taking any maximum. -/
def diagonalAnimalFamily (m n : ℤ) : Set (Finset Lattice) :=
  {s | IsConnectedAnimal s ∧ s.card ≤ 3 * (n - m).toNat ∧
    s ⊆ (Finset.Icc m n) ×ˢ (Finset.Icc m n) ∧ (m, m) ∈ s ∧
    (∃ z ∈ s, nearestNeighborGraph.Adj z (n, n)) ∧ (n, n) ∉ s}

/-- Membership in the family, including both endpoint conditions. -/
theorem mem_diagonalAnimalFamily_iff (m n : ℤ) (s : Finset Lattice) :
    s ∈ diagonalAnimalFamily m n ↔
      IsConnectedAnimal s ∧ s.card ≤ 3 * (n - m).toNat ∧
      s ⊆ (Finset.Icc m n) ×ˢ (Finset.Icc m n) ∧ (m, m) ∈ s ∧
      (∃ z ∈ s, nearestNeighborGraph.Adj z (n, n)) ∧ (n, n) ∉ s := Iff.rfl

/-- The family is contained in the powerset of the closed coordinate cube. -/
theorem diagonalAnimalFamily_finite (m n : ℤ) : (diagonalAnimalFamily m n).Finite := by
  apply (((Finset.Icc m n) ×ˢ (Finset.Icc m n)).powerset.finite_toSet).subset
  intro s hs
  exact Finset.mem_powerset.mpr ((mem_diagonalAnimalFamily_iff m n s).mp hs).2.2.1

/-- Every path between the diagonal endpoints gives a member of the family
when its terminal vertex is excluded. -/
theorem Path.collectedSites_mem_diagonalAnimalFamily (m n : ℤ) (hmn : m < n)
    (p : Path (m, m) ((n - m).toNat, (n - m).toNat)) :
    p.collectedSites ∈ diagonalAnimalFamily m n := by
  have hdelta : ((n - m).toNat : ℤ) = n - m := Int.toNat_of_nonneg (by omega)
  have hpos : 0 < (n - m).toNat + (n - m).toNat := by omega
  have hend : (m, m) + (((n - m).toNat : ℤ), ((n - m).toNat : ℤ)) = (n, n) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, hdelta] <;> omega
  refine (mem_diagonalAnimalFamily_iff m n _).2
    ⟨p.collectedSites_isConnected hpos, ?_, ?_, p.start_mem_collectedSites hpos, ?_, ?_⟩
  · rw [p.collectedSites_card]
    dsimp only
    omega
  · intro z hz
    obtain ⟨i, rfl⟩ := (p.mem_collectedSites_iff z).mp hz
    have hbox := p.vertex_mem_Icc i.castSucc
    rw [hend] at hbox
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hbox.1.1, hbox.2.1⟩,
       Finset.mem_Icc.mpr ⟨hbox.1.2, hbox.2.2⟩⟩
  · let i : Fin ((n - m).toNat + (n - m).toNat) :=
      ⟨(n - m).toNat + (n - m).toNat - 1, by omega⟩
    refine ⟨p.vertex i.castSucc, p.vertex_mem_collectedSites i, ?_⟩
    have hilast : i.succ = Fin.last ((n - m).toNat + (n - m).toNat) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      dsimp only [i]
      omega
    have hfinish : p.vertex i.succ = (n, n) := by rw [hilast, p.finish, hend]
    rw [← hfinish]
    rcases p.step i with h | h
    · rw [h]
      left
      simp only [Prod.fst_add, Prod.snd_add, add_zero, sub_add_cancel_left,
        abs_neg, abs_one, and_self]
    · rw [h]
      right
      simp only [Prod.fst_add, Prod.snd_add, add_zero, sub_add_cancel_left,
        abs_neg, abs_one, and_self]
  · rw [← hend]
    exact p.finish_notMem_collectedSites

/-- A terminal-excluded path shows that the family is nonempty when `m < n`. -/
theorem diagonalAnimalFamily_nonempty (m n : ℤ) (hmn : m < n) :
    (diagonalAnimalFamily m n).Nonempty :=
  ⟨(horizontalFirst (m, m) ((n - m).toNat, (n - m).toNat)).collectedSites,
    Path.collectedSites_mem_diagonalAnimalFamily m n hmn _⟩

end LPPDifferentiability
