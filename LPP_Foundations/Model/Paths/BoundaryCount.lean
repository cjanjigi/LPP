/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Counting disjoint up-right paths by their first boundary hits. -/

@[expose] public section

namespace LPPDifferentiability

/-- A finite family of pairwise disjoint up-right rays starting in the closed
box `[0,N]²` has at most `2N+1` members. This is the finite north/east boundary
count used in GRS arXiv:1510.00860v1, Appendix A, lines 1475–1480 and
1633–1639; the northeast corner is counted once. -/
theorem card_le_north_east_boundary_of_disjoint_up_right_paths
    {I : Type*} [Fintype I] (p : I → ℕ → LPPDifferentiability.Lattice) (N : ℕ)
    (hStep : ∀ i n, p i (n+1) = p i n + (1,0) ∨ p i (n+1) = p i n + (0,1))
    (hStart : ∀ i, 0 ≤ (p i 0).1 ∧ (p i 0).1 ≤ (N : ℤ) ∧
      0 ≤ (p i 0).2 ∧ (p i 0).2 ≤ (N : ℤ))
    (hDisjoint : ∀ i j, i ≠ j → ∀ m n, p i m ≠ p j n) :
    Fintype.card I ≤ 2*N+1 := by
  classical
  -- Each step raises the level by one and never decreases either coordinate.
  have hcoords (i : I) (n : ℕ) :
      (p i 0).1 ≤ (p i n).1 ∧ (p i 0).2 ≤ (p i n).2 ∧
        (p i n).1 + (p i n).2 = (p i 0).1 + (p i 0).2 + (n : ℤ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rcases hStep i n with h | h <;>
        simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
  -- The level forces a boundary hit even without coordinate escape assumptions.
  have hex (i : I) : ∃ n : ℕ, (N : ℤ) ≤ (p i n).1 ∨ (N : ℤ) ≤ (p i n).2 := by
    refine ⟨2 * N + 1, ?_⟩
    have h := hcoords i (2 * N + 1)
    have hs := hStart i
    push_cast at h
    omega
  let t : I → ℕ := fun i => Nat.find (hex i)
  have hfirst (i : I) : (N : ℤ) ≤ (p i (t i)).1 ∨ (N : ℤ) ≤ (p i (t i)).2 :=
    Nat.find_spec (hex i)
  have hbound (i : I) :
      0 ≤ (p i (t i)).1 ∧ (p i (t i)).1 ≤ (N : ℤ) ∧
      0 ≤ (p i (t i)).2 ∧ (p i (t i)).2 ≤ (N : ℤ) := by
    have hstart := hStart i
    have hc := hcoords i (t i)
    by_cases hz : t i = 0
    · rw [hz]
      exact hstart
    · have hlt : t i - 1 < t i := by omega
      have hprev := Nat.find_min (hex i) hlt
      have hs := hStep i (t i - 1)
      have hindex : t i - 1 + 1 = t i := by omega
      rw [hindex] at hs
      rcases hs with hs | hs <;>
        simp only [hs, Prod.fst_add, Prod.snd_add] at * <;> omega
  -- Classify each hit as top edge, or right edge with the corner removed.
  let hit : I → Lattice := fun i => p i (t i)
  have hboundhit (i : I) :
      0 ≤ (hit i).1 ∧ (hit i).1 ≤ (N : ℤ) ∧
      0 ≤ (hit i).2 ∧ (hit i).2 ≤ (N : ℤ) := hbound i
  have hboundary (i : I) : (hit i).2 = (N : ℤ) ∨ (hit i).1 = (N : ℤ) := by
    have hb := hbound i
    have hf := hfirst i
    dsimp only [hit]
    omega
  have hxcast (i : I) : (((hit i).1.toNat : ℕ) : ℤ) = (hit i).1 :=
    Int.toNat_of_nonneg (hbound i).1
  have hycast (i : I) : (((hit i).2.toNat : ℕ) : ℤ) = (hit i).2 :=
    Int.toNat_of_nonneg (hbound i).2.2.1
  let f : I → Fin (N + 1) ⊕ Fin N := fun i =>
    if hy : (hit i).2 = (N : ℤ) then
      Sum.inl ⟨(hit i).1.toNat, by have h := hboundhit i; have hc := hxcast i; omega⟩
    else
      Sum.inr ⟨(hit i).2.toNat, by
        have h := hboundhit i
        have hc := hycast i
        omega⟩
  have hinj : Function.Injective f := by
    intro i j heq
    have hh : hit i = hit j := by
      by_cases hi : (hit i).2 = (N : ℤ)
      · by_cases hj : (hit j).2 = (N : ℤ)
        · have he : (⟨(hit i).1.toNat, by have h := hboundhit i; have hc := hxcast i; omega⟩ : Fin (N + 1)) =
              ⟨(hit j).1.toNat, by have h := hboundhit j; have hc := hxcast j; omega⟩ := by
            simpa [f, hi, hj] using heq
          have hv := congrArg Fin.val he
          change (hit i).1.toNat = (hit j).1.toNat at hv
          apply Prod.ext
          · have hi' := hxcast i
            have hj' := hxcast j
            omega
          · omega
        · simp [f, hi, hj] at heq
      · by_cases hj : (hit j).2 = (N : ℤ)
        · simp [f, hi, hj] at heq
        · have he : (⟨(hit i).2.toNat, by have h := hboundhit i; have hc := hycast i; omega⟩ : Fin N) =
              ⟨(hit j).2.toNat, by have h := hboundhit j; have hc := hycast j; omega⟩ := by
            simpa [f, hi, hj] using heq
          have hv := congrArg Fin.val he
          change (hit i).2.toNat = (hit j).2.toNat at hv
          have hbi := hboundary i
          have hbj := hboundary j
          apply Prod.ext
          · omega
          · have hi' := hycast i
            have hj' := hycast j
            omega
    by_contra hij
    exact hDisjoint i j hij (t i) (t j) hh
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  omega

end LPPDifferentiability
