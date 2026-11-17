/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPaths
public import LPP_Foundations.Model.Paths.BoundaryCount
import Mathlib.Tactic

/-! Count locally shielded rightmost paths on a spaced grid. -/

@[expose] public section
open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- Local north-boundary shields in spaced cells give the finite boundary count.
The two shield guards are obtained from strict west or south separation. -/
theorem card_shielded_rightmost_grid_cells_le
    (C : Lattice → Lattice → ℝ) (M1 M2 n : ℕ)
    (S : Finset Lattice)
    (hIndices : ∀ p ∈ S,
      0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2 ∧ p.2 < (n : ℤ))
    (hShield : ∀ p ∈ S,
      let c : Lattice := (((M1 : ℤ) + 1) * p.1, ((M2 : ℤ) + 1) * p.2)
      ∃ a : ℤ, 0 < a ∧ a < (M1 : ℤ) ∧
        ∀ v : Lattice,
          v ∉ Set.Icc c (c + ((M1 : ℤ), (M2 : ℤ))) →
          (v.1 ≤ c.1 ∨ v.2 ≤ c.2) → ∀ r s : ℕ,
            rightmostCocyclePath C v r ≠
              rightmostCocyclePath C (c + (a, (M2 : ℤ))) s) :
    S.card ≤ 2 * (max (M1 + 1) (M2 + 1) * n) + 1
    := by
  classical
  let corner (i : ↥S) : Lattice :=
    (((M1 : ℤ) + 1) * i.val.1, ((M2 : ℤ) + 1) * i.val.2)
  let a (i : ↥S) : ℤ := Classical.choose (hShield i.val i.property)
  have ha (i : ↥S) : 0 < a i ∧ a i < (M1 : ℤ) ∧
      ∀ v : Lattice,
        v ∉ Set.Icc (corner i) (corner i + ((M1 : ℤ), (M2 : ℤ))) →
        (v.1 ≤ (corner i).1 ∨ v.2 ≤ (corner i).2) → ∀ r s : ℕ,
          rightmostCocyclePath C v r ≠
            rightmostCocyclePath C (corner i + (a i, (M2 : ℤ))) s :=
    Classical.choose_spec (hShield i.val i.property)
  let start (i : ↥S) : Lattice := corner i + (a i, (M2 : ℤ))
  let ray (i : ↥S) (k : ℕ) := rightmostCocyclePath C (start i) k
  let N := max (M1 + 1) (M2 + 1) * n
  have hmax1 : (M1 : ℤ) + 1 ≤ (max (M1 + 1) (M2 + 1) : ℕ) := by
    exact_mod_cast (le_max_left (M1 + 1) (M2 + 1))
  have hmax2 : (M2 : ℤ) + 1 ≤ (max (M1 + 1) (M2 + 1) : ℕ) := by
    exact_mod_cast (le_max_right (M1 + 1) (M2 + 1))
  -- Every selected north-boundary point lies in the counting square.
  have hstart (i : ↥S) : 0 ≤ (ray i 0).1 ∧ (ray i 0).1 ≤ (N : ℤ) ∧
      0 ≤ (ray i 0).2 ∧ (ray i 0).2 ≤ (N : ℤ) := by
    have hi := hIndices i.val i.property
    have hai := ha i
    have hx : ((M1 : ℤ) + 1) * (i.val.1 + 1) ≤
        (max (M1 + 1) (M2 + 1) : ℕ) * (n : ℤ) := by
      calc
        _ ≤ ((M1 : ℤ) + 1) * (n : ℤ) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hmax1 (by positivity)
    have hy : ((M2 : ℤ) + 1) * (i.val.2 + 1) ≤
        (max (M1 + 1) (M2 + 1) : ℕ) * (n : ℤ) := by
      calc
        _ ≤ ((M2 : ℤ) + 1) * (n : ℤ) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hmax2 (by positivity)
    have hx0 := mul_nonneg (show 0 ≤ (M1 : ℤ) + 1 by positivity) hi.1
    have hy0 := mul_nonneg (show 0 ≤ (M2 : ℤ) + 1 by positivity) hi.2.2.1
    dsimp [ray, rightmostCocyclePath, start, corner, N]
    push_cast at hx hy ⊢
    constructor <;> [skip; constructor <;> [skip; constructor]] <;> nlinarith
  -- Ordering two distinct cells puts the first start outside and west or south.
  have hbefore (i j : ↥S)
      (hij : i.val.1 < j.val.1 ∨ i.val.2 < j.val.2) :
      ∀ r s, ray i r ≠ ray j s := by
    have hside : (start i).1 < (corner j).1 ∨ (start i).2 < (corner j).2 := by
      rcases hij with hx | hy
      · left
        have hm := mul_le_mul_of_nonneg_left (show i.val.1 + 1 ≤ j.val.1 by omega)
          (show 0 ≤ (M1 : ℤ) + 1 by positivity)
        have hai := ha i
        dsimp [start, corner]
        nlinarith
      · right
        have hm := mul_le_mul_of_nonneg_left (show i.val.2 + 1 ≤ j.val.2 by omega)
          (show 0 ≤ (M2 : ℤ) + 1 by positivity)
        dsimp [start, corner]
        nlinarith
    have hout : start i ∉ Set.Icc (corner j) (corner j + ((M1 : ℤ), (M2 : ℤ))) := by
      intro h
      have hle := h.1
      rcases hside with hx | hy
      · have hh := hle.1
        omega
      · have hh := hle.2
        omega
    have hguard : (start i).1 ≤ (corner j).1 ∨ (start i).2 ≤ (corner j).2 := by
      rcases hside with hx | hy
      · exact Or.inl (le_of_lt hx)
      · exact Or.inr (le_of_lt hy)
    exact (ha j).2.2 (start i) hout hguard
  have hdisjoint (i j : ↥S) (hij : i ≠ j) : ∀ r s, ray i r ≠ ray j s := by
    have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    by_cases hx : i.val.1 < j.val.1
    · exact hbefore i j (Or.inl hx)
    by_cases hx' : j.val.1 < i.val.1
    · intro r s h
      exact hbefore j i (Or.inl hx') s r h.symm
    have heq : i.val.1 = j.val.1 := by omega
    have hy : i.val.2 ≠ j.val.2 := by
      intro h
      exact hval (Prod.ext heq h)
    rcases lt_or_gt_of_ne hy with hy | hy
    · exact hbefore i j (Or.inr hy)
    · intro r s h
      exact hbefore j i (Or.inr hy) s r h.symm
  have hstep (i : ↥S) (k : ℕ) : ray i (k + 1) = ray i k + (1, 0) ∨
      ray i (k + 1) = ray i k + (0, 1) := by
    simpa only [ray, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C (rightmostCocyclePath C (start i) k)
  have hc := card_le_north_east_boundary_of_disjoint_up_right_paths ray N hstep hstart hdisjoint
  simpa only [Fintype.card_coe, N] using hc

end LPP.Busemann
