/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.SeparatedLatticeSubset
public import Mathlib.Data.Nat.Dist
import Lean.Elab.Tactic.Omega

/-! Greedy separation for finite subsets of the natural lattice. -/

@[expose] public section

namespace LPPDifferentiability

private theorem int_abs_natCast_sub (a b : ℕ) :
    |(a : ℤ) - (b : ℤ)| = (Nat.dist a b : ℤ) := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    have hInt : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
    rw [abs_of_nonpos (sub_nonpos.mpr hInt)]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hba]
    have hInt : (b : ℤ) ≤ (a : ℤ) := by exact_mod_cast hba
    rw [abs_of_nonneg (sub_nonneg.mpr hInt)]
    omega

/-- Every finite natural-lattice set has a separated subset covering it at
the same coordinate radius, with the exact square-size loss. -/
theorem exists_separated_natural_lattice_subset
    (S : Finset (ℕ × ℕ)) (k : ℕ) :
    ∃ T : Finset (ℕ × ℕ),
      T ⊆ S ∧
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
        k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) ∧
      (∀ u ∈ S, ∃ v ∈ T,
        Nat.dist u.1 v.1 ≤ k ∧ Nat.dist u.2 v.2 ≤ k) ∧
      S.card ≤ (2 * k + 1) ^ 2 * T.card := by
  classical
  let castToLattice : ℕ × ℕ → Lattice := fun u => (u.1, u.2)
  have hcast : Function.Injective castToLattice := by
    intro u v huv
    apply Prod.ext
    · exact Int.ofNat.inj (congrArg Prod.fst huv)
    · exact Int.ofNat.inj (congrArg Prod.snd huv)
  let SInt : Finset Lattice := S.image castToLattice
  obtain ⟨U, hUSub, hUSeparated, hUCovers, hUCard⟩ :=
    exists_separated_lattice_subset SInt k
  let T : Finset (ℕ × ℕ) := S.filter fun u => castToLattice u ∈ U
  have hTSub : T ⊆ S := by
    intro u hu
    exact (Finset.mem_filter.mp hu).1
  have hTImage : T.image castToLattice = U := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
      exact (Finset.mem_filter.mp hu).2
    · intro hz
      rcases Finset.mem_image.mp (hUSub hz) with ⟨u, huS, huz⟩
      apply Finset.mem_image.mpr
      refine ⟨u, Finset.mem_filter.mpr ⟨huS, ?_⟩, huz⟩
      rw [huz]
      exact hz
  have hTCard : T.card = U.card := by
    calc
      T.card = (T.image castToLattice).card := by
        symm
        exact Finset.card_image_of_injective _ hcast
      _ = U.card := congrArg Finset.card hTImage
  have hTSeparated (u : ℕ × ℕ) (hu : u ∈ T)
      (v : ℕ × ℕ) (hv : v ∈ T) (huv : u ≠ v) :
      k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2 := by
    have huU : castToLattice u ∈ U := (Finset.mem_filter.mp hu).2
    have hvU : castToLattice v ∈ U := (Finset.mem_filter.mp hv).2
    have huvCast : castToLattice u ≠ castToLattice v := fun h => huv (hcast h)
    rcases hUSeparated _ huU _ hvU huvCast with hfirst | hsecond
    · left
      change (k : ℤ) < |(u.1 : ℤ) - (v.1 : ℤ)| at hfirst
      have hInt : (k : ℤ) < (Nat.dist u.1 v.1 : ℤ) := by
        rw [← int_abs_natCast_sub]
        exact hfirst
      exact_mod_cast hInt
    · right
      change (k : ℤ) < |(u.2 : ℤ) - (v.2 : ℤ)| at hsecond
      have hInt : (k : ℤ) < (Nat.dist u.2 v.2 : ℤ) := by
        rw [← int_abs_natCast_sub]
        exact hsecond
      exact_mod_cast hInt
  have hTCovers (u : ℕ × ℕ) (hu : u ∈ S) :
      ∃ v ∈ T, Nat.dist u.1 v.1 ≤ k ∧ Nat.dist u.2 v.2 ≤ k := by
    have huInt : castToLattice u ∈ SInt :=
      Finset.mem_image.mpr ⟨u, hu, rfl⟩
    obtain ⟨z, hzU, huz1, huz2⟩ := hUCovers _ huInt
    rcases Finset.mem_image.mp (hUSub hzU) with ⟨v, hvS, hvz⟩
    refine ⟨v, Finset.mem_filter.mpr ⟨hvS, ?_⟩, ?_, ?_⟩
    · rw [hvz]
      exact hzU
    · have hInt : |(u.1 : ℤ) - (v.1 : ℤ)| ≤ (k : ℤ) := by
        have h := huz1
        rw [← hvz] at h
        change |(u.1 : ℤ) - (v.1 : ℤ)| ≤ (k : ℤ) at h
        exact h
      have hNatInt : (Nat.dist u.1 v.1 : ℤ) ≤ (k : ℤ) := by
        rw [← int_abs_natCast_sub]
        exact hInt
      exact_mod_cast hNatInt
    · have hInt : |(u.2 : ℤ) - (v.2 : ℤ)| ≤ (k : ℤ) := by
        have h := huz2
        rw [← hvz] at h
        change |(u.2 : ℤ) - (v.2 : ℤ)| ≤ (k : ℤ) at h
        exact h
      have hNatInt : (Nat.dist u.2 v.2 : ℤ) ≤ (k : ℤ) := by
        rw [← int_abs_natCast_sub]
        exact hInt
      exact_mod_cast hNatInt
  have hSIntCard : SInt.card = S.card := by
    dsimp [SInt]
    rw [Finset.card_image_of_injective _ hcast]
  refine ⟨T, hTSub, hTSeparated, hTCovers, ?_⟩
  calc
    S.card = SInt.card := hSIntCard.symm
    _ ≤ (2 * k + 1) ^ 2 * U.card := hUCard
    _ = (2 * k + 1) ^ 2 * T.card := by rw [hTCard]

end LPPDifferentiability

end
