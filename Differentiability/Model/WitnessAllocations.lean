/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Bounds
import Lean.Elab.Tactic.Omega

/-! Exact counts and elementary upper bounds for natural-valued stage allocations. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The finite set of natural-valued vectors of length `N + 1` and exact total `t`.
Its cardinality is the source's stars-and-bars count. -/
theorem exists_finset_witness_allocations (N t : ℕ) :
    ∃ s : Finset (Fin (N + 1) → ℕ),
      (∀ m, m ∈ s ↔ (∑ i : Fin (N + 1), m i) = t) ∧
        s.card = Nat.choose (N + t) N := by
  classical
  let allocations :=
    {m : Fin (N + 1) → ℕ // (∑ i : Fin (N + 1), m i) = t}
  let encode : Sym (Fin (N + 1)) t ≃ allocations :=
    Sym.equivNatSumOfFintype (Fin (N + 1)) t
  let : Fintype allocations := Fintype.ofEquiv _ encode
  have hcard : Fintype.card allocations = Nat.choose (N + t) N := by
    calc
      Fintype.card allocations = Fintype.card (Sym (Fin (N + 1)) t) :=
        Fintype.card_congr encode.symm
      _ = Nat.choose (Fintype.card (Fin (N + 1)) + t - 1) t :=
        Sym.card_sym_eq_choose (α := Fin (N + 1)) t
      _ = Nat.choose (N + t) N := by
        rw [Fintype.card_fin]
        have hsize : N + 1 + t - 1 = N + t := by omega
        rw [hsize]
        exact (Nat.choose_symm_add (a := N) (b := t)).symm
  let s : Finset (Fin (N + 1) → ℕ) :=
    Finset.univ.image (fun m : allocations => m.1)
  refine ⟨s, ?_, ?_⟩
  · intro m
    simp only [s, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩
  · calc
      s.card = Finset.univ.card := by
        dsimp [s]
        exact Finset.card_image_of_injective _ Subtype.val_injective
      _ = Fintype.card allocations := Finset.card_univ
      _ = Nat.choose (N + t) N := hcard

/-- The exact-total allocation set has at most `2^(N + t)` elements. -/
theorem witness_allocations_card_le_two_pow (N t : ℕ) :
    ∃ s : Finset (Fin (N + 1) → ℕ),
      (∀ m, m ∈ s ↔ (∑ i : Fin (N + 1), m i) = t) ∧
        s.card ≤ 2 ^ (N + t) := by
  obtain ⟨s, hs, hcard⟩ := exists_finset_witness_allocations N t
  refine ⟨s, hs, ?_⟩
  rw [hcard]
  exact Nat.choose_le_two_pow (N + t) N

/-- If `t ≤ N`, the exact-total allocation set has at most `4^N` elements. -/
theorem witness_allocations_card_le_four_pow_of_le (N t : ℕ) (ht : t ≤ N) :
    ∃ s : Finset (Fin (N + 1) → ℕ),
      (∀ m, m ∈ s ↔ (∑ i : Fin (N + 1), m i) = t) ∧
        s.card ≤ 4 ^ N := by
  obtain ⟨s, hs, hcard⟩ := exists_finset_witness_allocations N t
  refine ⟨s, hs, ?_⟩
  rw [hcard]
  calc
    Nat.choose (N + t) N ≤ 2 ^ (N + t) := Nat.choose_le_two_pow (N + t) N
    _ ≤ 2 ^ (2 * N) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4 ^ N := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]

/-- The paper's threshold `N / 32` satisfies the allocation bound for every `N`,
including zero. -/
theorem witness_allocations_card_le_four_pow_div32 (N : ℕ) :
    ∃ s : Finset (Fin (N + 1) → ℕ),
      (∀ m, m ∈ s ↔ (∑ i : Fin (N + 1), m i) = N / 32) ∧
        s.card ≤ 4 ^ N := by
  exact witness_allocations_card_le_four_pow_of_le N (N / 32) (Nat.div_le_self _ _)

end LPPDifferentiability
