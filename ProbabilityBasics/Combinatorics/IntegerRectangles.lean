/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Finite rectangle regularity for the covering route cited in JR Appendix B.5. -/

public section

namespace ProbabilityBasics

/-- Finite integer rectangles have their expected area and a linear difference-set bound.
This is the finite rectangle regularity used in the covering argument cited in JR Appendix B.5. -/
theorem integer_rectangle_difference_regularities :
    let R : ℕ → ℕ → Finset (ℤ × ℤ) := fun a b =>
      Finset.Ico (0 : ℤ) (a : ℤ) ×ˢ Finset.Ico (0 : ℤ) (b : ℤ)
    ∀ a b : ℕ,
      (R a b).card = a * b ∧
      ((0, 0) ∈ R a b ↔ 0 < a ∧ 0 < b) ∧
      (∀ c d : ℕ, a ≤ c → b ≤ d → R a b ⊆ R c d) ∧
      (Finset.image (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.1 - p.2)
        ((R a b) ×ˢ (R a b))).card ≤ 4 * (R a b).card := by
  classical
  let R : ℕ → ℕ → Finset (ℤ × ℤ) := fun a b =>
    Finset.Ico (0 : ℤ) (a : ℤ) ×ˢ Finset.Ico (0 : ℤ) (b : ℤ)
  change ∀ a b : ℕ,
    (R a b).card = a * b ∧
    ((0, 0) ∈ R a b ↔ 0 < a ∧ 0 < b) ∧
    (∀ c d : ℕ, a ≤ c → b ≤ d → R a b ⊆ R c d) ∧
    (Finset.image (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.1 - p.2)
      ((R a b) ×ˢ (R a b))).card ≤ 4 * (R a b).card
  have hRcard (a b : ℕ) : (R a b).card = a * b := by
    simp [R]
  have hSymCard (n : ℕ) : (Finset.Ico (-(n : ℤ)) (n : ℤ)).card = 2 * n := by
    rw [Int.card_Ico]
    have hwidth : (n : ℤ) - (-(n : ℤ)) = ((2 * n : ℕ) : ℤ) := by omega
    rw [hwidth, Int.toNat_natCast]
  intro a b
  refine ⟨hRcard a b, ?_, ?_, ?_⟩
  · simp [R]
  · intro c d hac hbd
    apply Finset.product_subset_product
    · intro z hz
      rcases Finset.mem_Ico.mp hz with ⟨hz0, hza⟩
      exact Finset.mem_Ico.mpr ⟨hz0, lt_of_lt_of_le hza (by exact_mod_cast hac)⟩
    · intro z hz
      rcases Finset.mem_Ico.mp hz with ⟨hz0, hzb⟩
      exact Finset.mem_Ico.mpr ⟨hz0, lt_of_lt_of_le hzb (by exact_mod_cast hbd)⟩
  · let D : Finset (ℤ × ℤ) :=
      Finset.Ico (-(a : ℤ)) (a : ℤ) ×ˢ Finset.Ico (-(b : ℤ)) (b : ℤ)
    have hImageSubset :
        (Finset.image (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.1 - p.2)
          ((R a b) ×ˢ (R a b))) ⊆ D := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨⟨p, q⟩, hpq, rfl⟩
      rcases Finset.mem_product.mp hpq with ⟨hp, hq⟩
      simp only [R, Finset.mem_product] at hp hq
      rcases hp with ⟨hp1, hp2⟩
      rcases hq with ⟨hq1, hq2⟩
      rcases Finset.mem_Ico.mp hp1 with ⟨hp10, hp1a⟩
      rcases Finset.mem_Ico.mp hq1 with ⟨hq10, hq1a⟩
      rcases Finset.mem_Ico.mp hp2 with ⟨hp20, hp2b⟩
      rcases Finset.mem_Ico.mp hq2 with ⟨hq20, hq2b⟩
      change (p.1 - q.1, p.2 - q.2) ∈
        Finset.Ico (-(a : ℤ)) (a : ℤ) ×ˢ Finset.Ico (-(b : ℤ)) (b : ℤ)
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Ico.mpr
        constructor <;> omega
      · apply Finset.mem_Ico.mpr
        constructor <;> omega
    have hDcard : D.card = 4 * (R a b).card := by
      calc
        D.card = (Finset.Ico (-(a : ℤ)) (a : ℤ)).card *
            (Finset.Ico (-(b : ℤ)) (b : ℤ)).card := by simp [D]
        _ = (2 * a) * (2 * b) := by rw [hSymCard, hSymCard]
        _ = 4 * (R a b).card := by rw [hRcard]; ring
    calc
      (Finset.image (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.1 - p.2)
        ((R a b) ×ˢ (R a b))).card ≤ D.card := Finset.card_le_card hImageSubset
      _ = 4 * (R a b).card := hDcard

end ProbabilityBasics
