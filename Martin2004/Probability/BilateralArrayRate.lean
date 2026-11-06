/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralIncrementMoments
public import ProbabilityBasics.Analysis.PositiveSubadditiveRate

/-! The finite expected rate of the actual stationary proper-interval array.
No mean or rate is introduced as a public definition. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- Integrating actual superadditivity and translating the second interval
gives positive-index superadditivity of origin expectations. -/
theorem integral_bilateralArray_origin_superadditive
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (hadd : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∫ x : BilateralArray, x ⟨(0, (m : ℤ)), by omega⟩ ∂(ρ : Measure _)) +
      (∫ x : BilateralArray, x ⟨(0, (n : ℤ)), by omega⟩ ∂(ρ : Measure _)) ≤
      ∫ x : BilateralArray, x ⟨(0, ((m + n : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _) := by
  have hs : (∫ x : BilateralArray, x ⟨((m : ℤ), ((m + n : ℕ) : ℤ)), by omega⟩
      ∂(ρ : Measure _)) =
      ∫ x : BilateralArray, x ⟨(0, (n : ℤ)), by omega⟩ ∂(ρ : Measure _) := by
    simpa only [zero_add, add_zero, Nat.cast_add, add_comm] using
      integral_bilateralArray_coordinate_translate ρ hS 0 (n : ℤ) (m : ℤ) (by omega)
  rw [← hs, ← integral_add (hi _) (hi _)]
  apply integral_mono_ae ((hi _).add (hi _)) (hi _)
  exact hadd.mono fun x hx => hx 0 m (m + n) (by omega) (by omega)

/-- A finite upper bound on all positive normalized origin means produces
their actual limiting rate, with its exact LUB characterization. -/
theorem exists_bilateralArray_expected_rate
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (hnonneg : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ p, 0 ≤ x p)
    (hadd : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (B : ℝ)
    (hB : ∀ n : ℕ,
      (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) /
        (n + 1 : ℝ) ≤ B) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ B ∧
      IsLUB (range (fun n : ℕ =>
        (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) /
          (n + 1 : ℝ))) q ∧
      Tendsto (fun n : ℕ =>
        (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) /
          (n + 1 : ℝ)) atTop (𝓝 q) := by
  let f : ℕ → ℝ := fun n => ∫ x : BilateralArray,
    x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)
  -- Index zero is unused by the positive-index theorem and is not a source diagonal.
  let a : ℕ → ℝ := fun n => -f (n - 1)
  have ha (n : ℕ) (hn : 0 < n) : a n =
      -(∫ x : BilateralArray, x ⟨(0, (n : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
    dsimp only [a, f]
    congr 1
    have he : n - 1 + 1 = n := by omega
    simp only [he]
  have hsub : ∀ m n : ℕ, 0 < m → 0 < n → a (m + n) ≤ a m + a n := by
    intro m n hm hn
    rw [ha m hm, ha n hn, ha (m + n) (by omega)]
    have hs := integral_bilateralArray_origin_superadditive ρ hS hi hadd m n hm hn
    linarith only [hs]
  have hlower : ∀ n : ℕ, 0 < n → (-B) * (n : ℝ) ≤ a n := by
    intro n hn
    have hb := hB (n - 1)
    have he : n - 1 + 1 = n := by omega
    change f (n - 1) / ((n - 1 : ℕ) + 1 : ℝ) ≤ B at hb
    have hc : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast he
    rw [hc] at hb
    have hb' := (div_le_iff₀ (Nat.cast_pos.mpr hn)).mp hb
    dsimp only [a]
    linarith only [hb']
  obtain ⟨γ, hγlim, hγinf⟩ := exists_positive_subadditive_rate a hsub (-B) hlower
  have he (n : ℕ) : a (n + 1) / ((n + 1 : ℕ) : ℝ) = -(f n / (n + 1 : ℝ)) := by
    simp only [a, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, neg_div]
  have hlim : Tendsto (fun n : ℕ => f n / (n + 1 : ℝ)) atTop (𝓝 (-γ)) := by
    simpa only [he, neg_neg] using hγlim.neg
  have hbelow : BddBelow (range (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ))) := by
    refine ⟨-B, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [he]
    exact neg_le_neg (hB n)
  have hupper (n : ℕ) : f n / (n + 1 : ℝ) ≤ -γ := by
    have hl := csInf_le hbelow (mem_range_self n)
    rw [← hγinf, he] at hl
    linarith only [hl]
  have hlub : IsLUB (range (fun n : ℕ => f n / (n + 1 : ℝ))) (-γ) :=
    IsLUB.range_of_tendsto hupper hlim
  refine ⟨-γ, ?_, ?_, hlub, hlim⟩
  · have hf0 : 0 ≤ f 0 :=
      integral_nonneg_of_ae (hnonneg.mono fun _ hx => hx ⟨(0, 1), by omega⟩)
    exact (div_nonneg hf0 (show 0 ≤ ((0 : ℕ) : ℝ) + 1 by positivity)).trans (hupper 0)
  · exact hlub.2 (by rintro _ ⟨n, rfl⟩; exact hB n)

end LPPDifferentiability
