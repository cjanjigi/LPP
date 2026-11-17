/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Cardinality limits for intervals and rectangles with floor endpoints. -/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace ProbabilityBasics

/-- The integer points between two nonnegative linearly growing floors have
asymptotic density equal to the difference of their slopes. This is the side
length normalization used in `ProbabilityBasics/Analysis/RectangleInvariant.lean:153-160`. -/
theorem tendsto_floor_interval_card_div (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun n : ℕ =>
      ((Finset.Ico ((⌊(n : ℝ) * a⌋₊ : ℕ) : ℤ)
        ((⌊(n : ℝ) * b⌋₊ : ℕ) : ℤ)).card : ℝ) / (n : ℝ))
      atTop (𝓝 (b - a)) := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  let A : ℕ → ℕ := fun n => ⌊(n : ℝ) * a⌋₊
  let B : ℕ → ℕ := fun n => ⌊(n : ℝ) * b⌋₊

  have hEndpoints (n : ℕ) : A n ≤ B n := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (le_of_lt hab) (Nat.cast_nonneg n)

  have hFloorA : Tendsto (fun n : ℕ => (A n : ℝ) / (n : ℝ)) atTop (𝓝 a) := by
    simpa only [A, Function.comp_def, mul_comm] using
      ((tendsto_nat_floor_mul_div_atTop (a := a) ha).comp
        tendsto_natCast_atTop_atTop)
  have hFloorB : Tendsto (fun n : ℕ => (B n : ℝ) / (n : ℝ)) atTop (𝓝 b) := by
    simpa only [B, Function.comp_def, mul_comm] using
      ((tendsto_nat_floor_mul_div_atTop (a := b) hb.le).comp
        tendsto_natCast_atTop_atTop)

  have hCardInt (n : ℕ) :
      ((Finset.Ico (A n : ℤ) (B n : ℤ)).card : ℤ) = (B n : ℤ) - (A n : ℤ) := by
    exact Int.card_Ico_of_le (a := (A n : ℤ)) (b := (B n : ℤ)) (by exact_mod_cast hEndpoints n)
  have hCardReal (n : ℕ) :
      ((Finset.Ico (A n : ℤ) (B n : ℤ)).card : ℝ) = (B n : ℝ) - (A n : ℝ) := by
    exact_mod_cast hCardInt n

  have hCardRatio (n : ℕ) :
      ((Finset.Ico (A n : ℤ) (B n : ℤ)).card : ℝ) / (n : ℝ) =
        (B n : ℝ) / (n : ℝ) - (A n : ℝ) / (n : ℝ) := by
    rw [hCardReal n, sub_div]

  have hRatioLimit : Tendsto
      (fun n : ℕ => (B n : ℝ) / (n : ℝ) - (A n : ℝ) / (n : ℝ))
      atTop (𝓝 (b - a)) := hFloorB.sub hFloorA
  apply hRatioLimit.congr'
  filter_upwards [] with n
  exact (hCardRatio n).symm

/-- The number of integer points in a floor rectangle, divided by `n^2`,
tends to the product of its side lengths. This is the area normalization used
in `ProbabilityBasics/Analysis/RectangleInvariant.lean:148-174`. -/
theorem tendsto_floor_rectangle_card_div_sq
    (a b : Fin 2 → ℝ) (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j) :
    Tendsto (fun n : ℕ =>
      (((Finset.Ico ((⌊(n : ℝ) * a 0⌋₊ : ℕ) : ℤ)
          ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico ((⌊(n : ℝ) * a 1⌋₊ : ℕ) : ℤ)
          ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))).card : ℝ) / (n : ℝ)^2)
      atTop (𝓝 ((b 0 - a 0) * (b 1 - a 1))) := by
  let I0 : ℕ → Finset ℤ := fun n =>
    Finset.Ico ((⌊(n : ℝ) * a 0⌋₊ : ℕ) : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)
  let I1 : ℕ → Finset ℤ := fun n =>
    Finset.Ico ((⌊(n : ℝ) * a 1⌋₊ : ℕ) : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)

  have hSide0 : Tendsto (fun n : ℕ => ((I0 n).card : ℝ) / (n : ℝ))
      atTop (𝓝 (b 0 - a 0)) := by
    simpa only [I0] using tendsto_floor_interval_card_div (a 0) (b 0) (ha 0) (hab 0)
  have hSide1 : Tendsto (fun n : ℕ => ((I1 n).card : ℝ) / (n : ℝ))
      atTop (𝓝 (b 1 - a 1)) := by
    simpa only [I1] using tendsto_floor_interval_card_div (a 1) (b 1) (ha 1) (hab 1)
  have hSideProduct : Tendsto
      (fun n : ℕ => (((I0 n).card : ℝ) / (n : ℝ)) * (((I1 n).card : ℝ) / (n : ℝ)))
      atTop (𝓝 ((b 0 - a 0) * (b 1 - a 1))) := by
    exact hSide0.mul hSide1

  have hCardRatio (n : ℕ) :
      (((I0 n).product (I1 n)).card : ℝ) / (n : ℝ)^2 =
        (((I0 n).card : ℝ) / (n : ℝ)) * (((I1 n).card : ℝ) / (n : ℝ)) := by
    by_cases hn : n = 0
    · subst n
      simp [I0, I1]
    · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      rw [Finset.product_eq_sprod, Finset.card_product]
      push_cast
      field_simp [hnR]

  apply hSideProduct.congr'
  filter_upwards [] with n
  exact (hCardRatio n).symm

end ProbabilityBasics
