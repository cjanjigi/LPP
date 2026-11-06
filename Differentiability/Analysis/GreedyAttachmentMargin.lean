/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Greedy attachment remaining-coordinate margins

The remaining coordinates are compared with the point on the line at the same
level. The bounds use the middle-slope interval and the terminal level.
-/

public section

namespace LPPDifferentiability

/-- A central endpoint gives both remaining coordinates a margin of
`r / 4 - |d|`, where `d` is the first-coordinate deviation from the line. -/
theorem greedy_attachment_remaining_coordinate_margin
    (m j r a b : ℕ) (d : ℝ)
    (hm : 0 < m)
    (hj_lo : (1 / 4 : ℝ) ≤ (j : ℝ) / (m : ℝ))
    (hj_hi : (j : ℝ) / (m : ℝ) ≤ 3 / 4)
    (ha : (a : ℝ) = (r : ℝ) / (m : ℝ) * (j : ℝ) - d)
    (hb : (b : ℝ) = (r : ℝ) / (m : ℝ) * ((m - j : ℕ) : ℝ) + d) :
    (a : ℝ) + (b : ℝ) = (r : ℝ) ∧
      (r : ℝ) / 4 - |d| ≤ (a : ℝ) ∧
      (r : ℝ) / 4 - |d| ≤ (b : ℝ) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hr_nonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hjR_le : (j : ℝ) ≤ (m : ℝ) := by
    have hmul := (div_le_iff₀ hmR).mp hj_hi
    nlinarith
  have hj_le : j ≤ m := by exact_mod_cast hjR_le
  have hsubNat : m - j + j = m := Nat.sub_add_cancel hj_le
  have hsubR : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
    have hsubCast : ((m - j : ℕ) : ℝ) + (j : ℝ) = (m : ℝ) := by
      exact_mod_cast hsubNat
    linarith
  have hcomplement_lo : (1 / 4 : ℝ) ≤ 1 - (j : ℝ) / (m : ℝ) := by
    linarith
  have hcomplement_eq :
      1 - (j : ℝ) / (m : ℝ) = ((m : ℝ) - (j : ℝ)) / (m : ℝ) := by
    field_simp [hm_ne]
  have hcomplement_ratio :
      (1 / 4 : ℝ) ≤ ((m : ℝ) - (j : ℝ)) / (m : ℝ) := by
    rw [← hcomplement_eq]
    exact hcomplement_lo
  have hfirst_base : (r : ℝ) / 4 ≤ (r : ℝ) / (m : ℝ) * (j : ℝ) := by
    calc
      (r : ℝ) / 4 = (r : ℝ) * (1 / 4 : ℝ) := by ring
      _ ≤ (r : ℝ) * ((j : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hj_lo hr_nonneg
      _ = (r : ℝ) / (m : ℝ) * (j : ℝ) := by
        field_simp [hm_ne]
  have hsecond_base :
      (r : ℝ) / 4 ≤ (r : ℝ) / (m : ℝ) * ((m - j : ℕ) : ℝ) := by
    calc
      (r : ℝ) / 4 = (r : ℝ) * (1 / 4 : ℝ) := by ring
      _ ≤ (r : ℝ) * (((m : ℝ) - (j : ℝ)) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hcomplement_ratio hr_nonneg
      _ = (r : ℝ) / (m : ℝ) * ((m - j : ℕ) : ℝ) := by
        rw [hsubR]
        field_simp [hm_ne]
  have hsum : (a : ℝ) + (b : ℝ) = (r : ℝ) := by
    rw [ha, hb, hsubR]
    field_simp [hm_ne]
    ring
  have ha_margin : (r : ℝ) / 4 - |d| ≤ (a : ℝ) := by
    rw [ha]
    have hneg : -|d| ≤ -d := neg_le_neg (le_abs_self d)
    linarith
  have hb_margin : (r : ℝ) / 4 - |d| ≤ (b : ℝ) := by
    rw [hb]
    linarith [hsecond_base, neg_abs_le d]
  exact ⟨hsum, ha_margin, hb_margin⟩

/-- A deviation bounded by `K` leaves positive natural coordinates when the
remaining level is strictly above `4K+4`. -/
theorem greedy_attachment_remaining_coordinates_positive_of_large_level
    (m j r a b K : ℕ) (d : ℝ)
    (hm : 0 < m)
    (hj_lo : (1 / 4 : ℝ) ≤ (j : ℝ) / (m : ℝ))
    (hj_hi : (j : ℝ) / (m : ℝ) ≤ 3 / 4)
    (hdev : |d| ≤ (K : ℝ))
    (hlevel : 4 * (K : ℝ) + 4 < (r : ℝ))
    (ha : (a : ℝ) = (r : ℝ) / (m : ℝ) * (j : ℝ) - d)
    (hb : (b : ℝ) = (r : ℝ) / (m : ℝ) * ((m - j : ℕ) : ℝ) + d) :
    0 < a ∧ 0 < b := by
  have hmargin := greedy_attachment_remaining_coordinate_margin
    m j r a b d hm hj_lo hj_hi ha hb
  have hpositive_margin : 0 < (r : ℝ) / 4 - |d| := by
    nlinarith
  have ha_pos : 0 < (a : ℝ) := lt_of_lt_of_le hpositive_margin hmargin.2.1
  have hb_pos : 0 < (b : ℝ) := lt_of_lt_of_le hpositive_margin hmargin.2.2
  exact ⟨by exact_mod_cast ha_pos, by exact_mod_cast hb_pos⟩

/-- At the exact terminal level `L = 4K+4`, both remaining natural
coordinates are at least one. -/
theorem greedy_attachment_remaining_coordinates_at_terminal_level
    (m j r a b K : ℕ) (d : ℝ)
    (hm : 0 < m)
    (hj_lo : (1 / 4 : ℝ) ≤ (j : ℝ) / (m : ℝ))
    (hj_hi : (j : ℝ) / (m : ℝ) ≤ 3 / 4)
    (hdev : |d| ≤ (K : ℝ))
    (hlevel : (r : ℝ) = 4 * (K : ℝ) + 4)
    (ha : (a : ℝ) = (r : ℝ) / (m : ℝ) * (j : ℝ) - d)
    (hb : (b : ℝ) = (r : ℝ) / (m : ℝ) * ((m - j : ℕ) : ℝ) + d) :
    1 ≤ a ∧ 1 ≤ b := by
  have hmargin := greedy_attachment_remaining_coordinate_margin
    m j r a b d hm hj_lo hj_hi ha hb
  have hsource_margin : (1 : ℝ) ≤ (r : ℝ) / 4 - |d| := by
    nlinarith
  have ha_one : (1 : ℝ) ≤ (a : ℝ) := le_trans hsource_margin hmargin.2.1
  have hb_one : (1 : ℝ) ≤ (b : ℝ) := le_trans hsource_margin hmargin.2.2
  exact ⟨by exact_mod_cast ha_one, by exact_mod_cast hb_one⟩

end LPPDifferentiability

end
