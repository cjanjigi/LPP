/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Deterministic clipping bounds for the signed finite last-passage model. -/

@[expose] public section

namespace LPPDifferentiability

/-- Clipping a real weight to `[-L,L]` stays in that interval, for `L ≥ 0`. -/
theorem clipped_weight_bounds (ω : Environment) (L : ℝ) (hL : 0 ≤ L) :
    ∀ z, -L ≤ max (-L) (min L (ω z)) ∧
      max (-L) (min L (ω z)) ≤ L ∧
      |max (-L) (min L (ω z))| ≤ L := by
  intro z
  have hlow : -L ≤ max (-L) (min L (ω z)) := le_max_left _ _
  have hup : max (-L) (min L (ω z)) ≤ L :=
    max_le (by linarith) (min_le_left _ _)
  exact ⟨hlow, hup, abs_le.mpr ⟨hlow, hup⟩⟩

/-- The clipped weight and its two nonnegative remainders recover every signed weight. -/
theorem clipped_weight_decomposition (ω : Environment) (L : ℝ) (hL : 0 ≤ L) :
    ∀ z, ω z = max (-L) (min L (ω z)) + max (ω z - L) 0 -
      max (-ω z - L) 0 := by
  intro z
  by_cases hneg : ω z < -L
  · have hωL : ω z ≤ L := by linarith
    rw [min_eq_right hωL, max_eq_left (le_of_lt hneg)]
    rw [max_eq_right (show ω z - L ≤ 0 by linarith),
      max_eq_left (show 0 ≤ -ω z - L by linarith)]
    linarith
  · by_cases hpos : L < ω z
    · have hlow : -L ≤ ω z := by linarith
      rw [min_eq_left (le_of_lt hpos), max_eq_right (by linarith)]
      rw [max_eq_left (show 0 ≤ ω z - L by linarith),
        max_eq_right (show -ω z - L ≤ 0 by linarith)]
      linarith
    · have hlow : -L ≤ ω z := le_of_not_gt hneg
      have hup : ω z ≤ L := le_of_not_gt hpos
      rw [min_eq_right hup, max_eq_right hlow]
      rw [max_eq_right (show ω z - L ≤ 0 by linarith),
        max_eq_right (show -ω z - L ≤ 0 by linarith)]
      ring

/-- The original passage maximum is bounded by the clipped and positive-remainder maxima. -/
theorem lastPassage_le_clipped_add_positive_remainder (ω : Environment) (u : Lattice)
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    lastPassage ω u d ≤
      lastPassage (fun z => max (-L) (min L (ω z))) u d +
        lastPassage (fun z => max (ω z - L) 0) u d := by
  calc
    lastPassage ω u d ≤
        lastPassage
          ((fun z => max (-L) (min L (ω z))) + (fun z => max (ω z - L) 0)) u d :=
      lastPassage_mono ω _ u d (by
        intro z
        change ω z ≤ max (-L) (min L (ω z)) + max (ω z - L) 0
        have hdecomp := clipped_weight_decomposition ω L hL z
        have hn : 0 ≤ max (-ω z - L) 0 := le_max_right _ _
        linarith)
    _ ≤ lastPassage (fun z => max (-L) (min L (ω z))) u d +
        lastPassage (fun z => max (ω z - L) 0) u d :=
      lastPassage_add_le _ _ u d

/-- The clipped passage maximum is bounded by the original and negative-remainder maxima. -/
theorem lastPassage_clipped_le_add_negative_remainder (ω : Environment) (u : Lattice)
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    lastPassage (fun z => max (-L) (min L (ω z))) u d ≤
      lastPassage ω u d + lastPassage (fun z => max (-ω z - L) 0) u d := by
  calc
    lastPassage (fun z => max (-L) (min L (ω z))) u d ≤
        lastPassage (ω + (fun z => max (-ω z - L) 0)) u d :=
      lastPassage_mono _ _ u d (by
        intro z
        change max (-L) (min L (ω z)) ≤ ω z + max (-ω z - L) 0
        have hdecomp := clipped_weight_decomposition ω L hL z
        have hp : 0 ≤ max (ω z - L) 0 := le_max_right _ _
        linarith)
    _ ≤ lastPassage ω u d + lastPassage (fun z => max (-ω z - L) 0) u d :=
      lastPassage_add_le _ _ u d

/-- The clipped field has passage magnitude at most path length times its cutoff. -/
theorem lastPassage_clipped_abs_le (ω : Environment) (u : Lattice) (d : ℕ × ℕ)
    (L : ℝ) (hL : 0 ≤ L) :
    |lastPassage (fun z => max (-L) (min L (ω z))) u d| ≤
      ((d.1 + d.2 : ℕ) : ℝ) * L :=
  lastPassage_abs_le _ u d L (fun z => (clipped_weight_bounds ω L hL z).2.2)

end LPPDifferentiability
