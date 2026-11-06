/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.TiltStripCardinality

/-! The literal closed-strip slice on level zero. -/

@[expose] public section

namespace LPPDifferentiability

/-- The literal interval image on level zero is exactly the closed strip slice. -/
theorem tiltStripStartSlice_mem_iff (a s : ℝ) (z : Lattice) :
    z ∈ (Finset.Icc (Int.ceil (-8 * s)) (Int.floor (8 * s))).image
        (fun i => (i, -i)) ↔
      z.1 + z.2 = 0 ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ 8 * s := by
  simpa only [Int.cast_zero, mul_zero, zero_sub, zero_add, neg_mul] using
    (tiltStripLevelSlice_mem_iff a s (0 : ℤ) z)

/-- The literal starting slice has real cardinality at most `17s` for `s ≥ 1`. -/
theorem tiltStripCanonicalStartSlice_card_le (a s : ℝ) (hs : 1 ≤ s) :
    ((Finset.Icc (Int.ceil (-8 * s)) (Int.floor (8 * s))).image
        (fun i => (i, -i))).card ≤
      17 * s := by
  simpa only [Int.cast_zero, mul_zero, zero_sub, zero_add, neg_mul] using
    (tiltStripStartSlice_card_le a s hs)

end LPPDifferentiability
