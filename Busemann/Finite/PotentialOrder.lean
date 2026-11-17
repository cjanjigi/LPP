/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteTiltedPotential

/-! Order properties of the literal finite point-to-line maximum. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Every endpoint candidate is below the finite maximum of JR1810.03580v3. -/
theorem finiteTiltedPotential_candidate_le (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) (hx : x.1 + x.2 ≤ n)
    (k : Fin ((n - (x.1 + x.2)).toNat + 1)) :
    ((lastPassage ω x (k.val, (n - (x.1 + x.2)).toNat - k.val) +
      h.1 * (k.val : ℝ) +
      h.2 * (((n - (x.1 + x.2)).toNat - k.val : ℕ) : ℝ) : ℝ) : EReal) ≤
      finiteTiltedPotential ω h x n := by
  classical
  unfold finiteTiltedPotential
  split_ifs
  · apply EReal.coe_le_coe
    apply Finset.le_max'
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)

/-- The finite maximum of JR1810.03580v3 is bounded exactly when all candidates are. -/
theorem finiteTiltedPotential_le_coe_iff (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) (hx : x.1 + x.2 ≤ n) (r : ℝ) :
    finiteTiltedPotential ω h x n ≤ (r : EReal) ↔
      ∀ k : Fin ((n - (x.1 + x.2)).toNat + 1),
        lastPassage ω x (k.val, (n - (x.1 + x.2)).toNat - k.val) +
          h.1 * (k.val : ℝ) +
          h.2 * (((n - (x.1 + x.2)).toNat - k.val : ℕ) : ℝ) ≤ r := by
  classical
  constructor
  · intro hbound k
    have hcandidate := finiteTiltedPotential_candidate_le ω h x n hx k
    exact EReal.coe_le_coe_iff.mp (hcandidate.trans hbound)
  · intro hbound
    unfold finiteTiltedPotential
    split_ifs
    · apply EReal.coe_le_coe
      apply Finset.max'_le
      intro y hy
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
      exact hbound k

/-- The active finite maximum in JR1810.03580v3 is not positive infinity. -/
theorem finiteTiltedPotential_ne_top (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) (hx : x.1 + x.2 ≤ n) :
    finiteTiltedPotential ω h x n ≠ ⊤ := by
  classical
  unfold finiteTiltedPotential
  split_ifs
  · exact EReal.coe_ne_top _

/-- The active finite maximum in JR1810.03580v3 is not negative infinity. -/
theorem finiteTiltedPotential_ne_bot (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) (hx : x.1 + x.2 ≤ n) :
    finiteTiltedPotential ω h x n ≠ ⊥ := by
  classical
  unfold finiteTiltedPotential
  split_ifs
  · exact EReal.coe_ne_bot _

end LPP.Busemann
