/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant

/-!
# A lower bound for subadditive homogeneous functions on the quadrant

The theorem here is the proof of the statement `martin_remark_5_1_i_lower` in
`Frozen/Martin/Remark51.lean` (Martin (2004), Remark 5.1(i), first sentence, for `d = 2`). A
homogeneous, symmetric, subadditive function on the closed quadrant is bounded below by its value
at `(1, 1)` times the half-sum of the coordinates.

## Main results

- `martin_remark_5_1_i_lower`: `h x ≥ ((x₁ + x₂)/2) h (1, 1)`.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Remark 5.1(i).
-/

@[expose] public section

open scoped NNReal

namespace LPPDifferentiability.Full

/-- Lower bound from Martin (2004), Remark 5.1(i), first sentence, for `d = 2`. A homogeneous,
symmetric, subadditive function `h` on the closed positive quadrant satisfies
`h x ≥ ((x₁ + x₂)/2) h (1, 1)`. The proof is deterministic: halve the point `(x₁ + x₂, x₁ + x₂)`
using homogeneity, and compare it with `x` and its swap using subadditivity and symmetry. -/
theorem martin_remark_5_1_i_lower (h : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x)
    (hsymm : ∀ x : Quadrant, h (x.2, x.1) = h x)
    (hsub : ∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y)
    (x : Quadrant) :
    ((x.1 : ℝ) + x.2) / 2 * h (1, 1) ≤ h x :=
by
  -- Step 0: the coefficient (x1 + x2)/2 is a nonnegative real number c.
  have hs0 : (0 : ℝ) ≤ ((x.1 : ℝ) + x.2) / 2 :=
    div_nonneg (add_nonneg x.1.coe_nonneg x.2.coe_nonneg) (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = ((x.1 : ℝ) + x.2) / 2 :=
    ⟨Real.toNNReal _, Real.coe_toNNReal _ hs0⟩
  -- Steps 1-2: subadditivity at x and its swap, then symmetry.
  have hswap : h (x.1 + x.2, x.2 + x.1) ≤ h x + h x := by
    have h1 := hsub x (x.2, x.1)
    rw [hsymm x] at h1
    exact h1
  -- Step 3: homogeneity with c = 2 gives h(x1 + x2, x1 + x2) = 2 h(c, c).
  have hdouble : h (x.1 + x.2, x.2 + x.1) = 2 * h (c, c) := by
    have e : ((2 : ℝ≥0) * (c, c).1, (2 : ℝ≥0) * (c, c).2) = (x.1 + x.2, x.2 + x.1) := by
      refine Prod.ext ?_ ?_
      · apply NNReal.eq
        dsimp only
        push_cast
        rw [hc]
        ring
      · apply NNReal.eq
        dsimp only
        push_cast
        rw [hc]
        ring
    have h2 := hhom 2 (c, c)
    rw [e] at h2
    exact h2.trans (by norm_num)
  -- Step 4: combining steps 1-3 gives h(c, c) <= h x.
  have hdiag : h (c, c) ≤ h x := by linarith
  -- Step 5: homogeneity with the point (1, 1) gives h(c, c) = c h(1, 1).
  have hhom11 : h (c, c) = (c : ℝ) * h (1, 1) := by
    simpa using hhom c (1, 1)
  -- Step 6: since c = (x1 + x2)/2, this is the claimed inequality.
  rw [← hc, ← hhom11]
  exact hdiag

end LPPDifferentiability.Full
