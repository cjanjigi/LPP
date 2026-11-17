/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Analysis.QuadrantSuperdifferential
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.OrderClosed

/-! Geometry of the literal full-quadrant superdifferential. -/

public section

namespace LPPDifferentiability

/-- For every function on the closed quadrant, its literal superdifferential
is a closed convex set. This is the geometric claim used in equation (2.5)
and Lemma 4.5(c) of arXiv:1810.03580v3. -/
theorem isClosed_and_convex_quadrantSuperdifferential
    (g : Quadrant → ℝ) (ξ : Quadrant) :
    IsClosed (quadrantSuperdifferential g ξ) ∧
      Convex ℝ (quadrantSuperdifferential g ξ) := by
  let normal : Quadrant → ((ℝ × ℝ) →ₗ[ℝ] ℝ) := fun z =>
    { toFun := fun v =>
        v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
          v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ))
      map_add' := by
        intro v w
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      map_smul' := by
        intro c v
        change c * v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
            c * v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ)) =
          c * (v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
            v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ)))
        ring }
  have hset : quadrantSuperdifferential g ξ =
      ⋂ z : Quadrant, {v : ℝ × ℝ | normal z v ≤ g ξ - g z} := by
    ext v
    simp [quadrantSuperdifferential, normal]
  rw [hset]
  change IsClosed (⋂ z : Quadrant, {v | normal z v ≤ g ξ - g z}) ∧
    Convex ℝ (⋂ z : Quadrant, {v | normal z v ≤ g ξ - g z})
  constructor
  · -- Each fixed comparison point gives one closed linear halfspace.
    apply isClosed_iInter
    intro z
    apply isClosed_le
    · change Continuous fun v : ℝ × ℝ =>
        v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
          v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ))
      fun_prop
    · exact continuous_const
  · -- Each halfspace is a linear preimage of a convex lower interval.
    apply convex_iInter
    intro z
    change Convex ℝ ((normal z) ⁻¹' Set.Iic (g ξ - g z))
    exact (convex_Iic (g ξ - g z)).linear_preimage (normal z)

end LPPDifferentiability
