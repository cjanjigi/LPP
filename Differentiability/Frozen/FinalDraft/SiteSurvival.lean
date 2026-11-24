/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Model.Paths.UpRightRay

/-! Survival of the origin cluster in oriented site percolation. -/

@[expose] public section

namespace LPPDifferentiability.FinalDraft

/-- Survival from the origin through sites of weight `M`. The starting site
is free, as in `OpenReach`, and each later site of the ray must be open. -/
def orientedSiteSurvival (M : ℝ) : Set Environment :=
  {ω | ∃ γ : ℕ → Lattice, γ 0 = 0 ∧ IsUpRightRay γ ∧
    ∀ n : ℕ, ω (γ (n + 1)) = M}

end LPPDifferentiability.FinalDraft
