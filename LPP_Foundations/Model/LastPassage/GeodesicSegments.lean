/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage

/-! Finite maximizing segments traced by one infinite lattice path. -/

@[expose] public section

namespace LPPDifferentiability

/-- Every positive-length segment of `γ` is represented by a maximizing finite
path. This imposes no rightmost tie-breaking condition. -/
def has_maximizing_segments (ω : Environment) (γ : ℕ → Lattice) : Prop :=
  ∀ m N : ℕ, 0 < N →
    ∃ (d : ℕ × ℕ) (p : Path (γ m) d),
      d.1 + d.2 = N ∧
      (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = γ (m + i.val)) ∧
      pathWeight ω p = lastPassage ω (γ m) d

/-- Expand the finite-segment property with its original displacement and path. -/
theorem has_maximizing_segments_iff (ω : Environment) (γ : ℕ → Lattice) :
    has_maximizing_segments ω γ ↔
      ∀ m N : ℕ, 0 < N →
        ∃ (d : ℕ × ℕ) (p : Path (γ m) d),
          d.1 + d.2 = N ∧
          (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = γ (m + i.val)) ∧
          pathWeight ω p = lastPassage ω (γ m) d := Iff.rfl

end LPPDifferentiability
