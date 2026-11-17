/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Lattice

/-! Aligned-tail coalescence for two lattice paths. -/

@[expose] public section

namespace LPPDifferentiability

/-- Paths with declared roots `u` and `v` agree on tails whose absolute levels
are aligned. The starting times may depend on both paths and roots. Start and
step properties, when needed, are separate hypotheses. -/
def paths_coalesce (u v : Lattice) (γ δ : ℕ → Lattice) : Prop :=
  ∃ m n : ℕ,
    u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
    ∀ k : ℕ, γ (m + k) = δ (n + k)

/-- Expand coalescence without changing the two starting-time witnesses. -/
theorem paths_coalesce_iff (u v : Lattice) (γ δ : ℕ → Lattice) :
    paths_coalesce u v γ δ ↔
      ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, γ (m + k) = δ (n + k) := Iff.rfl

/-- Reversing coalescing paths exchanges their original starting times. -/
theorem paths_coalesce_symm (u v : Lattice) (γ δ : ℕ → Lattice)
    (h : paths_coalesce u v γ δ) : paths_coalesce v u δ γ := by
  rcases h with ⟨m, n, hlevel, htail⟩
  exact ⟨n, m, hlevel.symm, fun k => (htail k).symm⟩

end LPPDifferentiability
