/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import Mathlib.Topology.Instances.Real.Lemmas

/-! Passage-difference limits along a single supplied lattice ray. -/

@[expose] public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- Passage differences along `γ` converge to the supplied field at every
entry index beyond both sites. This states only the limit property of that
same ray and field. -/
def has_passage_difference_limits (ω : Environment) (γ : ℕ → Lattice)
    (C : Lattice → Lattice → ℝ) : Prop :=
  ∀ x y : Lattice, ∀ N : ℕ, x ≤ γ N → y ≤ γ N →
    Tendsto (fun n : ℕ =>
      lastPassage ω x
        (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
      lastPassage ω y
        (((γ (N + n)).1 - y.1).toNat, ((γ (N + n)).2 - y.2).toNat))
      atTop (𝓝 (C x y))

/-- Expand the all-entry limit property for the same ray and supplied field. -/
theorem has_passage_difference_limits_iff
    (ω : Environment) (γ : ℕ → Lattice) (C : Lattice → Lattice → ℝ) :
    has_passage_difference_limits ω γ C ↔
      ∀ x y : Lattice, ∀ N : ℕ, x ≤ γ N → y ≤ γ N →
        Tendsto (fun n : ℕ =>
          lastPassage ω x
            (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
          lastPassage ω y
            (((γ (N + n)).1 - y.1).toNat, ((γ (N + n)).2 - y.2).toNat))
          atTop (𝓝 (C x y)) := Iff.rfl

end LPPDifferentiability
