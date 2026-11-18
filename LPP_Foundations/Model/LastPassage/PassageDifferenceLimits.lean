/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Model.LatticeDisplacement
public import Mathlib.Topology.Instances.Real.Lemmas
import LPP_Foundations.Model.LastPassage.Basic

/-! Passage with comparable endpoints and passage-difference limits along a supplied ray. -/

@[expose] public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- Passage through an intermediate comparable site gives a lower bound on total passage. -/
theorem lastPassage_superadditive_between (ω : Environment) (a b c : Lattice)
    (hab : a ≤ b) (hbc : b ≤ c) :
    lastPassage ω a (natDisplacement a b) + lastPassage ω b (natDisplacement b c) ≤
      lastPassage ω a (natDisplacement a c) := by
  have h := lastPassage_superadditive ω a (natDisplacement a b) (natDisplacement b c)
  rw [add_cast_natDisplacement a b hab, natDisplacement_add a b c hab hbc] at h
  exact h

/-- Passage differences along `γ` converge to the supplied field at every
entry index beyond both sites. This states only the limit property of that
same ray and field. -/
def has_passage_difference_limits (ω : Environment) (γ : ℕ → Lattice)
    (C : Lattice → Lattice → ℝ) : Prop :=
  ∀ x y : Lattice, ∀ N : ℕ, x ≤ γ N → y ≤ γ N →
    Tendsto (fun n : ℕ =>
      lastPassage ω x (natDisplacement x (γ (N + n))) -
      lastPassage ω y (natDisplacement y (γ (N + n))))
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
