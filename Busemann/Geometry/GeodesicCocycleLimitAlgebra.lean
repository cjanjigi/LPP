/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Geometry.GeodesicPassageDifferenceLimit
import Mathlib.Tactic

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

/-- Finite root-relative limits determine exactly one additive pair field.
The conclusion uses every common valid entry index, including entries from
signed sites southwest of the ray's root. -/
theorem unique_additive_pair_field_of_root_limits
    (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hescape₁ : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
    (hescape₂ : Tendsto (fun n : ℕ => (γ n).2) atTop atTop)
    (b : Lattice → ℝ)
    (hLimit : ∀ x : Lattice, ∀ N : ℕ, x ≤ γ N →
      Tendsto (fun n : ℕ =>
        lastPassage ω x
          (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
        lastPassage ω u
          (((γ (N + n)).1 - u.1).toNat, ((γ (N + n)).2 - u.2).toNat))
        atTop (𝓝 (b x))) :
    ∃! B : Lattice → Lattice → ℝ,
      (∀ x y : Lattice, ∀ N : ℕ, x ≤ γ N → y ≤ γ N →
        Tendsto (fun n : ℕ =>
          lastPassage ω x
            (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
          lastPassage ω y
            (((γ (N + n)).1 - y.1).toNat, ((γ (N + n)).2 - y.2).toNat))
          atTop (𝓝 (B x y))) ∧ is_additive B := by
  let B : Lattice → Lattice → ℝ := fun x y => b x - b y
  have hPair (x y : Lattice) (N : ℕ) (hx : x ≤ γ N) (hy : y ≤ γ N) :
      Tendsto (fun n : ℕ =>
        lastPassage ω x
          (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
        lastPassage ω y
          (((γ (N + n)).1 - y.1).toNat, ((γ (N + n)).2 - y.2).toNat))
        atTop (𝓝 (B x y)) := by
    have h := (hLimit x N hx).sub (hLimit y N hy)
    convert h using 1; (try funext n); ring
  have hAdd : is_additive B := by
    intro x y z
    dsimp only [B]
    ring
  refine ⟨B, ⟨hPair, hAdd⟩, ?_⟩
  intro C hC
  funext x y
  obtain ⟨nx, hnx⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hescape₁) x.1)
  obtain ⟨ny, hny⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hescape₁) y.1)
  obtain ⟨mx, hmx⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hescape₂) x.2)
  obtain ⟨my, hmy⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hescape₂) y.2)
  let N := max (max nx ny) (max mx my)
  have hx : x ≤ γ N := by
    constructor
    · exact hnx _ (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact hmx _ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hy : y ≤ γ N := by
    constructor
    · exact hny _ (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact hmy _ (le_trans (le_max_right _ _) (le_max_right _ _))
  exact tendsto_nhds_unique (hC.1 x y N hx hy) (hPair x y N hx hy)

end LPP.Busemann
