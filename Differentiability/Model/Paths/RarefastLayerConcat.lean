/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.WeightConcat

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Layer-by-layer concatenation of crossings and connectors

Step 6 of the proof of Proposition 3.4 of the differentiability preprint joins, layer by layer, a
crossing with very negative defect in each layer and a connector with small defect between
consecutive layers. This file proves the deterministic part: finitely many layers already give one
actual path whose defect has the additive bound. Only finite prefixes are built.
-/

public section

namespace LPPDifferentiability

namespace Path

private theorem exists_path_transport_weight (ω : Environment) {a b : Lattice}
    {d : ℕ × ℕ} (h : a = b) (p : Path a d) :
    ∃ p' : Path b d, pathWeight ω p' = pathWeight ω p := by
  subst h
  exact ⟨p, rfl⟩

/-- Let `f` be additive on lattice displacements. Suppose that each layer `k`
has a crossing that starts at a vertex satisfying `P k`, ends at a vertex
satisfying `Q k`, and has defect `f (displacement) - weight < -A`. Suppose
also that every vertex satisfying `Q k` is joined to every vertex satisfying
`P (k + 1)` by a connector with defect at most `B`. Then one start vertex
satisfying `P 0` begins, for every `k`, an actual path that ends at a vertex
satisfying `Q k` and has defect less than `-(k + 1) A + k B`. -/
theorem exists_layer_concat_defect (ω : Environment) (f : Lattice → ℝ)
    (hf : ∀ x y : Lattice, f (x + y) = f x + f y) (A B : ℝ)
    (P Q : ℕ → Lattice → Prop)
    (hcross : ∀ k : ℕ, ∃ u : Lattice, P k u ∧ ∃ e : ℕ × ℕ, ∃ q : Path u e,
      Q k (u + ((e.1 : ℤ), (e.2 : ℤ))) ∧
        f ((e.1 : ℤ), (e.2 : ℤ)) - pathWeight ω q < -A)
    (hconn : ∀ k : ℕ, ∀ x y : Lattice, Q k x → P (k + 1) y →
      ∃ e : ℕ × ℕ, ∃ q : Path x e, x + ((e.1 : ℤ), (e.2 : ℤ)) = y ∧
        f ((e.1 : ℤ), (e.2 : ℤ)) - pathWeight ω q ≤ B) :
    ∃ u : Lattice, P 0 u ∧ ∀ k : ℕ, ∃ e : ℕ × ℕ, ∃ q : Path u e,
      Q k (u + ((e.1 : ℤ), (e.2 : ℤ))) ∧
        f ((e.1 : ℤ), (e.2 : ℤ)) - pathWeight ω q <
          -(((k : ℝ) + 1) * A) + (k : ℝ) * B := by
  obtain ⟨u, hPu, e₀, q₀, hQ₀, hd₀⟩ := hcross 0
  refine ⟨u, hPu, ?_⟩
  intro k
  induction k with
  | zero =>
      refine ⟨e₀, q₀, hQ₀, ?_⟩
      have hzero : -((((0 : ℕ) : ℝ) + 1) * A) + ((0 : ℕ) : ℝ) * B = -A := by
        push_cast
        ring
      rw [hzero]
      exact hd₀
  | succ k ih =>
      obtain ⟨e, q, hQ, hd⟩ := ih
      obtain ⟨u', hP', e', q', hQ', hd'⟩ := hcross (k + 1)
      obtain ⟨e₁, q₁, hend, hd₁⟩ := hconn k _ _ hQ hP'
      have hu' : u' = u + (((e + e₁).1 : ℤ), ((e + e₁).2 : ℤ)) := by
        rw [← hend]
        apply Prod.ext <;>
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> ring
      obtain ⟨q₂, hq₂⟩ := exists_path_transport_weight ω hu' q'
      refine ⟨e + e₁ + e', (q.concat q₁).concat q₂, ?_, ?_⟩
      · have hpt : u + (((e + e₁ + e').1 : ℤ), ((e + e₁ + e').2 : ℤ)) =
            u' + ((e'.1 : ℤ), (e'.2 : ℤ)) := by
          rw [hu']
          apply Prod.ext <;>
            simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> ring
        rw [hpt]
        exact hQ'
      · have hsplit : ((((e + e₁ + e').1 : ℕ) : ℤ), (((e + e₁ + e').2 : ℕ) : ℤ)) =
            (((e.1 : ℤ), (e.2 : ℤ)) + ((e₁.1 : ℤ), (e₁.2 : ℤ))) +
              ((e'.1 : ℤ), (e'.2 : ℤ)) := by
          apply Prod.ext <;>
            simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add]
        rw [hsplit, hf, hf, pathWeight_concat, pathWeight_concat, hq₂]
        push_cast
        linarith

end Path

end LPPDifferentiability

end
