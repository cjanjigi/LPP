/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.ProcessSample
public import LPP_Foundations.Model.LatticeEdgeRegularity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Regularity of the literal signed horizontal-then-vertical coordinate path sum. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- The literal signed coordinate path sum is jointly measurable, integrable
under coordinate integrability, and agrees pointwise with each outgoing edge
on its unit step. -/
theorem coordinate_path_sum_regularities (P : Measure ProcessSample)
    (hInt : ∀ j x i, Integrable (fun s : ProcessSample => s.2 j x i) P) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
    let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
      S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
        S (fun k => s.2 j (y.1, k) 1) x.2 y.2
    Measurable (fun q : ℕ × Lattice × Lattice × ProcessSample =>
      R q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ j x y, Integrable (R j x y) P) ∧
    (∀ s j x, R j x (x + (1, 0)) s = s.2 j x 0 ∧
      R j x (x + (0, 1)) s = s.2 j x 1) := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
  let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
    S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
      S (fun k => s.2 j (y.1, k) 1) x.2 y.2
  change Measurable (fun q : ℕ × Lattice × Lattice × ProcessSample =>
      R q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ j x y, Integrable (R j x y) P) ∧
    (∀ s j x, R j x (x + (1, 0)) s = s.2 j x 0 ∧
      R j x (x + (0, 1)) s = s.2 j x 1)
  let u : ℕ → Lattice → Fin 2 → ProcessSample → ℝ := fun j x i s => s.2 j x i
  have hRawEdge : Measurable (fun q : ℕ × Lattice × Fin 2 × ProcessSample =>
      u q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    apply measurable_from_prod_countable_right
    intro j
    apply measurable_from_prod_countable_right
    intro x
    apply measurable_from_prod_countable_right
    intro i
    exact (measurable_pi_apply i).comp
      ((measurable_pi_apply x).comp ((measurable_pi_apply j).comp measurable_snd))
  have hMeas := measurable_lattice_coordinate_path_sum u hRawEdge
  have hIntegrable := integrable_lattice_coordinate_path_sum P u hInt
  have hUnit := lattice_coordinate_path_sum_unit_values u
  have hIcoSucc (a : ℤ) : Finset.Ico a (a + 1) = {a} := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  exact ⟨hMeas, hIntegrable, fun s j x => by
    simp [R, S, hIcoSucc]⟩

end LPP.Busemann
