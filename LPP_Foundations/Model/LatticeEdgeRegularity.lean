/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Interval

/-! Regularity of the literal signed coordinate path sum for measurable edge families. -/

public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- A jointly measurable edge family has a jointly measurable signed coordinate path sum.
The index type may be uncountable; only the lattice coordinates are countable. -/
theorem measurable_lattice_coordinate_path_sum
    {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    (u : A → Lattice → Fin 2 → Ω → ℝ)
    (hu : Measurable (fun q : A × Lattice × Fin 2 × Ω =>
      u q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
      else -(∑ k ∈ Finset.Ico b a, f k)
    let R : A → Lattice → Lattice → Ω → ℝ := fun a x y s =>
      S (fun k => u a (k, x.2) 0 s) x.1 y.1 +
        S (fun k => u a (y.1, k) 1 s) x.2 y.2
    Measurable (fun q : A × Lattice × Lattice × Ω =>
      R q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let R : A → Lattice → Lattice → Ω → ℝ := fun a x y s =>
    S (fun k => u a (k, x.2) 0 s) x.1 y.1 +
      S (fun k => u a (y.1, k) 1 s) x.2 y.2
  change Measurable (fun q : A × Lattice × Lattice × Ω =>
    R q.1 q.2.1 q.2.2.1 q.2.2.2)
  have hcoord (x : Lattice) (i : Fin 2) :
      Measurable (fun p : A × Ω => u p.1 x i p.2) := by
    exact hu.comp (measurable_fst.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))
  have hfixed (x y : Lattice) :
      Measurable (fun p : A × Ω => R p.1 x y p.2) := by
    have hHorizontal : Measurable (fun p : A × Ω =>
        S (fun k => u p.1 (k, x.2) 0 p.2) x.1 y.1) := by
      by_cases hxy : x.1 ≤ y.1
      · simp only [S, ite_eq_left hxy]
        exact Finset.measurable_sum _ fun k _ => hcoord (k, x.2) 0
      · simp only [S, ite_eq_right hxy]
        exact (Finset.measurable_sum _ fun k _ => hcoord (k, x.2) 0).neg
    have hVertical : Measurable (fun p : A × Ω =>
        S (fun k => u p.1 (y.1, k) 1 p.2) x.2 y.2) := by
      by_cases hxy : x.2 ≤ y.2
      · simp only [S, ite_eq_left hxy]
        exact Finset.measurable_sum _ fun k _ => hcoord (y.1, k) 1
      · simp only [S, ite_eq_right hxy]
        exact (Finset.measurable_sum _ fun k _ => hcoord (y.1, k) 1).neg
    exact hHorizontal.add hVertical
  have hReordered : Measurable (fun q : Lattice × Lattice × A × Ω =>
      R q.2.2.1 q.1 q.2.1 q.2.2.2) := by
    apply measurable_from_prod_countable_right
    intro x
    apply measurable_from_prod_countable_right
    intro y
    exact hfixed x y
  have hPermutation : Measurable (fun q : A × Lattice × Lattice × Ω =>
      (q.2.1, (q.2.2.1, (q.1, q.2.2.2)))) := by
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  exact hReordered.comp hPermutation

/-- Coordinate integrability makes every finite signed coordinate path sum integrable. -/
theorem integrable_lattice_coordinate_path_sum
    {A Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : A → Lattice → Fin 2 → Ω → ℝ)
    (hInt : ∀ a x i, Integrable (u a x i) P) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
      else -(∑ k ∈ Finset.Ico b a, f k)
    let R : A → Lattice → Lattice → Ω → ℝ := fun a x y s =>
      S (fun k => u a (k, x.2) 0 s) x.1 y.1 +
        S (fun k => u a (y.1, k) 1 s) x.2 y.2
    ∀ a x y, Integrable (R a x y) P := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let R : A → Lattice → Lattice → Ω → ℝ := fun a x y s =>
    S (fun k => u a (k, x.2) 0 s) x.1 y.1 +
      S (fun k => u a (y.1, k) 1 s) x.2 y.2
  change ∀ a x y, Integrable (R a x y) P
  intro a x y
  have hHorizontal : Integrable
      (fun s : Ω => ∑ k ∈ Finset.Ico x.1 y.1, u a (k, x.2) 0 s) P :=
    integrable_finsetSum _ fun k _ => hInt a (k, x.2) 0
  have hVertical : Integrable
      (fun s : Ω => ∑ k ∈ Finset.Ico x.2 y.2, u a (y.1, k) 1 s) P :=
    integrable_finsetSum _ fun k _ => hInt a (y.1, k) 1
  have hHorizontalReverse : Integrable
      (fun s : Ω => ∑ k ∈ Finset.Ico y.1 x.1, u a (k, x.2) 0 s) P :=
    integrable_finsetSum _ fun k _ => hInt a (k, x.2) 0
  have hVerticalReverse : Integrable
      (fun s : Ω => ∑ k ∈ Finset.Ico y.2 x.2, u a (y.1, k) 1 s) P :=
    integrable_finsetSum _ fun k _ => hInt a (y.1, k) 1
  have hHorizontalSigned :
      Integrable (fun s : Ω => S (fun k => u a (k, x.2) 0 s) x.1 y.1) P := by
    by_cases hxy : x.1 ≤ y.1
    · simpa [S, hxy] using hHorizontal
    · simpa [S, hxy] using hHorizontalReverse.neg
  have hVerticalSigned :
      Integrable (fun s : Ω => S (fun k => u a (y.1, k) 1 s) x.2 y.2) P := by
    by_cases hxy : x.2 ≤ y.2
    · simpa [S, hxy] using hVertical
    · simpa [S, hxy] using hVerticalReverse.neg
  change Integrable (fun s =>
    S (fun k => u a (k, x.2) 0 s) x.1 y.1 +
      S (fun k => u a (y.1, k) 1 s) x.2 y.2) P
  exact hHorizontalSigned.add hVerticalSigned

/-- Each outgoing unit path sum equals its actual edge value pointwise. -/
theorem lattice_coordinate_path_sum_unit_values
    {A Ω : Type*} (u : A → Lattice → Fin 2 → Ω → ℝ) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
      else -(∑ k ∈ Finset.Ico b a, f k)
    let R : A → Lattice → Lattice → Ω → ℝ := fun a x y s =>
      S (fun k => u a (k, x.2) 0 s) x.1 y.1 +
        S (fun k => u a (y.1, k) 1 s) x.2 y.2
    ∀ a x s, R a x (x + (1, 0)) s = u a x 0 s ∧
      R a x (x + (0, 1)) s = u a x 1 s := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let R : A → Lattice → Lattice → Ω → ℝ := fun a x y s =>
    S (fun k => u a (k, x.2) 0 s) x.1 y.1 +
      S (fun k => u a (y.1, k) 1 s) x.2 y.2
  change ∀ a x s, R a x (x + (1, 0)) s = u a x 0 s ∧
    R a x (x + (0, 1)) s = u a x 1 s
  intro a x s
  have hIcoSucc (b : ℤ) : Finset.Ico b (b + 1) = {b} := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  constructor <;> simp [R, S, hIcoSucc]

end LPPDifferentiability
