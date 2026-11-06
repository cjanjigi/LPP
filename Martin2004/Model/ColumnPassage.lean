/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-!
# The one-site-per-column passage time

This module defines `columnPassage`, the passage time `T̃(m, n)` of Martin (2004),
from the proof of Lemma 4.1.
A path picks one site in each column `0, ..., m - 1`, at heights that do not decrease and stay
between `0` and `n`. The value is the largest total weight of such a path.

The module also proves the basic facts used later: unfolding, bounds over the paths, attainment,
monotonicity, measurability and integrability.
-/

open MeasureTheory

namespace LPPDifferentiability

/-- The one-site-per-column passage time `T̃(m, n)` of Martin (2004), in the proof of
Lemma 4.1. A path chooses one site in each column `0, 1, ..., m - 1`, at heights
`y 0 ≤ y 1 ≤ ... ≤ y (m - 1)` between `0` and `n`; `T̃(m, n)` is the largest total weight
of the chosen sites. With zero-one weights this is the count `L((0,0),(m,n))` of marked
horizontal edges in Seppäläinen (1998), equation (3.1), with the weight of site `(i, y)`
read as the mark of the edge from `(i, y)` to `(i + 1, y)`. -/
noncomputable def columnPassage (ω : Environment) (m n : ℕ) : ℝ :=
  ⨆ y : {y : Fin m → Fin (n + 1) // Monotone y},
    ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y.1 i : ℕ) : ℤ))

/-- The family of one-site-per-column paths is nonempty: the constant height `0` is admissible. -/
private instance nonempty_monotoneHeights (m n : ℕ) :
    Nonempty {y : Fin m → Fin (n + 1) // Monotone y} :=
  ⟨⟨fun _ => 0, fun _ _ _ => le_rfl⟩⟩

/-- Unfolding lemma for `columnPassage`: the value is the supremum, over the admissible
heights, of the total weight of the chosen sites. Martin (2004), proof of Lemma 4.1. -/
theorem columnPassage_def (ω : Environment) (m n : ℕ) :
    columnPassage ω m n = ⨆ y : {y : Fin m → Fin (n + 1) // Monotone y},
      ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y.1 i : ℕ) : ℤ)) :=
  rfl

/-- Every one-site-per-column path has total weight at most `T̃(m, n)`. Martin (2004),
proof of Lemma 4.1: the passage time is a maximum over these paths. -/
theorem sum_le_columnPassage (ω : Environment) {m n : ℕ} (y : Fin m → Fin (n + 1))
    (hy : Monotone y) :
    ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y i : ℕ) : ℤ)) ≤ columnPassage ω m n := by
  rw [columnPassage_def]
  exact le_ciSup (f := fun y' : {y' : Fin m → Fin (n + 1) // Monotone y'} =>
      ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y'.1 i : ℕ) : ℤ)))
    (Set.finite_range _).bddAbove ⟨y, hy⟩

/-- `T̃(m, n)` is attained by some one-site-per-column path. The family of paths is finite and
nonempty (the constant path at height `0` is admissible), so the maximum exists. Martin (2004),
proof of Lemma 4.1. -/
theorem exists_columnPassage_eq (ω : Environment) (m n : ℕ) :
    ∃ y : Fin m → Fin (n + 1), Monotone y ∧
      columnPassage ω m n = ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y i : ℕ) : ℤ)) := by
  obtain ⟨y, hy⟩ := exists_eq_ciSup_of_finite
    (f := fun y' : {y' : Fin m → Fin (n + 1) // Monotone y'} =>
      ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y'.1 i : ℕ) : ℤ)))
  exact ⟨y.1, y.2, by rw [columnPassage_def]; exact hy.symm⟩

/-- A common upper bound for the total weight of every one-site-per-column path bounds
`T̃(m, n)`. Martin (2004), proof of Lemma 4.1. -/
theorem columnPassage_le_of_forall {ω : Environment} {m n : ℕ} {c : ℝ}
    (h : ∀ y : Fin m → Fin (n + 1), Monotone y →
      ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y i : ℕ) : ℤ)) ≤ c) :
    columnPassage ω m n ≤ c := by
  rw [columnPassage_def]
  exact ciSup_le fun y => h y.1 y.2

/-- With no columns the passage time is the empty sum, which is `0`. Martin (2004),
proof of Lemma 4.1: the only path with `m = 0` has no sites. -/
theorem columnPassage_zero_left (ω : Environment) (n : ℕ) : columnPassage ω 0 n = 0 := by
  rw [columnPassage_def]
  simp

/-- `T̃(m, n)` reads only the sites in the box `[0, m) × [0, n]`, and it is monotone in those
weights. Martin (2004), proof of Lemma 4.1: every chosen site lies in this box. -/
theorem columnPassage_le_of_leOn {ω ω' : Environment} {m n : ℕ}
    (h : ∀ i j : ℕ, i < m → j ≤ n → ω ((i : ℤ), (j : ℤ)) ≤ ω' ((i : ℤ), (j : ℤ))) :
    columnPassage ω m n ≤ columnPassage ω' m n := by
  refine columnPassage_le_of_forall fun y hy => ?_
  refine le_trans (Finset.sum_le_sum fun i _ =>
    h (i : ℕ) (y i : ℕ) i.isLt (Nat.le_of_lt_succ (y i).isLt)) ?_
  exact sum_le_columnPassage ω' y hy

/-- `T̃(m, n)` is a measurable function of the environment. This is not a step of Martin's argument:
it is needed so that the expectation `E T̃(m, n)` in Martin (2004), equation (4.1), makes
sense. -/
theorem measurable_columnPassage (m n : ℕ) :
    Measurable (fun ω : Environment => columnPassage ω m n) := by
  simp only [columnPassage_def]
  refine Measurable.iSup fun y => ?_
  show Measurable fun ω : Environment => ∑ i : Fin m, ω (((i : ℕ) : ℤ), ((y.1 i : ℕ) : ℤ))
  fun_prop

/-- If the one-site weight has a finite mean, then `T̃(m, n)` is integrable under the product law.
This is not a step of Martin's argument: it is needed for the expectation in Martin (2004),
equation (4.1). The bound is the sum of the absolute values of the weights in the box. -/
theorem integrable_columnPassage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (m n : ℕ) :
    Integrable (fun ω : Environment => columnPassage ω m n) (environmentLaw μ) := by
  have hcoord : ∀ z : Lattice, Integrable (fun ω : Environment => |ω z|) (environmentLaw μ) := by
    intro z
    have hf : Measurable fun ω : Environment => ω z := measurable_pi_apply z
    have hg : Integrable (fun t : ℝ => |t|)
        (Measure.map (fun ω : Environment => ω z) (environmentLaw μ)) := by
      rw [environmentLaw, Measure.infinitePi_map_eval]
      exact hμ.abs
    exact (integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable).mp hg
  refine Integrable.mono'
    (g := fun ω : Environment =>
      ∑ i : Fin m, ∑ j ∈ Finset.range (n + 1), |ω (((i : ℕ) : ℤ), (j : ℤ))|)
    (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hcoord (((i : ℕ) : ℤ), (j : ℤ)))
    (measurable_columnPassage m n).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  show ‖columnPassage ω m n‖ ≤
    ∑ i : Fin m, ∑ j ∈ Finset.range (n + 1), |ω (((i : ℕ) : ℤ), (j : ℤ))|
  obtain ⟨y, -, hy⟩ := exists_columnPassage_eq ω m n
  rw [Real.norm_eq_abs, hy]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j : ℕ => |ω (((i : ℕ) : ℤ), (j : ℤ))|)
    (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (y i).isLt)

end LPPDifferentiability
