/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Challenge: Martin's concentration lemma for the maximum of set sums

This file states Martin (2004), Lemma 3.1, using only Mathlib. It contains the statement, with
its proof left open, and exactly the definitions the statement uses. The solution file proves the
same statement from the library.

## Main results

- `concentration_of_max_of_sums`: Martin (2004), Lemma 3.1.

## References

- J. B. Martin, "Limiting shape for directed percolation models", Ann. Probab. 32 (2004).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace LPPAudit.Concentration

/-- The maximum `Z` over the sets `c` in the nonempty family `C` of the sums `∑ i ∈ c, Y i`: the maximum of
set sums of Martin (2004), Lemma 3.1. -/
def maxOfSetSums {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (C : Finset (Finset ι)) (hC : C.Nonempty)
    (Y : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  C.sup' hC (fun c => ∑ i ∈ c, Y i ω)

/-- Every `Y i` is bounded by `L` in absolute value almost surely: the hypothesis `|Y_i| ≤ L` of
Martin (2004), Lemma 3.1. -/
def IsAlmostSurelyBoundedBy {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (P : Measure Ω) (Y : ι → Ω → ℝ)
    (L : ℝ) : Prop :=
  ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ L

/-- Every set of the family `C` has at most `R` elements: the size hypothesis of Martin (2004),
Lemma 3.1. -/
def HasSetsOfSizeAtMost {ι : Type*} (C : Finset (Finset ι)) (R : ℕ) : Prop :=
  ∀ c ∈ C, c.card ≤ R

/-- The deviation event `{|Z - E Z| ≥ u}` of the random variable `Z` under the measure `P`. -/
def deviationSet {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) (u : ℝ) : Set Ω :=
  {ω | u ≤ |Z ω - ∫ η, Z η ∂P|}

/-- The bound `exp (64 - u² / (64 R L²))` printed in Martin (2004), Lemma 3.1 (with Lean's convention that
division by zero is zero). -/
noncomputable def martinConcentrationBound (R : ℕ) (L u : ℝ) : ℝ :=
  Real.exp (64 - u ^ 2 / (64 * R * L ^ 2))

/-- Martin (2004), Lemma 3.1.

Let `Y i`, `i` in a finite index type, be independent measurable real random variables with `|Y i| ≤ L`
almost surely. Let `C` be a nonempty family of subsets of the index type, each with at most `R` elements, and
let `Z` be the maximum over the sets `c` in `C` of the sums `∑ i ∈ c, Y i`. Then for every `u > 0`,
`P (|Z - E Z| ≥ u) ≤ exp (64 - u² / (64 R L²))`. (With Lean's division by zero the bound is `exp 64 ≥ 1` when
`R = 0` or `L = 0`.) -/
theorem concentration_of_max_of_sums {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) (L : ℝ) (hL : IsAlmostSurelyBoundedBy P Y L) (C : Finset (Finset ι))
    (hC : C.Nonempty) (R : ℕ) (hR : HasSetsOfSizeAtMost C R) (u : ℝ) (hu : 0 < u) :
    P.real (deviationSet P (maxOfSetSums C hC Y) u) ≤ martinConcentrationBound R L u := by
  sorry

end LPPAudit.Concentration
