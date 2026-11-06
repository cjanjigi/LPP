/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Statements.Concentration

/-!
# Solution: Martin's concentration lemma for the maximum of set sums

Proves `LPPAudit.Concentration.concentration_of_max_of_sums` of the challenge file from the library. The
definitions and the statement are the same as in the challenge file, character for character.

The proof has two parts. First, for every definition, a theorem `<name>_eq` shows that it is the
library definition it copies (an equality, proved by `rfl`). These theorems state facts about definitions
only. Second, the main theorem follows from the library theorem
`LPPStatements.Concentration.concentration_of_max_of_sums`, which is proved from Martin’s concentration lemma.
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

/-! ### Each definition above is the library definition it copies -/

/-- The challenge definition agrees with the corresponding library definition. -/
theorem maxOfSetSums_eq {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (C : Finset (Finset ι))
    (hC : C.Nonempty) (Y : ι → Ω → ℝ) :
    maxOfSetSums C hC Y = LPPStatements.Concentration.maxOfSetSums C hC Y := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem IsAlmostSurelyBoundedBy_eq {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (P : Measure Ω)
    (Y : ι → Ω → ℝ) (L : ℝ) :
    IsAlmostSurelyBoundedBy P Y L = LPPStatements.Concentration.IsAlmostSurelyBoundedBy P Y L := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem HasSetsOfSizeAtMost_eq {ι : Type*} (C : Finset (Finset ι)) (R : ℕ) :
    HasSetsOfSizeAtMost C R = LPPStatements.Concentration.HasSetsOfSizeAtMost C R := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem deviationSet_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) (u : ℝ) :
    deviationSet P Z u = LPPStatements.Concentration.deviationSet P Z u := rfl

/-- The challenge definition agrees with the corresponding library definition. -/
theorem martinConcentrationBound_eq (R : ℕ) (L u : ℝ) :
    martinConcentrationBound R L u = LPPStatements.Concentration.martinConcentrationBound R L u := rfl

/-! ### The main theorem -/

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
    P.real (deviationSet P (maxOfSetSums C hC Y) u) ≤ martinConcentrationBound R L u :=
  LPPStatements.Concentration.concentration_of_max_of_sums P Y hY hind L hL C hC R hR u hu

end LPPAudit.Concentration
