/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Statements.ProbabilityDefinitions
public import ProbabilityBasics.Foundations.Concentration.MaxOfSums31

/-!
# Martin's concentration lemma for the maximum of set sums, in two versions

Lemma 3.1 of Martin (2004) bounds the deviation of the maximum of sums of bounded independent random
variables over a family of index sets. It is proved in the library by the entropy method, as
`ProbabilityBasics.Concentration.martin_lemma_3_1`.

* Version A, `literal_concentration_of_max_of_sums`: the statement of `martin_lemma_3_1`, verbatim,
  as a universally quantified proposition, with `literal_concentration_of_max_of_sums_holds` proved
  from that theorem.
* Version B, `plain_concentration_of_max_of_sums`: the same mathematics with the named definitions
  of `ProbabilityDefinitions.lean` (the maximum of set sums, the deviation event, the printed
  bound). The theorem `concentration_of_max_of_sums` states it and is proved from version A;
  `plain_concentration_of_max_of_sums_iff_literal` shows the versions are equivalent.

## References

* J. B. Martin, Limiting shape for directed percolation models, Ann. Probab. 32 (2004), Lemma 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace LPPStatements.Concentration

set_option linter.unusedVariables false in
/-- Version A of Martin (2004), Lemma 3.1: the statement of
`ProbabilityBasics.Concentration.martin_lemma_3_1`, verbatim. -/
def literal_concentration_of_max_of_sums.{u, v} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type v}
    [Fintype ι] (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P) (L : ℝ)
    (hL : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ L) (C : Finset (Finset ι)) (hC : C.Nonempty) (R : ℕ)
    (hR : ∀ c ∈ C, c.card ≤ R) (u : ℝ) (hu : 0 < u),
    P.real {ω | u ≤ |C.sup' hC (fun c => ∑ i ∈ c, Y i ω) -
        ∫ η, C.sup' hC (fun c => ∑ i ∈ c, Y i η) ∂P|} ≤
      Real.exp (64 - u ^ 2 / (64 * R * L ^ 2))

/-- Version A holds: it is `ProbabilityBasics.Concentration.martin_lemma_3_1`. -/
theorem literal_concentration_of_max_of_sums_holds.{u, v} : literal_concentration_of_max_of_sums.{u, v} := by
  unfold literal_concentration_of_max_of_sums
  intros
  apply ProbabilityBasics.Concentration.martin_lemma_3_1
  all_goals assumption

set_option linter.unusedVariables false in
/-- Version B of Martin (2004), Lemma 3.1: for independent measurable random variables `Y i`, `i` in
a finite index type, with `|Y i| ≤ L` almost surely, a nonempty family `C` of sets of at most `R`
indices and `Z` the maximum over `C` of the set sums,
`P (|Z - E Z| ≥ u) ≤ exp (64 - u² / (64 R L²))` for every `u > 0`. -/
def plain_concentration_of_max_of_sums.{u, v} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type v} [Fintype ι] (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (L : ℝ) (hL : IsAlmostSurelyBoundedBy P Y L) (C : Finset (Finset ι)) (hC : C.Nonempty)
    (R : ℕ) (hR : HasSetsOfSizeAtMost C R) (u : ℝ) (hu : 0 < u),
    P.real (deviationSet P (maxOfSetSums C hC Y) u) ≤ martinConcentrationBound R L u

/-- Version B is equivalent to version A. -/
theorem plain_concentration_of_max_of_sums_iff_literal.{u, v} :
    plain_concentration_of_max_of_sums.{u, v} ↔ literal_concentration_of_max_of_sums.{u, v} := by
  unfold plain_concentration_of_max_of_sums literal_concentration_of_max_of_sums
  exact Iff.rfl

/-- Martin (2004), Lemma 3.1.

Let `Y i`, `i` in a finite index type, be independent measurable real random variables with
`|Y i| ≤ L` almost surely. Let `C` be a nonempty family of subsets of the index type, each with at
most `R` elements, and let `Z` be the maximum over the sets `c` in `C` of the sums `∑ i ∈ c, Y i`.
Then for every `u > 0`, `P (|Z - E Z| ≥ u) ≤ exp (64 - u² / (64 R L²))`. (With Lean's division by
zero the bound is `exp 64 ≥ 1` when `R = 0` or `L = 0`.) -/
theorem concentration_of_max_of_sums {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) (L : ℝ) (hL : IsAlmostSurelyBoundedBy P Y L) (C : Finset (Finset ι))
    (hC : C.Nonempty) (R : ℕ) (hR : HasSetsOfSizeAtMost C R) (u : ℝ) (hu : 0 < u) :
    P.real (deviationSet P (maxOfSetSums C hC Y) u) ≤ martinConcentrationBound R L u :=
  literal_concentration_of_max_of_sums_holds P Y hY hind L hL C hC R hR u hu

end LPPStatements.Concentration

/-- Label: Martin (2004), Lemma 3.1. -/
alias Martin2004.lemma_3_1 := LPPStatements.Concentration.concentration_of_max_of_sums
