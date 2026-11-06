/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Statements.ProbabilityDefinitions
public import ProbabilityBasics.Frozen.Foundations.BK.BKInequality
public import ProbabilityBasics.Frozen.Foundations.BK.BKInequalityFamily
public import ProbabilityBasics.Frozen.Foundations.BK.BKInequalityInfinitePi
public import ProbabilityBasics.Frozen.Foundations.BK.BKInequalityFamilyInfinitePi
public import ProbabilityBasics.Frozen.Foundations.BK.VdBKTheorem33
public import Mathlib.Probability.ProductMeasure

/-!
# The BK inequality, in two versions

Theorem 3.3 of van den Berg and Kesten (1985) says that, for two increasing events, the probability
that they occur disjointly is at most the product of their probabilities. This file states it for
increasing events on `{0,1}^n` and its extensions to finite and countable products of ordered spaces
and to finite families of events (the extensions to families follow the proof of Corollary 3.10).

For each of the five BK inequalities of the library there are two statements, both type checked:

* version A, `literal_X`: the corresponding library proposition, copied verbatim as a universally
  quantified proposition, with `literal_X_holds` proved from that proposition;
* version B, `plain_X`: the same mathematics with the named definitions of
  `ProbabilityDefinitions.lean`; the theorem with the descriptive name states it and is proved from
  version A; `plain_X_iff_literal` shows the two versions are equivalent.

## Main results

* `bk_inequality`: two increasing events, finitely many coordinates.
* `bk_inequality_family`: a finite family of increasing events, finitely many coordinates.
* `bk_inequality_countable`: two increasing events, countably many coordinates.
* `bk_inequality_family_countable`: a finite family of increasing events, countably many
  coordinates.
* `bk_inequality_bernoulli_cube`: van den Berg and Kesten (1985), Theorem 3.3, for two increasing
  events on `{0,1}^n` with independent Bernoulli coordinates (the theorem
  `ProbabilityBasics.BK.vdBK_theorem_3_3` of the `Frozen` folder).

## References

* J. van den Berg and H. Kesten, Inequalities with applications to percolation and reliability,
  J. Appl. Probab. 22 (1985), Theorem 3.3 and Corollary 3.10.
-/

@[expose] public section

open MeasureTheory ProbabilityBasics.BK

namespace LPPStatements.BK

/-! ### Two events, finitely many coordinates -/

set_option linter.unusedVariables false in
/-- Version A of the BK inequality for two events and finitely many coordinates: the statement
`ProbabilityBasics.BK.bk_inequality` of the `Frozen` folder, verbatim. -/
def literal_bk_inequality.{u, v} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v} [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, OrderTopology (E i)]
    [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] [Fintype ι] {A B : Set (∀ i, E i)} (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B),
    Measure.pi μ (boxOccurrence A B) ≤ Measure.pi μ A * Measure.pi μ B

/-- Version A holds: it is `ProbabilityBasics.BK.bk_inequality`. -/
theorem literal_bk_inequality_holds.{u, v} : literal_bk_inequality.{u, v} := by
  unfold literal_bk_inequality
  intros
  apply ProbabilityBasics.BK.bk_inequality
  all_goals assumption

set_option linter.unusedVariables false in
/-- Version B of the BK inequality for two events and finitely many coordinates: for increasing
events `A` and `B` on a finite product of totally ordered probability spaces, the probability that
`A` and `B` occur disjointly is at most `P[A] P[B]`. -/
def plain_bk_inequality.{u, v} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Fintype ι] {A B : Set (∀ i, E i)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B),
    SatisfiesBKInequality (Measure.pi μ) A B

/-- Version B is equivalent to version A. -/
theorem plain_bk_inequality_iff_literal.{u, v} :
    plain_bk_inequality.{u, v} ↔ literal_bk_inequality.{u, v} := by
  unfold plain_bk_inequality literal_bk_inequality
  constructor
  · intro h ι E _ _ _ _ _ _ μ _ _ A B hAm hBm hA hB
    exact h μ ⟨hAm, hA⟩ ⟨hBm, hB⟩
  · intro h ι E _ _ _ _ _ _ μ _ _ A B hA hB
    exact h μ hA.1 hB.1 hA.2 hB.2

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, from {0,1}^n to finite products of ordered spaces.

For two increasing events `A` and `B` on a finite product of totally ordered spaces `E i`, each with
a second countable order topology, its Borel σ-algebra and an arbitrary probability measure `μ i`,
the product measure of the disjoint occurrence of `A` and `B` is at most the product of their
measures. Theorem 3.3 of the paper proves the positive-event inequality for independent
Bernoulli coordinates on `{0,1}^n`. The finite ordered-space statement formalized here extends
that result, using the box operation of Remark 3.5 (d) (disjoint finite sets of coordinates
witness `A` and `B`). -/
theorem bk_inequality {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Fintype ι] {A B : Set (∀ i, E i)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    SatisfiesBKInequality (Measure.pi μ) A B :=
  literal_bk_inequality_holds μ hA.1 hB.1 hA.2 hB.2

/-! ### A finite family of events, finitely many coordinates -/

set_option linter.unusedVariables false in
/-- Version A of the BK inequality for a finite family of events and finitely many coordinates: the
statement `ProbabilityBasics.BK.bk_inequality_family` of the `Frozen` folder, verbatim. -/
def literal_bk_inequality_family.{u, v, w} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v} [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, OrderTopology (E i)]
    [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] [Fintype ι] {J : Type w} [Fintype J]
    {A : J → Set (∀ i, E i)} (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j)),
    Measure.pi μ (disjointOccurrence A) ≤ ∏ j, Measure.pi μ (A j)

/-- Version A holds: it is `ProbabilityBasics.BK.bk_inequality_family`. -/
theorem literal_bk_inequality_family_holds.{u, v, w} : literal_bk_inequality_family.{u, v, w} := by
  unfold literal_bk_inequality_family
  intros
  apply ProbabilityBasics.BK.bk_inequality_family
  all_goals assumption

set_option linter.unusedVariables false in
/-- Version B of the BK inequality for a finite family of events and finitely many coordinates. -/
def plain_bk_inequality_family.{u, v, w} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Fintype ι] {J : Type w} [Fintype J] {A : J → Set (∀ i, E i)}
    (hA : ∀ j, IsIncreasingEvent (A j)),
    SatisfiesBKFamilyInequality (Measure.pi μ) A

/-- Version B is equivalent to version A. -/
theorem plain_bk_inequality_family_iff_literal.{u, v, w} :
    plain_bk_inequality_family.{u, v, w} ↔ literal_bk_inequality_family.{u, v, w} := by
  unfold plain_bk_inequality_family literal_bk_inequality_family
  constructor
  · intro h ι E _ _ _ _ _ _ μ _ _ J _ A hAm hA
    exact h μ (fun j => ⟨hAm j, hA j⟩)
  · intro h ι E _ _ _ _ _ _ μ _ _ J _ A hA
    exact h μ (fun j => (hA j).1) (fun j => (hA j).2)

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, to a finite family of events on finite products of ordered spaces.

For a finite family of increasing events `A j`, `j` in a finite index type, on a finite product of
totally ordered spaces with arbitrary probability measures, the product measure of the disjoint
occurrence of all the `A j` is at most the product of their measures. In the paper this is the
inequality that the probability of the disjoint occurrence of `E_1, ..., E_k` is at most
`P[E_1] ... P[E_k]`, obtained from Theorem 3.3 by induction over the family in the proof of
Corollary 3.10. -/
theorem bk_inequality_family {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Fintype ι] {J : Type*} [Fintype J] {A : J → Set (∀ i, E i)}
    (hA : ∀ j, IsIncreasingEvent (A j)) :
    SatisfiesBKFamilyInequality (Measure.pi μ) A :=
  literal_bk_inequality_family_holds μ (fun j => (hA j).1) (fun j => (hA j).2)

/-! ### Two events, countably many coordinates -/

set_option linter.unusedVariables false in
/-- Version A of the BK inequality for two events and countably many coordinates: the statement
`ProbabilityBasics.BK.bk_inequality_infinitePi` of the `Frozen` folder, verbatim. -/
def literal_bk_inequality_countable.{u, v} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v} [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, OrderTopology (E i)]
    [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] [Countable ι] {A B : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B),
    Measure.infinitePi μ (boxOccurrence A B) ≤
      Measure.infinitePi μ A * Measure.infinitePi μ B

/-- Version A holds: it is `ProbabilityBasics.BK.bk_inequality_infinitePi`. -/
theorem literal_bk_inequality_countable_holds.{u, v} : literal_bk_inequality_countable.{u, v} := by
  unfold literal_bk_inequality_countable
  intros
  apply ProbabilityBasics.BK.bk_inequality_infinitePi
  all_goals assumption

set_option linter.unusedVariables false in
/-- Version B of the BK inequality for two events and countably many coordinates. -/
def plain_bk_inequality_countable.{u, v} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Countable ι] {A B : Set (∀ i, E i)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B),
    SatisfiesBKInequality (Measure.infinitePi μ) A B

/-- Version B is equivalent to version A. -/
theorem plain_bk_inequality_countable_iff_literal.{u, v} :
    plain_bk_inequality_countable.{u, v} ↔ literal_bk_inequality_countable.{u, v} := by
  unfold plain_bk_inequality_countable literal_bk_inequality_countable
  constructor
  · intro h ι E _ _ _ _ _ _ μ _ _ A B hAm hBm hA hB
    exact h μ ⟨hAm, hA⟩ ⟨hBm, hB⟩
  · intro h ι E _ _ _ _ _ _ μ _ _ A B hA hB
    exact h μ hA.1 hB.1 hA.2 hB.2

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, to countable products of ordered spaces.

For two increasing events `A` and `B` on a countable product of totally ordered spaces with
arbitrary probability measures, the infinite product measure of the disjoint occurrence of `A` and
`B` is at most the product of their measures. When the disjoint occurrence is not measurable, the
left side is the outer measure. The paper proves Theorem 3.3 for finitely many Bernoulli coordinates
and reduces infinite graphs to finite ones in the proof of Corollary 3.10 only by "obvious limit
arguments". -/
theorem bk_inequality_countable {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Countable ι] {A B : Set (∀ i, E i)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    SatisfiesBKInequality (Measure.infinitePi μ) A B :=
  literal_bk_inequality_countable_holds μ hA.1 hB.1 hA.2 hB.2

/-! ### A finite family of events, countably many coordinates -/

set_option linter.unusedVariables false in
/-- Version A of the BK inequality for a finite family of events and countably many coordinates: the
statement `ProbabilityBasics.BK.bk_inequality_family_infinitePi` of the `Frozen` folder,
verbatim. -/
def literal_bk_inequality_family_countable.{u, v, w} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v} [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, OrderTopology (E i)]
    [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] [Countable ι] {J : Type w} [Fintype J]
    {A : J → Set (∀ i, E i)} (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j)),
    Measure.infinitePi μ (disjointOccurrence A) ≤ ∏ j, Measure.infinitePi μ (A j)

/-- Version A holds: it is `ProbabilityBasics.BK.bk_inequality_family_infinitePi`. -/
theorem literal_bk_inequality_family_countable_holds.{u, v, w} :
    literal_bk_inequality_family_countable.{u, v, w} := by
  unfold literal_bk_inequality_family_countable
  intros
  apply ProbabilityBasics.BK.bk_inequality_family_infinitePi
  all_goals assumption

set_option linter.unusedVariables false in
/-- Version B of the BK inequality for a finite family of events and countably many coordinates. -/
def plain_bk_inequality_family_countable.{u, v, w} : Prop :=
  ∀ {ι : Type u} {E : ι → Type v}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Countable ι] {J : Type w} [Fintype J] {A : J → Set (∀ i, E i)}
    (hA : ∀ j, IsIncreasingEvent (A j)),
    SatisfiesBKFamilyInequality (Measure.infinitePi μ) A

/-- Version B is equivalent to version A. -/
theorem plain_bk_inequality_family_countable_iff_literal.{u, v, w} :
    plain_bk_inequality_family_countable.{u, v, w} ↔
      literal_bk_inequality_family_countable.{u, v, w} := by
  unfold plain_bk_inequality_family_countable literal_bk_inequality_family_countable
  constructor
  · intro h ι E _ _ _ _ _ _ μ _ _ J _ A hAm hA
    exact h μ (fun j => ⟨hAm j, hA j⟩)
  · intro h ι E _ _ _ _ _ _ μ _ _ J _ A hA
    exact h μ (fun j => (hA j).1) (fun j => (hA j).2)

/-- Extends van den Berg and Kesten (1985), Theorem 3.3, to a finite family of events on countable products of ordered spaces.

For a finite family of increasing events `A j`, `j` in a finite index type, on a countable product
of totally ordered spaces with arbitrary probability measures, the infinite product measure of the
disjoint occurrence of all the `A j` is at most the product of their measures. When the disjoint
occurrence is not measurable, the left side is the outer measure. -/
theorem bk_inequality_family_countable {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    [Countable ι] {J : Type*} [Fintype J] {A : J → Set (∀ i, E i)}
    (hA : ∀ j, IsIncreasingEvent (A j)) :
    SatisfiesBKFamilyInequality (Measure.infinitePi μ) A :=
  literal_bk_inequality_family_countable_holds μ (fun j => (hA j).1) (fun j => (hA j).2)

/-! ### Bernoulli cube: two increasing events on `{0,1}^n` -/

/-- Version A of van den Berg and Kesten's inequality on `{0,1}^n`: the statement
`ProbabilityBasics.BK.vdBK_theorem_3_3` of the `Frozen` folder, verbatim, with the variable binders
made universal. -/
def literal_vdBK_theorem_3_3 : Prop :=
  ∀ {n : ℕ} (p : Fin n → unitInterval) {A B : Set (Fin n → Bool)} (_hA : IsUpperSet A)
    (_hB : IsUpperSet B),
    bernoulliProduct p (vdBKDisjointOccurrence A B) ≤ bernoulliProduct p A * bernoulliProduct p B

/-- Version A holds: it is `ProbabilityBasics.BK.vdBK_theorem_3_3`. -/
theorem literal_vdBK_theorem_3_3_holds : literal_vdBK_theorem_3_3 := by
  unfold literal_vdBK_theorem_3_3
  intro n p A B hA hB
  exact ProbabilityBasics.BK.vdBK_theorem_3_3 p hA hB

/-- Version B of van den Berg and Kesten's inequality on `{0,1}^n`: for increasing events `A` and
`B` and the Bernoulli product measure with parameters `p`, the probability that `A` and `B` occur
disjointly is at most `P[A] P[B]`. -/
def plain_vdBK_theorem_3_3 : Prop :=
  ∀ {n : ℕ} (p : Fin n → unitInterval) {A B : Set (Fin n → Bool)},
    IsIncreasingBoolEvent A → IsIncreasingBoolEvent B → SatisfiesVdBKInequality p A B

/-- Version B is equivalent to version A. -/
theorem plain_vdBK_theorem_3_3_iff_literal :
    plain_vdBK_theorem_3_3 ↔ literal_vdBK_theorem_3_3 := by
  unfold plain_vdBK_theorem_3_3 literal_vdBK_theorem_3_3
  constructor
  · intro h n p A B hA hB
    exact h p hA hB
  · intro h n p A B hA hB
    exact h p hA hB

/-- van den Berg and Kesten (1985), Theorem 3.3.

For two increasing events `A` and `B` in `{0,1}^n`, with independent Bernoulli coordinates
`P[ω_i = 1] = p i`, the probability that `A` and `B` occur disjointly is at most `P[A] P[B]`:
inequality (3.4) of the paper, with disjoint occurrence as defined on page 562. -/
theorem bk_inequality_bernoulli_cube {n : ℕ} (p : Fin n → unitInterval) {A B : Set (Fin n → Bool)}
    (hA : IsIncreasingBoolEvent A) (hB : IsIncreasingBoolEvent B) :
    SatisfiesVdBKInequality p A B :=
  literal_vdBK_theorem_3_3_holds p hA hB

end LPPStatements.BK

/-! ### Labels -/

/-- Label: extends van den Berg and Kesten (1985), Theorem 3.3, to finitely many coordinates in totally
ordered spaces. -/
alias VanDenBergKesten1985.theorem_3_3_ordered_spaces := LPPStatements.BK.bk_inequality

/-- Label: extends van den Berg and Kesten (1985), Theorem 3.3 (repeated, as for Corollary 3.10), to a finite
family of events on finitely many coordinates in totally ordered spaces. -/
alias VanDenBergKesten1985.theorem_3_3_family_ordered_spaces :=
  LPPStatements.BK.bk_inequality_family

/-- Label: extends van den Berg and Kesten (1985), Theorem 3.3, to countably many coordinates in totally
ordered spaces. -/
alias VanDenBergKesten1985.theorem_3_3_countable_ordered_spaces :=
  LPPStatements.BK.bk_inequality_countable

/-- Label: extends van den Berg and Kesten (1985), Theorem 3.3 (repeated, as for Corollary 3.10), to a finite
family of events on countably many coordinates in totally ordered spaces. -/
alias VanDenBergKesten1985.theorem_3_3_family_countable_ordered_spaces :=
  LPPStatements.BK.bk_inequality_family_countable

/-- Label: van den Berg and Kesten (1985), Theorem 3.3, for two increasing events on `{0,1}^n` with independent
Bernoulli coordinates. -/
alias VanDenBergKesten1985.theorem_3_3 := LPPStatements.BK.bk_inequality_bernoulli_cube
