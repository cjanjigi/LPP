/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.BK.AgreementCylinder
public import ProbabilityBasics.Frozen.Foundations.BK.IsWitnessSet
public import ProbabilityBasics.Frozen.Foundations.BK.DisjointOccurrence
public import ProbabilityBasics.Foundations.BK.Family

/-!
# The BK inequality for a finite family of events

The theorem here is the proof of the statement `ProbabilityBasics.BK.bk_inequality_family` in
`Frozen/Foundations/BK/BKInequalityFamily.lean`: for a finite family of increasing events in a
product of finitely many totally ordered probability spaces, the product measure of their disjoint
occurrence is at most the product of their measures. Theorem 3.3 of van den
Berg and Kesten (1985) treats two increasing events on finite independent
Bernoulli bits; this module extends it to finite event families on products
of finitely many totally ordered probability spaces.
-/

@[expose] public section

open MeasureTheory ProbabilityBasics.BK

namespace ProbabilityBasics.Full

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  {μ : ∀ i, Measure (E i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- The BK inequality for a finite family of increasing events and finitely many coordinates in
totally ordered spaces. This is the proof of the statement
`ProbabilityBasics.BK.bk_inequality_family` in `Frozen/`. It follows from
`ProbabilityBasics.BK.bk_inequality_family_pi`; the only difference from the statement in
`Frozen/` is that `μ` is implicit here, so that the proof in `Frozen/` can name exactly the
theorem's own explicit arguments. -/
theorem bk_inequality_family [Fintype ι] {J : Type*} [Fintype J]
    {A : J → Set (∀ i, E i)}
    (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j)) :
    Measure.pi μ (disjointOccurrence A) ≤ ∏ j, Measure.pi μ (A j) :=
  bk_inequality_family_pi μ hAm hA

end ProbabilityBasics.Full
