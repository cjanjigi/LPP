-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ProbabilityBasics.Full.Foundations.BKInequalityFamily
public import ProbabilityBasics.Frozen.Foundations.BK.DisjointOccurrence
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **BK inequality for a finite family, finitely many coordinates.** -/
theorem bk_inequality_family [Fintype ι] {J : Type*} [Fintype J]
    {A : J → Set (∀ i, E i)}
    (hAm : ∀ j, MeasurableSet (A j)) (hA : ∀ j, IsUpperSet (A j)) :
    Measure.pi μ (disjointOccurrence A) ≤ ∏ j, Measure.pi μ (A j) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact ProbabilityBasics.Full.bk_inequality_family hAm hA
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ProbabilityBasics.BK
-- FROZEN_ANCHOR_SUFFIX_END
