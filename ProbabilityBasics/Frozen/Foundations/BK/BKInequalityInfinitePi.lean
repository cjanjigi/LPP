-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ProbabilityBasics.Full.Foundations.BKInequalityInfinitePi
public import ProbabilityBasics.Frozen.Foundations.BK.BoxOccurrence
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **BK inequality, countably many coordinates.** The left side is the
outer measure when the disjoint-occurrence event is not measurable. -/
theorem bk_inequality_infinitePi [Countable ι] {A B : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.infinitePi μ (boxOccurrence A B) ≤
      Measure.infinitePi μ A * Measure.infinitePi μ B :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact ProbabilityBasics.Full.bk_inequality_infinitePi hAm hBm hA hB
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ProbabilityBasics.BK
-- FROZEN_ANCHOR_SUFFIX_END
