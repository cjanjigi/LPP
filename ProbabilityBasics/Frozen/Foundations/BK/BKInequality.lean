-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ProbabilityBasics.Full.Foundations.BKInequality
public import ProbabilityBasics.Frozen.Foundations.BK.BoxOccurrence
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **BK inequality, finitely many coordinates.** -/
theorem bk_inequality [Fintype ι] {A B : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi μ (boxOccurrence A B) ≤ Measure.pi μ A * Measure.pi μ B :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact ProbabilityBasics.Full.bk_inequality hAm hBm hA hB
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ProbabilityBasics.BK
-- FROZEN_ANCHOR_SUFFIX_END
