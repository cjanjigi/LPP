/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.BK.AgreementCylinder
public import ProbabilityBasics.Frozen.Foundations.BK.IsWitnessSet
public import ProbabilityBasics.Frozen.Foundations.BK.BoxOccurrence
public import ProbabilityBasics.Foundations.BK.Countable

/-!
# The BK inequality for countably many coordinates

The theorem here is the proof of the statement `ProbabilityBasics.BK.bk_inequality_infinitePi` in
`Frozen/Foundations/BK/BKInequalityInfinitePi.lean`: for two increasing events `A` and `B` in a
product of countably many totally ordered probability spaces, the infinite product measure of the
box occurrence of `A` and `B` is at most the product of their measures.
Theorem 3.3 of van den Berg and Kesten (1985) treats two increasing events on
finite independent Bernoulli bits; this module extends it to countably many
totally ordered probability spaces.
-/

@[expose] public section

open MeasureTheory ProbabilityBasics.BK

namespace ProbabilityBasics.Full

variable {ι : Type*} {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, LinearOrder (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, OrderTopology (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]
  {μ : ∀ i, Measure (E i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- The BK inequality for countably many coordinates in totally ordered spaces. This is the proof
of the statement `ProbabilityBasics.BK.bk_inequality_infinitePi` in `Frozen/`. It follows from
`ProbabilityBasics.BK.bk_inequality_infinitePi_impl`; the only difference from the statement in
`Frozen/` is that `μ` is implicit here, so that the proof in `Frozen/` can name exactly the
theorem's own explicit arguments. -/
theorem bk_inequality_infinitePi [Countable ι] {A B : Set (∀ i, E i)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.infinitePi μ (boxOccurrence A B) ≤
      Measure.infinitePi μ A * Measure.infinitePi μ B :=
  bk_inequality_infinitePi_impl μ hAm hBm hA hB

end ProbabilityBasics.Full
