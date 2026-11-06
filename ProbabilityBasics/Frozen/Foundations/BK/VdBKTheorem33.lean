-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ProbabilityBasics.Full.Foundations.VdBKTheorem33
public import ProbabilityBasics.Frozen.Foundations.BK.VdBKDisjointOccurrence
public import ProbabilityBasics.Frozen.Foundations.BK.BernoulliProduct
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Topology.UnitInterval

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.BK

variable {n : ℕ}

/-- **van den Berg–Kesten (1985), Theorem 3.3.** If `A` and `B` are
increasing events in `{0,1}ⁿ`, then (3.4) `P[A ∘ B] ≤ P[A] P[B]`. -/
theorem vdBK_theorem_3_3 (p : Fin n → unitInterval) {A B : Set (Fin n → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    bernoulliProduct p (vdBKDisjointOccurrence A B) ≤
      bernoulliProduct p A * bernoulliProduct p B :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact ProbabilityBasics.Full.vdBK_theorem_3_3 p hA hB
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ProbabilityBasics.BK
-- FROZEN_ANCHOR_SUFFIX_END
