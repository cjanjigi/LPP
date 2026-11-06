/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.BK.OnesOf
public import ProbabilityBasics.Frozen.Foundations.BK.ConfigOfOnes
public import ProbabilityBasics.Frozen.Foundations.BK.VdBKDisjointOccurrence
public import ProbabilityBasics.Frozen.Foundations.BK.BernoulliProduct
public import ProbabilityBasics.Foundations.BK.Theorem33

/-!
# The van den Berg-Kesten inequality for independent bits

The theorem here is the proof of the statement `ProbabilityBasics.BK.vdBK_theorem_3_3` in
`Frozen/Foundations/BK/VdBKTheorem33.lean`: for increasing events in `{0,1}ⁿ` under independent
bits, the probability of the disjoint occurrence is at most the product of the probabilities
(van den Berg and Kesten (1985), Theorem 3.3).
-/

@[expose] public section

open MeasureTheory ProbabilityBasics.BK

namespace ProbabilityBasics.Full

/-- Van den Berg and Kesten (1985), Theorem 3.3, for increasing events in `{0,1}ⁿ` under
independent bits. This is the proof of the statement `ProbabilityBasics.BK.vdBK_theorem_3_3` in
`Frozen/`, stated exactly as there. It follows from `ProbabilityBasics.BK.theorem_3_3`. -/
theorem vdBK_theorem_3_3 {n : ℕ} (p : Fin n → unitInterval) {A B : Set (Fin n → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    bernoulliProduct p (vdBKDisjointOccurrence A B) ≤
      bernoulliProduct p A * bernoulliProduct p B :=
  theorem_3_3 p hA hB

end ProbabilityBasics.Full
