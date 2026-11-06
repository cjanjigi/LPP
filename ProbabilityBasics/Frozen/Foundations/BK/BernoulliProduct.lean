module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Topology.UnitInterval

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics.BK

variable {n : ℕ}

/-- Independent coordinates with `P[ω_i = 1] = p i`. -/
noncomputable def bernoulliProduct (p : Fin n → unitInterval) : Measure (Fin n → Bool) :=
  Measure.pi fun i => bernoulliMeasure true false (p i)

end ProbabilityBasics.BK
