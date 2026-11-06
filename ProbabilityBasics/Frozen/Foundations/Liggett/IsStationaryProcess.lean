module

public import Mathlib.Probability.IdentDistrib

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics

variable {Ω : Type*} [MeasurableSpace Ω] {β : Type*} [MeasurableSpace β]

/-- A process `Y 0, Y 1, Y 2, ...` is stationary when the shifted process
`Y 1, Y 2, Y 3, ...` has the same joint law. Joint laws are laws on the
sequence space `ℕ → β` with its product σ-algebra. -/
def IsStationaryProcess (μ : Measure Ω) (Y : ℕ → Ω → β) : Prop :=
  IdentDistrib (fun ω n => Y (n + 1) ω) (fun ω n => Y n ω) μ μ

end ProbabilityBasics
