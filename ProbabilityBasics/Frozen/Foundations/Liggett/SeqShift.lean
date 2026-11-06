module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

@[expose] public section

namespace ProbabilityBasics

variable {β : Type*} [MeasurableSpace β]

/-- The left shift on sequences: `(seqShift x) n = x (n + 1)`. -/
def seqShift (x : ℕ → β) : ℕ → β := fun n => x (n + 1)

end ProbabilityBasics
