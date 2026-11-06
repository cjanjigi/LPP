module

public import ProbabilityBasics.Frozen.Foundations.Liggett.SeqShift
public import Mathlib.Dynamics.Ergodic.Ergodic

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics

variable {Ω : Type*} [MeasurableSpace Ω] {β : Type*} [MeasurableSpace β]

/-- A process is ergodic when the left shift is ergodic for its joint law. -/
def IsErgodicProcess (μ : Measure Ω) (Y : ℕ → Ω → β) : Prop :=
  Ergodic (seqShift (β := β)) (μ.map fun ω n => Y n ω)

end ProbabilityBasics
