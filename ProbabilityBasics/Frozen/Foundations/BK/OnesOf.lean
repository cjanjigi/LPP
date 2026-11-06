module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace ProbabilityBasics.BK

variable {n : ℕ}

/-- `K(ω)`: the coordinates where `ω` equals `1` (here `true`). -/
def onesOf (ω : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ω i = true

end ProbabilityBasics.BK
