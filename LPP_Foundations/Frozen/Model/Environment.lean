module

public import LPP_Foundations.Frozen.Model.Lattice

@[expose] public section

namespace LPPDifferentiability

/-- Real site weights, with no boundedness or sign restriction. -/
abbrev Environment := Lattice → ℝ

end LPPDifferentiability
