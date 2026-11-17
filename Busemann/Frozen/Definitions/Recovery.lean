module

public import LPP_Foundations.Frozen.Model.Environment

@[expose] public section

namespace LPP.Busemann

/-- Pointwise zero-temperature recovery by the two outgoing edge increments. -/
def recovers_environment (ω : LPPDifferentiability.Environment) (B : LPPDifferentiability.Lattice → LPPDifferentiability.Lattice → ℝ) : Prop :=
  ∀ x : LPPDifferentiability.Lattice,
    min (B x (x + ((1 : ℤ), (0 : ℤ)))) (B x (x + ((0 : ℤ), (1 : ℤ)))) = ω x

end LPP.Busemann

