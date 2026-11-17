module

public import LPP_Foundations.Frozen.Model.Environment

@[expose] public section

namespace LPP.Busemann

/-- The pointwise additive identity for a real field on ordered lattice-site pairs. -/
def is_additive (B : LPPDifferentiability.Lattice → LPPDifferentiability.Lattice → ℝ) : Prop :=
  ∀ x y z : LPPDifferentiability.Lattice, B x y + B y z = B x z

end LPP.Busemann

