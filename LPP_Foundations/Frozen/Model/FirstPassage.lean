module

public import LPP_Foundations.Frozen.Model.PathWeight
public import LPP_Foundations.Model.Paths.Fintype
public import LPP_Foundations.Model.Paths.Nonempty
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace LPPDifferentiability

/-- PROPOSED NEW DEFINITION (author decision). The minimum of all path weights
from u to u + d, with the same terminal-excluded path weight and the same
finite nonempty path family as the frozen `lastPassage`. Source (2.9), line 238.
Reading: S(z), the first-passage time. -/
noncomputable def firstPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) : ℝ := by
  classical
  exact (Finset.univ.image (pathWeight ω : Path u d → ℝ)).min'
    (Finset.Nonempty.image (Finset.univ_nonempty) _)

end LPPDifferentiability
