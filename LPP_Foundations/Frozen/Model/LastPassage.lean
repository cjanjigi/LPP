module

public import LPP_Foundations.Frozen.Model.PathWeight
public import LPP_Foundations.Model.Paths.Fintype
public import LPP_Foundations.Model.Paths.Nonempty
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace LPPDifferentiability

/-- The maximum of all path weights from u to u + d; its family is proved finite and nonempty. -/
noncomputable def lastPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) : ℝ := by
  classical
  exact (Finset.univ.image (pathWeight ω : Path u d → ℝ)).max'
    (Finset.Nonempty.image (Finset.univ_nonempty) _)

end LPPDifferentiability
