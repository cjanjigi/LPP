module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Path
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Collect every vertex except the terminal vertex. -/
noncomputable def pathWeight (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) : ℝ := ∑ i : Fin (d.1 + d.2), ω (p.vertex i.castSucc)

end LPPDifferentiability
