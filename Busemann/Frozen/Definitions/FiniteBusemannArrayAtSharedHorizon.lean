-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge
public import LPP_Foundations.Frozen.Model.Environment

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Every coordinate uses the same one-based horizon selected by the single Fin input. -/
noncomputable def finiteBusemannArrayAtSharedHorizon (n : ℕ)
    (h : ℕ → ℝ × ℝ) (p : Environment × Fin (n + 1)) :
    ℕ → Lattice → Fin 2 → ℝ :=
  fun j x i => finiteBusemannEdge p.1 (h j) x ((p.2.val + 1 : ℕ) : ℤ) i

end LPP.Busemann
