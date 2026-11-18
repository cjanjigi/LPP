/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FutureVariables
public import Busemann.Frozen.Definitions.PastVariables
public import Mathlib.Probability.Independence.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability

namespace LPP.Busemann

/-- For every set of starting sites `I`, the weights in `I` and both cocycle
branches at every supporting tilt and all northeast pairs rooted in `I` are
jointly independent of the weights outside the union of the northeast cones
rooted in `I`. This is backward independence in Theorem 2.7(f) of the Strong
Existence manuscript, from Janjigian and Rassoul-Agha, arXiv:1810.03580v3,
Theorem 4.8(b) at zero temperature. -/
def HasBackwardIndependence (g : Quadrant → ℝ) (P : Measure ProcessSample)
    (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ) : Prop :=
  ∀ I : Set Lattice, IndepFun (futureVariables g I Bminus Bplus) (pastVariables I) P

end LPP.Busemann
