/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import Mathlib.Probability.Independence.Basic

/-!
# Weights at levels at most `m`

This file gives the shared definition of the sigma-algebra `levelsAtMost m`: the
information carried by the weights at all sites of level at most `m`. The
independence argument in the flat-segment case conditions on this information. The
definition is not stated in Section 2.3 of the differentiability preprint, which uses the
weights only through the shifted law and the top field.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The weights at levels at most `m`: the smallest sigma-algebra on environments
that makes every weight `ω z` measurable for each site `z` on a level at most `m`.
Here a level is a coordinate sum, as in `levelSet`. -/
@[instance_reducible] def levelsAtMost (m : ℤ) : MeasurableSpace Environment :=
  ⨆ (z : Lattice) (_ : z.1 + z.2 ≤ m),
    MeasurableSpace.comap (fun ω : Environment => ω z) inferInstance

end LPPDifferentiability
