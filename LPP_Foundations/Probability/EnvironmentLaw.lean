/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw

/-!
# The canonical environment law is a probability measure

The i.i.d. product law of the site weights is a probability measure whenever the one-site law is.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- The canonical environment law is a probability measure. -/
instance instIsProbabilityMeasureEnvironmentLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (environmentLaw μ) := by
  unfold environmentLaw
  infer_instance

end LPPDifferentiability
