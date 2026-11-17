/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RealQuantileExtension
public import Mathlib.MeasureTheory.Constructions.UnitInterval

import Busemann.Process.MeasurableRealQuantileFamily
import Busemann.Process.RealQuantileJointLaw

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- The published real quantile is jointly measurable and samples the actual
conditional rightmost-path law from one uniform interval parameter. -/
theorem exists_measurable_real_rightmost_quantile_sampler_with_law
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun a : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y a) u)
        processEnvironment P
    ∃ q : Lattice → Environment → unitInterval → (ℕ → Lattice),
      (∀ u : Lattice, Measurable
        (fun a : Environment × unitInterval => q u a.1 a.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) ∧
      (∀ u : Lattice,
        (((environmentLaw μ).prod (volume : Measure unitInterval)).map
          (fun a : Environment × unitInterval => (a.1, q u a.1 a.2))) =
        P.map (fun a : ProcessSample =>
          (processEnvironment a,
            rightmostCocyclePath (fun x y => B x y a) u))) := by
  obtain ⟨q, hqMeas, hqCDF⟩ :=
    exists_measurable_real_rightmost_quantile_family μ P hMarginal B hB
  refine ⟨q, hqMeas, hqCDF, ?_⟩
  exact real_rightmost_quantile_joint_law μ P hMarginal B hB q hqMeas hqCDF

end LPP.Busemann
