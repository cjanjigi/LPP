/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Model.Paths.Coalescence
public import LPP_Foundations.Probability.TranslationEquiv

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- A measurable system of locally rightmost geodesics on the i.i.d. weight
space. Each root's path is obtained almost surely by translating the path
from zero in the shifted environment, and every pair of paths coalesces
almost surely. -/
def IsShiftCovariantCoalescingGeodesicSystem
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (π : Lattice → Environment → (ℕ → Lattice)) : Prop :=
  (∀ u : Lattice, Measurable (π u)) ∧
    (∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      IsLocallyRightmostGeodesic ω u (π u ω)) ∧
    (∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      π u ω = (fun n : ℕ => π 0 (environmentTranslationEquiv u ω) n + u)) ∧
    (∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      paths_coalesce u v (π u ω) (π v ω))

end LPP.Busemann
