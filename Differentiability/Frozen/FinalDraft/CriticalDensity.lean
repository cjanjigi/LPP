/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Frozen.FinalDraft.SiteSurvival
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Probability.Distributions.Bernoulli

/-! Critical density for survival of the origin cluster. -/

@[expose] public section

open ProbabilityTheory

namespace LPPDifferentiability.FinalDraft

/-- The critical density is the infimum of the Bernoulli site densities for
which the origin has a positive probability of an infinite open ray. -/
noncomputable def orientedSiteCriticalDensity : ℝ :=
  sInf {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧
    0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1)}

end LPPDifferentiability.FinalDraft
