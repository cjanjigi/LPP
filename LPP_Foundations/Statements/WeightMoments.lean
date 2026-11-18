/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Absolute moments of the weight law

This condition requires a finite absolute moment of some order above a given threshold.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPStatements

/-- The absolute value of a weight has a finite moment of some order `q > p`. At `p = 2` this is
the moment assumption in Strong Existence, Section 2.1. -/
def HasAbsoluteMomentAbove (μ : Measure ℝ) (p : ℝ) : Prop :=
  ∃ q : ℝ, p < q ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ q) ∂μ) < ∞

/-- The absolute moment condition written as an explicit integral bound. -/
theorem hasAbsoluteMomentAbove_iff (μ : Measure ℝ) (p : ℝ) :
    HasAbsoluteMomentAbove μ p ↔
      ∃ q : ℝ, p < q ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ q) ∂μ) < ∞ :=
  Iff.rfl

end LPPStatements
