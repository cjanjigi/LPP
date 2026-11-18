/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinWeakContinuity
public import LPP_Foundations.Statements.ShapeDefinitions

/-!
# Expected-rate shapes of an i.i.d. law

Martin (2004), Section 2: for a weight law `μ`, the expected last-passage time
`E T(0, ⌊n x⌋)`, divided by `n`, is the quantity whose limit defines the shape
function `g` in each direction `x` of the closed quadrant. `IsExpectedRateShape μ g`
says that `g` is such a limit, in every direction.

The module proves two routine facts. A law has at most one expected-rate shape,
because limits are unique. Any expected-rate shape of a law with a finite first
moment and the positive square-root tail is continuous on the closed quadrant,
and it equals the mean times `s` on the horizontal axis. Both facts come from the
existence and uniqueness theorem
`exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- The Martin shape modules use the common expected-rate shape predicate. -/
def IsExpectedRateShape (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  LPPStatements.IsExpectedRateShape μ g

/-- A law has at most one expected-rate shape. In each direction the two
candidates are limits of the same sequence, so they agree by uniqueness of limits
in the real line. -/
theorem isExpectedRateShape_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {g h : Quadrant → ℝ} (hg : IsExpectedRateShape μ g) (hh : IsExpectedRateShape μ h) :
    g = h := by
  funext x
  exact tendsto_nhds_unique (hg x) (hh x)

/-- Any expected-rate shape of a law with a finite first moment and the positive
square-root tail (2.6) is continuous on the whole closed quadrant, and on the
horizontal axis it equals the mean times `s`. Both conclusions follow from the
unique continuous expected-rate witness of the existence theorem,
because an expected-rate shape is that witness. -/
theorem isExpectedRateShape_continuous_and_axis_of_integrable_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.HasFiniteMean μ)
    (hpos : LPPStatements.HasSqrtUpperTail μ)
    {g : Quadrant → ℝ} (hg : IsExpectedRateShape μ g) :
    Continuous g ∧ ∀ s : ℝ≥0, g (s, 0) = (∫ t : ℝ, t ∂μ) * (s : ℝ) := by
  obtain ⟨h, hh, _⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      μ hμ hpos
  have hgh : g = h :=
    isExpectedRateShape_unique μ hg (show IsExpectedRateShape μ h from hh.1.1.1)
  rw [hgh]
  exact ⟨hh.2, fun s => hh.1.1.2.2.2.1 s⟩

end LPPDifferentiability
