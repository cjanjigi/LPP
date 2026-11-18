/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.NormNum

/-!
# Square-root distance between distribution functions

Martin (2004), Lemmas 4.2–4.6, use the integral of the square root of the absolute difference
between two distribution functions. The integral takes values in `ℝ≥0∞`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The square-root CDF distance of two laws in Martin (2004), Lemma 4.2. -/
noncomputable def sqrtCdfDistance (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (ENNReal.ofReal |μ.real (Iic x) - ν.real (Iic x)|) ^ (1 / 2 : ℝ)

/-- The same distance written with the real square root inside `ENNReal.ofReal`, as in
Martin (2004), Lemma 4.3. -/
theorem sqrtCdfDistance_eq_lintegral_ofReal_rpow (μ ν : Measure ℝ) :
    sqrtCdfDistance μ ν =
      ∫⁻ x : ℝ, ENNReal.ofReal (|(μ (Iic x)).toReal - (ν (Iic x)).toReal| ^ (1 / 2 : ℝ)) := by
  unfold sqrtCdfDistance
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), measureReal_def,
    measureReal_def]

end LPPDifferentiability
