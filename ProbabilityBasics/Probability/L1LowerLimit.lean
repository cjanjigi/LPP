/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.Scheffe
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Integral convergence from a nonnegative lower limit

An extended-real lower limit controls the minima with a finite real constant.
Together with convergence of the means, the Scheffé minimum criterion gives
convergence in integral absolute error. No pointwise upper
bound or pointwise convergence of the original sequence is assumed.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- Capping a real sequence at a finite lower bound on its extended lower limit
produces an ordinary convergent real sequence. -/
theorem tendsto_min_const_of_le_liminf_ereal {c : ℕ → ℝ} {q : ℝ}
    (h : (q : EReal) ≤ liminf (fun n => (c n : EReal)) atTop) :
    Tendsto (fun n => min (c n) q) atTop (𝓝 q) := by
  apply tendsto_order.mpr
  constructor
  · intro a haq
    have ha : (a : EReal) < liminf (fun n => (c n : EReal)) atTop :=
      (EReal.coe_lt_coe haq).trans_le h
    filter_upwards [eventually_lt_of_lt_liminf ha] with n hn
    exact lt_min (EReal.coe_lt_coe_iff.mp hn) haq
  · intro b hqb
    exact Eventually.of_forall fun n => (min_le_right (c n) q).trans_lt hqb

/-- On a probability space, nonnegative integrable real functions whose
extended lower limit is at least `q` and whose actual means converge to `q`
converge to `q` in integral absolute error. -/
theorem tendsto_integral_abs_sub_of_ae_le_liminf {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {C : ℕ → Ω → ℝ} {q : ℝ}
    (hC : ∀ n, Integrable (C n) ν)
    (hnonneg : ∀ n, ∀ᵐ ω ∂ν, 0 ≤ C n ω) (hq : 0 ≤ q)
    (hlower : ∀ᵐ ω ∂ν, (q : EReal) ≤ liminf (fun n => (C n ω : EReal)) atTop)
    (hmean : Tendsto (fun n => ∫ ω, C n ω ∂ν) atTop (𝓝 q)) :
    Tendsto (fun n => ∫ ω, |C n ω - q| ∂ν) atTop (𝓝 0) := by
  apply tendsto_integral_abs_sub_of_ae_min hC (integrable_const q) hnonneg
    (ae_of_all ν fun _ => hq)
  · filter_upwards [hlower] with ω hω
    exact tendsto_min_const_of_le_liminf_ereal hω
  · simpa only [integral_const, probReal_univ, one_smul] using hmean

end LPPDifferentiability
