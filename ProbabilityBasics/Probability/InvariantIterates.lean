/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Almost-everywhere invariance along all forward iterates -/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- An almost-everywhere invariant function is constant along its forward
orbit on one common full-measure set. -/
theorem ae_all_iterate_eq_of_ae_invariant {Ω Y : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} {g : Ω → Y}
    (hT : MeasurePreserving T μ μ) (hg : ∀ᵐ ω ∂μ, g (T ω) = g ω) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, g ((T^[n]) ω) = g ω := by
  apply ae_all_iff.mpr
  intro n
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ n ih =>
    filter_upwards [(hT.iterate n).quasiMeasurePreserving.ae hg, ih] with ω hstep hprev
    rw [Function.iterate_succ_apply', hstep, hprev]

end LPPDifferentiability
