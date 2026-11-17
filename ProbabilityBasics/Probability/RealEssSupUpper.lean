/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Data.EReal.Basic

/-!
# Real upper bounds and extended-real essential suprema

A real number that lies below every almost-everywhere real upper bound of a
function lies below that function's extended-real essential supremum.
-/

public section

open MeasureTheory

namespace ProbabilityBasics

/-- If every almost-everywhere real upper bound of `f` also bounds `a`, then
`a` lies below the extended-real essential supremum of `f`. This is the fourth
conditional helper in the one-sided variational plan. -/
theorem coe_le_essSup_of_forall_ae_le {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P] (f : α → ℝ) (a : ℝ)
    (hupper : ∀ c : ℝ, (∀ᵐ ω ∂P, f ω ≤ c) → a ≤ c) :
    (a : EReal) ≤ essSup (fun ω => (f ω : EReal)) P := by
  let q : EReal := essSup (fun ω => (f ω : EReal)) P
  have hbound : ∀ᵐ ω ∂P, (f ω : EReal) ≤ q := by
    exact ae_le_essSup (μ := P)
  by_cases htop : q = ⊤
  · simp [q, htop]
  · have hnotbot : q ≠ ⊥ := by
      intro hbot
      obtain ⟨ω, hω⟩ := hbound.exists
      rw [hbot] at hω
      exact (not_le_of_gt (EReal.bot_lt_coe (f ω))) hω
    have hreal : ∀ᵐ ω ∂P, f ω ≤ q.toReal := by
      filter_upwards [hbound] with ω hω
      have hω' := hω.trans (EReal.le_coe_toReal htop)
      exact EReal.coe_le_coe_iff.1 hω'
    have ha := hupper q.toReal hreal
    calc
      (a : EReal) ≤ (q.toReal : EReal) := EReal.coe_le_coe ha
      _ = q := EReal.coe_toReal htop hnotbot
      _ = essSup (fun ω => (f ω : EReal)) P := rfl

end ProbabilityBasics
