/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! # Heavy attachment ceiling cutoffs

The ceilings in the attachment construction eventually exceed the fixed tube and box sizes.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The attachment ceiling has the linear upper bound used in the
polynomial estimate, for scales at least one. -/
theorem heavy_attachment_ceiling_add_one_bound (kappa s : ℝ)
    (hkappa : 0 < kappa) (hs : 1 ≤ s) :
    ((Nat.ceil (kappa * s) + 1 : ℕ) : ℝ) ≤ (kappa + 2) * s := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have hceil : (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hkappa.le hs0)).le
  have hcast : ((Nat.ceil (kappa * s) + 1 : ℕ) : ℝ) =
      (Nat.ceil (kappa * s) : ℝ) + 1 := by
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  calc
    (Nat.ceil (kappa * s) : ℝ) + 1 ≤ kappa * s + 2 := by linarith
    _ ≤ (kappa + 2) * s := by nlinarith [hs]

/-- Above the real threshold, the natural ceiling reaches
both fixed cutoffs from the attachment construction. -/
theorem heavy_attachment_source_ceiling_cutoffs_of_threshold
    (K : ℕ) (kappa s : ℝ) (hkappa : 0 < kappa)
    (hscale : max 1 (max
      (((2 * K + 5 : ℕ) : ℝ) / kappa)
      (((4 * K + 4 : ℕ) : ℝ) / kappa)) ≤ s) :
    2 * K + 5 ≤ Nat.ceil (kappa * s) ∧
      4 * K + 4 ≤ Nat.ceil (kappa * s) := by
  have hthreshold := (le_max_right 1 _).trans hscale
  have hcut1 := (le_max_left _ _).trans hthreshold
  have hcut2 := (le_max_right _ _).trans hthreshold
  have hreal1 : ((2 * K + 5 : ℕ) : ℝ) ≤ kappa * s := by
    calc
      ((2 * K + 5 : ℕ) : ℝ) ≤ s * kappa :=
        (div_le_iff₀ hkappa).mp hcut1
      _ = kappa * s := by ring
  have hreal2 : ((4 * K + 4 : ℕ) : ℝ) ≤ kappa * s := by
    calc
      ((4 * K + 4 : ℕ) : ℝ) ≤ s * kappa :=
        (div_le_iff₀ hkappa).mp hcut2
      _ = kappa * s := by ring
  constructor
  · exact_mod_cast hreal1.trans (Nat.le_ceil (kappa * s))
  · exact_mod_cast hreal2.trans (Nat.le_ceil (kappa * s))

/-- The two fixed-size conditions hold eventually for the
ceiling `Nat.ceil (kappa * s)`, since `kappa` is positive. -/
theorem eventually_heavy_attachment_source_ceiling_cutoffs
    (K : ℕ) (kappa : ℝ) (hkappa : 0 < kappa) :
    ∀ᶠ s : ℝ in atTop,
      2 * K + 5 ≤ Nat.ceil (kappa * s) ∧
        4 * K + 4 ≤ Nat.ceil (kappa * s) := by
  have hthreshold : ∀ᶠ s : ℝ in atTop,
      max 1 (max
        (((2 * K + 5 : ℕ) : ℝ) / kappa)
        (((4 * K + 4 : ℕ) : ℝ) / kappa)) ≤ s :=
    eventually_ge_atTop _
  filter_upwards [hthreshold] with s hs
  exact heavy_attachment_source_ceiling_cutoffs_of_threshold K kappa s hkappa hs

end LPPDifferentiability

end
