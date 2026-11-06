/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.LatticeShellBorelCantelli

import Mathlib.Tactic
import Mathlib.Tactic.Positivity

/-!
# Uniform deviations on the nonnegative lattice

Finite exceptional sets have a positive length threshold. A generic
exponential tail bound then gives one almost-sure event on which every
positive relative-deviation tolerance holds eventually.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- A finite set of lattice points is avoided once the coordinate sum is
large enough. The threshold is positive, even for an empty set. -/
theorem exists_length_threshold_outside_finite_set
    {S : Set (ℕ × ℕ)} (hS : S.Finite) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 → z ∉ S := by
  classical
  let lengths := hS.toFinset.image (fun z : ℕ × ℕ => z.1 + z.2)
  by_cases hne : lengths.Nonempty
  · refine ⟨lengths.max' hne + 1, by omega, ?_⟩
    intro z hz hzS
    have hzLength : z.1 + z.2 ∈ lengths := by
      change z.1 + z.2 ∈ hS.toFinset.image (fun x : ℕ × ℕ => x.1 + x.2)
      exact Finset.mem_image.mpr ⟨z, hS.mem_toFinset.mpr hzS, rfl⟩
    have hle : z.1 + z.2 ≤ lengths.max' hne :=
      Finset.le_max' _ _ hzLength
    omega
  · refine ⟨1, by omega, ?_⟩
    intro z _ hzS
    have hzLength : z.1 + z.2 ∈ lengths := by
      change z.1 + z.2 ∈ hS.toFinset.image (fun x : ℕ × ℕ => x.1 + x.2)
      exact Finset.mem_image.mpr ⟨z, hS.mem_toFinset.mpr hzS, rfl⟩
    exact hne ⟨z.1 + z.2, hzLength⟩

/-- A generic exponential envelope away from the origin gives one
probability-one event on which every positive relative-deviation tolerance
holds beyond a positive length threshold. The event bound is a premise of
this generic bookkeeping result; no particular random field or concentration
theorem is inferred from it. -/
theorem ae_eventually_lattice_relative_deviation_of_exp_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → (ℕ × ℕ → ℝ))
    (hTail : ∀ ε : ℝ, 0 < ε →
      ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧
        ∀ z : ℕ × ℕ, z ≠ (0, 0) →
          μ.real {ω | ε * ((z.1 + z.2 : ℕ) : ℝ) ≤ |D ω z|} ≤
            K * Real.exp (-c * ((z.1 + z.2 : ℕ) : ℝ))) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
        |D ω z| < ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  let A : ℕ → ℕ × ℕ → Set Ω := fun k z =>
    {ω | (1 / ((k : ℝ) + 1)) * ((z.1 + z.2 : ℕ) : ℝ) ≤ |D ω z|}
  have hfinite (k : ℕ) : ∀ᵐ ω ∂μ, {z | ω ∈ A k z}.Finite := by
    have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨K, c, hK, hc, hTailk⟩ := hTail _ hε
    exact ae_finite_lattice_bad_set_of_exp_tail μ (A k) hK hc (by
      intro z hz
      simpa [A] using hTailk z hz)
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, {z | ω ∈ A k z}.Finite := by
    exact ae_all_iff.mpr hfinite
  filter_upwards [hall] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN, hNbad⟩ :=
    exists_length_threshold_outside_finite_set (hω k)
  refine ⟨N, hN, ?_⟩
  intro z hz
  have hnotbad : ¬ (1 / ((k : ℝ) + 1) *
      ((z.1 + z.2 : ℕ) : ℝ) ≤ |D ω z|) := by
    simpa [A] using hNbad z hz
  have hlen : (0 : ℝ) < ((z.1 + z.2 : ℕ) : ℝ) := by
    have hlenNat : 0 < z.1 + z.2 := by omega
    exact_mod_cast hlenNat
  calc
    |D ω z| < (1 / ((k : ℝ) + 1)) * ((z.1 + z.2 : ℕ) : ℝ) :=
      lt_of_not_ge hnotbad
    _ < ε * ((z.1 + z.2 : ℕ) : ℝ) := mul_lt_mul_of_pos_right hk hlen

end LPPDifferentiability

end
