/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Hard cutoffs of real-valued functions

The hard cutoff agrees with the original function wherever its absolute value
is below the cutoff level. It is dominated by the original absolute value,
and on any fixed finite orbit segment it eventually agrees at every point.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- Keep a value when its absolute value is at most `L`, and use zero otherwise. -/
noncomputable def hardCutoff {Ω : Type*} (f : Ω → ℝ) (L : ℝ) (ω : Ω) : ℝ :=
  if |f ω| ≤ L then f ω else 0

/-- A hard cutoff is bounded in absolute value by the original value. -/
theorem hardCutoff_abs_le {Ω : Type*} (f : Ω → ℝ) (L : ℝ) (ω : Ω) :
    |hardCutoff f L ω| ≤ |f ω| := by
  by_cases h : |f ω| ≤ L
  · simp [hardCutoff, h]
  · simp [hardCutoff, h]

/-- A hard cutoff of a measurable function is measurable. -/
theorem measurable_hardCutoff {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ) (hf : Measurable f) (L : ℝ) :
    Measurable (hardCutoff f L) := by
  unfold hardCutoff
  exact Measurable.ite
    (measurableSet_le (continuous_abs.measurable.comp hf) measurable_const) hf measurable_const

/-- Integrability of the input alone suffices for integrability of its hard cutoff. -/
theorem integrable_hardCutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (L : ℝ) :
    Integrable (hardCutoff f L) μ := by
  have hscalar : Measurable (fun x : ℝ => if |x| ≤ L then x else 0) := by
    exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      measurable_id measurable_const
  have hmeasurable : AEMeasurable (hardCutoff f L) μ := by
    change AEMeasurable (fun ω => (fun x : ℝ => if |x| ≤ L then x else 0) (f ω)) μ
    exact hscalar.comp_aemeasurable hf.aemeasurable
  apply hf.mono hmeasurable.aestronglyMeasurable
  filter_upwards [Filter.Eventually.of_forall (hardCutoff_abs_le f L)] with ω hω
  simpa only [Real.norm_eq_abs] using hω

/-- The average of the first `n` values along the forward orbit of `ω`.

The definition also assigns a value at `n = 0`; all orbit statements below
that use a threshold restrict to positive `n`. -/
noncomputable def orbitAverage {Ω : Type*} (f : Ω → ℝ) (T : Ω → Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ j ∈ Finset.range n, f ((T^[j]) ω)) / (n : ℝ)

/-- One finite sum of absolute orbit values bounds each of its terms. -/
theorem hardCutoff_eq_of_sum_abs_le {Ω : Type*} (f : Ω → ℝ) (T : Ω → Ω)
    (ω : Ω) (N : ℕ) (L : ℝ)
    (hL : (∑ j ∈ Finset.range N, |f ((T^[j]) ω)|) ≤ L)
    {j : ℕ} (hj : j < N) :
    hardCutoff f L ((T^[j]) ω) = f ((T^[j]) ω) := by
  have hterm : |f ((T^[j]) ω)| ≤ ∑ i ∈ Finset.range N, |f ((T^[i]) ω)| :=
    Finset.single_le_sum (f := fun i => |f ((T^[i]) ω)|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hj)
  have hcut : |f ((T^[j]) ω)| ≤ L := hterm.trans hL
  simp [hardCutoff, hcut]

/-- On a finite orbit segment, every cutoff level above one finite bound agrees
with the input at every orbit point. This is pointwise and needs no assumptions
on the map or the function. -/
theorem hardCutoff_eventually_eq_finite_orbit {Ω : Type*} (f : Ω → ℝ)
    (T : Ω → Ω) (ω : Ω) (N : ℕ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ j : ℕ, j < N → hardCutoff f L ((T^[j]) ω) = f ((T^[j]) ω) := by
  refine ⟨∑ j ∈ Finset.range N, |f ((T^[j]) ω)|, ?_⟩
  intro L hL j hj
  exact hardCutoff_eq_of_sum_abs_le f T ω N L hL hj

/-- If two functions agree at the first `N` orbit points, their averages agree
through every horizon `k ≤ N`. -/
theorem orbitAverage_eq_of_eq_finite_orbit {Ω : Type*} (f g : Ω → ℝ)
    (T : Ω → Ω) (ω : Ω) (N k : ℕ) (hk : k ≤ N)
    (h : ∀ j : ℕ, j < N → f ((T^[j]) ω) = g ((T^[j]) ω)) :
    orbitAverage f T k ω = orbitAverage g T k ω := by
  unfold orbitAverage
  have hsum :
      (∑ j ∈ Finset.range k, f ((T^[j]) ω)) =
        ∑ j ∈ Finset.range k, g ((T^[j]) ω) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact h j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
  rw [hsum]

/-- Finite averages and their strict threshold event are eventually exactly
the same for a hard cutoff and the original function. -/
theorem hardCutoff_eventually_orbit_averages_and_threshold {Ω : Type*}
    (f : Ω → ℝ) (T : Ω → Ω) (ω : Ω) (N : ℕ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      (∀ k : ℕ, k ≤ N →
        orbitAverage (hardCutoff f L) T k ω = orbitAverage f T k ω) ∧
      (∀ threshold : ℝ,
        ((∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
          threshold < orbitAverage (hardCutoff f L) T k ω) ↔
         (∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ threshold < orbitAverage f T k ω)) ) := by
  obtain ⟨L₀, hvalues⟩ := hardCutoff_eventually_eq_finite_orbit f T ω N
  refine ⟨L₀, ?_⟩
  intro L hL
  have hvaluesL : ∀ j : ℕ, j < N →
      hardCutoff f L ((T^[j]) ω) = f ((T^[j]) ω) := hvalues L hL
  constructor
  · intro k hk
    exact orbitAverage_eq_of_eq_finite_orbit (hardCutoff f L) f T ω N k hk
      (fun j hj => hvaluesL j hj)
  · intro threshold
    constructor
    · rintro ⟨k, hk0, hkN, havg⟩
      have heq := orbitAverage_eq_of_eq_finite_orbit
        (hardCutoff f L) f T ω N k hkN (fun j hj => hvaluesL j hj)
      rw [heq] at havg
      exact ⟨k, hk0, hkN, havg⟩
    · rintro ⟨k, hk0, hkN, havg⟩
      have heq := orbitAverage_eq_of_eq_finite_orbit
        (hardCutoff f L) f T ω N k hkN (fun j hj => hvaluesL j hj)
      exact ⟨k, hk0, hkN, by rw [heq]; exact havg⟩

end LPPDifferentiability
