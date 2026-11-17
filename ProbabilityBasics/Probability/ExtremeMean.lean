/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Extreme

/-!
# Extreme means of random vectors

An integrable random vector in a closed convex set is almost surely constant
when its mean is an extreme point of that set.
-/

public section

open MeasureTheory

namespace ProbabilityBasics

/-- If an integrable random vector lies almost surely in a closed convex set and its mean is an
extreme point of that set, then the vector equals its mean almost surely. This is the ordinary
extreme-point step of Janjigian–Rassoul-Agha, Lemma 4.5(c), reading lines 833–834; the general
probability argument is supplied here. -/
theorem ae_eq_integral_of_mem_extremePoints
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (C : Set E) (X : Ω → E)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hX_integrable : Integrable X P)
    (hX_mem : ∀ᵐ ω ∂P, X ω ∈ C)
    (hmean_extreme : (∫ ω, X ω ∂P) ∈ Set.extremePoints ℝ C) :
    ∀ᵐ ω ∂P, X ω = ∫ s, X s ∂P := by
  -- Either the vector is already constant at its average, or a measurable split detects variation.
  rcases ae_eq_const_or_exists_average_ne_compl hX_integrable with hconstant | hsplit
  · filter_upwards [hconstant] with ω hω
    simpa only [Function.const_apply, average_eq_integral] using hω
  · obtain ⟨t, ht_measurable, ht_pos, ht_complement_pos, h_averages_ne⟩ := hsplit
    -- Convexity and closedness put the two restricted averages back in the set.
    have hleft_mem : (⨍ ω in t, X ω ∂P) ∈ C := by
      exact hC_convex.set_average_mem hC_closed ht_pos (by finiteness)
        (ae_restrict_of_ae hX_mem) hX_integrable.integrableOn
    have hright_mem : (⨍ ω in tᶜ, X ω ∂P) ∈ C := by
      exact hC_convex.set_average_mem hC_closed ht_complement_pos (by finiteness)
        (ae_restrict_of_ae hX_mem) hX_integrable.integrableOn
    -- The full average is strictly between these two averages.
    have haverage_segment :
        (⨍ ω, X ω ∂P) ∈ openSegment ℝ (⨍ ω in t, X ω ∂P) (⨍ ω in tᶜ, X ω ∂P) :=
      average_mem_openSegment_compl_self ht_measurable.nullMeasurableSet ht_pos
        ht_complement_pos hX_integrable
    have hmean_segment :
        (∫ ω, X ω ∂P) ∈ openSegment ℝ (⨍ ω in t, X ω ∂P) (⨍ ω in tᶜ, X ω ∂P) := by
      simpa only [average_eq_integral] using haverage_segment
    -- An extreme point in an open segment forces both endpoints to equal the mean.
    obtain ⟨hleft_eq_mean, hright_eq_mean⟩ :=
      (mem_extremePoints.mp hmean_extreme).2 _ hleft_mem _ hright_mem hmean_segment
    exact False.elim (h_averages_ne (hleft_eq_mean.trans hright_eq_mean.symm))

end ProbabilityBasics
