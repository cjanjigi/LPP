/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteContourBadLabels

/-!
# A finite family of all-bad label events

This file bounds the probability that at least one event of a finite family occurs. Each event
says that no site of one of the given finite sets is good. The bound is the number of events
times the single-event bound of `FiniteContourBadLabels`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- The union of finitely many all-bad label events is measurable, and its probability is at
most the number of events times the single-event power bound. The label sets may overlap; the
only geometric premise is the size bound `m ≤ 8 * (B i).card` for each set. -/
theorem measurable_and_measureReal_exists_all_bad_natural_site_family_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ × ℕ → Set Ω)
    (hG : ∀ v, MeasurableSet (G v))
    (k m : ℕ) (ζ : ℝ) (hζpos : 0 < ζ) (hζlt : ζ < 1)
    (hMarginal : ∀ v, MeasurableSet (G v) → P.real ((G v)ᶜ) ≤ ζ)
    (hSeparatedIndep : ∀ T : Finset (ℕ × ℕ),
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
        k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) →
      iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => G v.1) P)
    {ι : Type*} [DecidableEq ι]
    (W : Finset ι) (B : ι → Finset (ℕ × ℕ))
    (hSize : ∀ i ∈ W, m ≤ 8 * (B i).card) :
    MeasurableSet {ω : Ω | ∃ i ∈ W, ∀ x ∈ B i, ω ∉ G x} ∧
      P.real {ω : Ω | ∃ i ∈ W, ∀ x ∈ B i, ω ∉ G x} ≤
        (W.card : ℝ) *
          Real.rpow ζ ((m : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
  classical
  let E : ι → Set Ω := fun i => {ω : Ω | ∀ x ∈ B i, ω ∉ G x}
  have hMeasurable (i : ι) : MeasurableSet (E i) :=
    measurableSet_all_bad_sites G hG (B i)
  have hEvent :
      {ω : Ω | ∃ i ∈ W, ∀ x ∈ B i, ω ∉ G x} = ⋃ i ∈ W, E i := by
    ext ω
    simp [E]
  have hEach (i : ι) (hi : i ∈ W) :
      P.real (E i) ≤
        Real.rpow ζ ((m : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
    simpa [E] using
      measure_all_bad_natural_sites_le_real_power
        P G hG k m ζ hζpos hζlt hMarginal hSeparatedIndep (B i) (hSize i hi)
  constructor
  · rw [hEvent]
    exact Finset.measurableSet_biUnion W fun i _ => hMeasurable i
  · rw [hEvent]
    calc
      P.real (⋃ i ∈ W, E i) ≤ ∑ i ∈ W, P.real (E i) :=
        measureReal_biUnion_finset_le W E
      _ ≤ ∑ i ∈ W,
            Real.rpow ζ ((m : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun i hi => hEach i hi
      _ = (W.card : ℝ) *
            Real.rpow ζ ((m : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
        simp

end LPPDifferentiability

end
