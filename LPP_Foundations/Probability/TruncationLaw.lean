/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentMap

/-!
# Laws of clipped weights and their remainders

The clipping and remainder maps are the real functions used in the finite
last-passage truncation. Strict-tail preimages are computed directly, so the laws
keep the atoms at the clipping thresholds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The strict-tail preimage of the positive remainder is an open upper tail. -/
theorem positive_remainder_strict_tail_preimage (L t : ℝ) (ht : 0 ≤ t) :
    (fun x : ℝ => max (x - L) 0) ⁻¹' Set.Ioi t = Set.Ioi (L + t) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioi, lt_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h
    left
    linarith

/-- The strict-tail preimage of the negative remainder is an open lower tail. -/
theorem negative_remainder_strict_tail_preimage (L t : ℝ) (ht : 0 ≤ t) :
    (fun x : ℝ => max (-x - L) 0) ⁻¹' Set.Ioi t = Set.Iio (-L - t) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, lt_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h
    left
    linarith

/-- The positive-remainder strict tail keeps its atom-sensitive upper-tail cutoff. -/
theorem map_positive_remainder_strict_tail (μ : Measure ℝ) (L t : ℝ) (ht : 0 ≤ t) :
    (μ.map (fun x : ℝ => max (x - L) 0)) (Set.Ioi t) = μ (Set.Ioi (L + t)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi,
    positive_remainder_strict_tail_preimage L t ht]

/-- The negative-remainder strict tail keeps its atom-sensitive lower-tail cutoff. -/
theorem map_negative_remainder_strict_tail (μ : Measure ℝ) (L t : ℝ) (ht : 0 ≤ t) :
    (μ.map (fun x : ℝ => max (-x - L) 0)) (Set.Ioi t) = μ (Set.Iio (-L - t)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi,
    negative_remainder_strict_tail_preimage L t ht]

/-- The clipping map sends the iid environment law to the law of the clipped marginal. -/
theorem environmentLaw_map_clipped (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) :
    (environmentLaw μ).map
        (fun ω : Environment => fun z : Lattice => max (-L) (min L (ω z))) =
      environmentLaw (μ.map (fun x : ℝ => max (-L) (min L x))) := by
  exact environmentLaw_map_coordinatewise μ
    (fun x : ℝ => max (-L) (min L x)) (by fun_prop)

/-- The positive remainder field has the iid law of the remainder marginal. -/
theorem environmentLaw_map_positive_remainder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) :
    (environmentLaw μ).map
        (fun ω : Environment => fun z : Lattice => max (ω z - L) 0) =
      environmentLaw (μ.map (fun x : ℝ => max (x - L) 0)) := by
  exact environmentLaw_map_coordinatewise μ (fun x : ℝ => max (x - L) 0) (by fun_prop)

/-- The negative remainder field has the iid law of the remainder marginal. -/
theorem environmentLaw_map_negative_remainder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) :
    (environmentLaw μ).map
        (fun ω : Environment => fun z : Lattice => max (-ω z - L) 0) =
      environmentLaw (μ.map (fun x : ℝ => max (-x - L) 0)) := by
  exact environmentLaw_map_coordinatewise μ (fun x : ℝ => max (-x - L) 0) (by fun_prop)

end LPPDifferentiability
