/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteBadAvoidance

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Measure.Real

/-!
# Avoidance of bad sites in positive boxes

This file bounds from below the probability that no site of a finite forbidden set is bad. The
forbidden set is a finite set together with boxes of side `L + 1` placed above a finite net of
points. A site is bad when its value lies strictly below `-T`.
-/

@[expose] public section

open MeasureTheory Set

namespace LPPDifferentiability

private theorem positive_box_card (w : Lattice) (L : ℕ) :
    (Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
      Finset.Icc w.2 (w.2 + (L : ℤ))).card = (L + 1) ^ 2 := by
  have hinterval (a : ℤ) : (Finset.Icc a (a + (L : ℤ))).card = L + 1 := by
    have hcast : ((Finset.Icc a (a + (L : ℤ))).card : ℤ) = (L : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (a := a) (b := a + (L : ℤ)) (by omega)]
      omega
    exact_mod_cast hcast
  rw [Finset.card_product, hinterval w.1, hinterval w.2, pow_two]

private theorem positive_box_union_card_le (J N : Finset Lattice) (L : ℕ) :
    (J ∪ N.biUnion (fun w : Lattice =>
      Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
        Finset.Icc w.2 (w.2 + (L : ℤ)))).card ≤
      J.card + N.card * (L + 1) ^ 2 := by
  let box : Lattice → Finset Lattice := fun w =>
    Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
      Finset.Icc w.2 (w.2 + (L : ℤ))
  have hsum : (∑ w ∈ N, (box w).card) = N.card * (L + 1) ^ 2 := by
    calc
      (∑ w ∈ N, (box w).card) = ∑ _w ∈ N, (L + 1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact positive_box_card w L
      _ = N.card * (L + 1) ^ 2 := by simp
  calc
    (J ∪ N.biUnion box).card ≤ J.card + (N.biUnion box).card :=
      Finset.card_union_le _ _
    _ ≤ J.card + ∑ w ∈ N, (box w).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ = J.card + N.card * (L + 1) ^ 2 := by rw [hsum]

/-- The sites of the boxes above a finite net, together with the sites of `J`, are all safe with
probability at least one minus the number of sites times the strict lower-tail probability of
`μ`. Each box is the product of two integer intervals of length `L`, starting at the net point. -/
theorem measureReal_positive_bad_box_avoidance_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (J N : Finset Lattice) (L : ℕ) :
    let F := J ∪ N.biUnion (fun w : Lattice =>
      Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
        Finset.Icc w.2 (w.2 + (L : ℤ)))
    MeasurableSet {ω : Environment | ∀ z ∈ F, -T ≤ ω z} ∧
      (environmentLaw μ).real {ω : Environment | ∀ z ∈ F, -T ≤ ω z} ≥
        1 - ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) *
          μ.real (Iio (-T)) := by
  classical
  dsimp only
  let F : Finset Lattice := J ∪ N.biUnion (fun w : Lattice =>
    Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
      Finset.Icc w.2 (w.2 + (L : ℤ)))
  let bad : Set Environment := {ω | ∃ z ∈ F, ω z < -T}
  have hSafeEq :
      {ω : Environment | ∀ z ∈ J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
          Finset.Icc w.2 (w.2 + (L : ℤ))), -T ≤ ω z} = badᶜ := by
    ext ω
    simp [bad, F, not_lt]
  obtain ⟨hBadMeas, hBadBound⟩ := measureReal_exists_bad_site_le μ T F
  have hSafeMeas : MeasurableSet
      {ω : Environment | ∀ z ∈ J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ
          Finset.Icc w.2 (w.2 + (L : ℤ))), -T ≤ ω z} := by
    rw [hSafeEq]
    exact hBadMeas.compl
  have hCard : F.card ≤ J.card + N.card * (L + 1) ^ 2 :=
    positive_box_union_card_le J N L
  have hCardReal : (F.card : ℝ) ≤
      ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hCard
  have hTailNonneg : 0 ≤ μ.real (Iio (-T)) := measureReal_nonneg
  have hBadBound' : (environmentLaw μ).real bad ≤
      ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * μ.real (Iio (-T)) := by
    calc
      (environmentLaw μ).real bad ≤ (F.card : ℝ) * μ.real (Iio (-T)) := hBadBound
      _ ≤ ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * μ.real (Iio (-T)) :=
        mul_le_mul_of_nonneg_right hCardReal hTailNonneg
  constructor
  · exact hSafeMeas
  · rw [hSafeEq, probReal_compl_eq_one_sub (μ := environmentLaw μ) hBadMeas]
    linarith

end LPPDifferentiability
end
