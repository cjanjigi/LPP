/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.MeasureTheory.Measure.Real

import Lean.Elab.Tactic.Omega

/-!
# Finite bad-site avoidance

This file bounds the probability that some site of a finite set is bad, using a union bound over
the sites. It then shows that a finite forbidden set made of boxes is avoided with high
probability.
-/

@[expose] public section

open MeasureTheory
open Set
open scoped BigOperators

namespace LPPDifferentiability

private theorem measureReal_bad_site_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : ℝ) (z : Lattice) :
    (environmentLaw μ).real {ω : Environment | ω z < -T} = μ.real (Iio (-T)) := by
  have hSet : {ω : Environment | ω z < -T} =
      (fun ω : Environment => ω z) ⁻¹' Iio (-T) := by
    ext ω
    simp [Set.mem_Iio]
  rw [hSet]
  change ((environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Iio (-T))).toReal =
    (μ (Iio (-T))).toReal
  calc
    ((environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Iio (-T))).toReal =
        (((environmentLaw μ).map (fun ω : Environment => ω z)) (Iio (-T))).toReal := by
          rw [Measure.map_apply (measurable_environment_eval z) measurableSet_Iio]
    _ = μ.real (Iio (-T)) := by
      rw [environmentLaw_map_eval μ z]
      rfl

/-- The probability that some site of a finite set `S` is bad, that is, lies strictly below `-T`,
is at most the number of sites times the strict lower-tail probability of `μ`. -/
theorem measureReal_exists_bad_site_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : ℝ) (S : Finset Lattice) :
    MeasurableSet {ω : Environment | ∃ z ∈ S, ω z < -T} ∧
      (environmentLaw μ).real {ω : Environment | ∃ z ∈ S, ω z < -T} ≤
        (S.card : ℝ) * μ.real (Iio (-T)) := by
  classical
  let bad : Lattice → Set Environment := fun z => {ω | ω z < -T}
  have hEvent :
      {ω : Environment | ∃ z ∈ S, ω z < -T} = ⋃ z ∈ S, bad z := by
    ext ω
    simp [bad]
  have hMeas : MeasurableSet {ω : Environment | ∃ z ∈ S, ω z < -T} := by
    rw [hEvent]
    exact Finset.measurableSet_biUnion S fun z _ =>
      measurableSet_lt (measurable_environment_eval z) measurable_const
  have hMarginal (z : Lattice) :
      (environmentLaw μ).real (bad z) = μ.real (Iio (-T)) := by
    exact measureReal_bad_site_eq μ T z
  constructor
  · exact hMeas
  · rw [hEvent]
    calc
      (environmentLaw μ).real (⋃ z ∈ S, bad z) ≤
          ∑ z ∈ S, (environmentLaw μ).real (bad z) :=
        measureReal_biUnion_finset_le S bad
      _ = ∑ _z ∈ S, μ.real (Iio (-T)) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hMarginal z
      _ = (S.card : ℝ) * μ.real (Iio (-T)) := by simp

private theorem backward_box_card (w : Lattice) (L : ℕ) :
    (Finset.Icc (w.1 - (L : ℤ)) w.1 ×ˢ
      Finset.Icc (w.2 - (L : ℤ)) w.2).card = (L + 1) ^ 2 := by
  have hinterval (a : ℤ) : (Finset.Icc (a - (L : ℤ)) a).card = L + 1 := by
    have hcast :
        ((Finset.Icc (a - (L : ℤ)) a).card : ℤ) = (L : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (a := a - (L : ℤ)) (b := a) (by omega)]
      omega
    exact_mod_cast hcast
  rw [Finset.card_product, hinterval w.1, hinterval w.2, pow_two]

private theorem backward_box_union_card_le (J N : Finset Lattice) (L : ℕ) :
    (J ∪ N.biUnion (fun w : Lattice =>
      Finset.Icc (w.1 - (L : ℤ)) w.1 ×ˢ
        Finset.Icc (w.2 - (L : ℤ)) w.2)).card ≤ J.card + N.card * (L + 1) ^ 2 := by
  let box : Lattice → Finset Lattice := fun w =>
    Finset.Icc (w.1 - (L : ℤ)) w.1 ×ˢ
      Finset.Icc (w.2 - (L : ℤ)) w.2
  have hsum : (∑ w ∈ N, (box w).card) = N.card * (L + 1) ^ 2 := by
    calc
      (∑ w ∈ N, (box w).card) = ∑ _w ∈ N, (L + 1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact backward_box_card w L
      _ = N.card * (L + 1) ^ 2 := by simp
  calc
    (J ∪ N.biUnion box).card ≤ J.card + (N.biUnion box).card := Finset.card_union_le _ _
    _ ≤ J.card + ∑ w ∈ N, (box w).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ = J.card + N.card * (L + 1) ^ 2 := by rw [hsum]

/-- The forbidden set is the union of `J` and the integer boxes of side `L + 1` whose top-right
corners are the points of `N`. The event that no site of this set is bad has probability at
least one minus the number of sites times the strict lower-tail probability of `μ`. -/
theorem measureReal_finite_bad_box_avoidance_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (J N : Finset Lattice) (L : ℕ) :
    let F := J ∪ N.biUnion (fun w : Lattice =>
      Finset.Icc (w.1 - (L : ℤ)) w.1 ×ˢ
        Finset.Icc (w.2 - (L : ℤ)) w.2)
    MeasurableSet {ω : Environment | ∀ z ∈ F, -T ≤ ω z} ∧
      (environmentLaw μ).real {ω : Environment | ∀ z ∈ F, -T ≤ ω z} ≥
        1 - ((J.card + N.card * (L + 1) ^ 2 : ℕ) : ℝ) * μ.real (Iio (-T)) := by
  classical
  dsimp only
  let F : Finset Lattice := J ∪ N.biUnion (fun w : Lattice =>
    Finset.Icc (w.1 - (L : ℤ)) w.1 ×ˢ
      Finset.Icc (w.2 - (L : ℤ)) w.2)
  let bad : Set Environment := {ω | ∃ z ∈ F, ω z < -T}
  have hSafeEq :
      {ω : Environment | ∀ z ∈ J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc (w.1 - (L : ℤ)) w.1 ×ˢ
          Finset.Icc (w.2 - (L : ℤ)) w.2), -T ≤ ω z} = badᶜ := by
    ext ω
    simp [bad, F, not_lt]
  obtain ⟨hBadMeas, hBadBound⟩ := measureReal_exists_bad_site_le μ T F
  have hSafeMeas : MeasurableSet
      {ω : Environment | ∀ z ∈ J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc (w.1 - (L : ℤ)) w.1 ×ˢ
          Finset.Icc (w.2 - (L : ℤ)) w.2), -T ≤ ω z} := by
    rw [hSafeEq]
    exact hBadMeas.compl
  have hCard : F.card ≤ J.card + N.card * (L + 1) ^ 2 := by
    exact backward_box_union_card_le J N L
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
