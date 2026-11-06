/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.RayLaw
public import ProbabilityBasics.Probability.CesaroLaw
public import Mathlib.Probability.IdentDistrib

/-!
# Liggett inputs for the signed ray array

The array below is the negative last-passage value with natural
subtraction on all index pairs. Liggett's argument uses only pairs `m < n`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The negative last-passage array along a natural lattice ray. -/
@[expose] noncomputable def negLastPassageRayArray (a : ℕ × ℕ) (m n : ℕ)
    (ω : Environment) : ℝ :=
  -lastPassage ω (m • ((a.1 : ℤ), (a.2 : ℤ))) ((n - m) • a)

/-- Evaluation is the natural-subtraction formula for the array. -/
@[simp] theorem negLastPassageRayArray_apply (a : ℕ × ℕ) (m n : ℕ)
    (ω : Environment) :
    negLastPassageRayArray a m n ω =
      -lastPassage ω (m • ((a.1 : ℤ), (a.2 : ℤ))) ((n - m) • a) := rfl

/-- Each origin term of the array is measurable. -/
theorem measurable_negLastPassageRayArray_origin (a : ℕ × ℕ) (n : ℕ) :
    Measurable (fun ω : Environment => negLastPassageRayArray a 0 n ω) := by
  simpa [negLastPassageRayArray] using measurable_neg_lastPassage_ray a n

/-- A marginal first moment makes every origin term of the array
integrable under the environment law. -/
theorem integrable_negLastPassageRayArray_origin (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ)
    (a : ℕ × ℕ) (n : ℕ) :
    Integrable (fun ω : Environment => negLastPassageRayArray a 0 n ω)
      (environmentLaw μ) := by
  simpa [negLastPassageRayArray] using integrable_neg_lastPassage_ray μ hμ a n

/-- The origin array satisfies Liggett's pointwise subadditivity on its
domain `0 < m < n`. -/
theorem negLastPassageRayArray_origin_subadditive (a : ℕ × ℕ)
    (ω : Environment) (m n : ℕ) (_hm : 0 < m) (hmn : m < n) :
    negLastPassageRayArray a 0 n ω ≤
      negLastPassageRayArray a 0 m ω + negLastPassageRayArray a m n ω := by
  have hindex : m + (n - m) = n := by omega
  have h := neg_lastPassage_ray_cocycle ω a m (n - m)
  rw [lastPassage_translate_iterate, add_zero, hindex] at h
  simpa [negLastPassageRayArray] using h

/-- The complete adjacent positive-length columns of the array have
the same joint law. -/
theorem negLastPassageRayArray_column_identDistrib (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℕ × ℕ) (m : ℕ) :
    IdentDistrib
      (fun ω : Environment => fun j : ℕ =>
        negLastPassageRayArray a (m + 1) (m + 1 + (j + 1)) ω)
      (fun ω : Environment => fun j : ℕ =>
        negLastPassageRayArray a m (m + (j + 1)) ω)
      (environmentLaw μ) (environmentLaw μ) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [negLastPassageRayArray, Nat.add_sub_cancel_left] using
      (measurable_neg_lastPassage_column
        ((m + 1) • ((a.1 : ℤ), (a.2 : ℤ))) a).aemeasurable
  · simpa only [negLastPassageRayArray, Nat.add_sub_cancel_left] using
      (measurable_neg_lastPassage_column
        (m • ((a.1 : ℤ), (a.2 : ℤ))) a).aemeasurable
  · simpa only [negLastPassageRayArray, Nat.add_sub_cancel_left] using
      environmentLaw_map_neg_lastPassage_ray_column μ a m

private theorem ray_tail_block_length_sub (j k : ℕ) :
    (j + 2) * k - (j + 1) * k = k := by
  rw [show j + 2 = (j + 1) + 1 by omega, Nat.add_mul, Nat.one_mul,
    Nat.add_sub_cancel_left]

private theorem ray_tail_start_add (j k : ℕ) :
    j * k + k = (j + 1) * k := by
  rw [Nat.add_mul, Nat.one_mul]

/-- The sequence of blocks beginning at index one is measurable. -/
theorem measurable_negLastPassageRayArray_tailBlocks (a : ℕ × ℕ) (k : ℕ) :
    Measurable (fun ω : Environment => fun j : ℕ =>
      negLastPassageRayArray a ((j + 1) * k) ((j + 2) * k) ω) := by
  simpa only [negLastPassageRayArray, ray_tail_block_length_sub,
    cast_natRay_smul, ← mul_smul, ← add_nsmul, one_smul, ray_tail_start_add] using
    measurable_neg_lastPassage_blocks
      (k • ((a.1 : ℤ), (a.2 : ℤ))) (k • a)

/-- The positive-size tail block sequence and its left shift
are identically distributed. -/
theorem negLastPassageRayArray_tailBlocks_identDistrib (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℕ × ℕ) (k : ℕ) :
    IdentDistrib
      (fun ω : Environment =>
        sequenceShift (fun j : ℕ =>
          negLastPassageRayArray a ((j + 1) * k) ((j + 2) * k) ω))
      (fun ω : Environment => fun j : ℕ =>
        negLastPassageRayArray a ((j + 1) * k) ((j + 2) * k) ω)
      (environmentLaw μ) (environmentLaw μ) := by
  let B : Environment → ℕ → ℝ := fun ω j =>
    negLastPassageRayArray a ((j + 1) * k) ((j + 2) * k) ω
  have hpres := measurePreserving_neg_lastPassage_ray_blocks_shift μ a k 1
  have hmeasB : Measurable B := by
    simpa only [B] using measurable_negLastPassageRayArray_tailBlocks a k
  have hshift : MeasurePreserving
      (fun x : ℕ → ℝ => fun j => x (j + 1))
      ((environmentLaw μ).map B) ((environmentLaw μ).map B) := by
    refine ⟨?_, ?_⟩
    · change Measurable sequenceShift
      exact measurable_sequenceShift
    · change ((environmentLaw μ).map B).map
        (fun x : ℕ → ℝ => fun j => x (j + 1)) =
          (environmentLaw μ).map B
      simpa only [B, negLastPassageRayArray, ray_tail_block_length_sub]
        using hpres.map_eq
  refine ⟨(hshift.measurable.comp hmeasB).aemeasurable,
    hmeasB.aemeasurable, ?_⟩
  change Measure.map
      ((fun x : ℕ → ℝ => fun j => x (j + 1)) ∘ B) (environmentLaw μ) =
    Measure.map B (environmentLaw μ)
  calc
    _ = ((environmentLaw μ).map B).map
        (fun x : ℕ → ℝ => fun j => x (j + 1)) :=
      (Measure.map_map hshift.measurable hmeasB).symm
    _ = _ := hshift.map_eq

/-- Every positive block size gives an ergodic shift on the tail block
sequence, for each nonzero direction. -/
theorem ergodic_negLastPassageRayArray_tailBlocks_shift (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℕ × ℕ) (ha : a ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    Ergodic sequenceShift
      ((environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
        negLastPassageRayArray a ((j + 1) * k) ((j + 2) * k) ω)) := by
  change Ergodic (fun x : ℕ → ℝ => fun j => x (j + 1))
    ((environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
      negLastPassageRayArray a ((j + 1) * k) ((j + 2) * k) ω))
  simpa only [negLastPassageRayArray, ray_tail_block_length_sub] using
    ergodic_neg_lastPassage_ray_blocks_shift μ a ha k hk 1

end LPPDifferentiability
