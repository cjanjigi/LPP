/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.PassageMeanBounds
public import LPP_Foundations.Model.Paths.SliceAllocation
public import Martin2004.Probability.BoundedPathConcentration
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite allocation upper tails

These are the planar allocation estimates in the proof of Martin (2004),
Lemma 3.2. Each allocation is represented by one deterministic path, with its
signed mean and the stated concentration constants. A union bound handles
the finite family without requiring independence between allocations.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- A finite family of uniformly bounded event probabilities has the count bound. -/
theorem measureReal_iUnion_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] [Fintype ι]
    (E : ι → Set Ω) (q : ℝ) (hE : ∀ i, ν.real (E i) ≤ q) :
    ν.real (⋃ i, E i) ≤ (Fintype.card ι : ℝ) * q := by
  calc
    _ ≤ ∑ i, ν.real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _i : ι, q := Finset.sum_le_sum fun i _ => hE i
    _ = _ := by simp

/-- An almost surely bounded marginal bounds its actual signed mean above. -/
theorem integral_id_le_of_ae_abs_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (hμ : ∀ᵐ x ∂μ, |x| ≤ L) : (∫ x : ℝ, x ∂μ) ≤ L := by
  have hi := integrable_id_of_ae_abs_le μ L hμ
  calc
    (∫ x : ℝ, x ∂μ) ≤ ∫ _x : ℝ, L ∂μ := by
      apply integral_mono_ae hi (integrable_const L)
      filter_upwards [hμ] with x hx using (le_abs_self x).trans hx
    _ = L := by simp

/-- The actual slice expression is integrable under a bounded marginal. -/
theorem SliceAllocation.integrable_weight_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℕ}
    (h : SliceAllocation a b) (u : Lattice) (L : ℝ)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    Integrable (fun ω : Environment => h.weight ω u) (environmentLaw μ) := by
  obtain ⟨p, hp⟩ := h.exists_path u
  have he : (fun ω : Environment => h.weight ω u) = fun ω => pathWeight ω p :=
    funext fun ω => (hp ω).symm
  rw [he]
  exact integrable_pathWeight μ (integrable_id_of_ae_abs_le μ L hμ) p

/-- The exact signed mean of an actual allocation, with its moment produced. -/
theorem SliceAllocation.integral_weight_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℕ}
    (h : SliceAllocation a b) (u : Lattice) (L : ℝ)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    (∫ ω : Environment, h.weight ω u ∂environmentLaw μ) =
      (a + b : ℕ) * ∫ x : ℝ, x ∂μ := by
  obtain ⟨p, hp⟩ := h.exists_path u
  have he : (fun ω : Environment => h.weight ω u) = fun ω => pathWeight ω p :=
    funext fun ω => (hp ω).symm
  rw [he]
  exact integral_pathWeight μ (integrable_id_of_ae_abs_le μ L hμ) p

/-- A fixed actual allocation has Martin's upper-tail estimate. -/
theorem SliceAllocation.measure_weight_ge_le_martin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℕ}
    (h : SliceAllocation a b) (u : Lattice) {L t : ℝ}
    (hL : 0 < L) (ht : 0 < t) (hab : 0 < a + b)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    (environmentLaw μ).real {ω : Environment |
      (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + t ≤ h.weight ω u} ≤
      Real.exp (-t ^ 2 / (64 * (a + b : ℕ) * L ^ 2) + 64) := by
  obtain ⟨p, hp⟩ := h.exists_path u
  have hm := integral_id_le_of_ae_abs_le μ L hμ
  have hmean := h.integral_weight_of_ae_abs_le μ u L hμ
  have hcmp : (a + b : ℕ) * (∫ x : ℝ, x ∂μ) ≤
      (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have htail := measure_abs_pathWeight_sub_integral_ge_le_martin μ hL ht hμ p hab
  have hpi : (∫ ω : Environment, pathWeight ω p ∂environmentLaw μ) =
      (a + b : ℕ) * (∫ x : ℝ, x ∂μ) := by
    rw [show (fun ω : Environment => pathWeight ω p) =
      (fun ω : Environment => h.weight ω u) from funext hp]
    exact hmean
  apply le_trans (measureReal_mono (μ := environmentLaw μ) ?_) htail
  intro ω hω
  change (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + t ≤ h.weight ω u at hω
  change t ≤ |pathWeight ω p - ∫ η : Environment, pathWeight η p ∂environmentLaw μ|
  rw [hp ω, hpi]
  exact (by linarith : t ≤ h.weight ω u - (a + b : ℕ) * (∫ x : ℝ, x ∂μ)).trans
    (le_abs_self _)

/-- The actual finite passage estimate before integer-ray normalization. -/
theorem measure_lastPassage_ge_le_choose_mul_exp
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : Lattice) (a b : ℕ)
    {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (hab : 0 < a + b)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    (environmentLaw μ).real {ω : Environment |
      (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + t ≤ lastPassage ω u (a, b)} ≤
      (Nat.choose (a + b) a : ℝ) *
        Real.exp (-t ^ 2 / (64 * (a + b : ℕ) * L ^ 2) + 64) := by
  classical
  let E : SliceAllocation a b → Set Environment := fun h =>
    {ω | (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + t ≤ h.weight ω u}
  have hsub : {ω : Environment |
      (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + t ≤ lastPassage ω u (a, b)} ⊆
      ⋃ h, E h := by
    intro ω hω
    change (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + t ≤ lastPassage ω u (a, b) at hω
    rw [lastPassage_eq_max_sliceAllocation ω u a b] at hω
    obtain ⟨h, _, hh⟩ := Finset.mem_image.mp (Finset.max'_mem
      (Finset.univ.image (fun h : SliceAllocation a b => h.weight ω u))
      (Finset.Nonempty.image Finset.univ_nonempty _))
    apply Set.mem_iUnion.mpr
    exact ⟨h, by simpa only [E, Set.mem_ofPred_eq, hh] using hω⟩
  calc
    _ ≤ (environmentLaw μ).real (⋃ h, E h) := measureReal_mono hsub
    _ ≤ (Fintype.card (SliceAllocation a b) : ℝ) *
        Real.exp (-t ^ 2 / (64 * (a + b : ℕ) * L ^ 2) + 64) :=
      measureReal_iUnion_le_card_mul _ E _ fun h =>
        h.measure_weight_ge_le_martin μ u hL ht hab hμ
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast sliceAllocation_card_le_choose a b) (Real.exp_pos _).le

/-- Exact finite integer-ray tail, with Martin's constants and signed actual mean. -/
theorem measure_lastPassage_nat_ray_ge_le_martin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b n : ℕ)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (hab : 0 < a + b) (hn : 0 < n)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    (environmentLaw μ).real {ω : Environment |
      (n : ℝ) * ((b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + ε) ≤
        lastPassage ω 0 (n * a, n * b)} ≤
      (Nat.choose (n * (a + b)) (n * a) : ℝ) *
        Real.exp (64 - n * ε ^ 2 / (64 * (a + b : ℕ) * L ^ 2)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have habr : (0 : ℝ) < (a + b : ℕ) := by exact_mod_cast hab
  have h := measure_lastPassage_ge_le_choose_mul_exp μ 0 (n * a) (n * b)
    hL (mul_pos hnr hε) (by simpa only [Nat.mul_add] using Nat.mul_pos hn hab) hμ
  have he : -(n * ε) ^ 2 / (64 * (n * a + n * b : ℕ) * L ^ 2) + 64 =
      64 - n * ε ^ 2 / (64 * (a + b : ℕ) * L ^ 2) := by
    push_cast
    field_simp
    ring
  have ht : (n * b : ℕ) * (∫ x : ℝ, x ∂μ) + (n * a : ℕ) * L + n * ε =
      (n : ℝ) * ((b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + ε) := by
    push_cast
    ring
  rw [he, ht, ← Nat.mul_add] at h
  exact h

end LPPDifferentiability
