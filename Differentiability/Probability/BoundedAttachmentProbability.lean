/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.SharpPathConcentration
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The bounded deterministic attachment family

One fixed finite family is used throughout the good event. Different attachment
paths may overlap; only the one-path Hoeffding estimate and a union bound enter.
-/

public section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology

namespace LPPDifferentiability

/-- The exact source constant `32` after substituting the attachment tolerance. -/
theorem measure_attachment_path_bad_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M η s : ℝ}
    (hM : 0 < M) (hη : 0 < η) (hs : 0 < s)
    (hb : ∀ᵐ x ∂μ, |x| ≤ M) {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (hd : 0 < d.1 + d.2) (hds : ((d.1 + d.2 : ℕ) : ℝ) ≤ s) :
    (environmentLaw μ).real {ω : Environment |
      pathWeight ω p < (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ - η * s / 4} ≤
        exp (-η ^ 2 * s / (32 * M ^ 2)) := by
  have hdr : (0 : ℝ) < (d.1 + d.2 : ℕ) := by exact_mod_cast hd
  have htail := measure_pathWeight_lt_mean_sub_le μ hM (by positivity : 0 < η * s / 4) hb p
  apply htail.trans
  apply exp_le_exp.mpr
  have hden : 2 * ((d.1 + d.2 : ℕ) : ℝ) * M ^ 2 ≤ 2 * s * M ^ 2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hds (by norm_num))
      (sq_nonneg M)
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (η * s / 4))
    (by positivity : 0 < 2 * ((d.1 + d.2 : ℕ) : ℝ) * M ^ 2) hden
  calc
    -(η * s / 4) ^ 2 / (2 * ((d.1 + d.2 : ℕ) : ℝ) * M ^ 2) ≤
        -(η * s / 4) ^ 2 / (2 * s * M ^ 2) := by
      simpa only [neg_div] using neg_le_neg hdiv
    _ = -η ^ 2 * s / (32 * M ^ 2) := by
      field_simp [ne_of_gt hs, ne_of_gt hM]
      ring

/-- The all-attachments event is measurable for any one actual deterministic family. -/
theorem measurableSet_all_attachment_paths
    {J : Type*} [Fintype J] (u : J → Lattice) (d : J → ℕ × ℕ)
    (p : (j : J) → Path (u j) (d j)) (a : J → ℝ) :
    MeasurableSet {ω : Environment | ∀ j, a j ≤ pathWeight ω (p j)} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pathWeight (p j))

/-- The original-space finite-family bound from the bounded attachment argument. -/
theorem bounded_attachment_family_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {J : Type*} [Fintype J] (u : J → Lattice) (d : J → ℕ × ℕ)
    (p : (j : J) → Path (u j) (d j)) (m : ℕ)
    (hm : ∀ j, (d j).1 + (d j).2 = m)
    {D M η s : ℝ} (hD : 1 ≤ D) (hM : 0 < M) (hη : 0 < η) (hs : 0 < s)
    (hb : ∀ᵐ x ∂μ, |x| ≤ M) (hm0 : 0 < m) (hms : (m : ℝ) ≤ s)
    (hcard : (Fintype.card J : ℝ) ≤ 2 * D * s + 2) :
    MeasurableSet {ω : Environment | ∀ j,
      (m : ℝ) * ∫ x : ℝ, x ∂μ - η * s / 4 ≤ pathWeight ω (p j)} ∧
    max 0 (1 - (2 * D * s + 2) * exp (-η ^ 2 * s / (32 * M ^ 2))) ≤
      (environmentLaw μ).real {ω : Environment | ∀ j,
        (m : ℝ) * ∫ x : ℝ, x ∂μ - η * s / 4 ≤ pathWeight ω (p j)} := by
  classical
  let E : Set Environment := {ω | ∀ j,
    (m : ℝ) * ∫ x : ℝ, x ∂μ - η * s / 4 ≤ pathWeight ω (p j)}
  have hmE : MeasurableSet E := measurableSet_all_attachment_paths u d p _
  refine ⟨hmE, ?_⟩
  have hbad (j : J) : (environmentLaw μ).real
      {ω : Environment | pathWeight ω (p j) <
        (m : ℝ) * ∫ x : ℝ, x ∂μ - η * s / 4} ≤ exp (-η ^ 2 * s / (32 * M ^ 2)) := by
    have hd0 : 0 < (d j).1 + (d j).2 := by rw [hm j]; exact hm0
    have hds : (((d j).1 + (d j).2 : ℕ) : ℝ) ≤ s := by rw [hm j]; exact hms
    simpa only [hm j] using measure_attachment_path_bad_le μ hM hη hs hb (p j) hd0 hds
  have hcomp : Eᶜ = ⋃ j : J, {ω : Environment | pathWeight ω (p j) <
      (m : ℝ) * ∫ x : ℝ, x ∂μ - η * s / 4} := by
    ext ω
    simp only [E, mem_compl_iff, mem_ofPred_eq, not_forall, not_le, mem_iUnion]
  have hcompBound : (environmentLaw μ).real Eᶜ ≤
      (2 * D * s + 2) * exp (-η ^ 2 * s / (32 * M ^ 2)) := by
    rw [hcomp]
    calc
      _ ≤ ∑ j : J, (environmentLaw μ).real {ω : Environment | pathWeight ω (p j) <
          (m : ℝ) * ∫ x : ℝ, x ∂μ - η * s / 4} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : J, exp (-η ^ 2 * s / (32 * M ^ 2)) :=
        Finset.sum_le_sum fun j _ => hbad j
      _ = (Fintype.card J : ℝ) * exp (-η ^ 2 * s / (32 * M ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (exp_pos _).le
  rw [probReal_compl_eq_one_sub hmE] at hcompBound
  have hDnonneg : 0 ≤ D := zero_le_one.trans hD
  have hcoeff : 0 ≤ 2 * D * s + 2 := by positivity
  exact max_le measureReal_nonneg (by linarith only [hcompBound, hcoeff])

/-- The explicit lower bound is a probability value at positive scales. -/
theorem bounded_attachment_lower_bound_mem_Icc
    {D M η s : ℝ} (hD : 1 ≤ D) (hs : 0 ≤ s) :
    max 0 (1 - (2 * D * s + 2) * exp (-η ^ 2 * s / (32 * M ^ 2))) ∈ Icc (0 : ℝ) 1 := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hnonneg : 0 ≤ (2 * D * s + 2) * exp (-η ^ 2 * s / (32 * M ^ 2)) := by positivity
  exact ⟨le_max_left _ _, max_le zero_le_one (by linarith only [hnonneg])⟩

/-- Polynomially many bounded attachments retain a probability tending to one. -/
theorem tendsto_bounded_attachment_lower_bound (D : ℝ) {M η : ℝ}
    (hM : 0 < M) (hη : 0 < η) :
    Tendsto (fun s : ℝ => max 0
      (1 - (2 * D * s + 2) * exp (-η ^ 2 * s / (32 * M ^ 2)))) atTop (𝓝 1) := by
  let c : ℝ := η ^ 2 / (32 * M ^ 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have h0 : Tendsto (fun s : ℝ => exp (-c * s)) atTop (𝓝 0) := by
    simpa only [rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  have h1 : Tendsto (fun s : ℝ => s * exp (-c * s)) atTop (𝓝 0) := by
    simpa only [rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
  have hdecay : Tendsto (fun s : ℝ =>
      (2 * D * s + 2) * exp (-η ^ 2 * s / (32 * M ^ 2))) atTop (𝓝 0) := by
    have he : ∀ s : ℝ, -η ^ 2 * s / (32 * M ^ 2) = -c * s := by
      intro s
      dsimp only [c]
      ring
    have h := (h1.const_mul (2 * D)).add (h0.const_mul 2)
    simp only [mul_zero, add_zero] at h
    apply h.congr
    intro s
    rw [he]
    ring
  have h : Tendsto (fun s : ℝ => max 0
      (1 - (2 * D * s + 2) * exp (-η ^ 2 * s / (32 * M ^ 2)))) atTop
      (𝓝 (max (0 : ℝ) (1 - (0 : ℝ)))) :=
    tendsto_const_nhds.max (tendsto_const_nhds.sub hdecay)
  simpa only [sub_zero, max_eq_right zero_le_one] using h

end LPPDifferentiability
