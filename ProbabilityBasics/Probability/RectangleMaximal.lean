/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Probability.RectangleMaximalBox
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-! The finite weak maximal bound for signed rectangle averages. -/

public section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace ProbabilityBasics

/-- Krengel's finite maximal inequality for signed rectangular averages,
proved by finite covering and boundary enlargement (Section 6.2, Corollary 2.7). -/
theorem finite_rectangle_maximal_weak_one_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i)
    (N : ℕ) (t : ℝ) (ht : 0 < t) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    μ.real {s | ∃ n ∈ Finset.Icc 1 N,
      t * ((R n).card : ℝ) < ∑ v ∈ R n, |f (T v s)|} ≤
      (4 / t) * ∫ s, |f s| ∂μ := by
  classical
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let E : Set Ω := {s | ∃ n ∈ Finset.Icc 1 N,
    t * ((R n).card : ℝ) < ∑ v ∈ R n, |f (T v s)|}
  let hfAES : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  let g : Ω → ℝ := hfAES.mk f
  let Eg : Set Ω := {s | ∃ n ∈ Finset.Icc 1 N,
    t * ((R n).card : ℝ) < ∑ v ∈ R n, |g (T v s)|}
  let M : ℕ := max ⌊(N : ℝ) * b 0⌋₊ ⌊(N : ℝ) * b 1⌋₊
  let I : ℝ := ∫ s, |f s| ∂μ
  change μ.real E ≤ (4 / t) * I

  have hgMeas : Measurable g := hfAES.measurable_mk
  have hfg : f =ᵐ[μ] g := hfAES.ae_eq_mk
  have hgInt : Integrable g μ := hf.congr hfg
  have hall : ∀ᵐ s ∂μ, ∀ v : ℤ × ℤ, f (T v s) = g (T v s) := by
    rw [ae_all_iff]
    intro v
    have hcomp := (hT v).quasiMeasurePreserving.ae_eq_comp hfg
    filter_upwards [hcomp] with s hs
    simpa only [Function.comp_apply] using hs
  have hsum (s : Ω) (hs : ∀ v : ℤ × ℤ, f (T v s) = g (T v s))
      (n : ℕ) :
      (∑ v ∈ R n, |f (T v s)|) = ∑ v ∈ R n, |g (T v s)| := by
    apply Finset.sum_congr rfl
    intro v hv
    simp only [hs v]
  have hEvent (s : Ω) (hs : ∀ v : ℤ × ℤ, f (T v s) = g (T v s)) :
      s ∈ E ↔ s ∈ Eg := by
    simp only [E, Eg, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, hstrict⟩
      exact ⟨n, hn, (hsum s hs n) ▸ hstrict⟩
    · rintro ⟨n, hn, hstrict⟩
      exact ⟨n, hn, (hsum s hs n).symm ▸ hstrict⟩
  have hEeq : E =ᵐ[μ] Eg := by
    filter_upwards [hall] with s hs
    exact propext (hEvent s hs)
  have hMeasureE : μ.real E = μ.real Eg := MeasureTheory.measureReal_congr hEeq
  have hAbsInt : (∫ s, |g s| ∂μ) = I := by
    dsimp [I]
    apply integral_congr_ae
    filter_upwards [hfg] with s hs
    exact (congrArg abs hs).symm

  have hbox (m : ℕ) :
      t * (m : ℝ)^2 * μ.real E ≤
        4 * (((m + M : ℕ) : ℝ)^2) * I := by
    have hraw := finite_rectangle_box_integral_of_measurable
      μ T hzero hadd hT g hgMeas hgInt b hb N m t ht
    change t * (m : ℝ)^2 * μ.real Eg ≤
      4 * (((m + M : ℕ) : ℝ)^2) * (∫ s, |g s| ∂μ) at hraw
    rw [hMeasureE.symm, hAbsInt] at hraw
    exact hraw

  have hdiv (m : ℕ) (hm : 0 < m) :
      t * μ.real E ≤
        4 * ((((m + M : ℕ) : ℝ) / (m : ℝ))^2) * I := by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hsq : 0 < (m : ℝ)^2 := sq_pos_of_pos hmR
    have hquot := (div_le_div_iff₀ hsq hsq).2
      (mul_le_mul_of_nonneg_right (hbox m) hsq.le)
    have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmR
    have hleft :
        (t * (m : ℝ)^2 * μ.real E) / (m : ℝ)^2 = t * μ.real E := by
      field_simp [hmNe]
    have hright :
        (4 * (((m + M : ℕ) : ℝ)^2) * I) / (m : ℝ)^2 =
          4 * ((((m + M : ℕ) : ℝ) / (m : ℝ))^2) * I := by
      push_cast
      field_simp [hmNe]
    rw [hleft, hright] at hquot
    exact hquot

  have hMdiv : Tendsto (fun m : ℕ => (M : ℝ) / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (M : ℝ)
  have hratioAdd :
      Tendsto (fun m : ℕ => 1 + (M : ℝ) / (m : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hMdiv
  let q : ℕ → ℝ := fun m => ((m + M : ℕ) : ℝ) / (m : ℝ)
  have hratio : Tendsto q atTop (𝓝 1) := by
    refine hratioAdd.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    dsimp [q]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    push_cast
    field_simp [hmR]
  have hratioSq : Tendsto (fun m : ℕ => q m ^ 2) atTop (𝓝 1) := by
    simpa using hratio.pow 2
  have hRhs : Tendsto (fun m : ℕ => 4 * q m ^ 2 * I) atTop (𝓝 (4 * I)) := by
    simpa using (tendsto_const_nhds.mul hratioSq).mul_const I
  have hEventually :
      (fun _ : ℕ => t * μ.real E) ≤ᶠ[atTop] fun m => 4 * q m ^ 2 * I := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    simpa [q] using hdiv m hm
  have hLimit := le_of_tendsto_of_tendsto tendsto_const_nhds hRhs hEventually
  have hScaled : μ.real E ≤ (4 / t) * I := by
    have hmul : μ.real E * t ≤ 4 * I := by
      calc
        μ.real E * t = t * μ.real E := by ring
        _ ≤ 4 * I := hLimit
    calc
      μ.real E ≤ (4 * I) / t := (le_div_iff₀ ht).2 hmul
      _ = (4 / t) * I := by ring
  exact hScaled

end ProbabilityBasics
