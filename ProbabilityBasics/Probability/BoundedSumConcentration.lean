/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concentration of a bounded independent sum

This proves the singleton case of Martin (2004), Lemma 3.1, with its constants.
It makes no assertion about maxima over several subsets.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace LPPDifferentiability

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An almost surely bounded real random variable is integrable. -/
theorem integrable_of_ae_abs_le [IsProbabilityMeasure μ] {Y : Ω → ℝ} {L : ℝ}
    (hm : Measurable Y) (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ L) : Integrable Y μ := by
  refine (integrable_const L).mono' hm.aestronglyMeasurable ?_
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using hω

/-- Centering a variable in `[-L,L]` gives MGF parameter exactly `L²`. -/
theorem hasSubgaussianMGF_centered_of_ae_abs_le [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {L : ℝ} (hL : 0 ≤ L) (hm : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ L) :
    HasSubgaussianMGF (fun ω => Y ω - ∫ x, Y x ∂μ) (NNReal.mk (L ^ 2) (sq_nonneg L)) μ := by
  have hi : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-L) L := by
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have h := hasSubgaussianMGF_of_mem_Icc hm.aemeasurable hi
  have heq : ((‖L - -L‖₊ / 2) ^ (2 : ℕ) : ℝ≥0) = NNReal.mk (L ^ 2) (sq_nonneg L) := by
    apply NNReal.eq
    change (|L - -L| / 2) ^ (2 : ℕ) = L ^ 2
    rw [abs_of_nonneg (by linarith : 0 ≤ L - -L)]
    ring
  rwa [heq] at h

/-- The two tails of a centered sub-Gaussian variable give an absolute tail bound. -/
theorem measure_abs_ge_le_of_hasSubgaussianMGF {Y : Ω → ℝ} {c : ℝ≥0}
    [IsProbabilityMeasure μ] (h : HasSubgaussianMGF Y c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |Y ω|} ≤ 2 * exp (-u ^ 2 / (2 * c)) := by
  have hs : {ω | u ≤ |Y ω|} = {ω | u ≤ Y ω} ∪ {ω | u ≤ -Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hs]
  calc
    _ ≤ μ.real {ω | u ≤ Y ω} + μ.real {ω | u ≤ -Y ω} := measureReal_union_le _ _
    _ ≤ exp (-u ^ 2 / (2 * c)) + exp (-u ^ 2 / (2 * c)) :=
      add_le_add (h.measure_ge_le hu) (h.neg.measure_ge_le hu)
    _ = _ := by ring

/-- Hoeffding's two-sided estimate, with centering and integrability produced here. -/
theorem measure_abs_sum_sub_integral_ge_le [Fintype ι] [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) {L u : ℝ} (hL : 0 ≤ L) (hu : 0 ≤ u)
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ L) :
    μ.real {ω | u ≤ |(∑ i, Y i ω) - ∫ x, ∑ i, Y i x ∂μ|} ≤
      2 * exp (-u ^ 2 / (2 * Fintype.card ι * L ^ 2)) := by
  classical
  have hint : ∀ i, Integrable (Y i) μ := fun i => integrable_of_ae_abs_le (hm i) (hb i)
  have hc : iIndepFun (fun i ω => Y i ω - ∫ x, Y i x ∂μ) μ :=
    hind.comp (fun i x => x - ∫ ω, Y i ω ∂μ) (fun _ => by fun_prop)
  have hg := HasSubgaussianMGF.sum_of_iIndepFun hc
    (s := Finset.univ) (c := fun _ => NNReal.mk (L ^ 2) (sq_nonneg L))
    (fun i _ => hasSubgaussianMGF_centered_of_ae_abs_le hL (hm i) (hb i))
  have heq : (fun ω => ∑ i, (Y i ω - ∫ x, Y i x ∂μ)) =
      (fun ω => (∑ i, Y i ω) - ∫ x, ∑ i, Y i x ∂μ) := by
    funext ω
    rw [Finset.sum_sub_distrib, integral_finsetSum _ (fun i _ => hint i)]
  rw [heq] at hg
  have hparameter : (∑ _i : ι, NNReal.mk (L ^ 2) (sq_nonneg L)) =
      Fintype.card ι • NNReal.mk (L ^ 2) (sq_nonneg L) := by
    rw [Finset.sum_const, Finset.card_univ]
  rw [hparameter] at hg
  have htail := measure_abs_ge_le_of_hasSubgaussianMGF hg hu
  rw [NNReal.coe_nsmul, NNReal.coe_mk, nsmul_eq_mul] at htail
  simpa only [mul_assoc] using htail

/-- The exact singleton specialization of Martin (2004), Lemma 3.1, retaining constants 64. -/
theorem measure_abs_sum_sub_integral_ge_le_martin [Fintype ι] [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) {L u : ℝ} (hL : 0 < L) (hu : 0 < u)
    (hN : 0 < Fintype.card ι) (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ L) :
    μ.real {ω | u ≤ |(∑ i, Y i ω) - ∫ x, ∑ i, Y i x ∂μ|} ≤
      exp (-u ^ 2 / (64 * Fintype.card ι * L ^ 2) + 64) := by
  have hbase := measure_abs_sum_sub_integral_ge_le Y hL.le hu.le hm hind hb
  have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hD : 0 < (Fintype.card ι : ℝ) * L ^ 2 := mul_pos hNr (sq_pos_of_pos hL)
  have hcmp : -u ^ 2 / (2 * Fintype.card ι * L ^ 2) ≤
      -u ^ 2 / (64 * Fintype.card ι * L ^ 2) := by
    have hn := sq_nonneg u
    field_simp
    nlinarith
  have htwo : (2 : ℝ) ≤ exp 64 := by
    have := Real.add_one_le_exp (64 : ℝ)
    linarith
  calc
    _ ≤ 2 * exp (-u ^ 2 / (2 * Fintype.card ι * L ^ 2)) := hbase
    _ ≤ exp 64 * exp (-u ^ 2 / (64 * Fintype.card ι * L ^ 2)) :=
      mul_le_mul htwo (exp_le_exp.mpr hcmp) (exp_pos _).le (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

/-- An empty family has no positive centered deviation. -/
theorem measure_abs_sum_sub_integral_ge_eq_zero_of_card_eq_zero
    [Fintype ι] [IsProbabilityMeasure μ] (Y : ι → Ω → ℝ) {u : ℝ}
    (hu : 0 < u) (hN : Fintype.card ι = 0) :
    μ.real {ω | u ≤ |(∑ i, Y i ω) - ∫ x, ∑ i, Y i x ∂μ|} = 0 := by
  have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hN
  simp [not_le.mpr hu]

/-- Zero bounds force zero sums almost surely, including the empty family. -/
theorem measure_abs_sum_sub_integral_ge_eq_zero_of_bound_zero
    [Fintype ι] [IsProbabilityMeasure μ] (Y : ι → Ω → ℝ) {u : ℝ}
    (hu : 0 < u) (hb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 0) :
    μ.real {ω | u ≤ |(∑ i, Y i ω) - ∫ x, ∑ i, Y i x ∂μ|} = 0 := by
  have hz : ∀ᵐ ω ∂μ, ∀ i, Y i ω = 0 := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hb i] with ω hω using abs_eq_zero.mp (le_antisymm hω (abs_nonneg _))
  have hs : (fun ω => ∑ i, Y i ω) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hz] with ω hω
    simp [hω]
  have hi : (∫ x, ∑ i, Y i x ∂μ) = 0 := by rw [integral_congr_ae hs]; simp
  have he : {ω | u ≤ |(∑ i, Y i ω) - ∫ x, ∑ i, Y i x ∂μ|} =ᵐ[μ] ∅ := by
    filter_upwards [hs] with ω hω
    simp [hi, hω, not_le.mpr hu]
  rw [measureReal_congr he]
  simp

end LPPDifferentiability
