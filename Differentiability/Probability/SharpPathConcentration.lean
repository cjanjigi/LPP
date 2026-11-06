/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BoundedPathConcentration
public import LPP_Foundations.Probability.PassageIntegrable
import Mathlib.Tactic.Linarith

/-!
# The sharp lower tail of a deterministic path

The terminal-excluded collected coordinates of a path are independent.
Hoeffding's lemma on the interval `[-M,M]` gives parameter `M²` per coordinate.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace LPPDifferentiability

/-- The one-sided Hoeffding bound, centered at the mean of the i.i.d. path weight. -/
theorem measure_pathWeight_lt_mean_sub_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M t : ℝ} (hM : 0 < M) (ht : 0 < t)
    (hb : ∀ᵐ x ∂μ, |x| ≤ M) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    (environmentLaw μ).real {ω : Environment |
      pathWeight ω p < (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ - t} ≤
        exp (-t ^ 2 / (2 * (d.1 + d.2 : ℕ) * M ^ 2)) := by
  classical
  let Y : Fin (d.1 + d.2) → Environment → ℝ :=
    fun i ω => ω (p.vertex i.castSucc)
  have hm (i : Fin (d.1 + d.2)) : Measurable (Y i) := measurable_environment_eval _
  have hbound (i : Fin (d.1 + d.2)) : ∀ᵐ ω ∂environmentLaw μ, |Y i ω| ≤ M :=
    ae_abs_path_collected_eval_le μ hb p i
  have hind : iIndepFun Y (environmentLaw μ) := iIndepFun_path_collected_eval μ p
  have hc : iIndepFun (fun i ω => Y i ω - ∫ x, Y i x ∂environmentLaw μ)
      (environmentLaw μ) :=
    hind.comp (fun i x => x - ∫ ω, Y i ω ∂environmentLaw μ) (fun _ => by fun_prop)
  have hg := HasSubgaussianMGF.sum_of_iIndepFun hc
    (s := Finset.univ) (c := fun _ => NNReal.mk (M ^ 2) (sq_nonneg M))
    (fun i _ => hasSubgaussianMGF_centered_of_ae_abs_le hM.le (hm i) (hbound i))
  have hi : Integrable (fun x : ℝ => x) μ :=
    integrable_of_ae_abs_le measurable_id hb
  have heq : (fun ω => ∑ i, (Y i ω - ∫ x, Y i x ∂environmentLaw μ)) =
      (fun ω => pathWeight ω p - (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ) := by
    funext ω
    rw [Finset.sum_sub_distrib]
    change pathWeight ω p - ∑ i : Fin (d.1 + d.2),
      (∫ x : Environment, x (p.vertex i.castSucc) ∂environmentLaw μ) = _
    simp only [integral_environment_eval μ hi, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [heq] at hg
  have hparameter : (∑ _i : Fin (d.1 + d.2), NNReal.mk (M ^ 2) (sq_nonneg M)) =
      (d.1 + d.2) • NNReal.mk (M ^ 2) (sq_nonneg M) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hparameter] at hg
  have htail := hg.neg.measure_ge_le ht.le
  rw [NNReal.coe_nsmul, NNReal.coe_mk, nsmul_eq_mul] at htail
  calc
    _ ≤ (environmentLaw μ).real {ω : Environment |
        t ≤ -(pathWeight ω p - (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ)} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith only [hω]
    _ ≤ _ := by simpa only [Pi.neg_apply, mul_assoc] using htail

/-- A zero-length path has an empty strict lower-tail event at positive distance. -/
theorem measure_pathWeight_lt_mean_sub_eq_zero_of_length_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (hd : d.1 + d.2 = 0) :
    (environmentLaw μ).real {ω : Environment |
      pathWeight ω p < (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ - t} = 0 := by
  have hz (ω : Environment) : pathWeight ω p = 0 := by
    simp only [pathWeight]
    have : IsEmpty (Fin (d.1 + d.2)) := by rw [hd]; infer_instance
    exact Finset.sum_eq_zero (fun i _ => isEmptyElim i)
  have he : {ω : Environment |
      pathWeight ω p < (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ - t} = ∅ := by
    ext ω
    simp only [hz, hd, Nat.cast_zero, zero_mul, zero_sub, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_lt]
    exact neg_nonpos.mpr ht.le
  rw [he, measureReal_empty]

/-- A zero marginal bound makes every fixed path identically zero almost surely. -/
theorem measure_pathWeight_lt_mean_sub_eq_zero_of_bound_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hb : ∀ᵐ x ∂μ, |x| ≤ 0) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    (environmentLaw μ).real {ω : Environment |
      pathWeight ω p < (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ - t} = 0 := by
  have hi : Integrable (fun x : ℝ => x) μ :=
    integrable_of_ae_abs_le measurable_id hb
  have htail := measure_abs_pathWeight_sub_integral_ge_eq_zero_of_bound_zero μ ht hb p
  rw [integral_pathWeight μ hi p] at htail
  apply le_antisymm (le_trans ?_ htail.le) (measureReal_nonneg)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hneg := neg_le_abs (pathWeight ω p - (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ)
  linarith only [hω, hneg]

end LPPDifferentiability
