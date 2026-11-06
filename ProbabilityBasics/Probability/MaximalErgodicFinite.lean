/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.InvariantIterates
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import ProbabilityBasics.Analysis.PositiveStrings
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# The bounded finite-horizon maximal ergodic inequality

Keane and Petersen (2006), pp. 248–249: apply the finite positive-string
estimate on each orbit, integrate, and remove the terminal string cost by
increasing the averaging length. This module proves only the bounded
finite-horizon step, for an integrable invariant threshold.
-/

public section

open MeasureTheory Finset Set

namespace LPPDifferentiability

/-- Some average with length between one and `N` exceeds the threshold. -/
@[expose] def finiteMaximalEvent {Ω : Type*} (T : Ω → Ω) (f threshold : Ω → ℝ)
    (N : ℕ) : Set Ω :=
  {ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ threshold ω < (∑ j ∈ range k, f ((T^[j]) ω)) / (k : ℝ)}

/-- A finite-horizon threshold event is measurable. -/
theorem measurableSet_finiteMaximalEvent {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {f threshold : Ω → ℝ} (hT : Measurable T) (hf : Measurable f)
    (hthreshold : Measurable threshold) (N : ℕ) : MeasurableSet (finiteMaximalEvent T f threshold N) := by
  simp only [finiteMaximalEvent, ← exists_prop, ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro _
  exact measurableSet_lt hthreshold ((Finset.measurable_sum _ fun j _ => hf.comp (hT.iterate j)).div_const _)

private theorem orbit_string_bound {Ω : Type*} {T : Ω → Ω} {f threshold : Ω → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M) {N : ℕ} (hN : 1 ≤ N)
    (ω : Ω) (hω : ∀ i : ℕ, threshold ((T^[i]) ω) = threshold ω) (m : ℕ) :
    -(N : ℝ) * (M + max (threshold ω) 0) ≤
      ∑ i ∈ range m, (finiteMaximalEvent T f threshold N).indicator
        (fun x => f x - threshold x) ((T^[i]) ω) := by
  classical
  let a : ℕ → ℝ := fun i => f ((T^[i]) ω) - threshold ω
  have hC : 0 ≤ M + max (threshold ω) 0 := add_nonneg hM (le_max_right _ _)
  have ha (i : ℕ) : -(M + max (threshold ω) 0) ≤ a i := by
    have hi := (abs_le.mp (hf ((T^[i]) ω))).1
    have hl := le_max_left (threshold ω) 0
    dsimp only [a]
    linarith only [hi, hl]
  have hevent (i : ℕ) : positive_string a N i ↔ (T^[i]) ω ∈ finiteMaximalEvent T f threshold N := by
    unfold positive_string finiteMaximalEvent
    simp only [mem_ofPred_eq]
    apply exists_congr
    intro k
    apply and_congr_right
    intro hk
    apply and_congr_right
    intro _
    have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hsum : (∑ j ∈ range k, a (i + j)) =
        (∑ j ∈ range k, f ((T^[j]) ((T^[i]) ω))) - (k : ℝ) * threshold ((T^[i]) ω) := by
      simp only [a, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hω i]
      congr 1
      apply sum_congr rfl
      intro j _
      rw [Nat.add_comm i j, Function.iterate_add_apply]
    rw [hsum, lt_div_iff₀ hkreal, mul_comm (threshold _) (k : ℝ)]
    exact sub_pos
  have hterm (i : ℕ) : positiveStringTerm a N i =
      (finiteMaximalEvent T f threshold N).indicator (fun x => f x - threshold x) ((T^[i]) ω) := by
    simp only [positiveStringTerm, Set.indicator_apply, hevent, a, hω i]
  have h := neg_mul_le_sum_positiveStringTerm a N hN (M + max (threshold ω) 0) hC ha m 0
  simpa only [Nat.zero_add, hterm] using h

/-- The bounded finite-horizon maximal inequality. The threshold is integrable
and invariant almost everywhere. Boundedness and measurability supply all
integrability premises used in the proof. -/
theorem integral_finiteMaximalEvent_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f threshold : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Measurable f) (hthreshold : Measurable threshold)
    (hthresholdint : Integrable threshold μ) (hthresholdinv : ∀ᵐ ω ∂μ, threshold (T ω) = threshold ω)
    {M : ℝ} (hM : 0 ≤ M) (hfbound : ∀ ω, |f ω| ≤ M) (N : ℕ) :
    0 ≤ ∫ ω in finiteMaximalEvent T f threshold N, (f ω - threshold ω) ∂μ := by
  classical
  by_cases hN : 1 ≤ N
  · have hE := measurableSet_finiteMaximalEvent hT.measurable hf hthreshold N
    let q := (finiteMaximalEvent T f threshold N).indicator (fun ω => f ω - threshold ω)
    have hfint : Integrable f μ :=
      (integrable_const M).mono' hf.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hfbound ω)
    have hq : Integrable q μ := (hfint.sub hthresholdint).indicator hE
    have hqmeas : Measurable q := (hf.sub hthreshold).indicator hE
    have hcost : Integrable (fun ω => -(N : ℝ) * (M + max (threshold ω) 0)) μ :=
      ((integrable_const M).add hthresholdint.pos_part).const_mul _
    have hsumint (m : ℕ) : Integrable (fun ω => ∑ i ∈ range m, q ((T^[i]) ω)) μ :=
      integrable_finsetSum _ fun i _ => (hT.iterate i).integrable_comp_of_integrable hq
    have hcomp (i : ℕ) : (∫ ω, q ((T^[i]) ω) ∂μ) = ∫ ω, q ω ∂μ := by
      have h := integral_map_of_stronglyMeasurable (μ := μ) (hT.iterate i).measurable hqmeas.stronglyMeasurable
      rw [(hT.iterate i).map_eq] at h
      exact h.symm
    have hbound (m : ℕ) :
        -(N : ℝ) * (M + ∫ ω, max (threshold ω) 0 ∂μ) ≤ (m : ℝ) * ∫ ω, q ω ∂μ := by
      have hpoint : ∀ᵐ ω ∂μ, -(N : ℝ) * (M + max (threshold ω) 0) ≤
          ∑ i ∈ range m, q ((T^[i]) ω) := by
        filter_upwards [ae_all_iterate_eq_of_ae_invariant hT hthresholdinv] with ω hω
        exact orbit_string_bound hM hfbound hN ω hω m
      have h := integral_mono_ae hcost (hsumint m) hpoint
      rw [integral_finsetSum (range m) (f := fun i ω => q ((T^[i]) ω))
        (fun i _ => (hT.iterate i).integrable_comp_of_integrable hq)] at h
      simpa only [integral_const_mul, integral_add (integrable_const M) hthresholdint.pos_part,
        integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
        hcomp, sum_const, card_range, nsmul_eq_mul] using h
    have hnonneg : 0 ≤ ∫ ω, q ω ∂μ := by
      by_contra hn
      have hneg : 0 < -(∫ ω, q ω ∂μ) := neg_pos.mpr (lt_of_not_ge hn)
      obtain ⟨m, hm⟩ := exists_nat_gt
        (((N : ℝ) * (M + ∫ ω, max (threshold ω) 0 ∂μ)) / (-(∫ ω, q ω ∂μ)))
      have hm' := (div_lt_iff₀ hneg).mp hm
      have hb := hbound m
      nlinarith only [hm', hb]
    simpa only [q, integral_indicator hE] using hnonneg
  · have hzero : N = 0 := by omega
    subst N
    have hE : finiteMaximalEvent T f threshold 0 = ∅ := by
      ext ω
      simp only [finiteMaximalEvent, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨k, hk, hk0, _⟩
      omega
    rw [hE, setIntegral_empty]

end LPPDifferentiability
