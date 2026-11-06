/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Closed finite-coordinate events from increasing continuous tests

This file proves the finite-event part of the extension of the order between measures, following
Liggett (1985), equation (2.14). The thresholds are closed, so atoms on the boundary are kept.
The laws are probability measures on real sequences.
-/

public section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction BigOperators

namespace LPPDifferentiability

/-- Continuous increasing approximation from above to a closed upper threshold. -/
@[expose] def closedUpperCutoff (m : ℕ) (a x : ℝ) : ℝ :=
  min 1 (max 0 (1 + (m : ℝ) * (x - a)))

theorem closedUpperCutoff_nonneg (m : ℕ) (a x : ℝ) :
    0 ≤ closedUpperCutoff m a x :=
  le_min zero_le_one (le_max_left _ _)

theorem closedUpperCutoff_le_one (m : ℕ) (a x : ℝ) :
    closedUpperCutoff m a x ≤ 1 := min_le_left _ _

theorem closedUpperCutoff_eq_one {m : ℕ} {a x : ℝ} (h : a ≤ x) :
    closedUpperCutoff m a x = 1 := by
  apply min_eq_left
  exact le_trans (by nlinarith [Nat.cast_nonneg (α := ℝ) m]) (le_max_right _ _)

private theorem continuous_closedUpperCutoff (m : ℕ) (a : ℝ) :
    Continuous (closedUpperCutoff m a) := by
  unfold closedUpperCutoff
  fun_prop

private theorem monotone_closedUpperCutoff (m : ℕ) (a : ℝ) :
    Monotone (closedUpperCutoff m a) := by
  intro x y hxy
  exact min_le_min le_rfl (max_le_max le_rfl (by gcongr))

private theorem tendsto_closedUpperCutoff (a x : ℝ) :
    Tendsto (fun m => closedUpperCutoff m a x) atTop
      (𝓝 (if a ≤ x then (1 : ℝ) else 0)) := by
  by_cases h : a ≤ x
  · simpa only [ite_eq_left h, closedUpperCutoff_eq_one h] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · have hax : 0 < a - x := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / (a - x))
    have hM' : 1 < (M : ℝ) * (a - x) := (div_lt_iff₀ hax).mp hM
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop M] with m hm
    have hMm : (M : ℝ) ≤ m := by exact_mod_cast hm
    have hzero : 1 + (m : ℝ) * (x - a) ≤ 0 := by nlinarith
    simp only [ite_eq_right h, closedUpperCutoff, max_eq_left hzero, min_eq_right zero_le_one]

private def orthantApprox {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (m : ℕ)
    (x : Fin n → ℝ) : ℝ := ∏ i ∈ S, closedUpperCutoff m (a i) (x i)

private theorem orthantApprox_nonneg {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ)
    (m : ℕ) (x : Fin n → ℝ) : 0 ≤ orthantApprox S a m x :=
  Finset.prod_nonneg fun _ _ => closedUpperCutoff_nonneg _ _ _

private theorem orthantApprox_le_one {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ)
    (m : ℕ) (x : Fin n → ℝ) : orthantApprox S a m x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => closedUpperCutoff_nonneg _ _ _)
    (fun _ _ => closedUpperCutoff_le_one _ _ _)

private theorem continuous_orthantApprox {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℝ) (m : ℕ) : Continuous (orthantApprox S a m) := by
  unfold orthantApprox
  exact continuous_finsetProd S fun i _ =>
    (continuous_closedUpperCutoff m (a i)).comp (continuous_apply i)

private def orthantTest {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (m : ℕ) :
    (Fin n → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨orthantApprox S a m, continuous_orthantApprox S a m⟩ 1
    (by
      intro x y
      change dist (orthantApprox S a m x) (orthantApprox S a m y) ≤ 1
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith [orthantApprox_nonneg S a m x,
        orthantApprox_nonneg S a m y, orthantApprox_le_one S a m x,
        orthantApprox_le_one S a m y])

private theorem monotone_orthantTest {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℝ) (m : ℕ) : Monotone (orthantTest S a m) := by
  intro x y hxy
  exact Finset.prod_le_prod₀ (fun _ _ => closedUpperCutoff_nonneg _ _ _)
    (fun i _ => monotone_closedUpperCutoff m (a i) (hxy i))

private theorem tendsto_orthantApprox {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ)
    (x : Fin n → ℝ) :
    Tendsto (fun m => orthantApprox S a m x) atTop
      (𝓝 (Set.indicator {x : Fin n → ℝ | ∀ i ∈ S, a i ≤ x i} (fun _ => (1 : ℝ)) x)) := by
  have h := tendsto_finsetProd S (fun i _ => tendsto_closedUpperCutoff (a i) (x i))
  have heq : (∏ i ∈ S, if a i ≤ x i then (1 : ℝ) else 0) =
      Set.indicator {x : Fin n → ℝ | ∀ i ∈ S, a i ≤ x i} (fun _ => (1 : ℝ)) x := by
    classical
    by_cases hx : ∀ i ∈ S, a i ≤ x i
    · rw [Set.indicator_of_mem (show x ∈ {x | ∀ i ∈ S, a i ≤ x i} from hx)]
      exact Finset.prod_eq_one fun i hi => ite_eq_left (hx i hi)
    · rw [Set.indicator_of_notMem (show x ∉ {x | ∀ i ∈ S, a i ≤ x i} from hx)]
      push Not at hx
      obtain ⟨i, hi, hia⟩ := hx
      exact Finset.prod_eq_zero hi (ite_eq_right (not_le.mpr hia))
  exact heq ▸ h

/-- The explicit finite-coordinate increasing bounded-continuous test inequalities
imply probability order for every finite closed upper-orthant cylinder. The
finite set `S` may ignore coordinates in the tested prefix. -/
theorem measure_finite_closed_upper_le_of_integral_le
    (μ ν : ProbabilityMeasure (ℕ → ℝ))
    (h : ∀ (n : ℕ) (f : (Fin n → ℝ) →ᵇ ℝ), Monotone f →
      (∫ z, f (fun i => z i.val) ∂(μ : Measure (ℕ → ℝ))) ≤
        ∫ z, f (fun i => z i.val) ∂(ν : Measure (ℕ → ℝ)))
    {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) :
    (μ : Measure (ℕ → ℝ)) {z | ∀ i ∈ S, a i ≤ z i.val} ≤
      (ν : Measure (ℕ → ℝ)) {z | ∀ i ∈ S, a i ≤ z i.val} := by
  classical
  let A : Set (ℕ → ℝ) := {z | ∀ i ∈ S, a i ≤ z i.val}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i : Fin n => MeasurableSet.iInter fun _ : i ∈ S =>
      measurableSet_le (measurable_const (a := a i))
        (show Measurable (fun z : ℕ → ℝ => z i.val) from measurable_pi_apply i.val)
  have hlim (ρ : ProbabilityMeasure (ℕ → ℝ)) :
      Tendsto (fun m => ∫ z, orthantTest S a m (fun i => z i.val)
        ∂(ρ : Measure (ℕ → ℝ))) atTop (𝓝 ((ρ : Measure (ℕ → ℝ)).real A)) := by
    rw [← integral_indicator_one hA]
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro m
      exact ((orthantTest S a m).continuous.measurable.comp
        (Measurable.of_eval fun i => measurable_pi_apply i.val)).aestronglyMeasurable
    · exact integrable_const 1
    · intro m
      exact Eventually.of_forall fun z => by
        change ‖orthantApprox S a m (fun i => z i.val)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (orthantApprox_nonneg S a m _)]
        exact orthantApprox_le_one S a m _
    · exact Eventually.of_forall fun z => tendsto_orthantApprox S a (fun i => z i.val)
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact le_of_tendsto_of_tendsto (hlim μ) (hlim ν)
    (Eventually.of_forall fun m => h n (orthantTest S a m) (monotone_orthantTest S a m))

end LPPDifferentiability
