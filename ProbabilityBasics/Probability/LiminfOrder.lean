/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.FiniteTestOrder
public import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Order.LiminfLimsup

/-!
# Stochastic order of normalized lower limits

This fills the monotone-limit extension omitted after Liggett (1985),
equation (2.14). Lower limits take values in `EReal`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace LPPDifferentiability

private theorem measurableSet_tail_upper (b : ℕ → ℝ) (N : ℕ) :
    MeasurableSet {z : ℕ → ℝ | ∀ j, N ≤ j → b j ≤ z j} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j : ℕ => MeasurableSet.iInter fun _ : N ≤ j =>
    measurableSet_le (measurable_const (a := b j))
      (show Measurable (fun z : ℕ → ℝ => z j) from measurable_pi_apply j)

private theorem measure_tail_upper_le
    (μ ν : ProbabilityMeasure (ℕ → ℝ))
    (h : ∀ (n : ℕ) (f : (Fin n → ℝ) →ᵇ ℝ), Monotone f →
      (∫ z, f (fun i => z i.val) ∂(μ : Measure (ℕ → ℝ))) ≤
        ∫ z, f (fun i => z i.val) ∂(ν : Measure (ℕ → ℝ)))
    (b : ℕ → ℝ) (N : ℕ) :
    (μ : Measure (ℕ → ℝ)) {z | ∀ j, N ≤ j → b j ≤ z j} ≤
      (ν : Measure (ℕ → ℝ)) {z | ∀ j, N ≤ j → b j ≤ z j} := by
  classical
  let W : ℕ → Set (ℕ → ℝ) := fun n => {z | ∀ j, N ≤ j → j < n → b j ≤ z j}
  have hW : Antitone W := by
    intro n m hnm z hz j hNj hjn
    exact hz j hNj (lt_of_lt_of_le hjn hnm)
  have hWm (n : ℕ) : MeasurableSet (W n) := by
    simp only [W, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j : ℕ => MeasurableSet.iInter fun _ : N ≤ j =>
      MeasurableSet.iInter fun _ : j < n => measurableSet_le (measurable_const (a := b j))
        (show Measurable (fun z : ℕ → ℝ => z j) from measurable_pi_apply j)
  have heq : {z : ℕ → ℝ | ∀ j, N ≤ j → b j ≤ z j} = ⋂ n, W n := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter, W]
    constructor
    · intro hz n j hNj _
      exact hz j hNj
    · intro hz j hNj
      exact hz (j + 1) j hNj (Nat.lt_succ_self j)
  have hfinite (n : ℕ) : (μ : Measure (ℕ → ℝ)) (W n) ≤
      (ν : Measure (ℕ → ℝ)) (W n) := by
    have hc := measure_finite_closed_upper_le_of_integral_le μ ν h
      (Finset.univ.filter fun i : Fin n => N ≤ i.val) (fun i => b i.val)
    have hset : {z : ℕ → ℝ | ∀ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
        b i.val ≤ z i.val} = W n := by
      ext z
      simp only [mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and, W]
      constructor
      · intro hz j hNj hjn
        exact hz ⟨j, hjn⟩ hNj
      · intro hz i hNi
        exact hz i.val hNi i.isLt
    simpa only [hset] using hc
  rw [heq, hW.measure_iInter (fun n => (hWm n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩,
    hW.measure_iInter (fun n => (hWm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact iInf_mono hfinite

private theorem measure_eventually_upper_le
    (μ ν : ProbabilityMeasure (ℕ → ℝ))
    (h : ∀ (n : ℕ) (f : (Fin n → ℝ) →ᵇ ℝ), Monotone f →
      (∫ z, f (fun i => z i.val) ∂(μ : Measure (ℕ → ℝ))) ≤
        ∫ z, f (fun i => z i.val) ∂(ν : Measure (ℕ → ℝ)))
    (b : ℕ → ℝ) :
    (μ : Measure (ℕ → ℝ)) {z | ∀ᶠ j in atTop, b j ≤ z j} ≤
      (ν : Measure (ℕ → ℝ)) {z | ∀ᶠ j in atTop, b j ≤ z j} := by
  have heq : {z : ℕ → ℝ | ∀ᶠ j in atTop, b j ≤ z j} =
      ⋃ N, {z | ∀ j, N ≤ j → b j ≤ z j} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, eventually_atTop]
  have hm : Monotone (fun N => {z : ℕ → ℝ | ∀ j, N ≤ j → b j ≤ z j}) := by
    intro N M hNM z hz j hMj
    exact hz j (hNM.trans hMj)
  rw [heq, hm.measure_iUnion, hm.measure_iUnion]
  exact iSup_mono fun N => measure_tail_upper_le μ ν h b N

private theorem le_liminf_normalized_iff (z : ℕ → ℝ) (a : ℝ) :
    (a : EReal) ≤ liminf (fun j => (z j / (j + 1) : ℝ) : ℕ → EReal) atTop ↔
      ∀ m : ℕ, ∀ᶠ j in atTop, (a - 1 / (m + 1) : ℝ) ≤ z j / (j + 1) := by
  rw [le_liminf_iff']
  constructor
  · intro hz m
    have hm : (a - 1 / (m + 1) : ℝ) < a := by
      have : (0 : ℝ) < 1 / (m + 1) := by positivity
      linarith
    simpa only [EReal.coe_le_coe_iff] using hz _ (EReal.coe_lt_coe_iff.mpr hm)
  · intro hz y hy
    obtain ⟨r, hyr, hra⟩ := EReal.exists_between_coe_real hy
    have hra' : r < a := EReal.coe_lt_coe_iff.mp hra
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hra')
    have hrq : r ≤ a - 1 / (m + 1) := by linarith
    filter_upwards [hz m] with j hj
    exact hyr.le.trans (EReal.coe_le_coe_iff.mpr (hrq.trans hj))

/-- Increasing bounded continuous finite-prefix tests order the real-threshold
upper tails of the normalized extended-real lower limit. No finiteness or
integrability of the lower limit is assumed. -/
theorem measure_normalized_liminf_ge_le_of_integral_le
    (μ ν : ProbabilityMeasure (ℕ → ℝ))
    (h : ∀ (n : ℕ) (f : (Fin n → ℝ) →ᵇ ℝ), Monotone f →
      (∫ z, f (fun i => z i.val) ∂(μ : Measure (ℕ → ℝ))) ≤
        ∫ z, f (fun i => z i.val) ∂(ν : Measure (ℕ → ℝ))) (a : ℝ) :
    (μ : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
      liminf (fun j => (z j / (j + 1) : ℝ) : ℕ → EReal) atTop} ≤
    (ν : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
      liminf (fun j => (z j / (j + 1) : ℝ) : ℕ → EReal) atTop} := by
  let b : ℕ → ℕ → ℝ := fun m j => (a - 1 / (m + 1)) * (j + 1)
  let E : ℕ → Set (ℕ → ℝ) := fun m => {z | ∀ᶠ j in atTop, b m j ≤ z j}
  have hE : Antitone E := by
    intro m k hmk z hz
    have hq : a - 1 / (m + 1 : ℝ) ≤ a - 1 / (k + 1 : ℝ) := by
      have hden : (m + 1 : ℝ) ≤ k + 1 := by exact_mod_cast Nat.add_le_add_right hmk 1
      have : 1 / (k + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) hden
      linarith
    filter_upwards [hz] with j hj
    exact (mul_le_mul_of_nonneg_right hq (by positivity)).trans hj
  have hEm (m : ℕ) : MeasurableSet (E m) := by
    have heq : E m = ⋃ N, {z | ∀ j, N ≤ j → b m j ≤ z j} := by
      ext z
      simp only [E, mem_ofPred_eq, mem_iUnion, eventually_atTop]
    rw [heq]
    exact MeasurableSet.iUnion fun N => measurableSet_tail_upper (b m) N
  have heq : {z : ℕ → ℝ | (a : EReal) ≤
      liminf (fun j => (z j / (j + 1) : ℝ) : ℕ → EReal) atTop} = ⋂ m, E m := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter, le_liminf_normalized_iff, E]
    apply forall_congr'
    intro m
    apply eventually_congr
    exact Eventually.of_forall fun j => le_div_iff₀ (by positivity : (0 : ℝ) < j + 1)
  rw [heq, hE.measure_iInter (fun m => (hEm m).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩,
    hE.measure_iInter (fun m => (hEm m).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact iInf_mono fun m => measure_eventually_upper_le μ ν h (b m)

end LPPDifferentiability
