/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralJointLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Data.Fintype.Fin

/-! Closed support of any weak subsequential limit of the actual finite
bilateral joint laws. The same limit retains all integer interval comparisons. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace LPPDifferentiability

/-- The closed event that one increment coordinate is nonnegative. -/
def bilateralNonnegativeCoordinate (t : ℤ) : Set BilateralJoint :=
  {p | 0 ≤ p.2 t}

/-- The closed event that increments majorize one proper array interval. -/
def bilateralIntervalMajorant (v : BilateralInterval) : Set BilateralJoint :=
  {p | p.1 v ≤ ∑ t ∈ Finset.Ico v.1.1 v.1.2, p.2 t}

theorem isClosed_bilateralNonnegativeCoordinate (t : ℤ) :
    IsClosed (bilateralNonnegativeCoordinate t) :=
  isClosed_le continuous_const ((continuous_apply t).comp continuous_snd)

theorem isClosed_bilateralIntervalMajorant (v : BilateralInterval) :
    IsClosed (bilateralIntervalMajorant v) := by
  apply isClosed_le ((continuous_apply v).comp continuous_fst)
  exact continuous_finsetSum _ fun t _ => (continuous_apply t).comp continuous_snd

/-- The actual uniform law assigns at most K/(N+1) to its first K indices. -/
theorem uniformOriginLaw_lt_le (N K : ℕ) :
    uniformOriginLaw N {u | u.val < K} ≤ (K : ℝ≥0∞) / (N + 1 : ℕ) := by
  classical
  rw [uniformOriginLaw, PMF.toMeasure_uniformOfFintype_apply {u : Fin (N + 1) | u.val < K}
    (Set.toFinite _).measurableSet]
  have hc : Fintype.card {u : Fin (N + 1) // u.val < K} ≤ K := by
    let f : {u : Fin (N + 1) // u.val < K} → Fin K := fun u => ⟨u.1.val, u.2⟩
    have hf : Function.Injective f := by
      intro u v h
      apply Subtype.ext
      apply Fin.ext
      dsimp only [f] at h
      exact congrArg (fun w : Fin K => w.val) h
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, div_eq_mul_inv]
  exact mul_le_mul_left (by exact_mod_cast hc) _

/-- Every finite law has nonnegative increments at all integer coordinates. -/
theorem ae_uniformBilateralJointLaw_nonneg
    (ρ : ProbabilityMeasure BilateralArray)
    (hρ : ∀ᵐ x ∂(ρ : Measure BilateralArray),
      (∀ v, 0 ≤ x v) ∧
      ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
        x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (N : ℕ) :
    ∀ᵐ p ∂(uniformBilateralJointLaw ρ N : Measure BilateralJoint), ∀ t, 0 ≤ p.2 t := by
  rw [uniformBilateralJointLaw_toMeasure]
  apply ae_all_iff.2
  intro t
  apply (ae_map_iff (measurable_uniformBilateralJointSampler N).aemeasurable
    (isClosed_bilateralNonnegativeCoordinate t).measurableSet).2
  filter_upwards [(uniformOriginProduct_fst (ρ : Measure BilateralArray) N).quasiMeasurePreserving.ae hρ]
    with p hp
  exact bilateralArrayIncrements_nonneg_of_nonneg_superadditive p.1 hp.1 hp.2 p.2.val t

/-- Under the literal finite product and pushforward, only finitely many roots
can fail a fixed proper-interval comparison. -/
theorem uniformBilateralJointLaw_majorant_compl_le
    (ρ : ProbabilityMeasure BilateralArray)
    (hρ : ∀ᵐ x ∂(ρ : Measure BilateralArray),
      ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
        x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (N : ℕ) (v : BilateralInterval) :
    (uniformBilateralJointLaw ρ N : Measure BilateralJoint)
      (bilateralIntervalMajorant v)ᶜ ≤
        ((-v.1.1).toNat : ℝ≥0∞) / (N + 1 : ℕ) := by
  rw [uniformBilateralJointLaw_toMeasure,
    Measure.map_apply (measurable_uniformBilateralJointSampler N)
      (isClosed_bilateralIntervalMajorant v).measurableSet.compl]
  let B : Set (Fin (N + 1)) := {u | u.val < (-v.1.1).toNat}
  calc
    _ ≤ uniformOriginProduct (ρ : Measure BilateralArray) N (Prod.snd ⁻¹' B) := by
      apply measure_mono_ae
      filter_upwards [(uniformOriginProduct_fst (ρ : Measure BilateralArray) N).quasiMeasurePreserving.ae hρ]
        with p hp
      intro hbad
      by_contra hroot
      have hr : bilateralIncrementRoot p.2.val < v.1.1 := by
        dsimp [B] at hroot
        simp only [not_lt] at hroot
        dsimp [bilateralIncrementRoot]
        omega
      exact hbad (interval_le_sum_Ico_bilateralArrayIncrements_of_superadditive
        p.1 hp p.2.val v.1.1 v.1.2 v.2 hr)
    _ = uniformOriginLaw N B :=
      (uniformOriginProduct_snd (ρ : Measure BilateralArray) N).measure_preimage
        (Set.toFinite B).measurableSet.nullMeasurableSet
    _ ≤ _ := uniformOriginLaw_lt_le N (-v.1.1).toNat

/-- Closed events whose complement has a fixed finite-root bound retain full
mass under any weak subsequential limit. -/
theorem prob_closed_eq_one_of_compl_le_uniformRoot
    {μs : ℕ → ProbabilityMeasure BilateralJoint} {ν : ProbabilityMeasure BilateralJoint}
    {r : ℕ → ℕ} (hr : StrictMono r)
    (hlim : Tendsto (fun i => μs (r i)) atTop (𝓝 ν))
    {F : Set BilateralJoint} (hF : IsClosed F) (K : ℕ)
    (hbad : ∀ N, (μs N : Measure BilateralJoint) Fᶜ ≤
      (K : ℝ≥0∞) / (N + 1 : ℕ)) : (ν : Measure BilateralJoint) F = 1 := by
  have hinv : Tendsto (fun i => ((r i + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp
      ((tendsto_add_atTop_nat 1).comp hr.tendsto_atTop)
  have hzero : Tendsto (fun i => (K : ℝ≥0∞) / (r i + 1 : ℕ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using ENNReal.Tendsto.const_mul hinv (Or.inr (by simp))
  have hone : Tendsto (fun i => 1 - (K : ℝ≥0∞) / (r i + 1 : ℕ)) atTop (𝓝 1) := by
    simpa only [tsub_zero] using
      ENNReal.Tendsto.sub tendsto_const_nhds hzero (Or.inl ENNReal.one_ne_top)
  have hlower (i : ℕ) : 1 - (K : ℝ≥0∞) / (r i + 1 : ℕ) ≤
      (μs (r i) : Measure BilateralJoint) F := by
    have h := hbad (r i)
    rw [prob_compl_eq_one_sub hF.measurableSet] at h
    exact tsub_le_iff_right.2 (by simpa only [add_comm] using tsub_le_iff_right.1 h)
  apply le_antisymm prob_le_one
  calc
    1 = atTop.limsup (fun i => 1 - (K : ℝ≥0∞) / (r i + 1 : ℕ)) := hone.limsup_eq.symm
    _ ≤ atTop.limsup (fun i => (μs (r i) : Measure BilateralJoint) F) :=
      limsup_le_limsup (Eventually.of_forall hlower)
    _ ≤ _ := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF

/-- A single event under the same weak limit contains nonnegative increments
and every proper integer interval comparison. -/
theorem ae_weakLimit_uniformBilateralJointLaw_support
    (ρ : ProbabilityMeasure BilateralArray) (ν : ProbabilityMeasure BilateralJoint)
    (hρ : ∀ᵐ x ∂(ρ : Measure BilateralArray),
      (∀ v, 0 ≤ x v) ∧
      ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
        x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    {r : ℕ → ℕ} (hr : StrictMono r)
    (hlim : Tendsto (fun i => uniformBilateralJointLaw ρ (r i)) atTop (𝓝 ν)) :
    ∀ᵐ p ∂(ν : Measure BilateralJoint),
      (∀ t, 0 ≤ p.2 t) ∧
      ∀ v : BilateralInterval, p.1 v ≤ ∑ t ∈ Finset.Ico v.1.1 v.1.2, p.2 t := by
  have hn : ∀ᵐ p ∂(ν : Measure BilateralJoint), ∀ t, 0 ≤ p.2 t := by
    apply ae_all_iff.2
    intro t
    apply (mem_ae_iff_prob_eq_one (isClosed_bilateralNonnegativeCoordinate t).measurableSet).2
    apply prob_closed_eq_one_of_compl_le_uniformRoot hr hlim
      (isClosed_bilateralNonnegativeCoordinate t) 0
    intro N
    have hN : ∀ᵐ p ∂(uniformBilateralJointLaw ρ N : Measure BilateralJoint),
        p ∈ bilateralNonnegativeCoordinate t :=
      (ae_uniformBilateralJointLaw_nonneg ρ hρ N).mono fun _ hp => hp t
    rw [prob_compl_eq_one_sub (isClosed_bilateralNonnegativeCoordinate t).measurableSet,
      (mem_ae_iff_prob_eq_one (isClosed_bilateralNonnegativeCoordinate t).measurableSet).1 hN]
    simp only [tsub_self]
    exact zero_le
  have hi : ∀ᵐ p ∂(ν : Measure BilateralJoint),
      ∀ v : BilateralInterval, p.1 v ≤ ∑ t ∈ Finset.Ico v.1.1 v.1.2, p.2 t := by
    apply ae_all_iff.2
    intro v
    apply (mem_ae_iff_prob_eq_one (isClosed_bilateralIntervalMajorant v).measurableSet).2
    exact prob_closed_eq_one_of_compl_le_uniformRoot hr hlim
      (isClosed_bilateralIntervalMajorant v) (-v.1.1).toNat
      (fun N => uniformBilateralJointLaw_majorant_compl_le ρ (hρ.mono fun _ hx => hx.2) N v)
  exact hn.and hi

end LPPDifferentiability
