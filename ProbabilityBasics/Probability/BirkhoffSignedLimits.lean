/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BirkhoffUpperIntegral
import Mathlib.Topology.Order.LiminfLimsup

/-! # Integrable real representatives of signed orbit-average limits

The positive and negative part reduction in Keane-Petersen,
arXiv:math/0608251v1, printed pp.249-250. Extended limits are proved finite
almost everywhere before any local real representative is introduced.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- The actual extended lower limit of the forward Birkhoff averages. -/
@[expose] noncomputable def birkhoffLower {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ)
    (ω : Ω) : EReal :=
  liminf (fun n => ((birkhoffAverage ℝ T f n ω : ℝ) : EReal)) atTop

theorem measurable_birkhoffLower {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {f : Ω → ℝ} (hT : Measurable T) (hf : Measurable f) :
    Measurable (birkhoffLower T f) := by
  apply Measurable.liminf
  intro n
  apply measurable_coe_real_ereal.comp
  unfold birkhoffAverage birkhoffSum
  exact (Finset.measurable_sum _ fun j _ => hf.comp (hT.iterate j)).const_smul ((n : ℝ)⁻¹)

theorem birkhoffLower_le_upper {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    birkhoffLower T f ω ≤ birkhoffUpper T f ω :=
  liminf_le_limsup

/-- Negation interchanges the actual upper and lower extended limits. -/
theorem birkhoffUpper_neg {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    birkhoffUpper T (-f) ω = -birkhoffLower T f ω := by
  simp only [birkhoffUpper, birkhoffLower, birkhoffAverage_neg_apply,
    EReal.coe_neg, ← Pi.neg_def, EReal.limsup_neg]

private theorem upper_mono {Ω : Type*} (T : Ω → Ω) {f g : Ω → ℝ}
    (hfg : ∀ ω, f ω ≤ g ω) (ω : Ω) : birkhoffUpper T f ω ≤ birkhoffUpper T g ω := by
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  apply EReal.coe_le_coe_iff.mpr
  unfold birkhoffAverage birkhoffSum
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hfg ((T^[j]) ω))
    (inv_nonneg.mpr (Nat.cast_nonneg n))

private theorem signed_bounds {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    -birkhoffUpper T (fun x => max (-f x) 0) ω ≤ birkhoffLower T f ω ∧
      birkhoffUpper T f ω ≤ birkhoffUpper T (fun x => max (f x) 0) ω := by
  constructor
  · have h := upper_mono T (f := -f) (g := fun x => max (-f x) 0)
      (fun x => le_max_left _ _) ω
    rw [birkhoffUpper_neg] at h
    exact EReal.neg_le_of_neg_le h
  · exact upper_mono T (fun x => le_max_left (f x) 0) ω

private theorem exists_integrable_real_of_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {F : Ω → EReal}
    {P Q : Ω → ℝ} (hT : MeasurePreserving T μ μ) (hF : Measurable F)
    (hPi : Integrable P μ) (hQi : Integrable Q μ)
    (hPn : ∀ᵐ ω ∂μ, 0 ≤ P ω) (hQn : ∀ᵐ ω ∂μ, 0 ≤ Q ω)
    (hb : ∀ᵐ ω ∂μ, ((-Q ω : ℝ) : EReal) ≤ F ω ∧ F ω ≤ (P ω : EReal))
    (hFinv : ∀ᵐ ω ∂μ, F (T ω) = F ω) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ ω ∂μ, (g ω : EReal) = F ω) ∧ (∀ᵐ ω ∂μ, g (T ω) = g ω) := by
  have hfinite : ∀ᵐ ω ∂μ, F ω ≠ ⊤ ∧ F ω ≠ ⊥ := by
    filter_upwards [hb] with ω hω
    exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hω.2,
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hω.1⟩
  let g : Ω → ℝ := fun ω => (F ω).toReal
  have hgm : Measurable g := hF.ereal_toReal
  have hgeq : ∀ᵐ ω ∂μ, (g ω : EReal) = F ω := by
    filter_upwards [hfinite] with ω hω
    exact EReal.coe_toReal hω.1 hω.2
  have hgi : Integrable g μ := by
    apply (hPi.add hQi).mono' hgm.aestronglyMeasurable
    filter_upwards [hb, hgeq, hPn, hQn] with ω hω heq hP hQ
    have hlo : -Q ω ≤ g ω := EReal.coe_le_coe_iff.mp (by rw [heq]; exact hω.1)
    have hhi : g ω ≤ P ω := EReal.coe_le_coe_iff.mp (by rw [heq]; exact hω.2)
    rw [Real.norm_eq_abs]
    change |g ω| ≤ P ω + Q ω
    exact abs_le.mpr ⟨by linarith only [hlo, hP], by linarith only [hhi, hQ]⟩
  have hginv : ∀ᵐ ω ∂μ, g (T ω) = g ω := by
    filter_upwards [hT.quasiMeasurePreserving.ae hgeq, hgeq, hFinv]
      with ω hshift hω hinv
    apply EReal.coe_injective
    exact hshift.trans (hinv.trans hω.symm)
  exact ⟨g, hgm, hgi, hgeq, hginv⟩

/-- Positive and negative parts prove that both actual signed limits admit
integrable invariant real representatives, with the lower below the upper. -/
theorem exists_integrable_birkhoffSignedLimits {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ) :
    ∃ u l : Ω → ℝ, Measurable u ∧ Integrable u μ ∧ Measurable l ∧ Integrable l μ ∧
      (∀ᵐ ω ∂μ, (u ω : EReal) = birkhoffUpper T f ω) ∧
      (∀ᵐ ω ∂μ, (l ω : EReal) = birkhoffLower T f ω) ∧
      (∀ᵐ ω ∂μ, u (T ω) = u ω) ∧ (∀ᵐ ω ∂μ, l (T ω) = l ω) ∧
      (∀ᵐ ω ∂μ, l ω ≤ u ω) := by
  obtain ⟨P, _, hPi, hPn, hPeq, _, _⟩ := exists_integrable_birkhoffUpper hT
    (hm.max measurable_const) hi.pos_part (fun ω => le_max_right _ _)
  obtain ⟨Q, _, hQi, hQn, hQeq, _, _⟩ := exists_integrable_birkhoffUpper hT
    (hm.neg.max measurable_const) hi.neg_part (fun ω => le_max_right _ _)
  have hbounds : ∀ᵐ ω ∂μ,
      ((-Q ω : ℝ) : EReal) ≤ birkhoffLower T f ω ∧
      birkhoffUpper T f ω ≤ (P ω : EReal) := by
    filter_upwards [hPeq, hQeq] with ω hP hQ
    rw [EReal.coe_neg, hP, hQ]
    exact signed_bounds T f ω
  have huBounds : ∀ᵐ ω ∂μ,
      ((-Q ω : ℝ) : EReal) ≤ birkhoffUpper T f ω ∧
      birkhoffUpper T f ω ≤ (P ω : EReal) := by
    filter_upwards [hbounds] with ω hω
    exact ⟨hω.1.trans (birkhoffLower_le_upper T f ω), hω.2⟩
  have hlBounds : ∀ᵐ ω ∂μ,
      ((-Q ω : ℝ) : EReal) ≤ birkhoffLower T f ω ∧
      birkhoffLower T f ω ≤ (P ω : EReal) := by
    filter_upwards [hbounds] with ω hω
    exact ⟨hω.1, (birkhoffLower_le_upper T f ω).trans hω.2⟩
  obtain ⟨u, hum, hui, hueq, huinv⟩ := exists_integrable_real_of_bounds hT
    (measurable_birkhoffUpper hT.measurable hm) hPi hQi hPn hQn huBounds
    (ae_birkhoffUpper_invariant hT hi)
  obtain ⟨l, hlm, hli, hleq, hlinv⟩ := exists_integrable_real_of_bounds hT
    (measurable_birkhoffLower hT.measurable hm) hPi hQi hPn hQn hlBounds
    (ae_liminf_birkhoffAverage_shift hT hi)
  refine ⟨u, l, hum, hui, hlm, hli, hueq, hleq, huinv, hlinv, ?_⟩
  filter_upwards [hueq, hleq] with ω hu hl
  apply EReal.coe_le_coe_iff.mp
  rw [hu, hl]
  exact birkhoffLower_le_upper T f ω

end LPPDifferentiability
