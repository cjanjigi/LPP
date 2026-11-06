/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.AnimalMaximum
public import LPP_Foundations.Probability.TruncationTails
public import Martin2004.Probability.DiagonalAnimalCenteredLower
public import LPP_Foundations.Model.Animals.DiagonalComparison
import Martin2004.Probability.DiagonalAnimalCenteredConvergence

/-!
# Almost-sure upper bounds for rooted animal maxima

The signed reduction replaces each site weight by its positive part, and uses the
canonical environment law of the positive-part law. The finite comparison keeps the
size `n + 1` and the factor two from the centered interval length.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace LPPDifferentiability

/-- Increasing every site weight increases the positive-size maximum. -/
theorem animalMaximum_mono (n : ℕ) (hn : 1 ≤ n) {w v : Lattice → ℝ}
    (hwv : ∀ z, w z ≤ v z) : animalMaximum n hn w ≤ animalMaximum n hn v := by
  apply (animalMaximum_le_iff n hn w _).2
  intro s hs
  exact (Finset.sum_le_sum (fun z _ => hwv z)).trans
    (animalWeight_le_animalMaximum n hn v hs)

/-- Replacing signed site weights by their positive parts can only increase
the finite animal maximum. No first moment is needed. -/
theorem animalMaximum_le_positivePart (n : ℕ) (hn : 1 ≤ n) (ω : Environment) :
    animalMaximum n hn ω ≤ animalMaximum n hn (fun z => max (ω z) 0) :=
  animalMaximum_mono n hn (fun z => le_max_left (ω z) 0)

/-- The positive-part mapped marginal is nonnegative almost everywhere. -/
theorem ae_nonneg_map_positivePart (μ : Measure ℝ) :
    ∀ᵐ x ∂μ.map (fun x : ℝ => max x 0), 0 ≤ x := by
  apply (ae_map_iff (by fun_prop) (by measurability)).2
  exact Eventually.of_forall (fun x => le_max_right x 0)

/-- The strict tail of the positive-part law equals the strict tail of the original law,
also at zero. -/
theorem map_positivePart_strict_tail (μ : Measure ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (μ.map (fun x : ℝ => max x 0)) (Ioi t) = μ (Ioi t) := by
  simpa only [sub_zero, zero_add] using map_positive_remainder_strict_tail μ 0 t ht

/-- Positive-part replacement preserves the integrated positive square-root
tail exactly, including laws with atoms. -/
theorem positivePart_sqrt_tail (μ : Measure ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), ((μ.map (fun x : ℝ => max x 0)) (Ioi t)) ^ (1 / 2 : ℝ)) =
      ∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ) := by
  simpa only [sub_zero] using positive_remainder_sqrt_tail μ 0

/-- The full positive-part field has the canonical law of the mapped marginal. -/
theorem environmentLaw_map_positivePart (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (environmentLaw μ).map (fun ω : Environment => fun z => max (ω z) 0) =
      environmentLaw (μ.map (fun x : ℝ => max x 0)) := by
  simpa only [sub_zero] using environmentLaw_map_positive_remainder μ 0

/-- Every full-measure event for the positive-part canonical law pulls back
to the positive-part field on the original environment. -/
theorem ae_positivePart_environment_of_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {P : Environment → Prop}
    (hP : ∀ᵐ η ∂environmentLaw (μ.map (fun x : ℝ => max x 0)), P η) :
    ∀ᵐ ω ∂environmentLaw μ, P (fun z => max (ω z) 0) := by
  have hmap : MeasurePreserving
      (fun ω : Environment => fun z => max (ω z) 0)
      (environmentLaw μ) (environmentLaw (μ.map (fun x : ℝ => max x 0))) :=
    ⟨measurable_coordinatewise_environment_map (fun x : ℝ => max x 0) (by fun_prop),
      environmentLaw_map_positivePart μ⟩
  exact hmap.quasiMeasurePreserving.ae hP

/-- The finite enclosing diagonal animal has twice the normalizing length.
The radius is `n + 1`, including at index zero. -/
theorem animalMaximum_rate_le_twice_centeredRate (n : ℕ) (ω : Environment)
    (hω : ∀ z, 0 ≤ ω z) :
    animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) ≤
      2 * diagonalAnimalCenteredRate n ω := by
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ diagonalAnimalMaximum (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ)
        (by omega) ω / ((n + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right
        (animalMaximum_le_diagonalAnimalMaximum (n + 1) (by omega) ω hω) hden.le
    _ = _ := by
      rw [diagonalAnimalCenteredRate_eq]
      push_cast
      field_simp

/-- The same finite maximum comparison holds for the extended upper limits
of normalized signed and positive-part animal maxima. -/
theorem limsup_animalMaximum_rate_le_positivePart (ω : Environment) :
    limsup (fun n : ℕ =>
      ((animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤
    limsup (fun n : ℕ =>
      ((animalMaximum (n + 1) (by omega) (fun z => max (ω z) 0) /
        ((n + 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop := by
  exact limsup_le_limsup (Eventually.of_forall (fun n => EReal.coe_le_coe_iff.mpr
    (div_le_div_of_nonneg_right
      (animalMaximum_le_positivePart (n + 1) (by omega) ω) (Nat.cast_nonneg _))))

/-- The finite enclosing comparison transfers a centered real limit to an upper
limit for the rooted animals, with factor two. -/
theorem limsup_animalMaximum_rate_le_twice_of_centered_tendsto
    (ω : Environment) (hω : ∀ z, 0 ≤ ω z) {q : ℝ}
    (hq : Tendsto (fun n => diagonalAnimalCenteredRate n ω) atTop (𝓝 q)) :
    limsup (fun n : ℕ =>
      ((animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤
      ((2 * q : ℝ) : EReal) := by
  have hscaled : Tendsto
      (fun n => ((2 * diagonalAnimalCenteredRate n ω : ℝ) : EReal))
      atTop (𝓝 ((2 * q : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr (hq.const_mul 2)
  calc
    _ ≤ limsup (fun n => ((2 * diagonalAnimalCenteredRate n ω : ℝ) : EReal)) atTop :=
      limsup_le_limsup (Eventually.of_forall (fun n =>
        EReal.coe_le_coe_iff.mpr (animalMaximum_rate_le_twice_centeredRate n ω hω)))
    _ = _ := hscaled.limsup_eq

/-- A finite extended upper bound gives an eventual epsilon bound on the same
sequence of normalized maxima. -/
theorem eventually_animalMaximum_rate_lt_of_limsup_le (ω : Environment) {B : ℝ}
    (hB : limsup (fun n : ℕ =>
      ((animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤
        (B : EReal)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) < B + ε := by
  have he := eventually_lt_of_limsup_lt
    (hB.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right B hε)))
  exact he.mono (fun _ hn => EReal.coe_lt_coe_iff.mp hn)

/-- One universal positive constant bounds the extended upper limit of rooted
animal maxima for every real probability law with finite positive
integrated square-root tail. The signed law needs no negative first moment. -/
theorem exists_animalMaximum_limsup_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∀ᵐ ω ∂environmentLaw μ,
        limsup (fun n : ℕ =>
          ((animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
          atTop ≤
            ((C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal : ℝ) : EReal) := by
  obtain ⟨C, hC, hsource⟩ := exists_diagonalAnimalMaximum_forward_and_centered_convergence
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro μ _ hpos
  let ν := μ.map (fun x : ℝ => max x 0)
  have htail :
      (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t)) ^ (1 / 2 : ℝ)) =
        ∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ) :=
    positivePart_sqrt_tail μ
  have hnonneg : ∀ᵐ x ∂ν, 0 ≤ x := ae_nonneg_map_positivePart μ
  obtain ⟨q, _, hqbound, _, _, _, _, _, _, _, _, _, hcentered⟩ :=
    hsource ν hnonneg (by rw [htail]; exact hpos)
  have hnonnegative_bound : ∀ᵐ η ∂environmentLaw ν,
      limsup (fun n : ℕ =>
        ((animalMaximum (n + 1) (by omega) η / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
        atTop ≤ ((2 * q : ℝ) : EReal) := by
    filter_upwards [ae_forall_environment_nonneg ν hnonneg, hcentered] with η hη hlimit
    exact limsup_animalMaximum_rate_le_twice_of_centered_tendsto η hη hlimit
  have hback := ae_positivePart_environment_of_ae μ hnonnegative_bound
  rw [htail] at hqbound
  filter_upwards [hback] with ω hω
  apply ((limsup_animalMaximum_rate_le_positivePart ω).trans hω).trans
  apply EReal.coe_le_coe_iff.mpr
  calc
    2 * q ≤ 2 * (C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) :=
      mul_le_mul_of_nonneg_left hqbound (by norm_num)
    _ = _ := by ring

/-- The same universal constant gives both the upper limit and all positive
epsilon-eventual bounds on one full-measure set for the signed law. -/
theorem exists_animalMaximum_limsup_and_eventually_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∀ᵐ ω ∂environmentLaw μ,
        (limsup (fun n : ℕ =>
          ((animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
          atTop ≤
            ((C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal : ℝ) : EReal)) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          animalMaximum (n + 1) (by omega) ω / ((n + 1 : ℕ) : ℝ) <
            C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε := by
  obtain ⟨C, hC, hbound⟩ := exists_animalMaximum_limsup_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hpos
  filter_upwards [hbound μ hpos] with ω hω
  exact ⟨hω, fun ε hε => eventually_animalMaximum_rate_lt_of_limsup_le ω hω ε hε⟩

end LPPDifferentiability
