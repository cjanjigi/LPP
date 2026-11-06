/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import ProbabilityBasics.Probability.FiniteProductDensity

/-!
# Finite changes of the infinite environment law

This file studies a finite change of the environment law, in which finitely many one-site
marginals are replaced by densities. The factors are bounded, normalized, measurable functions.
The bound on the second moment of the density is conditional on the one-site bound. Identifying
the law of the modified field is not done in this file.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

private theorem integrable_density_factor (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) :
    Integrable f μ := by
  refine (integrable_const (2 : ℝ)).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h2 x)

/-- Normalization is established before any infinite-product property is used. -/
theorem isProbabilityMeasure_withDensity_normalized_factor (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) (hmean : ∫ x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_density_factor μ f hf h0 h2)
      (Filter.Eventually.of_forall h0), hmean, ENNReal.ofReal_one]

/-- The finite product density is integrable under the environment law. -/
theorem integrable_prod_environment_factors (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (f : ℝ → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) :
    Integrable (fun ω : Environment => ∏ v ∈ R, f (ω v)) (environmentLaw μ) := by
  classical
  have hp := Integrable.fintype_prod (fun _ : R => integrable_density_factor μ f hf h0 h2)
  rw [← environmentLaw_map_finite_coordinates μ (fun v : R => (v : Lattice))
    Subtype.val_injective] at hp
  have hc := hp.comp_measurable (measurable_finite_environment_coordinates
    (fun v : R => (v : Lattice)))
  have heq : (fun ω : Environment => ∏ v ∈ R, f (ω v)) =
      (fun ω : Environment => ∏ v : R, f (ω v)) := by
    funext ω
    exact (Finset.prod_coe_sort R (fun v : Lattice => f (ω v))).symm
  rw [heq]
  exact hc

/-- Fubini's theorem on finitely many coordinates gives the mean of the finite product, including
the case of the empty region. -/
theorem integral_prod_environment_factors (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω : Environment, ∏ v ∈ R, f (ω v) ∂environmentLaw μ) =
      (∫ x, f x ∂μ) ^ R.card := by
  classical
  have h := integral_finite_environment_coordinates μ (fun v : R => (v : Lattice))
    Subtype.val_injective (fun x : R → ℝ => ∏ v : R, f (x v))
    (Finset.measurable_prod Finset.univ (fun v _ => hf.comp (measurable_pi_apply v)))
  calc
    (∫ ω : Environment, ∏ v ∈ R, f (ω v) ∂environmentLaw μ) =
        ∫ ω : Environment, ∏ v : R, f (ω v) ∂environmentLaw μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω =>
        (Finset.prod_coe_sort R (fun v : Lattice => f (ω v))).symm)
    _ = ∫ x : R → ℝ, ∏ v : R, f (x v) ∂Measure.pi (fun _ : R => μ) := h
    _ = (∫ x, f x ∂μ) ^ R.card := by
      rw [integral_fintype_prod_eq_prod, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe]

/-- A normalized one-site factor gives a finite product density with mean one. -/
theorem integral_prod_environment_factors_eq_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (f : ℝ → ℝ) (hf : Measurable f)
    (hmean : ∫ x, f x ∂μ = 1) :
    (∫ ω : Environment, ∏ v ∈ R, f (ω v) ∂environmentLaw μ) = 1 := by
  rw [integral_prod_environment_factors μ R f hf, hmean, one_pow]

/-- The square of the finite product density is integrable. Only the bounds on `f` are needed. -/
theorem integrable_sq_prod_environment_factors (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (f : ℝ → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) :
    Integrable (fun ω : Environment => (∏ v ∈ R, f (ω v)) ^ 2) (environmentLaw μ) := by
  classical
  have hp := integrable_sq_prod_factors (fun _ : R => μ) (fun _ => f)
    (fun _ => hf) (fun _ => h0) (fun _ => h2)
  rw [← environmentLaw_map_finite_coordinates μ (fun v : R => (v : Lattice))
    Subtype.val_injective] at hp
  have hc := hp.comp_measurable (measurable_finite_environment_coordinates
    (fun v : R => (v : Lattice)))
  have heq : (fun ω : Environment => (∏ v ∈ R, f (ω v)) ^ 2) =
      (fun ω : Environment => (∏ v : R, f (ω v)) ^ 2) := by
    funext ω
    rw [Finset.prod_coe_sort R (fun v : Lattice => f (ω v))]
  rw [heq]
  exact hc

/-- The squared-density moment is exactly the finite product of one-site moments. -/
theorem integral_sq_prod_environment_factors (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω : Environment, (∏ v ∈ R, f (ω v)) ^ 2 ∂environmentLaw μ) =
      (∫ x, (f x) ^ 2 ∂μ) ^ R.card := by
  simp_rw [← Finset.prod_pow]
  exact integral_prod_environment_factors μ R (fun x => (f x) ^ 2) (hf.pow_const 2)

/-- If the second moment of each one-site factor is at most `exp (3 δ^2)`, then the second moment
of the product over `R` is at most `exp (3 δ^2 * |R|)`. -/
theorem integral_sq_prod_environment_factors_le_exp (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (R : Finset Lattice) (f : ℝ → ℝ)
    (hf : Measurable f) (δ : ℝ)
    (hcost : (∫ x, (f x) ^ 2 ∂μ) ≤ Real.exp (3 * δ ^ 2)) :
    (∫ ω : Environment, (∏ v ∈ R, f (ω v)) ^ 2 ∂environmentLaw μ) ≤
      Real.exp (3 * δ ^ 2 * R.card) := by
  rw [integral_sq_prod_environment_factors μ R f hf]
  calc
    (∫ x, (f x) ^ 2 ∂μ) ^ R.card ≤ (Real.exp (3 * δ ^ 2)) ^ R.card :=
      pow_le_pow_left₀ (integral_nonneg (fun x => sq_nonneg (f x))) hcost R.card
    _ = Real.exp (3 * δ ^ 2 * R.card) := by
      rw [← Real.exp_nat_mul, mul_comm]

private theorem map_withDensity_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (F : A → B) (hF : Measurable F) (g : B → ℝ≥0∞)
    (hg : Measurable g) :
    (P.withDensity (fun x => g (F x))).map F = (P.map F).withDensity g := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs,
    ← lintegral_indicator (hF hs), ← lintegral_indicator hs,
    lintegral_map (hg.indicator hs) hF]
  exact lintegral_congr (fun x => by
    by_cases hx : F x ∈ s
    · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' s from hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' s from hx), Set.indicator_of_notMem hx])

private theorem map_withDensity_environment_superset (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (R S : Finset Lattice) (hRS : R ⊆ S)
    (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) :
    ((environmentLaw μ).withDensity
      (fun ω : Environment => ∏ v ∈ R, ENNReal.ofReal (f (ω v)))).map S.restrict =
      Measure.pi (fun v : S => if (v : Lattice) ∈ R then
        μ.withDensity (fun x => ENNReal.ofReal (f x)) else μ) := by
  classical
  let g : S → ℝ → ℝ := fun v x => if (v : Lattice) ∈ R then f x else 1
  have hg : ∀ v, Measurable (g v) := by
    intro v
    dsimp [g]
    split_ifs
    · exact hf
    · exact measurable_const
  have hg0 : ∀ v x, 0 ≤ g v x := by
    intro v x
    dsimp [g]
    split_ifs
    · exact h0 x
    · exact zero_le_one
  have hg2 : ∀ v x, g v x ≤ 2 := by
    intro v x
    dsimp [g]
    split_ifs
    · exact h2 x
    · norm_num
  have hd : (fun ω : Environment => ∏ v ∈ R, ENNReal.ofReal (f (ω v))) =
      (fun ω : Environment => ∏ v : S, ENNReal.ofReal (g v (S.restrict ω v))) := by
    funext ω
    simp only [g, Finset.restrict_def, apply_ite ENNReal.ofReal, ENNReal.ofReal_one]
    calc
      (∏ v ∈ R, ENNReal.ofReal (f (ω v))) =
          ∏ v ∈ R, if v ∈ R then ENNReal.ofReal (f (ω v)) else 1 := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [ite_eq_left hv]
      _ = ∏ v ∈ S, if v ∈ R then ENNReal.ofReal (f (ω v)) else 1 := by
        apply Finset.prod_subset hRS
        intro v _ hv
        rw [ite_eq_right hv]
      _ = ∏ v : S, if (v : Lattice) ∈ R then ENNReal.ofReal (f (ω v)) else 1 :=
        (Finset.prod_coe_sort S
          (fun v : Lattice => if v ∈ R then ENNReal.ofReal (f (ω v)) else 1)).symm
  rw [hd, map_withDensity_comp (environmentLaw μ) S.restrict
    (Finset.measurable_restrict S) (fun x : S → ℝ => ∏ v : S, ENNReal.ofReal (g v (x v)))
    (Finset.measurable_prod Finset.univ (fun v _ =>
      (hg v).ennreal_ofReal.comp (measurable_pi_apply v))),
    Finset.restrict_def, environmentLaw_map_finite_coordinates μ (fun v : S => (v : Lattice))
      Subtype.val_injective, ← pi_withDensity_factors (fun _ : S => μ) g hg hg0 hg2]
  congr 1
  funext v
  dsimp [g]
  split_ifs
  · rfl
  · rw [show (fun _ : ℝ => ENNReal.ofReal (1 : ℝ)) = (1 : ℝ → ℝ≥0∞) by
        funext x
        simp only [ENNReal.ofReal_one, Pi.one_apply]]
    exact withDensity_one

/-- Replacing finitely many marginals by normalized densities gives the infinite product measure
with those marginals, which equals the environment law multiplied by the finite product
density. -/
theorem infinitePi_finite_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (f : ℝ → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) (hmean : ∫ x, f x ∂μ = 1) :
    Measure.infinitePi (fun v : Lattice => if v ∈ R then
      μ.withDensity (fun x => ENNReal.ofReal (f x)) else μ) =
      (environmentLaw μ).withDensity
        (fun ω : Environment => ∏ v ∈ R, ENNReal.ofReal (f (ω v))) := by
  classical
  let ν : Lattice → Measure ℝ := fun v => if v ∈ R then
    μ.withDensity (fun x => ENNReal.ofReal (f x)) else μ
  have hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isProbabilityMeasure_withDensity_normalized_factor μ f hf h0 h2 hmean
  let : ∀ v, IsProbabilityMeasure (ν v) := fun v => by
    dsimp [ν]
    split_ifs
    · exact hprob
    · infer_instance
  apply (Measure.isProjectiveLimit_infinitePi ν).unique
  intro s
  let S := R ∪ s
  have hsS : s ⊆ S := Finset.subset_union_right
  have hRS : R ⊆ S := Finset.subset_union_left
  rw [← Finset.restrict₂_comp_restrict hsS,
    ← Measure.map_map (Finset.measurable_restrict₂ hsS) (Finset.measurable_restrict S),
    map_withDensity_environment_superset μ R S hRS f hf h0 h2]
  exact (isProjectiveMeasureFamily_pi ν S s hsS).symm

/-- The modified infinite product measure is absolutely continuous with respect to the environment
law, also when some factors vanish. -/
theorem infinitePi_finite_withDensity_absolutelyContinuous (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (R : Finset Lattice) (f : ℝ → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) (hmean : ∫ x, f x ∂μ = 1) :
    Measure.infinitePi (fun v : Lattice => if v ∈ R then
      μ.withDensity (fun x => ENNReal.ofReal (f x)) else μ) ≪ environmentLaw μ := by
  rw [infinitePi_finite_withDensity μ R f hf h0 h2 hmean]
  exact withDensity_absolutelyContinuous _ _

end LPPDifferentiability
