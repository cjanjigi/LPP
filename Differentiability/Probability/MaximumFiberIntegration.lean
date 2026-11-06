/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.MaximumConditionalBoost
public import Differentiability.Probability.MaximumModifiedFieldLaw
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating the actual maximum-resampling fibers

The original environment is the first coordinate of the unchanged joint law.
Reassociating its products gives explicit measurable section probabilities and
their integrals over original-environment events. These are Fubini identities,
not assertions identifying a Mathlib conditional expectation or disintegration.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ : ℝ}


/-- The joint law is obtained by reassociating the original environment and the
actual independent resample/coin fiber. -/
theorem maximum_modification_joint_eq_map_prod (hδ : δ ∈ Icc (0 : ℝ) 1) :
    (((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) = Measure.map
      (fun p : Environment × (Environment × (Lattice → Bool)) =>
        ((p.1, p.2.1), p.2.2)) (((environmentLaw μ)).prod ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))) := by
  let coin : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (environmentLaw μ) (environmentLaw μ)
      (Measure.infinitePi (fun _ : Lattice => coin)))).map_eq.symm

/-- Actual fiber probabilities of a measurable event vary measurably with the
original environment. -/
theorem measurable_maximum_resampling_fiber_probability (hδ : δ ∈ Icc (0 : ℝ) 1)
    {E : Set ((Environment × Environment) × (Lattice → Bool))}
    (hE : MeasurableSet E) :
    Measurable (fun w : Environment =>
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈ E}) := by
  let coin : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  exact measurable_measure_prodMk_left
    (hE.preimage (show Measurable
      (fun p : Environment × (Environment × (Lattice → Bool)) =>
        ((p.1, p.2.1), p.2.2)) by fun_prop))

/-- The same actual fiber probabilities, expressed as real numbers, are measurable. -/
theorem measurable_maximum_resampling_fiber_real (hδ : δ ∈ Icc (0 : ℝ) 1)
    {E : Set ((Environment × Environment) × (Lattice → Bool))}
    (hE : MeasurableSet E) :
    Measurable (fun w : Environment =>
      (((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈ E}) :=
  (measurable_maximum_resampling_fiber_probability μ hδ hE).ennreal_toReal

/-- Fubini over a measurable original-environment event, for the joint law. -/
theorem maximum_modification_joint_inter_eq_lintegral (hδ : δ ∈ Icc (0 : ℝ) 1)
    {A : Set Environment} (hA : MeasurableSet A)
    {E : Set ((Environment × Environment) × (Lattice → Bool))}
    (hE : MeasurableSet E) :
    (((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) {p | p.1.1 ∈ A ∧ p ∈ E} =
      ∫⁻ w in A, ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈ E} ∂(environmentLaw μ) := by
  let coin : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  let e : Environment × (Environment × (Lattice → Bool)) →
      (Environment × Environment) × (Lattice → Bool) :=
    fun p => ((p.1, p.2.1), p.2.2)
  have he : Measurable e := by fun_prop
  have hAE : MeasurableSet {p : (Environment × Environment) × (Lattice → Bool) |
      p.1.1 ∈ A ∧ p ∈ E} := (hA.preimage (by fun_prop)).inter hE
  rw [maximum_modification_joint_eq_map_prod μ hδ, Measure.map_apply he hAE]
  calc
    (((environmentLaw μ)).prod ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))) (e ⁻¹' {p | p.1.1 ∈ A ∧ p ∈ E}) =
        (((environmentLaw μ).restrict A).prod ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))) (e ⁻¹' E) := by
      rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply (hE.preimage he)]
      congr 1
      ext p
      simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_prod,
        mem_univ, and_true, e]
      exact and_comm
    _ = _ := Measure.prod_apply (hE.preimage he)

/-- The real-valued fiber probability is integrable on every measurable original
event because the corresponding actual joint event has finite probability. -/
theorem integrableOn_maximum_resampling_fiber_real (hδ : δ ∈ Icc (0 : ℝ) 1)
    {A : Set Environment} (hA : MeasurableSet A)
    {E : Set ((Environment × Environment) × (Lattice → Bool))}
    (hE : MeasurableSet E) :
    IntegrableOn (fun w : Environment =>
      (((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈ E}) A (environmentLaw μ) := by
  have : IsProbabilityMeasure (((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) := maximum_modification_joint_is_probability μ hδ
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_maximum_resampling_fiber_probability μ hδ hE).aemeasurable
  rw [← maximum_modification_joint_inter_eq_lintegral μ hδ hA hE]
  exact measure_ne_top (((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) _

/-- The average over the original environment of the actual fiber probabilities
is the real probability of the joint event. Every section is finite under the
actual fiber law. -/
theorem maximum_modification_joint_inter_real_eq_integral (hδ : δ ∈ Icc (0 : ℝ) 1)
    {A : Set Environment} (hA : MeasurableSet A)
    {E : Set ((Environment × Environment) × (Lattice → Bool))}
    (hE : MeasurableSet E) :
    ((((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {p | p.1.1 ∈ A ∧ p ∈ E} =
      ∫ w in A, (((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈ E} ∂(environmentLaw μ) := by
  let coin : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  rw [measureReal_def, maximum_modification_joint_inter_eq_lintegral μ hδ hA hE]
  exact (integral_toReal
    (measurable_maximum_resampling_fiber_probability μ hδ hE).aemeasurable
    (Filter.Eventually.of_forall fun _ => measure_lt_top ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) _)).symm

/-- The original event has exactly its original real probability under the
actual joint law, using the first marginal of the joint law. -/
theorem maximum_modification_original_real (hδ : δ ∈ Icc (0 : ℝ) 1)
    {A : Set Environment} (hA : MeasurableSet A) :
    (((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))).real {p | p.1.1 ∈ A} = (environmentLaw μ).real A := by
  have h := map_measureReal_apply
    (μ := (((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))))
    (f := fun p : (Environment × Environment) × (Lattice → Bool) => p.1.1)
    (by fun_prop) hA
  rw [maximum_modification_first_marginal μ hδ] at h
  exact h.symm

/-- Integration helper: a pointwise bound on actual fibers over A gives the
corresponding bound on the actual joint intersection. The fiber bound itself
must be proved separately. -/
theorem maximum_modification_joint_inter_real_le (hδ : δ ∈ Icc (0 : ℝ) 1)
    {A : Set Environment} (hA : MeasurableSet A)
    {E : Set ((Environment × Environment) × (Lattice → Bool))}
    (hE : MeasurableSet E) {b : ℝ} (_hb : 0 ≤ b)
    (hbound : ∀ w ∈ A,
      (((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈ E} ≤ b) :
    ((((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {p | p.1.1 ∈ A ∧ p ∈ E} ≤ b * ((environmentLaw μ)).real A := by
  rw [maximum_modification_joint_inter_real_eq_integral μ hδ hA hE]
  calc
    _ ≤ ∫ _ in A, b ∂(environmentLaw μ) := integral_mono_ae
      (integrableOn_maximum_resampling_fiber_real μ hδ hA hE) (integrable_const b)
      ((ae_restrict_iff' hA).mpr (Filter.Eventually.of_forall hbound))
    _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- A uniform bound on actual fibers also bounds the joint intersection itself. -/
theorem maximum_modification_joint_inter_real_le_of_fiber_bound
    (hδ : δ ∈ Icc (0 : ℝ) 1)
    {A : Set Environment} (hA : MeasurableSet A)
    {E : Set ((Environment × Environment) × (Lattice → Bool))}
    (hE : MeasurableSet E) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ w ∈ A,
      (((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈ E} ≤ b) :
    ((((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)))).real {p | p.1.1 ∈ A ∧ p ∈ E} ≤ b := by
  exact (maximum_modification_joint_inter_real_le μ hδ hA hE hb hbound).trans
    ((mul_le_mul_of_nonneg_left measureReal_le_one hb).trans_eq (mul_one b))

/-- This combines an arbitrary original event with the actual resample and coin
event, using Fubini's theorem and the fiber law above. -/
theorem maximum_modification_original_inter_tail_real
    (hδ : δ ∈ Icc (0 : ℝ) 1) {A : Set Environment}
    (hA : MeasurableSet A) (v : Lattice) (q : ℝ) :
    (((environmentLaw μ).prod (environmentLaw μ)).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))).real
      {p | p.1.1 ∈ A ∧ q ≤ p.1.2 v ∧ p.2 v = true} =
      (environmentLaw μ).real A * (μ.real (Ici q) * δ) := by
  have hE : MeasurableSet
      {p : (Environment × Environment) × (Lattice → Bool) |
        q ≤ p.1.2 v ∧ p.2 v = true} :=
    (measurableSet_le measurable_const
      (show Measurable (fun p : (Environment × Environment) × (Lattice → Bool) =>
        p.1.2 v) by fun_prop)).inter
      ((measurableSet_singleton true).preimage
        (show Measurable (fun p : (Environment × Environment) × (Lattice → Bool) =>
          p.2 v) by fun_prop))
  have h := maximum_modification_joint_inter_real_eq_integral μ hδ hA hE
  simp only [mem_ofPred_eq] at h
  rw [h]
  change (∫ _w in A, ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))).real
      {r : Environment × (Lattice → Bool) | q ≤ r.1 v ∧ r.2 v = true}
        ∂(environmentLaw μ)) = _
  simp_rw [maximum_resampling_fiber_tail_probability μ hδ v q]
  rw [setIntegral_const, smul_eq_mul]

end LPPDifferentiability
