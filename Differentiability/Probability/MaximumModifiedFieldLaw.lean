/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.MaximumMixtureLaw
public import LPP_Foundations.Probability.EnvironmentLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The law of the maximum-modified environment

An original iid environment, an independent copy and an independent Bernoulli
field define the modification in Lemma 4.1(i) of the differentiability preprint.
Finite restrictions and uniqueness of product measures prove independence of
the site triples and identify the law of the entire modified field.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability

private theorem map_zip_infinitePi {ι α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : ι → Measure α) (ν : ι → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    Measure.map (fun p : (ι → α) × (ι → β) => fun i => (p.1 i, p.2 i))
      ((Measure.infinitePi μ).prod (Measure.infinitePi ν)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  classical
  refine (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro I
  let zip : (ι → α) × (ι → β) → ι → α × β := fun p i => (p.1 i, p.2 i)
  let zipI : (I → α) × (I → β) → I → α × β := fun p i => (p.1 i, p.2 i)
  have hzip : Measurable zip := by fun_prop
  have hzipI : Measurable zipI := by fun_prop
  have hfin : Measure.map zipI
      ((Measure.pi fun i : I => μ i).prod (Measure.pi fun i : I => ν i)) =
        Measure.pi (fun i : I => (μ i).prod (ν i)) := by
    exact (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow α β I)
      (measurePreserving_arrowProdEquivProdArrow α β I (fun i : I => μ i)
        (fun i : I => ν i))).map_eq
  change Measure.map I.restrict (Measure.map zip _) = _
  rw [Measure.map_map (by fun_prop) hzip]
  have heq : I.restrict ∘ zip = zipI ∘ Prod.map I.restrict I.restrict := rfl
  rw [heq, ← Measure.map_map hzipI (by fun_prop), ← Measure.map_prod_map,
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact hfin
  all_goals fun_prop

/-- The source's independent original, copy, and coin field form a probability. -/
theorem maximum_modification_joint_is_probability (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure
      (((environmentLaw μ).prod (environmentLaw μ)).prod
        (Measure.infinitePi (fun _ : Lattice =>
          ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true))) := by
  let coin : Measure Bool :=
    ENNReal.ofReal (1 - δ) • Measure.dirac false + ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  change IsProbabilityMeasure
    (((environmentLaw μ).prod (environmentLaw μ)).prod
      (Measure.infinitePi (fun _ : Lattice => coin)))
  infer_instance

/-- The literal modification is measurable as an environment-valued map. -/
theorem measurable_maximum_modification (R : Finset Lattice) :
    Measurable (fun p : (Environment × Environment) × (Lattice → Bool) =>
      fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v) := by
  classical
  apply Measurable.of_eval
  intro v
  have hcond : MeasurableSet
      {p : (Environment × Environment) × (Lattice → Bool) | v ∈ R ∧ p.2 v = true} := by
    by_cases hv : v ∈ R
    · simp only [hv, true_and]
      exact (measurableSet_singleton true).preimage
        ((measurable_pi_apply v).comp measurable_snd)
    · simp only [hv, false_and, ofPred_false, MeasurableSet.empty]
  exact Measurable.ite hcond (by fun_prop) (by fun_prop)

/-- Modification increases every coordinate for every input, without a null exception. -/
theorem maximum_modification_ge_original (R : Finset Lattice)
    (p : (Environment × Environment) × (Lattice → Bool)) (v : Lattice) :
    p.1.1 v ≤
      if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v := by
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- Under the literal joint law the original environment still has its canonical law. -/
theorem maximum_modification_first_marginal (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    Measure.map (fun p : (Environment × Environment) × (Lattice → Bool) => p.1.1)
      (((environmentLaw μ).prod (environmentLaw μ)).prod
        (Measure.infinitePi (fun _ : Lattice =>
          ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true))) = environmentLaw μ := by
  let coin : Measure Bool :=
    ENNReal.ofReal (1 - δ) • Measure.dirac false + ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  change Measure.map (Prod.fst ∘ Prod.fst)
    (((environmentLaw μ).prod (environmentLaw μ)).prod
      (Measure.infinitePi (fun _ : Lattice => coin))) = _
  rw [← Measure.map_map measurable_fst measurable_fst]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

/-- The actual site triples have their entire independent product law. -/
theorem maximum_modification_triples_map (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    Measure.map (fun p : (Environment × Environment) × (Lattice → Bool) =>
      fun v => ((p.1.1 v, p.1.2 v), p.2 v))
      (((environmentLaw μ).prod (environmentLaw μ)).prod
        (Measure.infinitePi (fun _ : Lattice =>
          ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true))) =
      Measure.infinitePi (fun _ : Lattice =>
        (μ.prod μ).prod
          (ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true)) := by
  let coin : Measure Bool :=
    ENNReal.ofReal (1 - δ) • Measure.dirac false + ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  let A : Environment × Environment → Lattice → ℝ × ℝ :=
    fun p v => (p.1 v, p.2 v)
  let B : (Lattice → ℝ × ℝ) × (Lattice → Bool) → Lattice → (ℝ × ℝ) × Bool :=
    fun p v => (p.1 v, p.2 v)
  have hA : Measurable A := by fun_prop
  have hB : Measurable B := by fun_prop
  have hAmap : Measure.map A ((environmentLaw μ).prod (environmentLaw μ)) =
      Measure.infinitePi (fun _ : Lattice => μ.prod μ) :=
    map_zip_infinitePi (fun _ : Lattice => μ) (fun _ : Lattice => μ)
  change Measure.map (B ∘ Prod.map A id)
    (((environmentLaw μ).prod (environmentLaw μ)).prod
      (Measure.infinitePi (fun _ : Lattice => coin))) = _
  rw [← Measure.map_map hB (hA.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hA measurable_id, Measure.map_id, hAmap]
  exact map_zip_infinitePi (fun _ : Lattice => μ.prod μ) (fun _ : Lattice => coin)

/-- The source's site triples are independent under the actual original/copy/coin law. -/
theorem maximum_modification_triples_independent (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    iIndepFun
      (fun v (p : (Environment × Environment) × (Lattice → Bool)) =>
        ((p.1.1 v, p.1.2 v), p.2 v))
      (((environmentLaw μ).prod (environmentLaw μ)).prod
        (Measure.infinitePi (fun _ : Lattice =>
          ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true))) := by
  let coin : Measure Bool :=
    ENNReal.ofReal (1 - δ) • Measure.dirac false + ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  let J := ((environmentLaw μ).prod (environmentLaw μ)).prod
    (Measure.infinitePi (fun _ : Lattice => coin))
  let T : (Environment × Environment) × (Lattice → Bool) → Lattice → (ℝ × ℝ) × Bool :=
    fun p v => ((p.1.1 v, p.1.2 v), p.2 v)
  have hT : Measurable T := by fun_prop
  have hmap : Measure.map T J =
      Measure.infinitePi (fun _ : Lattice => (μ.prod μ).prod coin) :=
    maximum_modification_triples_map μ hδ
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).mpr
  rw [hmap]
  congr 1
  funext v
  change (μ.prod μ).prod coin = Measure.map ((fun t => t v) ∘ T) J
  rw [← Measure.map_map (measurable_pi_apply v) hT, hmap,
    Measure.infinitePi_map_eval]

/-- The complete modified environment law is the product of the actual one-site laws. -/
theorem maximum_modification_map_eq_infinitePi (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Measure.map (fun p : (Environment × Environment) × (Lattice → Bool) =>
      fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
      (((environmentLaw μ).prod (environmentLaw μ)).prod
        (Measure.infinitePi (fun _ : Lattice =>
          ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true))) =
      Measure.infinitePi (fun v : Lattice => if v ∈ R then
        Measure.map (fun p : (ℝ × ℝ) × Bool =>
          if p.2 then max p.1.1 p.1.2 else p.1.1)
          ((μ.prod μ).prod
            (ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true)) else μ) := by
  classical
  let coin : Measure Bool :=
    ENNReal.ofReal (1 - δ) • Measure.dirac false + ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure coin := maximum_resampling_coin_is_probability hδ
  let J := ((environmentLaw μ).prod (environmentLaw μ)).prod
    (Measure.infinitePi (fun _ : Lattice => coin))
  let T : (Environment × Environment) × (Lattice → Bool) → Lattice → (ℝ × ℝ) × Bool :=
    fun p v => ((p.1.1 v, p.1.2 v), p.2 v)
  let f : Lattice → (ℝ × ℝ) × Bool → ℝ :=
    fun v p => if v ∈ R ∧ p.2 = true then max p.1.1 p.1.2 else p.1.1
  have hT : Measurable T := by fun_prop
  have hf (v : Lattice) : Measurable (f v) := by
    have hcond : MeasurableSet {p : (ℝ × ℝ) × Bool | v ∈ R ∧ p.2 = true} := by
      by_cases hv : v ∈ R
      · simp only [hv, true_and]
        exact (measurableSet_singleton true).preimage measurable_snd
      · simp only [hv, false_and, ofPred_false, MeasurableSet.empty]
    exact Measurable.ite hcond (by fun_prop) (by fun_prop)
  have hmap : Measure.map T J =
      Measure.infinitePi (fun _ : Lattice => (μ.prod μ).prod coin) :=
    maximum_modification_triples_map μ hδ
  have hF : Measurable (fun t : Lattice → (ℝ × ℝ) × Bool =>
      fun v => f v (t v)) := by
    apply Measurable.of_eval
    intro v
    exact (hf v).comp (measurable_pi_apply v)
  change Measure.map ((fun t v => f v (t v)) ∘ T) J = _
  rw [← Measure.map_map hF hT, hmap, Measure.infinitePi_map_pi _ hf]
  congr 1
  funext v
  by_cases hv : v ∈ R
  · simp only [hv, ite_true]
    congr 1
    funext p
    simp only [f, hv, true_and]
  · simp only [f, hv, false_and, ite_false]
    change Measure.map (Prod.fst ∘ Prod.fst) ((μ.prod μ).prod coin) = μ
    rw [← Measure.map_map measurable_fst measurable_fst]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]

/-- In-region factors are exactly the source's retain-or-maximum mixture. -/
theorem maximum_modification_map_eq_mixture_product (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Measure.map (fun p : (Environment × Environment) × (Lattice → Bool) =>
      fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
      (((environmentLaw μ).prod (environmentLaw μ)).prod
        (Measure.infinitePi (fun _ : Lattice =>
          ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true))) =
      Measure.infinitePi (fun v : Lattice => if v ∈ R then
        ENNReal.ofReal (1 - δ) • μ + ENNReal.ofReal δ •
          Measure.map (fun p : ℝ × ℝ => max p.1 p.2) (μ.prod μ) else μ) := by
  rw [maximum_modification_map_eq_infinitePi μ hδ R]
  congr 1
  funext v
  by_cases hv : v ∈ R
  · simp only [hv, ite_true]
    exact maximum_resampling_map_eq_mixture μ hδ
  · simp only [hv, ite_false]

/-- Each in-region factor is the literal affine-density law from Lemma 4.1(i) of the
differentiability preprint. -/
theorem maximum_modification_map_eq_density_product (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Measure.map (fun p : (Environment × Environment) × (Lattice → Bool) =>
      fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
      (((environmentLaw μ).prod (environmentLaw μ)).prod
        (Measure.infinitePi (fun _ : Lattice =>
          ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true))) =
      Measure.infinitePi (fun v : Lattice => if v ∈ R then
        μ.withDensity (fun t => ENNReal.ofReal
          (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)))) else μ) := by
  rw [maximum_modification_map_eq_infinitePi μ hδ R]
  congr 1
  funext v
  by_cases hv : v ∈ R
  · simp only [hv, ite_true]
    exact maximum_resampling_map_eq_withDensity μ hδ
  · simp only [hv, ite_false]

end LPPDifferentiability
