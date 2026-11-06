/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.MaximumConditionalBoost
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Finite selected-site maximum boost counts

The proof of Lemma 4.2 of the differentiability preprint compares the number of
resampling boosts with a binomial variable. For each fixed original environment,
this file proves that comparison and its Chebyshev lower-tail bound.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability

private theorem threshold_bernoulli (p : unitInterval) :
    HasLaw (fun x : ℝ => if x ≤ (p : ℝ) then (1 : ℝ) else 0)
      (bernoulliMeasure (1 : ℝ) 0 p) (volume.restrict (Icc (0 : ℝ) 1)) := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  have hprob : (volume.restrict (Icc (0 : ℝ) 1)).real (Iic (p : ℝ)) = p := by
    rw [measureReal_def, Measure.restrict_apply measurableSet_Iic]
    have heq : Iic (p : ℝ) ∩ Icc 0 1 = Icc (0 : ℝ) (p : ℝ) := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · intro h; exact ⟨h.2.1, h.1⟩
      · intro h; exact ⟨h.2, h.1, h.2.trans p.2.2⟩
    rw [heq, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal p.2.1]
  have h := hasLaw_indicator_one_bernoulliMeasure (M := ℝ)
    (P := volume.restrict (Icc (0 : ℝ) 1)) (s := Iic (p : ℝ)) measurableSet_Iic.nullMeasurableSet
  have heq : (Iic (p : ℝ)).indicator (1 : ℝ → ℝ) =
      (fun x : ℝ => if x ≤ (p : ℝ) then (1 : ℝ) else 0) := by
    funext x
    simp only [Set.indicator_apply, Pi.one_apply, mem_Iic]
  have hp : (⟨(volume.restrict (Icc (0 : ℝ) 1)).real (Iic (p : ℝ)),
      hprob.symm ▸ p.property⟩ :
      unitInterval) = p := Subtype.ext hprob
  simpa only [heq, hp] using h

private theorem sum_bernoulli_hasLaw {ι : Type*} [Fintype ι]
    (p : unitInterval) :
    HasLaw (fun x : ι → ℝ => ∑ i, x i)
      ((binomial (Fintype.card ι) p).map (Nat.cast : ℕ → ℝ))
      (Measure.pi (fun _ : ι => bernoulliMeasure (1 : ℝ) 0 p)) := by
  classical
  let B : Measure (Set ι) := setBernoulli univ p
  have hcard : B.map Set.ncard = binomial (Fintype.card ι) p := by
    apply Measure.ext_of_singleton
    intro k
    rw [map_ncard_setBernoulli_singleton (finite_univ) p,
      binomial_singleton]
    simp only [ncard_univ, Nat.card_eq_fintype_card]
  have hmap : B.map (fun s => fun i : ι => if i ∈ s then (1 : ℝ) else 0) =
      Measure.pi (fun _ : ι => bernoulliMeasure (1 : ℝ) 0 p) := by
    rw [show B = setBernoulli univ p from rfl, setBernoulli_eq_map,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.infinitePi_eq_pi]
    change (Measure.pi (fun i : ι => bernoulliMeasure (i ∈ univ) False p)).map
      (fun (a : ι → Prop) i => if a i then (1 : ℝ) else 0) = _
    rw [Measure.pi_map_pi (f := fun (_ : ι) (b : Prop) => if b then (1 : ℝ) else 0)
      (fun _ => (by fun_prop))]
    congr 1
    funext i
    rw [map_bernoulliMeasure]
    simp only [mem_univ, ite_true, ite_false]
  refine ⟨by fun_prop, ?_⟩
  rw [← hmap, Measure.map_map (by fun_prop) (by fun_prop), ← hcard,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext s
  simp only [Function.comp_apply]
  rw [Set.ncard_eq_toFinset_card s]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  simp [Set.toFinset]

private theorem threshold_vector_hasLaw {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) :
    HasLaw (fun x : ι → ℝ => fun i => if x i ≤ (p i : ℝ) then (1 : ℝ) else 0)
      (Measure.pi (fun i => bernoulliMeasure (1 : ℝ) 0 (p i)))
      (Measure.pi (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1))) := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  refine ⟨(Measurable.of_eval (fun i => Measurable.ite
    (measurableSet_le (measurable_pi_apply i) measurable_const)
    measurable_const measurable_const)).aemeasurable, ?_⟩
  rw [Measure.pi_map_pi (f := fun i (x : ℝ) => if x ≤ (p i : ℝ) then (1 : ℝ) else 0)
    (fun i => (threshold_bernoulli (p i)).aemeasurable)]
  congr 1
  funext i
  exact (threshold_bernoulli (p i)).map_eq

open Classical in
private theorem independent_indicators_lower_tail {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (p : unitInterval)
    (hp : ∀ i, (p : ℝ) ≤ P.real (A i))
    (hi : iIndepFun (fun i ω => if ω ∈ A i then (1 : ℝ) else 0) P)
    (t : ℝ) :
    P.real {ω | (∑ i, if ω ∈ A i then (1 : ℝ) else 0) < t} ≤
      (binomial (Fintype.card ι) p).real {k | (k : ℝ) < t} := by
  classical
  let q : ι → unitInterval := fun i => ⟨P.real (A i), measureReal_nonneg, measureReal_le_one⟩
  have hactual (i : ι) : HasLaw (fun ω => if ω ∈ A i then (1 : ℝ) else 0)
      (bernoulliMeasure (1 : ℝ) 0 (q i)) P := by
    have h := hasLaw_indicator_one_bernoulliMeasure (P := P) (M := ℝ)
      (hA i).nullMeasurableSet
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      simp only [Set.indicator_apply, Pi.one_apply]))
  have hv := hi.hasLaw_pi hactual
  let U : Measure (ι → ℝ) := Measure.pi (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1))
  let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  let : IsProbabilityMeasure U := by dsimp [U]; infer_instance
  have hsum : HasLaw (fun x : ι → ℝ => ∑ i, if x i ≤ (p : ℝ) then (1 : ℝ) else 0)
      ((binomial (Fintype.card ι) p).map (Nat.cast : ℕ → ℝ)) U :=
    (sum_bernoulli_hasLaw p).fun_comp (threshold_vector_hasLaw (fun _ : ι => p))
  have hlarge :
      P.real {ω | (∑ i, if ω ∈ A i then (1 : ℝ) else 0) < t} =
      U.real {x | (∑ i, if x i ≤ (q i : ℝ) then (1 : ℝ) else 0) < t} := by
    exact (hv.measureReal_eq (p := fun y => (∑ i, y i) < t)
      (measurableSet_lt (by fun_prop) measurable_const)).trans
      ((threshold_vector_hasLaw q).measureReal_eq
        (p := fun y => (∑ i, y i) < t)
        (measurableSet_lt (by fun_prop) measurable_const)).symm
  rw [hlarge]
  calc
    _ ≤ U.real {x | (∑ i, if x i ≤ (p : ℝ) then (1 : ℝ) else 0) < t} := by
      refine measureReal_mono ?_ (measure_ne_top U _)
      intro x hx
      have hle : (∑ i, if x i ≤ (p : ℝ) then (1 : ℝ) else 0) ≤
          ∑ i, if x i ≤ (q i : ℝ) then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : x i ≤ (p : ℝ)
        · have hq : x i ≤ (q i : ℝ) := h.trans (hp i)
          rw [ite_eq_left h, ite_eq_left hq]
        · simp only [ite_eq_right h]
          split_ifs <;> norm_num
      exact hle.trans_lt hx
    _ = _ := by
      rw [hsum.measureReal_eq measurableSet_Iio]
      change ((binomial (Fintype.card ι) p).map (Nat.cast : ℕ → ℝ)).real (Iio t) = _
      exact map_measureReal_apply (by fun_prop) measurableSet_Iio

private theorem binomial_lower_tail_le (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (binomial n p).real {k | (k : ℝ) < (n : ℝ) * p / 2} ≤
      4 / ((n : ℝ) * p) := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  let U : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => ν)
  let : IsProbabilityMeasure U := by dsimp [U]; infer_instance
  let f : ℝ → ℝ := fun x => if x ≤ (p : ℝ) then 1 else 0
  let X : (Fin n → ℝ) → ℝ := fun x => ∑ i, f (x i)
  have hf : Measurable f := Measurable.ite (measurableSet_le measurable_id
    measurable_const) measurable_const measurable_const
  have hflaw : HasLaw f (bernoulliMeasure (1 : ℝ) 0 p) ν := threshold_bernoulli p
  have hfLp : MemLp f 2 ν := MemLp.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by dsimp [f]; split_ifs <;> norm_num))
  have hfmean : (∫ x, f x ∂ν) = p := by
    rw [hflaw.integral_eq, integral_bernoulliMeasure]
    simp
  have hfsecond : (∫ x, (f x) ^ 2 ∂ν) = p := by
    have h := hflaw.integral_comp (f := fun y : ℝ => y ^ 2) (by fun_prop)
    change (∫ x, (f x) ^ 2 ∂ν) = _ at h
    rw [h, integral_bernoulliMeasure]
    simp
  have hfvar : variance f ν = (p : ℝ) - (p : ℝ) ^ 2 := by
    rw [variance_eq_sub hfLp, hfmean]
    exact congrArg (fun z : ℝ => z - (p : ℝ) ^ 2) hfsecond
  have hXLp : MemLp X 2 U :=
    memLp_finsetSum Finset.univ (fun i _ =>
      hfLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => ν) i))
  have hXlaw : HasLaw X ((binomial n p).map (Nat.cast : ℕ → ℝ)) U := by
    simpa only [Fintype.card_fin] using
      (sum_bernoulli_hasLaw p).fun_comp (threshold_vector_hasLaw (fun _ : Fin n => p))
  have hmean : (∫ x, X x ∂U) = (n : ℝ) * p := by
    rw [integral_of_hasLaw_binomial hXlaw, mul_comm]
  have hvar : variance X U ≤ (n : ℝ) * p := by
    have h : variance X U = ∑ _ : Fin n, variance f ν := by
      have heq : (∑ i : Fin n, fun ω : Fin n → ℝ => f (ω i)) = X := by
        funext x
        simp only [Finset.sum_apply]
        rfl
      have h := variance_sum_pi (μ := fun _ : Fin n => ν) (X := fun _ : Fin n => f)
        (fun _ => hfLp)
      rw [heq] at h
      exact h
    rw [h, hfvar]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (Nat.cast_nonneg n)
  have hmean_pos : 0 < (n : ℝ) * p := mul_pos (Nat.cast_pos.mpr hn) hp
  have hcheb := meas_ge_le_variance_div_sq hXLp (half_pos hmean_pos)
  have hsub : {x | X x < (n : ℝ) * p / 2} ⊆
      {x | (n : ℝ) * p / 2 ≤ |X x - ∫ y, X y ∂U|} := by
    intro x hx
    change X x < (n : ℝ) * p / 2 at hx
    change (n : ℝ) * p / 2 ≤ |X x - ∫ y, X y ∂U|
    rw [hmean]
    have hneg : X x - (n : ℝ) * p ≤ 0 := by linarith only [hx, hmean_pos]
    rw [abs_of_nonpos hneg]
    linarith only [hx]
  have htail : U.real {x | X x < (n : ℝ) * p / 2} ≤
      variance X U / (((n : ℝ) * p / 2) ^ 2) := by
    have hbound := (measure_mono hsub).trans hcheb
    exact (ENNReal.toReal_mono (by finiteness) hbound).trans_eq
      (ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X U) (sq_nonneg _)))
  have hcompare : (binomial n p).real {k | (k : ℝ) < (n : ℝ) * p / 2} =
      U.real {x | X x < (n : ℝ) * p / 2} := by
    rw [hXlaw.measureReal_eq measurableSet_Iio]
    change _ = ((binomial n p).map (Nat.cast : ℕ → ℝ)).real (Iio _)
    exact (map_measureReal_apply (μ := binomial n p) (f := (Nat.cast : ℕ → ℝ))
      (s := Iio ((n : ℝ) * p / 2)) (by fun_prop) measurableSet_Iio).symm
  rw [hcompare]
  calc
    _ ≤ variance X U / (((n : ℝ) * p / 2) ^ 2) := htail
    _ ≤ ((n : ℝ) * p) / (((n : ℝ) * p / 2) ^ 2) :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = _ := by field_simp [ne_of_gt hp, ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]; ring

/-- The selected-site comparison parameter is a probability. -/
theorem maximum_resampling_comparator_parameter_mem_unit {δ α : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hα : α ∈ Ioo (0 : ℝ) 1) :
    δ * α / 2 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (mul_nonneg hδ.1.le hα.1.le) (by norm_num)
  · have hmul : δ * α ≤ 1 := by
      calc
        δ * α ≤ 1 * 1 := mul_le_mul hδ.2.le hα.2.le hα.1.le (by norm_num)
        _ = 1 := one_mul 1
    linarith only [hmul]

private theorem measurableSet_maximum_resampling_fiber_boost
    (w : Environment) (R : Finset Lattice) (c : ℝ) (v : Lattice) :
    MeasurableSet {p : Environment × (Lattice → Bool) |
      w v + c ≤ if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v} := by
  classical
  have hb : MeasurableSet {p : Environment × (Lattice → Bool) | p.2 v = true} :=
    (measurableSet_singleton true).preimage ((measurable_pi_apply v).comp measurable_snd)
  have hcond : MeasurableSet {p : Environment × (Lattice → Bool) |
      v ∈ R ∧ p.2 v = true} := by
    by_cases hv : v ∈ R
    · simpa only [hv, true_and] using hb
    · simp only [hv, false_and, ofPred_false]
      exact MeasurableSet.empty
  exact measurableSet_le measurable_const
    (Measurable.ite hcond (by fun_prop) measurable_const)

/-- The literal finite boost count has measurable strict lower-tail events. -/
theorem measurableSet_maximum_resampling_fiber_count_lt
    (w : Environment) (R S : Finset Lattice) (c t : ℝ) :
    MeasurableSet {p : Environment × (Lattice → Bool) |
      (∑ v ∈ S, if w v + c ≤
        (if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v)
        then (1 : ℝ) else 0) < t} := by
  apply measurableSet_lt _ measurable_const
  exact Finset.measurable_sum S (fun v _ => Measurable.ite
    (measurableSet_maximum_resampling_fiber_boost w R c v)
    measurable_const measurable_const)

/-- For a fixed original environment and a nonempty selected set of good sites,
the actual boost count stochastically dominates the standard binomial law.
The event probabilities and independence are derived from the actual
resampling law inside the proof. -/
theorem maximum_resampling_fiber_count_stochastic_domination
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ α c : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hα : α ∈ Ioo (0 : ℝ) 1) (hc : 0 < c)
    (w : Environment) (R S : Finset Lattice) (hSR : S ⊆ R) (_hS : S.Nonempty)
    (hF : ∀ v ∈ S, μ.real (Iic (w v)) ≤ 1 - α)
    (hgap : ∀ v ∈ S, c ≤
      sInf {s : ℝ | μ.real (Iic (w v)) + α / 2 ≤ μ.real (Iic s)} - w v)
    (t : ℝ) :
    ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
      ENNReal.ofReal (1 - δ) • Measure.dirac false +
        ENNReal.ofReal δ • Measure.dirac true))).real
      {p : Environment × (Lattice → Bool) |
        (∑ v ∈ S, if w v + c ≤
          (if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v)
          then (1 : ℝ) else 0) < t} ≤
      (binomial S.card ⟨δ * α / 2, maximum_resampling_comparator_parameter_mem_unit hδ hα⟩).real
        {k | (k : ℝ) < t} := by
  classical
  have hδcc : δ ∈ Icc (0 : ℝ) 1 := ⟨hδ.1.le, hδ.2.le⟩
  let ν : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  let : IsProbabilityMeasure ν := maximum_resampling_coin_is_probability hδcc
  let K := (environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice => ν))
  let : IsProbabilityMeasure K := by dsimp [K]; infer_instance
  let A : S → Set (Environment × (Lattice → Bool)) := fun v =>
    {p | w v + c ≤ if (v : Lattice) ∈ R ∧ p.2 v = true
      then max (w v) (p.1 v) else w v}
  have h := independent_indicators_lower_tail K A
    (fun v => measurableSet_maximum_resampling_fiber_boost w R c v)
    ⟨δ * α / 2, maximum_resampling_comparator_parameter_mem_unit hδ hα⟩
    (fun v => maximum_resampling_fiber_boost_probability_lower μ hδcc hα hc
      w R v (hSR v.property) (hF v v.property) (hgap v v.property))
    ((iIndepFun_maximum_resampling_fiber_boost μ hδcc w R c).precomp
      (g := fun v : S => (v : Lattice)) Subtype.val_injective) t
  have hsum (p : Environment × (Lattice → Bool)) :
      (∑ v : S, if p ∈ A v then (1 : ℝ) else 0) =
      ∑ v ∈ S, if w v + c ≤
        (if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v)
        then (1 : ℝ) else 0 :=
    Finset.sum_coe_sort S (fun v => if w v + c ≤
      (if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v)
      then (1 : ℝ) else 0)
  simp_rw [hsum] at h
  simpa only [K, ν, Fintype.card_coe] using h

/-- The Chebyshev estimate in the proof of Lemma 4.2 of the differentiability
preprint, for the fixed-environment boost count. Here `lam` is the binomial mean. -/
theorem maximum_resampling_fiber_count_lower_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ α c : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hα : α ∈ Ioo (0 : ℝ) 1) (hc : 0 < c)
    (w : Environment) (R S : Finset Lattice) (hSR : S ⊆ R) (hS : S.Nonempty)
    (hF : ∀ v ∈ S, μ.real (Iic (w v)) ≤ 1 - α)
    (hgap : ∀ v ∈ S, c ≤
      sInf {s : ℝ | μ.real (Iic (w v)) + α / 2 ≤ μ.real (Iic s)} - w v) :
    let lam : ℝ := (S.card : ℝ) * δ * α / 2
    0 < lam ∧
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))).real
        {p : Environment × (Lattice → Bool) |
          (∑ v ∈ S, if w v + c ≤
            (if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v)
            then (1 : ℝ) else 0) < lam / 2} ≤ 4 / lam := by
  dsimp only
  have hp : 0 < δ * α / 2 := div_pos (mul_pos hδ.1 hα.1) (by norm_num)
  have hn : 0 < S.card := hS.card_pos
  have hmean : (S.card : ℝ) * (δ * α / 2) = (S.card : ℝ) * δ * α / 2 := by ring
  constructor
  · rw [← hmean]
    exact mul_pos (Nat.cast_pos.mpr hn) hp
  · have hdom := maximum_resampling_fiber_count_stochastic_domination μ hδ hα hc
      w R S hSR hS hF hgap ((S.card : ℝ) * δ * α / 2 / 2)
    have hbin := binomial_lower_tail_le S.card hn
      ⟨δ * α / 2, maximum_resampling_comparator_parameter_mem_unit hδ hα⟩ hp
    change (binomial S.card ⟨δ * α / 2, maximum_resampling_comparator_parameter_mem_unit hδ hα⟩).real
      {k | (k : ℝ) < (S.card : ℝ) * (δ * α / 2) / 2} ≤
        4 / ((S.card : ℝ) * (δ * α / 2)) at hbin
    rw [hmean] at hbin
    exact hdom.trans hbin

end LPPDifferentiability
