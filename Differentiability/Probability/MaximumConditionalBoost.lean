/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.MaximumQuantileGap
public import Differentiability.Probability.MaximumMixtureLaw
public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Linarith

/-!
# Maximum resampling with the original environment fixed

The remaining randomness is the actual independent-copy environment times the
infinite field of independent Bernoulli coins. These are the fixed-environment
fiber facts of part (ii) of Lemma 4.1 of the differentiability preprint.
Conditional expectation and disintegration over the original environment are
not treated in this file.

## References

C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape
function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- Every finite injective vector of actual resample/coin pairs has the product
of the one-site laws. -/
theorem maximum_resampling_map_finite_pairs {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (f : I → Lattice) (hf : Function.Injective f) :
    Measure.map (fun p : Environment × (Lattice → Bool) =>
      fun i => (p.1 (f i), p.2 (f i)))
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) =
      Measure.pi (fun _ : I => μ.prod
        (ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)) := by
  let ν : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure ν := maximum_resampling_coin_is_probability hδ
  have hc : (Measure.infinitePi (fun _ : Lattice => ν)).map
      (fun χ => fun i => χ (f i)) = Measure.pi (fun _ : I => ν) := by
    have hi := (iIndepFun_infinitePi (P := fun _ : Lattice => ν)
      (X := fun (_ : Lattice) (b : Bool) => b) (fun _ => measurable_id)).precomp hf
    simpa only [Measure.infinitePi_map_eval] using
      hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply (f i)).aemeasurable)
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ Bool I
    (fun _ => μ) (fun _ => ν)).symm
  change _ = Measure.pi (fun _ : I => μ.prod ν)
  calc
    _ = Measure.map (MeasurableEquiv.arrowProdEquivProdArrow ℝ Bool I).symm
        (((environmentLaw μ).map (fun ω => fun i => ω (f i))).prod
          ((Measure.infinitePi (fun _ : Lattice => ν)).map
            (fun χ => fun i => χ (f i)))) := by
      rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [environmentLaw_map_finite_coordinates μ f hf, hc]
      exact hp.map_eq

/-- Reading an actual resample and coin at a site has their product law. -/
theorem maximum_resampling_map_pair (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) (v : Lattice) :
    Measure.map (fun p : Environment × (Lattice → Bool) => (p.1 v, p.2 v))
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) =
      μ.prod (ENNReal.ofReal (1 - δ) • Measure.dirac false +
        ENNReal.ofReal δ • Measure.dirac true) := by
  let ν : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure ν := maximum_resampling_coin_is_probability hδ
  change _ = μ.prod ν
  rw [show (fun p : Environment × (Lattice → Bool) => (p.1 v, p.2 v)) =
      Prod.map (fun ω : Environment => ω v) (fun χ : Lattice → Bool => χ v) from rfl,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    environmentLaw_map_eval μ v, Measure.infinitePi_map_eval]

/-- The actual resample/coin pairs are mutually independent across all sites. -/
theorem iIndepFun_maximum_resampling_pairs (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    iIndepFun (fun v (p : Environment × (Lattice → Bool)) => (p.1 v, p.2 v))
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) := by
  let ν : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure ν := maximum_resampling_coin_is_probability hδ
  apply iIndepFun_iff_finset.mpr
  intro S
  simp only [Finset.restrict_def]
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => (by fun_prop))).mpr
  rw [maximum_resampling_map_finite_pairs μ hδ (fun i : S => i.1)
    Subtype.val_injective]
  simp only [maximum_resampling_map_pair μ hδ]

/-- The sufficient trigger event has its actual fixed-environment probability. -/
theorem maximum_resampling_fiber_tail_probability (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (v : Lattice) (q : ℝ) :
    ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))).real
      {p : Environment × (Lattice → Bool) | q ≤ p.1 v ∧ p.2 v = true} =
      μ.real (Ici q) * δ := by
  let ν : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have hcoin : ν.real {true} = δ := by
    simp [ν, measureReal_def, Measure.add_apply, Measure.smul_apply,
      ENNReal.toReal_ofReal hδ.1]
  have h := map_measureReal_apply
    (μ := (environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice => ν)))
    (f := fun p : Environment × (Lattice → Bool) => (p.1 v, p.2 v))
    (s := Ici q ×ˢ ({true} : Set Bool))
    (by fun_prop) (measurableSet_Ici.prod (measurableSet_singleton true))
  rw [maximum_resampling_map_pair μ hδ, measureReal_prod_prod, hcoin] at h
  exact h.symm

/-- On the actual resampling fiber, every site satisfying the local CDF and
quantile-gap conditions is boosted with probability at least
`δ * α / 2`. No event law or independence assertion is assumed. -/
theorem maximum_resampling_fiber_boost_probability_lower (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ α c : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (hα : α ∈ Ioo (0 : ℝ) 1) (_hc : 0 < c)
    (w : Environment) (R : Finset Lattice) (v : Lattice) (hv : v ∈ R)
    (hF : μ.real (Iic (w v)) ≤ 1 - α)
    (hgap : c ≤ sInf {s : ℝ | μ.real (Iic (w v)) + α / 2 ≤ μ.real (Iic s)} - w v) :
    δ * α / 2 ≤
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))).real
        {p : Environment × (Lattice → Bool) |
          w v + c ≤ if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v} := by
  let ν : Measure Bool := ENNReal.ofReal (1 - δ) • Measure.dirac false +
    ENNReal.ofReal δ • Measure.dirac true
  have : IsProbabilityMeasure ν := maximum_resampling_coin_is_probability hδ
  let q : ℝ := sInf {s : ℝ | μ.real (Iic (w v)) + α / 2 ≤ μ.real (Iic s)}
  have htail : α / 2 ≤ μ.real (Ici q) := maximum_quantile_tail_lower μ hα hF
  have hsub : {p : Environment × (Lattice → Bool) | q ≤ p.1 v ∧ p.2 v = true} ⊆
      {p : Environment × (Lattice → Bool) |
        w v + c ≤ if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v} := by
    intro p hp
    change q ≤ p.1 v ∧ p.2 v = true at hp
    change w v + c ≤ if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v
    rw [ite_eq_left ⟨hv, hp.2⟩]
    have hq : w v + c ≤ q := by linarith only [hgap]
    exact (hq.trans hp.1).trans (le_max_right _ _)
  calc
    δ * α / 2 = (α / 2) * δ := by ring
    _ ≤ μ.real (Ici q) * δ := mul_le_mul_of_nonneg_right htail hδ.1
    _ = _ := (maximum_resampling_fiber_tail_probability μ hδ v q).symm
    _ ≤ _ := measureReal_mono hsub

/-- The indicators of the actual boost events are mutually independent at all
sites for every fixed original environment and every finite modification set. -/
theorem iIndepFun_maximum_resampling_fiber_boost (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (w : Environment) (R : Finset Lattice) (c : ℝ) :
    iIndepFun (fun v (p : Environment × (Lattice → Bool)) =>
      if w v + c ≤ (if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v)
      then (1 : ℝ) else 0)
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) := by
  classical
  have hm (v : Lattice) : Measurable (fun z : ℝ × Bool =>
      if w v + c ≤ (if v ∈ R ∧ z.2 = true then max (w v) z.1 else w v)
      then (1 : ℝ) else 0) := by
    have hb : MeasurableSet {z : ℝ × Bool | z.2 = true} := by
      change MeasurableSet (Prod.snd ⁻¹' ({true} : Set Bool))
      exact (measurableSet_singleton true).preimage measurable_snd
    have hcond : MeasurableSet {z : ℝ × Bool | v ∈ R ∧ z.2 = true} := by
      by_cases hv : v ∈ R
      · simpa only [hv, true_and] using hb
      · simp only [hv, false_and, ofPred_false]
        exact MeasurableSet.empty
    have hg : Measurable (fun z : ℝ × Bool =>
        if v ∈ R ∧ z.2 = true then max (w v) z.1 else w v) :=
      Measurable.ite hcond (by fun_prop) measurable_const
    exact Measurable.ite (measurableSet_le measurable_const hg)
      measurable_const measurable_const
  exact (iIndepFun_maximum_resampling_pairs μ hδ).comp _ hm

end LPPDifferentiability
