/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import ProbabilityBasics.Probability.IndependentMinimumMoment
public import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Literal sparse fields of two-predecessor minima

Each fixed color uses disjoint pairs of original iid coordinates. Measurable
sampling, currying and mapping prove its entire canonical product law.
The strict tail and its square-root integral retain all atoms. No independence
between colors or along an adaptively chosen path is asserted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The actual marginal, constructed from two independent original weights. -/
noncomputable def sparseMinimumLaw (μ : Measure ℝ) (L : ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun p : ℝ × ℝ => min (max (-L - p.1) 0) (max (-L - p.2) 0))

theorem measurable_sparseMinimum_pair (L : ℝ) :
    Measurable (fun p : ℝ × ℝ => min (max (-L - p.1) 0) (max (-L - p.2) 0)) := by
  fun_prop

instance instIsProbabilityMeasureSparseMinimumLaw (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) : IsProbabilityMeasure (sparseMinimumLaw μ L) := by
  unfold sparseMinimumLaw
  infer_instance

/-- False selects the first predecessor and true the second. -/
def sparseMinimumPredecessor (c : Fin 2 × Fin 2) (p : Lattice × Bool) : Lattice :=
  if p.2 then (2 * p.1.1 + (c.1 : ℤ), 2 * p.1.2 + (c.2 : ℤ) - 1)
  else (2 * p.1.1 + (c.1 : ℤ) - 1, 2 * p.1.2 + (c.2 : ℤ))

/-- Parity rules out cross collisions, including at negative lattice sites. -/
theorem sparseMinimumPredecessor_injective (c : Fin 2 × Fin 2) :
    Function.Injective (sparseMinimumPredecessor c) := by
  rintro ⟨⟨a₁, a₂⟩, i⟩ ⟨⟨b₁, b₂⟩, j⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  cases i <;> cases j
  · dsimp [sparseMinimumPredecessor] at h₁ h₂
    have ha : a₁ = b₁ := by omega
    have hb : a₂ = b₂ := by omega
    subst b₁
    subst b₂
    rfl
  · dsimp [sparseMinimumPredecessor] at h₁
    omega
  · dsimp [sparseMinimumPredecessor] at h₁
    omega
  · dsimp [sparseMinimumPredecessor] at h₁ h₂
    have ha : a₁ = b₁ := by omega
    have hb : a₂ = b₂ := by omega
    subst b₁
    subst b₂
    rfl

/-- Distinct sparse sites within one color use disjoint original-site supports. -/
theorem sparseMinimum_support_disjoint (c : Fin 2 × Fin 2) {a b : Lattice}
    (hab : a ≠ b) :
    Disjoint (Set.range fun i : Bool => sparseMinimumPredecessor c (a, i))
      (Set.range fun i : Bool => sparseMinimumPredecessor c (b, i)) := by
  rw [Set.disjoint_left]
  rintro z ⟨i, rfl⟩ ⟨j, h⟩
  exact hab (congrArg Prod.fst (sparseMinimumPredecessor_injective c h).symm)

/-- The literal four-color field on the original environment. -/
def sparseMinimumField (L : ℝ) (c : Fin 2 × Fin 2) (ω : Environment) : Environment :=
  fun a => min (max (-L - ω (sparseMinimumPredecessor c (a, false))) 0)
    (max (-L - ω (sparseMinimumPredecessor c (a, true))) 0)

/-- The public field is exactly the two-predecessor formula at 2a+c. -/
theorem sparseMinimumField_apply (L : ℝ) (c : Fin 2 × Fin 2) (ω : Environment)
    (a : Lattice) :
    sparseMinimumField L c ω a =
      min (max (-L - ω (2 * a.1 + (c.1 : ℤ) - 1, 2 * a.2 + (c.2 : ℤ))) 0)
        (max (-L - ω (2 * a.1 + (c.1 : ℤ), 2 * a.2 + (c.2 : ℤ) - 1)) 0) := rfl

theorem measurable_sparseMinimumField (L : ℝ) (c : Fin 2 × Fin 2) :
    Measurable (sparseMinimumField L c) := by
  unfold sparseMinimumField
  exact measurable_pi_iff.mpr fun a =>
    ((measurable_const.sub (measurable_environment_eval _)).max measurable_const).min
      ((measurable_const.sub (measurable_environment_eval _)).max measurable_const)

private theorem map_bool_minimum (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) :
    (Measure.infinitePi (fun _ : Bool => μ)).map
      (fun u : Bool → ℝ => min (max (-L - u false) 0) (max (-L - u true) 0)) =
      sparseMinimumLaw μ L := by
  have hpair := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => μ) (i := false) (j := true) Bool.false_ne_true
  rw [sparseMinimumLaw, ← hpair,
    Measure.map_map (measurable_sparseMinimum_pair L) (by fun_prop)]
  rfl

/-- The entire sparse field has its canonical product law, for each fixed color. -/
theorem environmentLaw_map_sparseMinimumField (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (c : Fin 2 × Fin 2) :
    (environmentLaw μ).map (sparseMinimumField L c) =
      environmentLaw (sparseMinimumLaw μ L) := by
  let sample : Environment → (Lattice × Bool → ℝ) :=
    fun ω p => ω (sparseMinimumPredecessor c p)
  let curry : (Lattice × Bool → ℝ) → (Lattice → Bool → ℝ) := fun u a i => u (a, i)
  let minimum : (Lattice → Bool → ℝ) → Environment := fun u a =>
    min (max (-L - u a false) 0) (max (-L - u a true) 0)
  have hs : (environmentLaw μ).map sample =
      Measure.infinitePi (fun _ : Lattice × Bool => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj (sparseMinimumPredecessor_injective c)
  have hc : (Measure.infinitePi (fun _ : Lattice × Bool => μ)).map curry =
      Measure.infinitePi (fun _ : Lattice => Measure.infinitePi (fun _ : Bool => μ)) :=
    Measure.infinitePi_map_curry (fun (_ : Lattice) (_ : Bool) => μ)
  calc
    _ = (((environmentLaw μ).map sample).map curry).map minimum := by
      rw [Measure.map_map (by fun_prop : Measurable minimum) (by fun_prop : Measurable curry),
        Measure.map_map (by fun_prop : Measurable (minimum ∘ curry))
          (by fun_prop : Measurable sample)]
      rfl
    _ = environmentLaw (sparseMinimumLaw μ L) := by
      rw [hs, hc]
      have hm := Measure.infinitePi_map_pi
        (μ := fun _ : Lattice => Measure.infinitePi (fun _ : Bool => μ))
        (f := fun (_ : Lattice) (u : Bool → ℝ) =>
          min (max (-L - u false) 0) (max (-L - u true) 0))
        (fun _ => by fun_prop)
      simpa only [map_bool_minimum, environmentLaw] using hm

/-- Every sparse coordinate has the actual product-pushforward marginal. -/
theorem environmentLaw_map_sparseMinimum_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (c : Fin 2 × Fin 2) (a : Lattice) :
    (environmentLaw μ).map (fun ω => sparseMinimumField L c ω a) =
      sparseMinimumLaw μ L := by
  rw [← environmentLaw_map_eval (sparseMinimumLaw μ L) a,
    ← environmentLaw_map_sparseMinimumField μ L c,
    Measure.map_map (measurable_environment_eval a) (measurable_sparseMinimumField L c)]
  rfl

/-- Mutual independence concerns all sparse sites of one fixed color. -/
theorem iIndepFun_sparseMinimumField (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (c : Fin 2 × Fin 2) :
    iIndepFun (fun a ω => sparseMinimumField L c ω a) (environmentLaw μ) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (X := fun a ω => sparseMinimumField L c ω a)
    (fun a => (measurable_environment_eval a).comp (measurable_sparseMinimumField L c))).mpr
  simp only [environmentLaw_map_sparseMinimum_eval]
  exact environmentLaw_map_sparseMinimumField μ L c

/-- The strict tail preserves atoms, including the atom at the cutoff. -/
theorem sparseMinimumLaw_strict_tail (μ : Measure ℝ) [SFinite μ] (L t : ℝ) (ht : 0 ≤ t) :
    sparseMinimumLaw μ L (Ioi t) = μ (Iio (-L - t)) ^ 2 := by
  rw [sparseMinimumLaw, Measure.map_apply (measurable_sparseMinimum_pair L) measurableSet_Ioi]
  have hpre : (fun p : ℝ × ℝ => min (max (-L - p.1) 0) (max (-L - p.2) 0)) ⁻¹'
      Ioi t = (Iio (-L - t)) ×ˢ (Iio (-L - t)) := by
    ext p
    simp only [mem_preimage, mem_Ioi, lt_min_iff, lt_max_iff, mem_prod, mem_Iio]
    constructor
    · rintro ⟨h₁ | h₁, h₂ | h₂⟩ <;> constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> left <;> linarith
  rw [hpre, Measure.prod_prod, pow_two]

/-- The integrated positive square-root tail equals the actual residual integral. -/
theorem sparseMinimumLaw_sqrt_tail (μ : Measure ℝ) [SFinite μ] (L : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), (sparseMinimumLaw μ L (Ioi t)) ^ (1 / 2 : ℝ)) =
      ∫⁻ x, ENNReal.ofReal (max (-L - x) 0) ∂μ := by
  rw [lintegral_eq_lintegral_meas_lt μ
    (ae_of_all _ fun x => le_max_right (-L - x) 0) (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (sparseMinimumLaw μ L (Ioi t)) ^ (1 / 2 : ℝ) = μ {a | t < max (-L - a) 0}
  rw [sparseMinimumLaw_strict_tail μ L t ht.le, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num
  congr 1
  ext x
  simp only [mem_Iio, mem_ofPred_eq]
  have ht0 : 0 < t := ht
  constructor
  · intro h
    left
    linarith
  · rintro (h | h) <;> linarith only [h, ht0]

/-- Only the original first moment is used to produce the residual first moment. -/
theorem integrable_sparseMinimum_residual (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) :
    Integrable (fun x : ℝ => max (-L - x) 0) μ :=
  ((integrable_const (-L)).sub hμ).sup (integrable_zero _ _ _)

/-- In real units the square-root tail integral is the genuine negative remainder mean. -/
theorem sparseMinimumLaw_sqrt_tail_eq_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), (sparseMinimumLaw μ L (Ioi t)) ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal (∫ x, max (-L - x) 0 ∂μ) := by
  rw [sparseMinimumLaw_sqrt_tail]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_sparseMinimum_residual μ hμ L)
    (ae_of_all _ fun x => le_max_right (-L - x) 0)).symm

/-- The independent-minimum result supplies the second moment. -/
theorem integrable_sparseMinimumLaw_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) :
    Integrable (fun x : ℝ => x ^ 2) (sparseMinimumLaw μ L) := by
  have hY := integrable_sparseMinimum_residual μ hμ L
  have hi : (fun p : ℝ × ℝ => max (-L - p.1) 0) ⟂ᵢ[μ.prod μ]
      (fun p : ℝ × ℝ => max (-L - p.2) 0) :=
    indepFun_prod (μ := μ) (ν := μ)
      (X := fun x : ℝ => max (-L - x) 0)
      (Y := fun x : ℝ => max (-L - x) 0) (by fun_prop) (by fun_prop)
  have hsq := integrable_min_sq_of_indep hi (hY.comp_fst μ) (hY.comp_snd μ)
    (ae_of_all _ fun p => le_max_right (-L - p.1) 0)
    (ae_of_all _ fun p => le_max_right (-L - p.2) 0)
  exact (integrable_map_measure (by fun_prop) (measurable_sparseMinimum_pair L).aemeasurable).mpr hsq

/-- The genuine squared-minimum mean is bounded by the square of the residual mean. -/
theorem integral_sparseMinimumLaw_sq_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) :
    (∫ x, x ^ 2 ∂sparseMinimumLaw μ L) ≤ (∫ x, max (-L - x) 0 ∂μ) ^ 2 := by
  have hY := integrable_sparseMinimum_residual μ hμ L
  have hi : (fun p : ℝ × ℝ => max (-L - p.1) 0) ⟂ᵢ[μ.prod μ]
      (fun p : ℝ × ℝ => max (-L - p.2) 0) :=
    indepFun_prod (μ := μ) (ν := μ)
      (X := fun x : ℝ => max (-L - x) 0)
      (Y := fun x : ℝ => max (-L - x) 0) (by fun_prop) (by fun_prop)
  have hb := integral_min_sq_le_mul_integral_of_indep hi (hY.comp_fst μ) (hY.comp_snd μ)
    (ae_of_all _ fun p => le_max_right (-L - p.1) 0)
    (ae_of_all _ fun p => le_max_right (-L - p.2) 0)
  rw [sparseMinimumLaw, integral_map (measurable_sparseMinimum_pair L).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) _)]
  have hf : (∫ p : ℝ × ℝ, max (-L - p.1) 0 ∂μ.prod μ) =
      ∫ x, max (-L - x) 0 ∂μ := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := μ) (ν := μ) (fun x : ℝ => max (-L - x) 0)
  have hs : (∫ p : ℝ × ℝ, max (-L - p.2) 0 ∂μ.prod μ) =
      ∫ x, max (-L - x) 0 ∂μ := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_snd (μ := μ) (ν := μ) (fun x : ℝ => max (-L - x) 0)
  rw [hf, hs] at hb
  simpa only [pow_two] using hb

end LPPDifferentiability
