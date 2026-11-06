/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Independent finite uniform origins

The parameter `n` gives a window of `n + 1` possible origins.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- The uniform law on a nonempty finite origin window. -/
@[expose] noncomputable def uniformOriginLaw (n : ℕ) : Measure (Fin (n + 1)) :=
  (PMF.uniformOfFintype (Fin (n + 1))).toMeasure

instance uniformOriginLaw_probability (n : ℕ) : IsProbabilityMeasure (uniformOriginLaw n) := by
  unfold uniformOriginLaw
  infer_instance

/-- The original experiment with an independent uniform origin added. -/
@[expose] noncomputable def uniformOriginProduct {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) : Measure (Ω × Fin (n + 1)) :=
  μ.prod (uniformOriginLaw n)

instance uniformOriginProduct_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (uniformOriginProduct μ n) := by
  unfold uniformOriginProduct
  infer_instance

/-- The positive integer origin used by Liggett. -/
@[expose] def uniformOrigin {Ω : Type*} {n : ℕ} (p : Ω × Fin (n + 1)) : ℕ :=
  p.2.val + 1

theorem uniformOrigin_bounds {Ω : Type*} {n : ℕ} (p : Ω × Fin (n + 1)) :
    1 ≤ uniformOrigin p ∧ uniformOrigin p ≤ n + 1 := by
  have := p.2.isLt
  dsimp [uniformOrigin]
  omega

theorem uniformOriginLaw_singleton (n : ℕ) (u : Fin (n + 1)) :
    uniformOriginLaw n {u} = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  simp [uniformOriginLaw]

theorem uniformOriginProduct_fst {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) :
    MeasurePreserving Prod.fst (uniformOriginProduct μ n) μ :=
  measurePreserving_fst

theorem uniformOriginProduct_snd {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving Prod.snd (uniformOriginProduct μ n) (uniformOriginLaw n) :=
  measurePreserving_snd

theorem indepFun_uniformOrigin {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) {X : Ω → E}
    (hX : Measurable X) :
    IndepFun (fun p : Ω × Fin (n + 1) => X p.1) uniformOrigin
      (uniformOriginProduct μ n) :=
  indepFun_prod (μ := μ) (ν := uniformOriginLaw n) hX
    (measurable_of_countable (fun u : Fin (n + 1) => u.val + 1))

theorem integrable_uniformOrigin_family {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (f : Fin (n + 1) → Ω → ℝ) (hm : ∀ u, Measurable (f u))
    (hi : ∀ u, Integrable (f u) μ) :
    Integrable (fun p : Ω × Fin (n + 1) => f p.2 p.1) (uniformOriginProduct μ n) := by
  apply (integrable_prod_iff' (measurable_from_prod_countable_left hm).aestronglyMeasurable).2
  refine ⟨ae_of_all _ hi, ?_⟩
  exact integrableOn_univ.mp (IntegrableOn.of_finite (Set.toFinite Set.univ))

theorem integral_uniformOriginLaw (n : ℕ) (f : Fin (n + 1) → ℝ) :
    (∫ u, f u ∂uniformOriginLaw n) = (∑ u, f u) / (n + 1 : ℝ) := by
  rw [integral_fintype (integrableOn_univ.mp
    (IntegrableOn.of_finite (Set.toFinite Set.univ)))]
  simp only [measureReal_def, uniformOriginLaw_singleton, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [div_eq_inv_mul]

/-- Finite averaging under the product measure. -/
theorem integral_uniformOrigin_family {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (f : Fin (n + 1) → Ω → ℝ) (hm : ∀ u, Measurable (f u))
    (hi : ∀ u, Integrable (f u) μ) :
    (∫ p, f p.2 p.1 ∂uniformOriginProduct μ n) =
      (∑ u, ∫ ω, f u ω ∂μ) / (n + 1 : ℝ) := by
  rw [uniformOriginProduct, integral_prod_symm _ (integrable_uniformOrigin_family μ n f hm hi)]
  exact integral_uniformOriginLaw _ _

end LPPDifferentiability
