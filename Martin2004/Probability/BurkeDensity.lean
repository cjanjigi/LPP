/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Lebesgue measure on three-space and the density of three exponential laws

Tools for the Burke property of one cell (`Probability/BurkeCell.lean`).

* A shear that adds a function of two coordinates to the third coordinate preserves
  Lebesgue measure on `ℝ × ℝ × ℝ`, and so do the two coordinate swaps used below.
* The product of three exponential laws is Lebesgue measure with the product density.

Mathlib has the shear for a product of two groups (`measurePreserving_prod_add`) and the
product of two density measures (`prod_withDensity`); this file combines them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Adding a measurable function of the last two coordinates to the first coordinate preserves
Lebesgue measure on `ℝ × ℝ × ℝ`. -/
theorem measurePreserving_shear_first (k : ℝ × ℝ → ℝ) (hk : Measurable k) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.1 + k p.2, p.2))
      (volume : Measure (ℝ × ℝ × ℝ)) volume := by
  have hskew : MeasurePreserving (fun z : (ℝ × ℝ) × ℝ => (z.1, z.2 + k z.1))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
      (g := fun q x => x + k q) (measurable_snd.add (hk.comp measurable_fst))
      (Filter.Eventually.of_forall fun q => map_add_right_eq_self (volume : Measure ℝ) (k q))
  have hswap₁ : MeasurePreserving (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  have hswap₂ : MeasurePreserving (Prod.swap : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
    Measure.measurePreserving_swap
  exact hswap₂.comp (hskew.comp hswap₁)

/-- Swapping the last two coordinates preserves Lebesgue measure on `ℝ × ℝ × ℝ`. -/
theorem measurePreserving_swap_last :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2, p.2.1))
      (volume : Measure (ℝ × ℝ × ℝ)) volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))

/-- Swapping the first two coordinates preserves Lebesgue measure on `ℝ × ℝ × ℝ`. -/
theorem measurePreserving_swap_first :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.2.1, p.1, p.2.2))
      (volume : Measure (ℝ × ℝ × ℝ)) volume := by
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) :=
    measurePreserving_prodAssoc volume volume volume
  have hassoc' : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ).symm
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) :=
    hassoc.symm _
  have hmid : MeasurePreserving (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) (id : ℝ → ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  exact hassoc.comp (hmid.comp hassoc')

/-- The product of three exponential laws is Lebesgue measure on `ℝ × ℝ × ℝ` with the product of
the three exponential densities. -/
theorem expMeasure_prod_prod_eq_withDensity (a b c : ℝ) :
    (expMeasure a).prod ((expMeasure b).prod (expMeasure c)) =
      (volume : Measure (ℝ × ℝ × ℝ)).withDensity
        (fun p => exponentialPDF a p.1 * (exponentialPDF b p.2.1 * exponentialPDF c p.2.2)) := by
  have hm : ∀ r : ℝ, Measurable (exponentialPDF r) := fun r =>
    (measurable_exponentialPDFReal r).ennreal_ofReal
  have hbc : Measurable (fun z : ℝ × ℝ => exponentialPDF b z.1 * exponentialPDF c z.2) :=
    ((hm b).comp measurable_fst).mul ((hm c).comp measurable_snd)
  show ((volume : Measure ℝ).withDensity (exponentialPDF a)).prod
      (((volume : Measure ℝ).withDensity (exponentialPDF b)).prod
        ((volume : Measure ℝ).withDensity (exponentialPDF c))) = _
  rw [prod_withDensity (hm b) (hm c), prod_withDensity (hm a) hbc]
  rfl

end LPPDifferentiability
