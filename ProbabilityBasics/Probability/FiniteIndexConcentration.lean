/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.SharpFiniteProductConcentration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp concentration for arbitrary finite index types

The sharp concentration estimates for a product over a finite index type `ι` are first proved
for a product indexed by `Fin n`, and then transferred along an enumeration of `ι`. The product
law, the mean of the observable, measurability, the bounds, and the coordinate oscillation are
carried along this transfer.

## Main results

- `integral_exp_centered_pi_le_sharp_of_fintype`: the sharp bound on the centered moment
  generating function.
- `hasSubgaussianMGF_centered_pi_sharp_of_fintype`: the sub-Gaussian bound for the centered
  function, with proxy `card ι * b ^ 2 / 4`.
- `measure_ge_centered_pi_le_sharp_of_fintype`: the upper tail at positive scale.
- `measure_ge_centered_pi_eq_of_scale_eq_zero_of_fintype`: the exact upper-tail probability at
  zero scale.

The bound `M` on the function and the bound `b` on its coordinate oscillation are hypotheses of
each statement. An application must verify them from its own definitions.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

noncomputable section

section FintypeConcentration

variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
variable (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
variable {F : (ι → Ω) → ℝ} {M b : ℝ}

local instance : DecidableEq ι := Classical.decEq ι

/-- The sharp centered MGF estimate for a heterogeneous finite product. -/
theorem integral_exp_centered_pi_le_sharp_of_fintype
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b) (t : ℝ) :
    (∫ x, Real.exp (t * (F x - ∫ z, F z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
      Real.exp ((Fintype.card ι : ℝ) * b ^ 2 * t ^ 2 / 8) := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let ν : Fin n → Measure Ω := fun j => μ (e.symm j)
  let r : (ι → Ω) ≃ᵐ (Fin n → Ω) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) e
  let G : (Fin n → Ω) → ℝ := fun y => F (r.symm y)
  have hmp : MeasurePreserving r (Measure.pi μ) (Measure.pi ν) := by
    change MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) e)
      (Measure.pi μ) (Measure.pi ν)
    simpa [ν] using
      (measurePreserving_piCongrLeft (α := fun _ : Fin n => Ω) ν e)
  have hG : Measurable G := hF.comp r.symm.measurable
  have hGbound : ∀ y, |G y| ≤ M := fun y => hbound (r.symm y)
  have hsymm_update (y : Fin n → Ω) (j : Fin n) (a : Ω) :
      r.symm (Function.update y j a) =
        Function.update (r.symm y) (e.symm j) a := by
    change Function.update y j a ∘ e =
      Function.update (y ∘ e) (e.symm j) a
    exact Function.update_comp_equiv y e j a
  have hoscG : ∀ y j a, |G (Function.update y j a) - G y| ≤ b := by
    intro y j a
    change |F (r.symm (Function.update y j a)) - F (r.symm y)| ≤ b
    rw [hsymm_update]
    exact hosc (r.symm y) (e.symm j) a
  have hmean : (∫ y, G y ∂Measure.pi ν) =
      ∫ x, F x ∂Measure.pi μ := by
    symm
    calc
      (∫ x, F x ∂Measure.pi μ) =
          ∫ x, G (r x) ∂Measure.pi μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp [G]
      _ = ∫ y, G y ∂Measure.pi ν := hmp.integral_comp' G
  have hfin := integral_exp_centered_pi_le_sharp
    ν hM hb hG hGbound hoscG t
  have htransport :
      (∫ x, Real.exp
        (t * (F x - ∫ z, F z ∂Measure.pi μ)) ∂Measure.pi μ) =
      ∫ y, Real.exp
        (t * (G y - ∫ z, G z ∂Measure.pi ν)) ∂Measure.pi ν := by
    calc
      _ = ∫ x, Real.exp
          (t * (G (r x) - ∫ z, G z ∂Measure.pi ν)) ∂Measure.pi μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          simp only [G, MeasurableEquiv.symm_apply_apply]
          rw [hmean]
      _ = _ := hmp.integral_comp'
        (fun y => Real.exp
          (t * (G y - ∫ z, G z ∂Measure.pi ν)))
  calc
    _ = ∫ y, Real.exp
        (t * (G y - ∫ z, G z ∂Measure.pi ν)) ∂Measure.pi ν := htransport
    _ ≤ Real.exp ((n : ℝ) * b ^ 2 * t ^ 2 / 8) := hfin
    _ = Real.exp ((Fintype.card ι : ℝ) * b ^ 2 * t ^ 2 / 8) := by
      simp [n]

/-- The sharp product MGF bound gives a sub-Gaussian object with proxy `card ι * b ^ 2 / 4`.
Exponential integrability follows from boundedness. -/
theorem hasSubgaussianMGF_centered_pi_sharp_of_fintype
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b) :
    HasSubgaussianMGF (fun x => F x - ∫ z, F z ∂Measure.pi μ)
      (⟨(Fintype.card ι : ℝ) * b ^ 2 / 4, by positivity⟩ : NNReal)
      (Measure.pi μ) := by
  have hmean : |∫ z, F z ∂Measure.pi μ| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (f := F) (C := M)
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hcenter : ∀ x, |F x - ∫ z, F z ∂Measure.pi μ| ≤ 2 * M := by
    intro x
    calc
      _ ≤ |F x| + |∫ z, F z ∂Measure.pi μ| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound x) hmean
      _ = 2 * M := by ring
  refine ⟨?_, ?_⟩
  · intro t
    exact integrable_exp_mul_of_mem_Icc (hF.sub_const _).aemeasurable
      (ae_of_all _ fun x => abs_le.mp (hcenter x))
  · intro t
    change (∫ x, Real.exp
        (t * (F x - ∫ z, F z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
      Real.exp (((Fintype.card ι : ℝ) * b ^ 2 / 4) * t ^ 2 / 2)
    calc
      _ ≤ Real.exp ((Fintype.card ι : ℝ) * b ^ 2 * t ^ 2 / 8) :=
        integral_exp_centered_pi_le_sharp_of_fintype
          μ hM hb hF hbound hosc t
      _ = Real.exp (((Fintype.card ι : ℝ) * b ^ 2 / 4) * t ^ 2 / 2) := by
        congr 1
        ring

/-- The sharp one-sided upper-tail bound, for positive scale `card ι * b ^ 2`. -/
theorem measure_ge_centered_pi_le_sharp_of_fintype
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b)
    {u : ℝ} (hu : 0 ≤ u)
    (hscale : 0 < (Fintype.card ι : ℝ) * b ^ 2) :
    (Measure.pi μ).real
      {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} ≤
      Real.exp (-(2 * u ^ 2) / ((Fintype.card ι : ℝ) * b ^ 2)) := by
  have hscale_ne : (Fintype.card ι : ℝ) * b ^ 2 ≠ 0 := ne_of_gt hscale
  have h := (hasSubgaussianMGF_centered_pi_sharp_of_fintype
    μ hM hb hF hbound hosc).measure_ge_le hu
  have hexp :
      -u ^ 2 / (2 * ((Fintype.card ι : ℝ) * b ^ 2 / 4)) =
        -(2 * u ^ 2) / ((Fintype.card ι : ℝ) * b ^ 2) := by
    field_simp [hscale_ne]
    ring
  change (Measure.pi μ).real
      {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} ≤
    Real.exp (-u ^ 2 / (2 * ((Fintype.card ι : ℝ) * b ^ 2 / 4))) at h
  rw [hexp] at h
  exact h

/-- The exact upper-tail probability at zero scale, including the empty index
and zero-oscillation cases. -/
theorem measure_ge_centered_pi_eq_of_scale_eq_zero_of_fintype
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b)
    (hscale : (Fintype.card ι : ℝ) * b ^ 2 = 0)
    {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi μ).real
      {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} =
      if u = 0 then 1 else 0 := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let ν : Fin n → Measure Ω := fun j => μ (e.symm j)
  let r : (ι → Ω) ≃ᵐ (Fin n → Ω) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) e
  let G : (Fin n → Ω) → ℝ := fun y => F (r.symm y)
  have hmp : MeasurePreserving r (Measure.pi μ) (Measure.pi ν) := by
    change MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) e)
      (Measure.pi μ) (Measure.pi ν)
    simpa [ν] using
      (measurePreserving_piCongrLeft (α := fun _ : Fin n => Ω) ν e)
  have hG : Measurable G := hF.comp r.symm.measurable
  have hGbound : ∀ y, |G y| ≤ M := fun y => hbound (r.symm y)
  have hsymm_update (y : Fin n → Ω) (j : Fin n) (a : Ω) :
      r.symm (Function.update y j a) =
        Function.update (r.symm y) (e.symm j) a := by
    change Function.update y j a ∘ e =
      Function.update (y ∘ e) (e.symm j) a
    exact Function.update_comp_equiv y e j a
  have hoscG : ∀ y j a, |G (Function.update y j a) - G y| ≤ b := by
    intro y j a
    change |F (r.symm (Function.update y j a)) - F (r.symm y)| ≤ b
    rw [hsymm_update]
    exact hosc (r.symm y) (e.symm j) a
  have hmean : (∫ y, G y ∂Measure.pi ν) =
      ∫ x, F x ∂Measure.pi μ := by
    symm
    calc
      (∫ x, F x ∂Measure.pi μ) =
          ∫ x, G (r x) ∂Measure.pi μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp [G]
      _ = ∫ y, G y ∂Measure.pi ν := hmp.integral_comp' G
  have hscaleFin : (n : ℝ) * b ^ 2 = 0 := by
    simpa [n] using hscale
  have hzero := measure_ge_centered_pi_eq_of_scale_eq_zero
    (μ := ν) (F := G) hM hb hG hGbound hoscG hscaleFin hu
  have hset :
      r ⁻¹' {y | u ≤ G y - ∫ z, G z ∂Measure.pi ν} =
        {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    simp [G, hmean]
  have hprob :
      (Measure.pi μ).real
        {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} =
      (Measure.pi ν).real
        {y | u ≤ G y - ∫ z, G z ∂Measure.pi ν} := by
    calc
      _ = ((Measure.pi μ).map r).real
          {y | u ≤ G y - ∫ z, G z ∂Measure.pi ν} := by
        rw [map_measureReal_apply r.measurable (by measurability)]
        rw [hset]
      _ = _ := by rw [hmp.map_eq]
  calc
    _ = (Measure.pi ν).real
        {y | u ≤ G y - ∫ z, G z ∂Measure.pi ν} := hprob
    _ = if u = 0 then 1 else 0 := hzero

end FintypeConcentration
end
end LPPDifferentiability
