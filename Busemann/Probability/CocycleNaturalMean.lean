/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.OriginEdgeL1
public import LPP_Foundations.Probability.TranslationEquiv

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Means of natural-displacement cocycle increments

A canonical stationary additive cocycle with integrable origin edges has
integrable increments to all natural displacements. Their means are the
corresponding signed linear combinations of the two origin edge means.
-/

public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem translated_edge_integrable_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (x e : Lattice)
    (he : Integrable (fun ω : Environment => C 0 e ω) (environmentLaw μ)) :
    Integrable (fun ω : Environment => C x (x + e) ω) (environmentLaw μ) ∧
    (∫ ω : Environment, C x (x + e) ω ∂environmentLaw μ) =
      ∫ ω : Environment, C 0 e ω ∂environmentLaw μ := by
  have hshift := measurePreserving_environmentTranslationEquiv μ x
  have hcov : (fun ω : Environment => C x (x + e) ω) =ᵐ[environmentLaw μ]
      (fun ω : Environment => C 0 e (environmentTranslationEquiv x ω)) := by
    filter_upwards [hC.2.1 0 e x] with ω hω
    simpa only [zero_add, add_comm e x] using hω
  have hcomp : Integrable
      (fun ω : Environment => C 0 e (environmentTranslationEquiv x ω))
      (environmentLaw μ) := by
    change Integrable ((fun ω : Environment => C 0 e ω) ∘ environmentTranslationEquiv x)
      (environmentLaw μ)
    exact hshift.integrable_comp_of_integrable he
  have hint : Integrable (fun ω : Environment => C x (x + e) ω)
      (environmentLaw μ) := hcomp.congr hcov.symm
  refine ⟨hint, ?_⟩
  calc
    (∫ ω : Environment, C x (x + e) ω ∂environmentLaw μ) =
        ∫ ω : Environment, C 0 e (environmentTranslationEquiv x ω)
          ∂environmentLaw μ := integral_congr_ae hcov
    _ = ∫ ω : Environment, C 0 e ω ∂environmentLaw μ :=
      hshift.integral_comp' (fun ω : Environment => C 0 e ω)

private theorem extend_origin_increment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (x e : Lattice)
    (hx : Integrable (fun ω : Environment => C 0 x ω) (environmentLaw μ))
    (he : Integrable (fun ω : Environment => C 0 e ω) (environmentLaw μ)) :
    Integrable (fun ω : Environment => C 0 (x + e) ω) (environmentLaw μ) ∧
    (∫ ω : Environment, C 0 (x + e) ω ∂environmentLaw μ) =
      (∫ ω : Environment, C 0 x ω ∂environmentLaw μ) +
      (∫ ω : Environment, C 0 e ω ∂environmentLaw μ) := by
  have hedge := translated_edge_integrable_mean μ C hC x e he
  have hadd : (fun ω : Environment => C 0 x ω + C x (x + e) ω) =ᵐ[environmentLaw μ]
      (fun ω : Environment => C 0 (x + e) ω) := by
    filter_upwards [hC.2.2] with ω hω
    exact hω 0 x (x + e)
  have hnew : Integrable (fun ω : Environment => C 0 (x + e) ω)
      (environmentLaw μ) := (hx.add hedge.1).congr hadd
  refine ⟨hnew, ?_⟩
  calc
    (∫ ω : Environment, C 0 (x + e) ω ∂environmentLaw μ) =
        ∫ ω : Environment, C 0 x ω + C x (x + e) ω ∂environmentLaw μ :=
      integral_congr_ae hadd.symm
    _ = (∫ ω : Environment, C 0 x ω ∂environmentLaw μ) +
          (∫ ω : Environment, C x (x + e) ω ∂environmentLaw μ) :=
      integral_add hx hedge.1
    _ = (∫ ω : Environment, C 0 x ω ∂environmentLaw μ) +
          (∫ ω : Environment, C 0 e ω ∂environmentLaw μ) := by rw [hedge.2]

private theorem cocycle_nat_displacement_integrable_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (hL1 : has_integrable_origin_edges (environmentLaw μ) C)
    (m n : ℕ) :
    Integrable (fun ω : Environment => C 0 ((m : ℤ), (n : ℤ)) ω)
      (environmentLaw μ) ∧
    (∫ ω : Environment, C 0 ((m : ℤ), (n : ℤ)) ω ∂environmentLaw μ) =
      (m : ℝ) * (∫ ω : Environment, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) +
      (n : ℝ) * (∫ ω : Environment, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) := by
  let mean₁ : ℝ := ∫ ω : Environment, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ
  let mean₂ : ℝ := ∫ ω : Environment, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ
  let Q (a b : ℕ) : Prop :=
    Integrable (fun ω : Environment => C 0 ((a : ℤ), (b : ℤ)) ω)
      (environmentLaw μ) ∧
    (∫ ω : Environment, C 0 ((a : ℤ), (b : ℤ)) ω ∂environmentLaw μ) =
      (a : ℝ) * mean₁ + (b : ℝ) * mean₂
  have hzero : (fun ω : Environment => C 0 ((0 : ℤ), (0 : ℤ)) ω) =ᵐ[environmentLaw μ]
      (fun _ : Environment => (0 : ℝ)) := by
    filter_upwards [hC.2.2] with ω hω
    have h := hω 0 0 0
    have hz : C 0 0 ω = 0 := by linarith only [h]
    have hsite : ((0 : ℤ), (0 : ℤ)) = (0 : Lattice) := by
      ext <;> rfl
    simpa only [hsite] using hz
  have hbase : Q 0 0 := by
    dsimp [Q]
    constructor
    · exact (integrable_zero Environment ℝ (environmentLaw μ)).congr hzero.symm
    · rw [integral_congr_ae hzero]
      simp
  have hstep₂ : ∀ a b : ℕ, Q a b → Q a (b + 1) := by
    intro a b hab
    have he := extend_origin_increment μ C hC
      ((a : ℤ), (b : ℤ)) ((0 : ℤ), (1 : ℤ)) hab.1 hL1.2
    change Integrable (fun ω : Environment => C 0 ((a : ℤ), ((b + 1 : ℕ) : ℤ)) ω)
        (environmentLaw μ) ∧
      (∫ ω : Environment, C 0 ((a : ℤ), ((b + 1 : ℕ) : ℤ)) ω ∂environmentLaw μ) =
        (a : ℝ) * mean₁ + ((b + 1 : ℕ) : ℝ) * mean₂
    constructor
    · simpa only [Prod.mk_add_mk, add_zero, Nat.cast_add, Nat.cast_one] using he.1
    · have hmean : (∫ ω : Environment,
          C 0 ((a : ℤ), ((b + 1 : ℕ) : ℤ)) ω ∂environmentLaw μ) =
          (∫ ω : Environment, C 0 ((a : ℤ), (b : ℤ)) ω ∂environmentLaw μ) +
          mean₂ := by
        simpa only [Prod.mk_add_mk, add_zero, Nat.cast_add, Nat.cast_one] using he.2
      rw [hmean, hab.2]
      push_cast
      ring
  have hvertical : ∀ b : ℕ, Q 0 b := by
    intro b
    induction b with
    | zero => exact hbase
    | succ b ih => simpa only [Nat.succ_eq_add_one] using hstep₂ 0 b ih
  have hstep₁ : ∀ a b : ℕ, Q a b → Q (a + 1) b := by
    intro a b hab
    have he := extend_origin_increment μ C hC
      ((a : ℤ), (b : ℤ)) ((1 : ℤ), (0 : ℤ)) hab.1 hL1.1
    change Integrable (fun ω : Environment => C 0 ((((a + 1 : ℕ) : ℤ)), (b : ℤ)) ω)
        (environmentLaw μ) ∧
      (∫ ω : Environment, C 0 ((((a + 1 : ℕ) : ℤ)), (b : ℤ)) ω ∂environmentLaw μ) =
        ((a + 1 : ℕ) : ℝ) * mean₁ + (b : ℝ) * mean₂
    constructor
    · simpa only [Prod.mk_add_mk, add_zero, zero_add, Nat.cast_add, Nat.cast_one] using he.1
    · have hmean : (∫ ω : Environment,
          C 0 ((((a + 1 : ℕ) : ℤ)), (b : ℤ)) ω ∂environmentLaw μ) =
          (∫ ω : Environment, C 0 ((a : ℤ), (b : ℤ)) ω ∂environmentLaw μ) +
          mean₁ := by
        simpa only [Prod.mk_add_mk, add_zero, zero_add, Nat.cast_add, Nat.cast_one] using he.2
      rw [hmean, hab.2]
      push_cast
      ring
  have hall : ∀ a b : ℕ, Q a b := by
    intro a
    induction a with
    | zero => exact hvertical
    | succ a ih =>
        intro b
        simpa only [Nat.succ_eq_add_one] using hstep₁ a b (ih b)
  exact hall m n

/-- A canonical integrable cocycle has an integrable increment to every natural displacement. -/
theorem integrable_cocycle_nat_displacement
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (hL1 : has_integrable_origin_edges (environmentLaw μ) C)
    (d : ℕ × ℕ) :
    Integrable (fun ω : Environment => C 0 ((d.1 : ℤ), (d.2 : ℤ)) ω)
      (environmentLaw μ) :=
  (cocycle_nat_displacement_integrable_mean μ C hC hL1 d.1 d.2).1

/-- The mean increment to a natural displacement is the sum of its two origin-edge means. -/
theorem integral_cocycle_nat_displacement
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (hL1 : has_integrable_origin_edges (environmentLaw μ) C)
    (d : ℕ × ℕ) :
    (∫ ω : Environment, C 0 ((d.1 : ℤ), (d.2 : ℤ)) ω ∂environmentLaw μ) =
      (d.1 : ℝ) * (∫ ω : Environment, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) +
      (d.2 : ℝ) * (∫ ω : Environment, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) :=
  (cocycle_nat_displacement_integrable_mean μ C hC hL1 d.1 d.2).2

end LPP.Busemann
