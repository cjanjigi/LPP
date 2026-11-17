/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.OriginEdgeL1
public import LPP_Foundations.Probability.TranslationEquiv
public import Martin2004.Shape.ExpectedRateShape

import Busemann.Analysis.LocalDefectAE
import Busemann.Probability.CocycleNaturalMean
import LPP_Foundations.Probability.PassageIntegrable
import Martin2004.Analysis.RationalPassageNormalization
import Mathlib.Tactic.Ring

/-! The expected-rate shape obeys real bounds from stationary cocycle defects. -/

@[expose] public section

open Filter MeasureTheory LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- A conditional almost-sure defect bound gives an upper bound on the expected-rate shape.

This is the real finite-passage limit step in GRS, Theorem 4.4(4.8), used in
the projection argument of Janjigian--Rassoul-Agha (2018), equation (4.21).
The passage estimate and the finite-displacement cocycle mean are derived
from the canonical cocycle hypotheses. The direction may lie on the boundary
of the normalized quadrant. -/
theorem expected_rate_le_cocycle_add_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ)
    (g : Quadrant → ℝ)
    (hg : IsExpectedRateShape μ g)
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (hL1 : has_integrable_origin_edges (environmentLaw μ) C)
    (c : ℝ)
    (hdefect : ∀ᵐ ω ∂environmentLaw μ,
      max (ω 0 - C 0 ((1 : ℤ), (0 : ℤ)) ω)
        (ω 0 - C 0 ((0 : ℤ), (1 : ℤ)) ω) ≤ c)
    (ξ : Quadrant) (hξ : ξ.1 + ξ.2 = 1) :
    g ξ ≤ c +
      (∫ ω : Environment, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) * (ξ.1 : ℝ) +
      (∫ ω : Environment, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) * (ξ.2 : ℝ) := by
  let P : Measure Environment := environmentLaw μ
  let e₁ : Lattice := ((1 : ℤ), (0 : ℤ))
  let e₂ : Lattice := ((0 : ℤ), (1 : ℤ))
  let d (n : ℕ) : ℕ × ℕ :=
    (⌊(n : ℝ) * (ξ.1 : ℝ)⌋₊, ⌊(n : ℝ) * (ξ.2 : ℝ)⌋₊)
  let ratio₁ (n : ℕ) : ℝ := ((d n).1 : ℝ) / (n : ℝ)
  let ratio₂ (n : ℕ) : ℝ := ((d n).2 : ℝ) / (n : ℝ)
  let ratioLength (n : ℕ) : ℝ := (((d n).1 + (d n).2 : ℕ) : ℝ) / (n : ℝ)
  let mean₁ : ℝ := ∫ ω : Environment, C 0 e₁ ω ∂environmentLaw μ
  let mean₂ : ℝ := ∫ ω : Environment, C 0 e₂ ω ∂environmentLaw μ

  -- Normalize the pair zero used by the finite-passage helper to the model's zero.
  have hzero : ((0, 0) : Lattice) = (0 : Lattice) := by
    ext <;> simp

  -- The supplied expected-rate clause is exactly the left sequence limit.
  have hleft : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω (0 : Lattice) (d n) ∂P) / (n : ℝ))
      atTop (𝓝 (g ξ)) := by
    simpa [P, d] using hg ξ

  -- Existing floor limits control each normalized coordinate and total length.
  have hratio₁ : Tendsto ratio₁ atTop (𝓝 (ξ.1 : ℝ)) := by
    simpa [ratio₁, d] using
      LPPDifferentiability.tendsto_nat_floor_mul_div_nat (ξ.1 : ℝ) (by positivity)
  have hratio₂ : Tendsto ratio₂ atTop (𝓝 (ξ.2 : ℝ)) := by
    simpa [ratio₂, d] using
      LPPDifferentiability.tendsto_nat_floor_mul_div_nat (ξ.2 : ℝ) (by positivity)
  have hratioLength : Tendsto ratioLength atTop
      (𝓝 ((ξ.1 : ℝ) + (ξ.2 : ℝ))) := by
    simpa [ratioLength, d] using
      LPPDifferentiability.tendsto_floor_pair_length (ξ.1 : ℝ) (ξ.2 : ℝ)
        (by positivity) (by positivity)

  -- Integrate the AE passage estimate at each floor displacement.
  have hscaled (n : ℕ) :
      (∫ ω : Environment, lastPassage ω (0 : Lattice) (d n) ∂P) / (n : ℝ) ≤
        ratio₁ n * mean₁ + ratio₂ n * mean₂ + ratioLength n * c := by
    have hpass := ae_lastPassage_le_cocycle_add_steps μ C hC c hdefect (d n)
    have hpass₀ : ∀ᵐ ω ∂P,
        lastPassage ω (0 : Lattice) (d n) ≤
          C 0 (((d n).1 : ℤ), ((d n).2 : ℤ)) ω +
            (((d n).1 + (d n).2 : ℕ) : ℝ) * c := by
      simpa only [P, hzero] using hpass
    have hpassIntegrable := integrable_lastPassage μ hμ (0 : Lattice) (d n)
    have hCIntegrable := integrable_cocycle_nat_displacement μ C hC hL1 (d n)
    have hconstantIntegrable : Integrable
        (fun _ : Environment => (((d n).1 + (d n).2 : ℕ) : ℝ) * c) P :=
      integrable_const _
    have hintegral := integral_mono_ae hpassIntegrable
      (hCIntegrable.add hconstantIntegrable) hpass₀
    have hmean := integral_cocycle_nat_displacement μ C hC hL1 (d n)
    have hbound :
        (∫ ω : Environment, lastPassage ω (0 : Lattice) (d n) ∂P) ≤
          ((d n).1 : ℝ) * mean₁ + ((d n).2 : ℝ) * mean₂ +
            (((d n).1 + (d n).2 : ℕ) : ℝ) * c := by
      calc
        _ ≤ ∫ ω : Environment,
              C 0 (((d n).1 : ℤ), ((d n).2 : ℤ)) ω +
                (((d n).1 + (d n).2 : ℕ) : ℝ) * c ∂P := hintegral
        _ = (∫ ω : Environment, C 0 (((d n).1 : ℤ), ((d n).2 : ℤ)) ω ∂P) +
              (((d n).1 + (d n).2 : ℕ) : ℝ) * c := by
            rw [integral_add hCIntegrable hconstantIntegrable]
            simp [P]
        _ = _ := by
            simpa [P, mean₁, mean₂] using congrArg
              (fun x : ℝ => x + (((d n).1 + (d n).2 : ℕ) : ℝ) * c) hmean
    have hdivide := div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)
    have hnormalize :
        (((d n).1 : ℝ) * mean₁ + ((d n).2 : ℝ) * mean₂ +
          (((d n).1 + (d n).2 : ℕ) : ℝ) * c) / (n : ℝ) =
        ratio₁ n * mean₁ + ratio₂ n * mean₂ + ratioLength n * c := by
      dsimp [ratio₁, ratio₂, ratioLength, d]
      push_cast
      simp only [div_eq_mul_inv]
      ring
    rw [hnormalize] at hdivide
    exact hdivide

  -- The right sequence limit is the desired affine expression.
  have hrightRaw : Tendsto
      (fun n : ℕ => ratio₁ n * mean₁ + ratio₂ n * mean₂ + ratioLength n * c)
      atTop (𝓝 ((ξ.1 : ℝ) * mean₁ + (ξ.2 : ℝ) * mean₂ +
        ((ξ.1 : ℝ) + (ξ.2 : ℝ)) * c)) := by
    exact (hratio₁.mul_const mean₁).add (hratio₂.mul_const mean₂) |>.add
      (hratioLength.mul_const c)
  have hξreal : (ξ.1 : ℝ) + (ξ.2 : ℝ) = 1 := by
    exact_mod_cast hξ
  have hlimitValue :
      (ξ.1 : ℝ) * mean₁ + (ξ.2 : ℝ) * mean₂ +
          ((ξ.1 : ℝ) + (ξ.2 : ℝ)) * c =
        c + mean₁ * (ξ.1 : ℝ) + mean₂ * (ξ.2 : ℝ) := by
    rw [hξreal]
    ring
  have hright : Tendsto
      (fun n : ℕ => ratio₁ n * mean₁ + ratio₂ n * mean₂ + ratioLength n * c)
      atTop (𝓝 (c + mean₁ * (ξ.1 : ℝ) + mean₂ * (ξ.2 : ℝ))) := by
    simpa only [hlimitValue] using hrightRaw

  -- Compare the two limits; the normalization is valid on the closed quadrant.
  have hlimit := le_of_tendsto_of_tendsto' hleft hright
    hscaled
  simpa [mean₁, mean₂, e₁, e₂] using hlimit

end LPP.Busemann
