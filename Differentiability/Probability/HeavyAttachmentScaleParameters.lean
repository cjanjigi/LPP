/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.HeavyAttachmentTotalDecay
public import Differentiability.Probability.NegativeThresholdMass
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Parameters for the heavy attachment estimate

For a probability law, one order controls the total failure limit and
all geometric, mass, tail, and weight-budget cutoffs at once.
-/

public section

open MeasureTheory
open Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- For the negative-part moments of the law, one order gives the total failure
limit and a single eventual cutoff for all attachment conditions. -/
theorem exists_heavy_attachment_scale_parameters
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p a D eta kappa : ℝ)
    (hp : 1 < p) (ha : a ∈ Ioo (0 : ℝ) 1) (hD : 1 ≤ D)
    (heta : 0 < eta) (hkappa : 0 < kappa) (hkappa16 : kappa ≤ 1 / 16)
    (hmoment :
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    kappa ≤ eta /
        (16 * (∫ x, max (-x) 0 ∂μ) + 16) →
    ∃ K : ℕ, 2 ≤ K ∧ 4 ≤ (K : ℝ) * (p - 1) ∧
      let C₁ : ℝ := ∫ x, max (-x) 0 ∂μ
      let Cₚ : ℝ := ∫ x, (max (-x) 0) ^ p ∂μ
      let theta0 : ℝ := min a (1 - a)
      let L : ℕ := 4 * K + 4
      let B : ℝ := 8 * D / (theta0 * kappa) + 2
      let C : ℝ := Cₚ * (64 * (K : ℝ) / eta) ^ p
      let epsilon : ℝ := (p - 1) / (2 * p)
      let m : ℝ → ℕ := fun s => Nat.ceil (kappa * s)
      let F : ℝ → ℝ := fun s =>
        (48 * D * s ^ 2 * (C * s ^ (-p)) ^ 2 +
          (D * s + 1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * (C * s ^ (-p)) +
          (D * s + 1) *
            (((((2 * K + 5) * (m s + 1) : ℕ) : ℝ) *
              (C * s ^ (-p))) ^ K)) +
        (D * s + 1) *
          ((2 * (m s : ℝ) * Cₚ * (s ^ (1 - epsilon)) ^ (-p)) ^ K +
            Real.exp (-((eta * s / 16) ^ 2) /
              (2 * s ^ (1 - epsilon) *
                (2 * C₁ * (m s : ℝ) + (eta * s / 16) / 3))))
      Tendsto F atTop (𝓝 0) ∧
      (∀ s, 0 < s → 0 ≤ F s) ∧
      ∀ᶠ s : ℝ in atTop,
        4 ≤ s ∧
        1 ≤ m s ∧
        1 ≤ theta0 * (m s : ℝ) / 4 ∧
        2 * K + 5 ≤ m s ∧
        4 * K + 4 ≤ m s ∧
        (m s : ℝ) ≤ 2 * kappa * s ∧
        (m s : ℝ) ≤ s ∧
        (2 : ℝ≥0∞)⁻¹ ≤ μ (Ici (-(eta * s / (64 * (K : ℝ)))) ) ∧
        μ.real (Iio (-(eta * s / (64 * (K : ℝ))))) ≤ C * s ^ (-p) ∧
        2 * C₁ * (m s : ℝ) +
          ((K - 1 : ℕ) : ℝ) * (eta * s / (64 * (K : ℝ))) +
          eta * s / 16 ≤ eta * s / 4 := by
  intro hkappaBudget
  obtain ⟨K, hK, hKp⟩ := exists_heavy_attachment_order p hp
  let C₁ : ℝ := ∫ x, max (-x) 0 ∂μ
  let Cₚ : ℝ := ∫ x, (max (-x) 0) ^ p ∂μ
  let theta0 : ℝ := min a (1 - a)
  let L : ℕ := 4 * K + 4
  let B : ℝ := 8 * D / (theta0 * kappa) + 2
  let C : ℝ := Cₚ * (64 * (K : ℝ) / eta) ^ p
  let epsilon : ℝ := (p - 1) / (2 * p)
  let m : ℝ → ℕ := fun s => Nat.ceil (kappa * s)
  let F : ℝ → ℝ := fun s =>
    (48 * D * s ^ 2 * (C * s ^ (-p)) ^ 2 +
      (D * s + 1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * (C * s ^ (-p)) +
      (D * s + 1) *
        (((((2 * K + 5) * (m s + 1) : ℕ) : ℝ) *
          (C * s ^ (-p))) ^ K)) +
    (D * s + 1) *
      ((2 * (m s : ℝ) * Cₚ * (s ^ (1 - epsilon)) ^ (-p)) ^ K +
        Real.exp (-((eta * s / 16) ^ 2) /
          (2 * s ^ (1 - epsilon) *
            (2 * C₁ * (m s : ℝ) + (eta * s / 16) / 3))))
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    exact integral_nonneg (fun _ => le_max_right _ _)
  have hCₚ : 0 ≤ Cₚ := by
    dsimp [Cₚ]
    exact integral_nonneg (fun x => Real.rpow_nonneg (le_max_right _ _) p)
  have htheta0 : 0 < theta0 := by
    dsimp [theta0]
    exact lt_min ha.1 (by linarith [ha.2])
  have hkappaBudget' : kappa ≤ eta / (16 * C₁ + 16) := by
    simpa only [C₁] using hkappaBudget
  have hKreal : 1 ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
  have htotal := tendsto_heavy_attachment_total_failure
    p C₁ Cₚ D eta kappa theta0 K hp hC₁ hCₚ hD heta hkappa htheta0 hK hKp
  have hF : Tendsto F atTop (𝓝 0) := by
    simpa only [L, B, C, epsilon, m, theta0, C₁, Cₚ] using htotal.1
  have hFnonneg : ∀ s, 0 < s → 0 ≤ F s := by
    simpa only [L, B, C, epsilon, m, theta0, C₁, Cₚ] using htotal.2

  have hceilCuts :=
    eventually_heavy_attachment_source_ceiling_cutoffs K kappa hkappa
  have hs4 : ∀ᶠ s : ℝ in atTop, 4 ≤ s := eventually_ge_atTop (4 : ℝ)
  have hsMiddle : ∀ᶠ s : ℝ in atTop, 4 / (theta0 * kappa) ≤ s :=
    eventually_ge_atTop (4 / (theta0 * kappa))
  have hsKappa : ∀ᶠ s : ℝ in atTop, 1 / kappa ≤ s :=
    eventually_ge_atTop (1 / kappa)
  have hgeometry : ∀ᶠ s : ℝ in atTop,
      4 ≤ s ∧
        1 ≤ m s ∧
        1 ≤ theta0 * (m s : ℝ) / 4 ∧
        2 * K + 5 ≤ m s ∧
        4 * K + 4 ≤ m s ∧
        (m s : ℝ) ≤ 2 * kappa * s ∧
        (m s : ℝ) ≤ s := by
    filter_upwards [hs4, hsMiddle, hsKappa, hceilCuts] with s hs4s hsmid hsk hcuts
    rcases hcuts with ⟨hcutTube, hcutBox⟩
    have hs0 : 0 ≤ s := le_trans (by norm_num) hs4s
    have hks : 1 ≤ kappa * s := by
      have h := (div_le_iff₀ hkappa).mp hsk
      linarith
    have hmiddle : 4 ≤ theta0 * kappa * s := by
      have h := (div_le_iff₀ (mul_pos htheta0 hkappa)).mp hsmid
      nlinarith
    have hceilLower : kappa * s ≤ (m s : ℝ) := by
      dsimp [m]
      exact Nat.le_ceil _
    have hceilUpper : (m s : ℝ) ≤ kappa * s + 1 := by
      dsimp [m]
      exact (Nat.ceil_lt_add_one (mul_nonneg hkappa.le hs0)).le
    have hAm : 4 ≤ theta0 * (m s : ℝ) := by
      calc
        4 ≤ theta0 * kappa * s := hmiddle
        _ = theta0 * (kappa * s) := by ring
        _ ≤ theta0 * (m s : ℝ) := mul_le_mul_of_nonneg_left hceilLower htheta0.le
    have hceilTwo : (m s : ℝ) ≤ 2 * kappa * s := by
      nlinarith [hceilUpper, hks]
    have hkapScale : kappa * s ≤ s / 16 := by
      calc
        kappa * s ≤ (1 / 16) * s := mul_le_mul_of_nonneg_right hkappa16 hs0
        _ = s / 16 := by ring
    have hceilS : (m s : ℝ) ≤ s := by
      nlinarith [hceilUpper, hkapScale, hs4s]
    have hmpos : 1 ≤ m s := by
      have hreal : (1 : ℝ) ≤ (m s : ℝ) := le_trans hks hceilLower
      exact_mod_cast hreal
    refine ⟨hs4s, hmpos, ?_, hcutTube, hcutBox, hceilTwo, hceilS⟩
    · nlinarith [hAm]

  have hmass : ∀ᶠ s : ℝ in atTop,
      (2 : ℝ≥0∞)⁻¹ ≤ μ (Ici (-(eta * s / (64 * (K : ℝ))))) :=
    eventually_measure_Ici_sourceScale_ge_half μ eta (K : ℝ) heta hKreal
  have htail : ∀ᶠ s : ℝ in atTop,
      μ.real (Iio (-(eta * s / (64 * (K : ℝ))))) ≤ C * s ^ (-p) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hsource := measureReal_Iio_sourceScale_le
      μ eta (K : ℝ) p s heta hKreal hp hs hmoment
    simpa only [C, Cₚ] using hsource
  have hKsub : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K)]
    norm_num
  have hbudget : ∀ᶠ s : ℝ in atTop,
      2 * C₁ * (m s : ℝ) +
          ((K - 1 : ℕ) : ℝ) * (eta * s / (64 * (K : ℝ))) +
          eta * s / 16 ≤ eta * s / 4 := by
    filter_upwards [eventually_ge_atTop (max 1 (128 * C₁ / eta))] with s hs
    have hcutoff : max 1 (128 * C₁ / eta) ≤ s := hs
    have hsource := heavy_attachment_weight_budget
      C₁ eta kappa K s hC₁ heta hK hkappa hkappaBudget' hcutoff
    simpa only [m, ← hKsub] using hsource

  refine ⟨K, hK, hKp, ?_⟩
  change Tendsto F atTop (𝓝 0) ∧
    (∀ s, 0 < s → 0 ≤ F s) ∧
    ∀ᶠ s : ℝ in atTop,
      4 ≤ s ∧
      1 ≤ m s ∧
      1 ≤ theta0 * (m s : ℝ) / 4 ∧
      2 * K + 5 ≤ m s ∧
      4 * K + 4 ≤ m s ∧
      (m s : ℝ) ≤ 2 * kappa * s ∧
      (m s : ℝ) ≤ s ∧
      (2 : ℝ≥0∞)⁻¹ ≤ μ (Ici (-(eta * s / (64 * (K : ℝ))))) ∧
      μ.real (Iio (-(eta * s / (64 * (K : ℝ))))) ≤ C * s ^ (-p) ∧
      2 * C₁ * (m s : ℝ) +
        ((K - 1 : ℕ) : ℝ) * (eta * s / (64 * (K : ℝ))) +
        eta * s / 16 ≤ eta * s / 4
  refine ⟨hF, hFnonneg, ?_⟩
  filter_upwards [hgeometry, hmass, htail, hbudget] with s hgeom hmassS htailS hbudgetS
  rcases hgeom with ⟨hs4s, hmpos, htrans, hcutTube, hcutBox, hmTwo, hmS⟩
  exact ⟨hs4s, hmpos, htrans, hcutTube, hcutBox, hmTwo, hmS,
    hmassS, htailS, hbudgetS⟩

end LPPDifferentiability

end
