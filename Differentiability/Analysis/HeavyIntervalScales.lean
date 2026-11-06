/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.AttachmentScales
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Heavy interval scales

Scalar bounds for the scale and cutoff in the general-weight interval proof.
-/

public section

namespace LPPDifferentiability

/-- The general interval scale retains the attachment geometry and pays its
source Lipschitz loss under the heavier mean budget. -/
theorem heavy_interval_scale_bounds (a theta delta eta L C1 : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (htheta : 0 < theta)
    (hthetaInterior : theta < min a (1 - a))
    (hdelta : 0 < delta) (heta : 0 < eta) (hL : 1 ≤ L)
    (hC1 : 0 ≤ C1) :
    let theta0 : ℝ := min a (1 - a)
    let r : ℝ := L + C1
    let kappa : ℝ :=
      min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1))))
    let cutoff : ℝ :=
      max 1 (max (4 / (theta0 * kappa))
        (max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta)))))
    0 < kappa ∧ kappa ≤ theta / 16 ∧ kappa ≤ 1 / 16 ∧
      kappa ≤ delta / 4 ∧
      kappa ≤ eta / (16 * (r + 1)) ∧
      kappa ≤ eta / (16 * C1 + 16) ∧ 1 ≤ cutoff ∧
      16 * L / eta ≤ cutoff ∧
      (∀ s : ℝ, cutoff ≤ s →
        kappa * s ≤ (Nat.ceil (kappa * s) : ℝ) ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 ∧
        theta0 * (Nat.ceil (kappa * s) : ℝ) / 4 ≥ 1 ∧
        2 * (Nat.ceil (kappa * s) : ℝ) ≤ s / 4 ∧
        (theta / 2) * s ≥
          2 * (Nat.ceil (kappa * s) : ℝ) * (1 + theta0 - theta / 2) ∧
        2 * (Nat.ceil (kappa * s) : ℝ) * r ≤ eta * s / 4 ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ delta * s / 2 ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ s ∧
        2 * (Nat.ceil (kappa * s) : ℝ) * L ≤ eta * s / 4) := by
  let theta0 : ℝ := min a (1 - a)
  let r : ℝ := L + C1
  let kappa : ℝ :=
    min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1))))
  let cutoff : ℝ :=
    max 1 (max (4 / (theta0 * kappa))
      (max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta)))))
  have hAttach :=
    attachment_scale_bounds a theta delta eta L C1
      ha ha1 htheta hthetaInterior hdelta heta hL
  rw [abs_of_nonneg hC1] at hAttach
  dsimp only [theta0, r, kappa, cutoff] at hAttach
  rcases hAttach with ⟨hkappaPos, hkappaTheta, hkappaDelta, hkappaEta, hForall⟩
  have hthetaLtOne : theta < 1 :=
    lt_trans hthetaInterior (lt_of_le_of_lt (min_le_left a (1 - a)) ha1)
  have hkappaSixteenth : kappa ≤ 1 / 16 := by
    nlinarith only [hkappaTheta, hthetaLtOne]
  have hDen : 16 * (C1 + 1) ≤ 16 * (r + 1) := by
    dsimp [r]
    nlinarith [hL]
  have hkappaC1 : kappa ≤ eta / (16 * C1 + 16) := by
    have hFraction : eta / (16 * (r + 1)) ≤ eta / (16 * (C1 + 1)) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 16 * (r + 1))
        (by positivity : 0 < 16 * (C1 + 1))]
      exact mul_le_mul_of_nonneg_left hDen heta.le
    calc
      kappa ≤ eta / (16 * (r + 1)) := hkappaEta
      _ ≤ eta / (16 * (C1 + 1)) := hFraction
      _ = eta / (16 * C1 + 16) := by congr 1; ring
  have hCutoffOne : 1 ≤ cutoff := by
    change 1 ≤ max 1 _
    exact le_max_left _ _
  have hCutoffMean : 16 * r / eta ≤ cutoff := by
    change 16 * r / eta ≤
      max 1 (max (4 / (theta0 * kappa))
        (max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta)))))
    calc
      16 * r / eta ≤ max (16 * r / eta) (4 / delta) := le_max_left _ _
      _ ≤ max (16 / theta) (max (16 * r / eta) (4 / delta)) := le_max_right _ _
      _ ≤ max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta))) :=
        le_max_right _ _
      _ ≤ max (4 / (theta0 * kappa))
          (max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta)))) :=
        le_max_right _ _
      _ ≤ max 1 (max (4 / (theta0 * kappa))
          (max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta))))) :=
        le_max_right _ _
  have hLleR : L ≤ r := by
    dsimp [r]
    linarith
  have hCutoffL : 16 * L / eta ≤ cutoff := by
    have hRatio : 16 * L / eta ≤ 16 * r / eta :=
      div_le_div_of_nonneg_right (by nlinarith [hLleR]) heta.le
    exact hRatio.trans hCutoffMean
  refine ⟨hkappaPos, hkappaTheta, hkappaSixteenth, hkappaDelta, hkappaEta,
    hkappaC1, hCutoffOne, hCutoffL, ?_⟩
  intro s hs
  have hGeometry := hForall s hs
  rcases hGeometry with
    ⟨hmLower, hmUpper, hSpacing, hLevel, hInteriority, hBudget, hTube, hmS⟩
  have hLoss :
      2 * (Nat.ceil (kappa * s) : ℝ) * L ≤ eta * s / 4 := by
    exact mul_le_mul_of_nonneg_left hLleR (by positivity) |>.trans hBudget
  exact ⟨hmLower, hmUpper, hSpacing, hLevel, hInteriority, hBudget,
    hTube, hmS, hLoss⟩

end LPPDifferentiability

end
