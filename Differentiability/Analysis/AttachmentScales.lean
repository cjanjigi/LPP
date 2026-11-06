/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Attachment scale estimates

The literal numerical scale and one cutoff for all sufficiently large levels.
-/

public section

namespace LPPDifferentiability

/-- Ceiling bounds at every nonnegative scale, independently of the cutoff. -/
theorem attachment_ceil_bounds (kappa s : ℝ) (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) :
    kappa * s ≤ (Nat.ceil (kappa * s) : ℝ) ∧
      (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 :=
  ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (mul_nonneg hkappa hs)).le⟩

/-- The source attachment scale satisfies all five requirements above one
cutoff chosen only from the source parameters. -/
theorem attachment_scale_bounds (a theta delta eta L muMean : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (htheta : 0 < theta)
    (hthetaInterior : theta < min a (1 - a))
    (hdelta : 0 < delta) (heta : 0 < eta) (hL : 1 ≤ L) :
    let theta0 : ℝ := min a (1 - a)
    let r : ℝ := L + |muMean|
    let kappa : ℝ :=
      min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1))))
    let cutoff : ℝ :=
      max 1 (max (4 / (theta0 * kappa))
        (max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta)))))
    0 < kappa ∧ kappa ≤ theta / 16 ∧ kappa ≤ delta / 4 ∧
      kappa ≤ eta / (16 * (r + 1)) ∧
      (∀ s : ℝ, cutoff ≤ s →
        kappa * s ≤ (Nat.ceil (kappa * s) : ℝ) ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 ∧
        theta0 * (Nat.ceil (kappa * s) : ℝ) / 4 ≥ 1 ∧
        2 * (Nat.ceil (kappa * s) : ℝ) ≤ s / 4 ∧
        (theta / 2) * s ≥
          2 * (Nat.ceil (kappa * s) : ℝ) * (1 + theta0 - theta / 2) ∧
        2 * (Nat.ceil (kappa * s) : ℝ) * r ≤ eta * s / 4 ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ delta * s / 2 ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ s) := by
  let theta0 : ℝ := min a (1 - a)
  let r : ℝ := L + |muMean|
  let kappa : ℝ :=
    min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1))))
  let cKappa : ℝ := 4 / (theta0 * kappa)
  let cSixteen : ℝ := 16
  let cTheta : ℝ := 16 / theta
  let cMean : ℝ := 16 * r / eta
  let cDelta : ℝ := 4 / delta
  let cutoff : ℝ :=
    max 1 (max cKappa (max cSixteen (max cTheta (max cMean cDelta))))
  have h1minus : 0 < 1 - a := by linarith
  have htheta0pos : 0 < theta0 := lt_min ha h1minus
  have htheta0half : theta0 ≤ 1 / 2 := by
    by_cases haHalf : a ≤ 1 / 2
    · have haLeRight : a ≤ 1 - a := by linarith
      simpa [theta0, min_eq_left haLeRight] using haHalf
    · have hright : 1 - a ≤ a := by linarith
      have hrightHalf : 1 - a ≤ 1 / 2 := by linarith
      simpa [theta0, min_eq_right hright] using hrightHalf
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrplus : 0 < r + 1 := by linarith
  have hkappapos : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hkappatheta : kappa ≤ theta / 16 := by
    change min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1)))) ≤
      theta / 16
    exact min_le_left _ _
  have hkappadelta : kappa ≤ delta / 4 := by
    change min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1)))) ≤
      delta / 4
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hkappaeta : kappa ≤ eta / (16 * (r + 1)) := by
    change min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1)))) ≤
      eta / (16 * (r + 1))
    exact (min_le_right _ _).trans (min_le_right _ _)
  have htheta0 : theta < theta0 := by simpa [theta0] using hthetaInterior
  change 0 < kappa ∧ kappa ≤ theta / 16 ∧ kappa ≤ delta / 4 ∧
    kappa ≤ eta / (16 * (r + 1)) ∧
    (∀ s : ℝ, cutoff ≤ s →
      kappa * s ≤ (Nat.ceil (kappa * s) : ℝ) ∧
      (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 ∧
      theta0 * (Nat.ceil (kappa * s) : ℝ) / 4 ≥ 1 ∧
      2 * (Nat.ceil (kappa * s) : ℝ) ≤ s / 4 ∧
      (theta / 2) * s ≥
        2 * (Nat.ceil (kappa * s) : ℝ) * (1 + theta0 - theta / 2) ∧
      2 * (Nat.ceil (kappa * s) : ℝ) * r ≤ eta * s / 4 ∧
      (Nat.ceil (kappa * s) : ℝ) ≤ delta * s / 2 ∧
      (Nat.ceil (kappa * s) : ℝ) ≤ s)
  have hcutKappa : cKappa ≤ cutoff := by
    dsimp [cutoff]
    calc
      cKappa ≤ max cKappa (max cSixteen (max cTheta (max cMean cDelta))) :=
        le_max_left _ _
      _ ≤ max 1 (max cKappa (max cSixteen (max cTheta (max cMean cDelta)))) :=
        le_max_right _ _
  have hcutSixteen : cSixteen ≤ cutoff := by
    dsimp [cutoff]
    calc
      cSixteen ≤ max cSixteen (max cTheta (max cMean cDelta)) := le_max_left _ _
      _ ≤ max cKappa (max cSixteen (max cTheta (max cMean cDelta))) :=
        le_max_right _ _
      _ ≤ max 1 (max cKappa (max cSixteen (max cTheta (max cMean cDelta)))) :=
        le_max_right _ _
  have hcutTheta : cTheta ≤ cutoff := by
    dsimp [cutoff]
    calc
      cTheta ≤ max cTheta (max cMean cDelta) := le_max_left _ _
      _ ≤ max cSixteen (max cTheta (max cMean cDelta)) := le_max_right _ _
      _ ≤ max cKappa (max cSixteen (max cTheta (max cMean cDelta))) :=
        le_max_right _ _
      _ ≤ max 1 (max cKappa (max cSixteen (max cTheta (max cMean cDelta)))) :=
        le_max_right _ _
  have hcutMean : cMean ≤ cutoff := by
    dsimp [cutoff]
    calc
      cMean ≤ max cMean cDelta := le_max_left _ _
      _ ≤ max cTheta (max cMean cDelta) := le_max_right _ _
      _ ≤ max cSixteen (max cTheta (max cMean cDelta)) := le_max_right _ _
      _ ≤ max cKappa (max cSixteen (max cTheta (max cMean cDelta))) :=
        le_max_right _ _
      _ ≤ max 1 (max cKappa (max cSixteen (max cTheta (max cMean cDelta)))) :=
        le_max_right _ _
  have hcutDelta : cDelta ≤ cutoff := by
    dsimp [cutoff]
    calc
      cDelta ≤ max cMean cDelta := le_max_right _ _
      _ ≤ max cTheta (max cMean cDelta) := le_max_right _ _
      _ ≤ max cSixteen (max cTheta (max cMean cDelta)) := le_max_right _ _
      _ ≤ max cKappa (max cSixteen (max cTheta (max cMean cDelta))) :=
        le_max_right _ _
      _ ≤ max 1 (max cKappa (max cSixteen (max cTheta (max cMean cDelta)))) :=
        le_max_right _ _
  have hthetaKpos : 0 < theta0 * kappa := mul_pos htheta0pos hkappapos
  have hcutKappaProduct : 4 ≤ theta0 * kappa * cutoff := by
    have h := (div_le_iff₀ hthetaKpos).mp (by
      simpa [cKappa] using hcutKappa)
    nlinarith only [h]
  have hcutThetaProduct : 16 ≤ theta * cutoff := by
    have h := (div_le_iff₀ htheta).mp (by simpa [cTheta] using hcutTheta)
    nlinarith only [h]
  have hcutMeanProduct : 16 * r ≤ eta * cutoff := by
    have h := (div_le_iff₀ heta).mp (by simpa [cMean] using hcutMean)
    nlinarith only [h]
  have hcutDeltaProduct : 4 ≤ delta * cutoff := by
    have h := (div_le_iff₀ hdelta).mp (by simpa [cDelta] using hcutDelta)
    nlinarith only [h]
  refine ⟨hkappapos, hkappatheta, hkappadelta, hkappaeta, ?_⟩
  intro s hs
  have hspos : 0 < s := by
    have h16 : 16 ≤ s := hcutSixteen.trans hs
    linarith
  have hsnonneg : 0 ≤ s := hspos.le
  have hcutKappaScale :=
    mul_le_mul_of_nonneg_left hs (mul_nonneg htheta0pos.le hkappapos.le)
  have hthetaKappaS : 4 ≤ theta0 * kappa * s := by
    have h := hcutKappaProduct.trans hcutKappaScale
    nlinarith only [h]
  have hcutThetaScale := mul_le_mul_of_nonneg_left hs htheta.le
  have hthetaS : 16 ≤ theta * s := by
    have h := hcutThetaProduct.trans hcutThetaScale
    nlinarith only [h]
  have hcutMeanScale := mul_le_mul_of_nonneg_left hs heta.le
  have hetaS : 16 * r ≤ eta * s := by
    have h := hcutMeanProduct.trans hcutMeanScale
    nlinarith only [h]
  have hcutDeltaScale := mul_le_mul_of_nonneg_left hs hdelta.le
  have hdeltaS : 4 ≤ delta * s := by
    have h := hcutDeltaProduct.trans hcutDeltaScale
    nlinarith only [h]
  have hmlo : kappa * s ≤ (Nat.ceil (kappa * s) : ℝ) := Nat.le_ceil _
  have hmhi : (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ kappa * s)).le
  have hkappasmall : kappa ≤ 1 / 16 := by
    nlinarith only [hkappatheta, htheta, htheta0, htheta0half]
  have hkappaS : kappa * s ≤ s / 16 := by
    have h := mul_le_mul_of_nonneg_right hkappasmall hsnonneg
    nlinarith only [h]
  have htheta0m : 4 ≤ theta0 * (Nat.ceil (kappa * s) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hmlo htheta0pos.le
    calc
      4 ≤ theta0 * kappa * s := hthetaKappaS
      _ = theta0 * (kappa * s) := by ring
      _ ≤ theta0 * (Nat.ceil (kappa * s) : ℝ) := h
  have htheta0m_div : theta0 * (Nat.ceil (kappa * s) : ℝ) / 4 ≥ 1 := by
    rw [ge_iff_le]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    nlinarith only [htheta0m]
  have htwoM : 2 * (Nat.ceil (kappa * s) : ℝ) ≤ s / 4 := by
    have hmUpper : 2 * (Nat.ceil (kappa * s) : ℝ) ≤ 2 * kappa * s + 2 := by
      calc
        2 * (Nat.ceil (kappa * s) : ℝ) ≤ 2 * (kappa * s + 1) :=
          mul_le_mul_of_nonneg_left hmhi (by norm_num)
        _ = 2 * kappa * s + 2 := by ring
    have hkappaTwice : 2 * kappa * s ≤ s / 8 := by
      calc
        2 * kappa * s = 2 * (kappa * s) := by ring
        _ ≤ 2 * (s / 16) := mul_le_mul_of_nonneg_left hkappaS (by norm_num)
        _ = s / 8 := by ring
    have hsSmall : 2 ≤ s / 8 := by
      have h16 := hcutSixteen.trans hs
      linarith
    calc
      2 * (Nat.ceil (kappa * s) : ℝ) ≤ 2 * kappa * s + 2 := hmUpper
      _ ≤ s / 8 + 2 := by linarith only [hkappaTwice]
      _ ≤ s / 8 + s / 8 := by linarith only [hsSmall]
      _ = s / 4 := by ring
  have hmLeS : (Nat.ceil (kappa * s) : ℝ) ≤ s := by
    have h16 := hcutSixteen.trans hs
    calc
      (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 := hmhi
      _ ≤ s / 16 + 1 := by linarith only [hkappaS]
      _ ≤ s := by linarith
  have hthetaKS : kappa * s ≤ theta * s / 16 := by
    have h := mul_le_mul_of_nonneg_right hkappatheta hsnonneg
    nlinarith only [h]
  have hfourM : 4 * (Nat.ceil (kappa * s) : ℝ) ≤ theta * s / 2 := by
    have hmUpper : 4 * (Nat.ceil (kappa * s) : ℝ) ≤ 4 * kappa * s + 4 := by
      nlinarith only [hmhi]
    have hthetaLarge : 4 * kappa * s + 4 ≤ theta * s / 2 := by
      nlinarith only [hthetaKS, hthetaS]
    exact hmUpper.trans hthetaLarge
  have hangleCoeff : 2 * (1 + theta0 - theta / 2) ≤ 4 := by
    nlinarith only [htheta0half, htheta]
  have hangleM :
      2 * (Nat.ceil (kappa * s) : ℝ) * (1 + theta0 - theta / 2) ≤
        4 * (Nat.ceil (kappa * s) : ℝ) := by
    have hmnonneg : 0 ≤ (Nat.ceil (kappa * s) : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_right hangleCoeff hmnonneg
    nlinarith only [h]
  have hangle :
      (theta / 2) * s ≥
        2 * (Nat.ceil (kappa * s) : ℝ) * (1 + theta0 - theta / 2) := by
    nlinarith only [hangleM, hfourM]
  have hrRatio : r / (r + 1) ≤ 1 := by
    apply (div_le_iff₀ hrplus).2
    linarith
  have hkappaR : 2 * kappa * r ≤ eta / 8 := by
    have h := mul_le_mul_of_nonneg_right hkappaeta (by positivity : 0 ≤ 2 * r)
    have hmul : 2 * kappa * r ≤ 2 * (eta / (16 * (r + 1))) * r := by
      nlinarith only [h]
    calc
      2 * kappa * r ≤ 2 * (eta / (16 * (r + 1))) * r := hmul
      _ = (eta / 8) * (r / (r + 1)) := by
        field_simp [hrplus.ne']
        ring
      _ ≤ eta / 8 := by
        have hmulRatio := mul_le_mul_of_nonneg_left hrRatio (show 0 ≤ eta / 8 by positivity)
        linarith only [hmulRatio]
  have hmeanQuarter : 2 * r ≤ eta * s / 8 := by
    nlinarith only [hetaS]
  have hmMeanUpper :
      2 * (Nat.ceil (kappa * s) : ℝ) * r ≤
        2 * kappa * s * r + 2 * r := by
    have h := mul_le_mul_of_nonneg_right hmhi (by positivity : 0 ≤ 2 * r)
    nlinarith only [h]
  have hmean : 2 * (Nat.ceil (kappa * s) : ℝ) * r ≤ eta * s / 4 := by
    have hscale := mul_le_mul_of_nonneg_right hkappaR hsnonneg
    nlinarith only [hmMeanUpper, hscale, hmeanQuarter]
  have hdeltaKappa : kappa * s ≤ delta * s / 4 := by
    have h := mul_le_mul_of_nonneg_right hkappadelta hsnonneg
    nlinarith only [h]
  have hdeltaQuarter : 1 ≤ delta * s / 4 := by nlinarith only [hdeltaS]
  have hmDelta : (Nat.ceil (kappa * s) : ℝ) ≤ delta * s / 2 := by
    nlinarith only [hmhi, hdeltaKappa, hdeltaQuarter]
  exact ⟨hmlo, hmhi, htheta0m_div, htwoM, hangle, hmean, hmDelta, hmLeS⟩

/-- Apply the one source cutoff to two lengths at once. -/
theorem attachment_scale_two_lengths (a theta delta eta L muMean s t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (htheta : 0 < theta)
    (hthetaInterior : theta < min a (1 - a))
    (hdelta : 0 < delta) (heta : 0 < eta) (hL : 1 ≤ L) :
    let theta0 : ℝ := min a (1 - a)
    let r : ℝ := L + |muMean|
    let kappa : ℝ :=
      min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1))))
    let cutoff : ℝ :=
      max 1 (max (4 / (theta0 * kappa))
        (max 16 (max (16 / theta) (max (16 * r / eta) (4 / delta)))))
    cutoff ≤ s → cutoff ≤ t →
      (kappa * s ≤ (Nat.ceil (kappa * s) : ℝ) ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 ∧
        theta0 * (Nat.ceil (kappa * s) : ℝ) / 4 ≥ 1 ∧
        2 * (Nat.ceil (kappa * s) : ℝ) ≤ s / 4 ∧
        (theta / 2) * s ≥
          2 * (Nat.ceil (kappa * s) : ℝ) * (1 + theta0 - theta / 2) ∧
        2 * (Nat.ceil (kappa * s) : ℝ) * r ≤ eta * s / 4 ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ delta * s / 2 ∧
        (Nat.ceil (kappa * s) : ℝ) ≤ s) ∧
      (kappa * t ≤ (Nat.ceil (kappa * t) : ℝ) ∧
        (Nat.ceil (kappa * t) : ℝ) ≤ kappa * t + 1 ∧
        theta0 * (Nat.ceil (kappa * t) : ℝ) / 4 ≥ 1 ∧
        2 * (Nat.ceil (kappa * t) : ℝ) ≤ t / 4 ∧
        (theta / 2) * t ≥
          2 * (Nat.ceil (kappa * t) : ℝ) * (1 + theta0 - theta / 2) ∧
        2 * (Nat.ceil (kappa * t) : ℝ) * r ≤ eta * t / 4 ∧
        (Nat.ceil (kappa * t) : ℝ) ≤ delta * t / 2 ∧
        (Nat.ceil (kappa * t) : ℝ) ≤ t) := by
  let theta0 : ℝ := min a (1 - a)
  let r : ℝ := L + |muMean|
  let kappa : ℝ :=
    min (theta / 16) (min (delta / 4) (eta / (16 * (r + 1))))
  let cKappa : ℝ := 4 / (theta0 * kappa)
  let cSixteen : ℝ := 16
  let cTheta : ℝ := 16 / theta
  let cMean : ℝ := 16 * r / eta
  let cDelta : ℝ := 4 / delta
  let cutoff : ℝ :=
    max 1 (max cKappa (max cSixteen (max cTheta (max cMean cDelta))))
  have h := attachment_scale_bounds a theta delta eta L muMean
    ha ha1 htheta hthetaInterior hdelta heta hL
  dsimp only [theta0, r, kappa, cutoff] at h
  rcases h with ⟨_, _, _, _, hforall⟩
  change cutoff ≤ s → cutoff ≤ t →
    (kappa * s ≤ (Nat.ceil (kappa * s) : ℝ) ∧
      (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 ∧
      theta0 * (Nat.ceil (kappa * s) : ℝ) / 4 ≥ 1 ∧
      2 * (Nat.ceil (kappa * s) : ℝ) ≤ s / 4 ∧
      (theta / 2) * s ≥
        2 * (Nat.ceil (kappa * s) : ℝ) * (1 + theta0 - theta / 2) ∧
      2 * (Nat.ceil (kappa * s) : ℝ) * r ≤ eta * s / 4 ∧
      (Nat.ceil (kappa * s) : ℝ) ≤ delta * s / 2 ∧
      (Nat.ceil (kappa * s) : ℝ) ≤ s) ∧
    (kappa * t ≤ (Nat.ceil (kappa * t) : ℝ) ∧
      (Nat.ceil (kappa * t) : ℝ) ≤ kappa * t + 1 ∧
      theta0 * (Nat.ceil (kappa * t) : ℝ) / 4 ≥ 1 ∧
      2 * (Nat.ceil (kappa * t) : ℝ) ≤ t / 4 ∧
      (theta / 2) * t ≥
        2 * (Nat.ceil (kappa * t) : ℝ) * (1 + theta0 - theta / 2) ∧
      2 * (Nat.ceil (kappa * t) : ℝ) * r ≤ eta * t / 4 ∧
      (Nat.ceil (kappa * t) : ℝ) ≤ delta * t / 2 ∧
      (Nat.ceil (kappa * t) : ℝ) ≤ t)
  intro hs ht
  exact ⟨hforall s hs, hforall t ht⟩

end LPPDifferentiability

end
