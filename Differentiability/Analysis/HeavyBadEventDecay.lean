/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.HeavyAttachmentCutoffs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Heavy attachment bad-event decay

The three deterministic polynomial bounds for the source's bad events tend
to zero. The later attachment weight-failure term is handled separately.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The source's first polynomial bad-event upper bound tends to zero. -/
theorem tendsto_heavy_bad_event_e1_bound (p D C : ℝ)
    (hp : 1 < p) (hD : 1 ≤ D) (hC : 0 ≤ C) :
    Tendsto (fun s : ℝ => 48 * D * s ^ 2 * (C * s ^ (-p)) ^ 2)
      atTop (𝓝 0) := by
  let r : ℝ := 2 * (p - 1)
  have hr : 0 < r := by dsimp [r]; linarith
  have hpow : Tendsto (fun s : ℝ => s ^ (-r)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hr
  let A : ℝ := 48 * D * C ^ 2
  have hbound : Tendsto (fun s : ℝ => A * s ^ (-r)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := A)).mul hpow
    simpa only [mul_zero] using h
  have hnonneg : ∀ᶠ s : ℝ in atTop,
      0 ≤ 48 * D * s ^ 2 * (C * s ^ (-p)) ^ 2 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have hcoef : 0 ≤ 48 * D := by nlinarith [hD]
    have htail : 0 ≤ C * s ^ (-p) :=
      mul_nonneg hC (Real.rpow_nonneg hs _)
    have htailSquare : 0 ≤ (C * s ^ (-p)) ^ 2 := by
      rw [pow_two]
      exact mul_nonneg htail htail
    exact mul_nonneg (mul_nonneg hcoef (sq_nonneg s)) htailSquare
  have hle : ∀ᶠ s : ℝ in atTop,
      48 * D * s ^ 2 * (C * s ^ (-p)) ^ 2 ≤ A * s ^ (-r) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hs0 : 0 ≤ s := hs.le
    have hSquare : (s ^ (-p)) ^ 2 = s ^ ((-p) * (2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      norm_num
    have hNatural : s ^ 2 = s ^ (2 : ℝ) :=
      (Real.rpow_natCast s 2).symm
    have hProduct : s ^ 2 * (s ^ (-p)) ^ 2 = s ^ (-r) := by
      calc
        s ^ 2 * (s ^ (-p)) ^ 2 = s ^ (2 : ℝ) * s ^ ((-p) * 2) := by
          rw [hNatural, hSquare]
        _ = s ^ ((2 : ℝ) + (-p) * 2) := by rw [← Real.rpow_add hs]
        _ = s ^ (-r) := by congr 1; dsimp [r]; ring
    dsimp [A]
    rw [mul_pow]
    calc
      48 * D * s ^ 2 * (C ^ 2 * (s ^ (-p)) ^ 2) =
          (48 * D * C ^ 2) * (s ^ 2 * (s ^ (-p)) ^ 2) := by ring
      _ ≤ (48 * D * C ^ 2) * s ^ (-r) := by
        rw [hProduct]
  exact squeeze_zero' hnonneg hle hbound

/-- The source's second polynomial bad-event upper bound tends to zero. -/
theorem tendsto_heavy_bad_event_e2_bound (p D B C : ℝ) (L : ℕ)
    (hp : 1 < p) (hD : 1 ≤ D) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    Tendsto
      (fun s : ℝ =>
        (D * s + 1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * (C * s ^ (-p)))
      atTop (𝓝 0) := by
  let q : ℝ := p - 1
  let M : ℝ := B * ((L + 1 : ℕ) : ℝ) ^ 2
  let A₁ : ℝ := D * C
  let A₂ : ℝ := (1 + M) * C
  have hq : 0 < q := by dsimp [q]; linarith
  have hp0 : 0 < p := by linarith
  have hfirst : Tendsto (fun s : ℝ => A₁ * s ^ (-q)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := A₁)).mul (tendsto_rpow_neg_atTop hq)
    simpa only [mul_zero] using h
  have hsecond : Tendsto (fun s : ℝ => A₂ * s ^ (-p)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := A₂)).mul (tendsto_rpow_neg_atTop hp0)
    simpa only [mul_zero] using h
  have hbound : Tendsto
      (fun s : ℝ => A₁ * s ^ (-q) + A₂ * s ^ (-p)) atTop (𝓝 0) := by
    simpa only [zero_add] using hfirst.add hsecond
  have hnonneg : ∀ᶠ s : ℝ in atTop,
      0 ≤ (D * s + 1 + M) * (C * s ^ (-p)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : 0 ≤ s := le_trans (by norm_num) hs
    have hD0 : 0 ≤ D := le_trans (by norm_num) hD
    have hM : 0 ≤ M := by
      dsimp [M]
      exact mul_nonneg hB (sq_nonneg ((L + 1 : ℕ) : ℝ))
    have hleft : 0 ≤ D * s + 1 + M :=
      add_nonneg (add_nonneg (mul_nonneg hD0 hs0) (by norm_num)) hM
    have hright : 0 ≤ C * s ^ (-p) :=
      mul_nonneg hC (Real.rpow_nonneg hs0 _)
    exact mul_nonneg hleft hright
  have hle : ∀ᶠ s : ℝ in atTop,
      (D * s + 1 + M) * (C * s ^ (-p)) ≤
        A₁ * s ^ (-q) + A₂ * s ^ (-p) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hscale : s * s ^ (-p) = s ^ (1 - p) := by
      calc
        s * s ^ (-p) = s ^ (1 : ℝ) * s ^ (-p) := by rw [Real.rpow_one]
        _ = s ^ (1 + (-p)) := by rw [← Real.rpow_add hs]
        _ = s ^ (1 - p) := by congr 1
    dsimp [A₁, A₂, M, q]
    calc
      (D * s + 1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * (C * s ^ (-p)) =
          (D * C) * (s * s ^ (-p)) +
            (1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * C * s ^ (-p) := by ring
      _ = (D * C) * s ^ (1 - p) +
            (1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * C * s ^ (-p) := by rw [hscale]
      _ ≤ (D * C) * s ^ (-(p - 1)) +
            (1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * C * s ^ (-p) := by
        rw [show (1 - p : ℝ) = -(p - 1) by ring]
  exact squeeze_zero' hnonneg hle hbound

/-- The source's third polynomial bad-event upper bound, with its actual natural
ceiling, tends to zero. -/
theorem tendsto_heavy_bad_event_e3_bound (p kappa D C : ℝ) (K : ℕ)
    (hp : 1 < p) (hK : 2 ≤ K)
    (hKp : 4 ≤ (K : ℝ) * (p - 1))
    (hkappa : 0 < kappa) (hD : 1 ≤ D) (hC : 0 ≤ C) :
    Tendsto
      (fun s : ℝ =>
        (D * s + 1) *
          ((((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
            (C * s ^ (-p))) ^ K)
      atTop (𝓝 0) := by
  let q : ℝ := p - 1
  let r : ℝ := (K : ℝ) * q - 1
  let a : ℝ := ((2 * K + 5 : ℕ) : ℝ)
  let A : ℝ := a * (kappa + 2) * C
  let Q : ℝ := (D + 1) * A ^ K
  have hq : 0 < q := by dsimp [q]; linarith
  have hKreal : 2 ≤ (K : ℝ) := by exact_mod_cast hK
  have hmargin : 1 ≤ ((K : ℝ) - 1) * q := by
    have hhalf : (K : ℝ) / 2 ≤ (K : ℝ) - 1 := by linarith
    have hhalfproduct : 2 ≤ ((K : ℝ) / 2) * q := by
      dsimp [q]
      nlinarith [hKp]
    have hcompare := mul_le_mul_of_nonneg_right hhalf hq.le
    nlinarith [hhalfproduct, hcompare]
  have hexponent : -r ≤ -q := by
    dsimp [r]
    dsimp [q] at hmargin
    linarith
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (show 0 < 2 * K + 5 by omega)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hpow : Tendsto (fun s : ℝ => s ^ (-q)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hq
  have hbound : Tendsto (fun s : ℝ => Q * s ^ (-q)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Q)).mul hpow
    simpa only [mul_zero] using h
  have hnonneg : ∀ᶠ s : ℝ in atTop,
      0 ≤ (D * s + 1) *
        ((((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
          (C * s ^ (-p))) ^ K := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : 0 ≤ s := le_trans (by norm_num) hs
    have hD0 : 0 ≤ D := le_trans (by norm_num) hD
    have htail : 0 ≤ C * s ^ (-p) :=
      mul_nonneg hC (Real.rpow_nonneg hs0 _)
    have hfactor : 0 ≤
        (((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
          (C * s ^ (-p)) :=
      mul_nonneg (Nat.cast_nonneg _) htail
    have hleft : 0 ≤ D * s + 1 :=
      add_nonneg (mul_nonneg hD0 hs0) (by norm_num)
    exact mul_nonneg hleft (pow_nonneg hfactor K)
  have hle : ∀ᶠ s : ℝ in atTop,
      (D * s + 1) *
        ((((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
          (C * s ^ (-p))) ^ K ≤ Q * s ^ (-q) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : 0 ≤ s := le_trans (by norm_num) hs
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hceilPlus :
        ((Nat.ceil (kappa * s) + 1 : ℕ) : ℝ) ≤ (kappa + 2) * s :=
      heavy_attachment_ceiling_add_one_bound kappa s hkappa hs
    have hlin : D * s + 1 ≤ (D + 1) * s := by
      have hD0 : 0 ≤ D := le_trans (by norm_num) hD
      nlinarith [hs]
    have htail : 0 ≤ C * s ^ (-p) :=
      mul_nonneg hC (Real.rpow_nonneg hs0 _)
    have hfactor :
        (((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
            (C * s ^ (-p)) ≤ A * s ^ (1 - p) := by
      have hcount :
          (((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) ≤
            a * ((kappa + 2) * s) := by
        calc
          (((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) =
              a * ((Nat.ceil (kappa * s) + 1 : ℕ) : ℝ) := by
                simp only [Nat.cast_mul]
                rfl
          _ ≤ a * ((kappa + 2) * s) :=
            mul_le_mul_of_nonneg_left hceilPlus ha.le
      have hscale : s * s ^ (-p) = s ^ (1 - p) := by
        calc
          s * s ^ (-p) = s ^ (1 : ℝ) * s ^ (-p) := by rw [Real.rpow_one]
          _ = s ^ (1 + (-p)) := by rw [← Real.rpow_add hspos]
          _ = s ^ (1 - p) := by congr 1
      calc
        (((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
            (C * s ^ (-p)) ≤
          (a * ((kappa + 2) * s)) * (C * s ^ (-p)) :=
            mul_le_mul_of_nonneg_right hcount htail
        _ = (a * (kappa + 2) * C) * (s * s ^ (-p)) := by ring
        _ = A * s ^ (1 - p) := by rw [hscale]
    have hfactorNonneg : 0 ≤
        (((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
          (C * s ^ (-p)) := by positivity
    have hpowFactor :
        ((((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
          (C * s ^ (-p))) ^ K ≤ (A * s ^ (1 - p)) ^ K :=
      pow_le_pow_left₀ hfactorNonneg hfactor K
    have hupper :
        (D * s + 1) *
          ((((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
            (C * s ^ (-p))) ^ K ≤
          (D + 1) * s * (A * s ^ (1 - p)) ^ K := by
      calc
        _ ≤ (D + 1) * s *
            ((((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
              (C * s ^ (-p))) ^ K :=
          mul_le_mul_of_nonneg_right hlin (pow_nonneg hfactorNonneg K)
        _ ≤ (D + 1) * s * (A * s ^ (1 - p)) ^ K :=
          mul_le_mul_of_nonneg_left hpowFactor (by positivity)
    have hpowScale : (s ^ (1 - p)) ^ K = s ^ ((1 - p) * (K : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
    have hcombine : s * s ^ ((1 - p) * (K : ℝ)) =
        s ^ (1 + (1 - p) * (K : ℝ)) := by
      calc
        s * s ^ ((1 - p) * (K : ℝ)) =
            s ^ (1 : ℝ) * s ^ ((1 - p) * (K : ℝ)) := by rw [Real.rpow_one]
        _ = s ^ (1 + (1 - p) * (K : ℝ)) := by rw [← Real.rpow_add hspos]
    have hexpEq : 1 + (1 - p) * (K : ℝ) = -r := by
      dsimp [r, q]
      ring
    have hscalePow :
        (D + 1) * s * (A * s ^ (1 - p)) ^ K = Q * s ^ (-r) := by
      calc
        (D + 1) * s * (A * s ^ (1 - p)) ^ K =
            (D + 1) * s * (A ^ K * (s ^ (1 - p)) ^ K) := by rw [mul_pow]
        _ = ((D + 1) * A ^ K) * (s * s ^ ((1 - p) * (K : ℝ))) := by
          rw [hpowScale]
          ring
        _ = ((D + 1) * A ^ K) * s ^ (1 + (1 - p) * (K : ℝ)) := by
          rw [hcombine]
        _ = Q * s ^ (-r) := by rw [hexpEq]
    have hpowOrder : s ^ (-r) ≤ s ^ (-q) :=
      Real.rpow_le_rpow_of_exponent_le hs hexponent
    have hQorder : Q * s ^ (-r) ≤ Q * s ^ (-q) :=
      mul_le_mul_of_nonneg_left hpowOrder hQ
    calc
      _ ≤ (D + 1) * s * (A * s ^ (1 - p)) ^ K := hupper
      _ = Q * s ^ (-r) := hscalePow
      _ ≤ Q * s ^ (-q) := hQorder
  exact squeeze_zero' hnonneg hle hbound

/-- The three source bad-event bounds have a sum tending to zero. -/
theorem tendsto_heavy_bad_event_bound_sum
    (p kappa D B C : ℝ) (K L : ℕ)
    (hp : 1 < p) (hK : 2 ≤ K)
    (hKp : 4 ≤ (K : ℝ) * (p - 1))
    (hkappa : 0 < kappa) (hD : 1 ≤ D)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    Tendsto
      (fun s : ℝ =>
        48 * D * s ^ 2 * (C * s ^ (-p)) ^ 2 +
          (D * s + 1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * (C * s ^ (-p)) +
          (D * s + 1) *
            ((((2 * K + 5) * (Nat.ceil (kappa * s) + 1) : ℕ) : ℝ) *
              (C * s ^ (-p))) ^ K)
      atTop (𝓝 0) := by
  have hE1 := tendsto_heavy_bad_event_e1_bound p D C hp hD hC
  have hE2 := tendsto_heavy_bad_event_e2_bound p D B C L hp hD hB hC
  have hE3 := tendsto_heavy_bad_event_e3_bound
    p kappa D C K hp hK hKp hkappa hD hC
  simpa only [zero_add, add_zero] using (hE1.add hE2).add hE3

end LPPDifferentiability

end
