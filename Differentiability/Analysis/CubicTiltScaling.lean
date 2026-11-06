/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Cubic length tilt arithmetic

Deterministic ceiling bounds, limits for the source resampling scale and its
actual binomial mean, and the source exponential cost under an explicit
cardinality bound.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The natural ceiling of the cubic length lies between the cubic scale and
twice that scale for `s ≥ 1`. -/
theorem cubic_length_ceil_bounds (s : ℝ) (hs : 1 ≤ s) :
    1 ≤ Nat.ceil (s ^ 3) ∧
      s ^ 3 ≤ (Nat.ceil (s ^ 3) : ℕ) ∧
      (Nat.ceil (s ^ 3) : ℝ) ≤ 2 * s ^ 3 := by
  have hs3 : 1 ≤ s ^ 3 := by
    have hfactor : 0 ≤ s ^ 2 + s + 1 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hfactor]
  have hceil : (Nat.ceil (s ^ 3) : ℝ) < s ^ 3 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.one_le_ceil_iff.mpr (by positivity)
  · exact Nat.le_ceil _
  · linarith

/-- The source resampling scale is positive and has the required quadratic
upper bound for `s ≥ 1`. -/
theorem cubic_tilt_delta_bounds (alpha phi c eta s : ℝ)
    (ha : 0 < alpha) (hphi : 0 < phi) (hc : 0 < c) (heta : 0 < eta)
    (hs : 1 ≤ s) :
    0 < 8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ)) ∧
      8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ)) ≤
        8 * eta / (alpha * phi * c * s ^ 2) := by
  have hceil := (cubic_length_ceil_bounds s hs).2.1
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hnpos : 0 < (Nat.ceil (s ^ 3) : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one
      (cubic_length_ceil_bounds s hs).1)
  have hratio : s / (Nat.ceil (s ^ 3) : ℝ) ≤ 1 / s ^ 2 := by
    have hs2 : 0 < s ^ 2 := by positivity
    apply (div_le_iff₀ hnpos).2
    calc
      s = s ^ 3 / s ^ 2 := by
        field_simp [hs2.ne']
      _ ≤ (Nat.ceil (s ^ 3) : ℝ) / s ^ 2 :=
        div_le_div_of_nonneg_right hceil (sq_nonneg s)
      _ = (1 / s ^ 2) * (Nat.ceil (s ^ 3) : ℝ) := by ring
  have hconstant : 0 ≤ 8 * eta / (alpha * phi * c) := by positivity
  constructor
  · positivity
  · calc
      8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ)) =
          (8 * eta / (alpha * phi * c)) *
            (s / (Nat.ceil (s ^ 3) : ℝ)) := by
              field_simp [ha.ne', hphi.ne', hc.ne', hnpos.ne']
      _ ≤ (8 * eta / (alpha * phi * c)) * (1 / s ^ 2) :=
        mul_le_mul_of_nonneg_left hratio hconstant
      _ = 8 * eta / (alpha * phi * c * s ^ 2) := by
          field_simp [ha.ne', hphi.ne', hc.ne', hspos.ne']

/-- The literal source resampling scale tends to zero as `s` tends to positive
infinity. -/
theorem tendsto_cubic_tilt_delta (alpha phi c eta : ℝ)
    (ha : 0 < alpha) (hphi : 0 < phi) (hc : 0 < c) (heta : 0 < eta) :
    Tendsto
      (fun s : ℝ =>
        8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ)))
      atTop (𝓝 0) := by
  let delta : ℝ → ℝ := fun s =>
    8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ))
  change Tendsto delta atTop (𝓝 0)
  let C : ℝ := 8 * eta / (alpha * phi * c)
  have hpow : Tendsto (fun s : ℝ => s ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hinv : Tendsto (fun s : ℝ => (s ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hboundLimit : Tendsto (fun s : ℝ => C / s ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun s : ℝ => C * (s ^ 2)⁻¹) atTop (𝓝 (C * 0)))
  have hnonneg : ∀ᶠ s : ℝ in atTop, 0 ≤ delta s := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    simpa only [delta] using
      (cubic_tilt_delta_bounds alpha phi c eta s ha hphi hc heta hs).1.le
  have hle : ∀ᶠ s : ℝ in atTop, delta s ≤ C / s ^ 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hdelta :=
      (cubic_tilt_delta_bounds alpha phi c eta s ha hphi hc heta hs).2
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    calc
      delta s ≤ 8 * eta / (alpha * phi * c * s ^ 2) := by
        simpa only [delta] using hdelta
      _ = C / s ^ 2 := by
        dsimp [C]
        field_simp [ha.ne', hphi.ne', hc.ne', hspos.ne']
  exact squeeze_zero' hnonneg hle hboundLimit

/-- The source resampling scale is eventually strictly between zero and one. -/
theorem eventually_cubic_tilt_delta_mem_Ioo (alpha phi c eta : ℝ)
    (ha : 0 < alpha) (hphi : 0 < phi) (hc : 0 < c) (heta : 0 < eta) :
    ∀ᶠ s : ℝ in atTop,
      0 < 8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ)) ∧
        8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ)) < 1 := by
  have hdelta := tendsto_cubic_tilt_delta alpha phi c eta ha hphi hc heta
  have hsmall : ∀ᶠ s : ℝ in atTop,
      8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ)) < 1 := by
    simpa only [Set.mem_Iio] using
      hdelta.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with s hs hlt
  exact ⟨(cubic_tilt_delta_bounds alpha phi c eta s ha hphi hc heta hs).1, hlt⟩

/-- The actual binomial mean, using `m = ceil (phi * n)`, is bounded below by
the source's linear quantity. -/
theorem cubic_tilt_binomial_mean_lower_bound (alpha phi c eta s : ℝ)
    (ha : 0 < alpha) (hphi : 0 < phi) (hc : 0 < c) (heta : 0 < eta)
    (hs : 1 ≤ s) :
    let n : ℕ := Nat.ceil (s ^ 3)
    let delta : ℝ := 8 * eta * s / (alpha * phi * c * (n : ℝ))
    let m : ℕ := Nat.ceil (phi * (n : ℝ))
    let lambda : ℝ := (m : ℝ) * delta * alpha / 2
    4 * eta * s / c ≤ lambda := by
  dsimp only
  let n : ℝ := (Nat.ceil (s ^ 3) : ℕ)
  let m : ℝ := (Nat.ceil (phi * n) : ℕ)
  let delta : ℝ := 8 * eta * s / (alpha * phi * c * n)
  change 4 * eta * s / c ≤ m * delta * alpha / 2
  have hceil : s ^ 3 ≤ n := by
    dsimp [n]
    exact Nat.le_ceil _
  have hnpos : 0 < n :=
    lt_of_lt_of_le (by positivity : 0 < s ^ 3) hceil
  have hm : phi * n ≤ m := by
    dsimp [m]
    exact Nat.le_ceil _
  have hfactor : 0 ≤ delta * alpha / 2 := by positivity
  have hidentity : 4 * eta * s / c = phi * n * (delta * alpha / 2) := by
    dsimp [n, delta]
    field_simp [ha.ne', hphi.ne', hc.ne', hnpos.ne']
    ring
  calc
    4 * eta * s / c = phi * n * (delta * alpha / 2) := hidentity
    _ ≤ m * (delta * alpha / 2) := mul_le_mul_of_nonneg_right hm hfactor
    _ = m * delta * alpha / 2 := by ring

/-- The actual binomial mean tends to positive infinity. -/
theorem tendsto_cubic_tilt_binomial_mean_atTop (alpha phi c eta : ℝ)
    (ha : 0 < alpha) (hphi : 0 < phi) (hc : 0 < c) (heta : 0 < eta) :
    Tendsto
      (fun s : ℝ =>
        let n : ℕ := Nat.ceil (s ^ 3)
        let delta : ℝ := 8 * eta * s / (alpha * phi * c * (n : ℝ))
        let m : ℕ := Nat.ceil (phi * (n : ℝ))
        (m : ℝ) * delta * alpha / 2)
      atTop atTop := by
  have hlinear : Tendsto (fun s : ℝ => 4 * eta * s / c) atTop atTop := by
    have hid : Tendsto (fun s : ℝ => s) atTop atTop := tendsto_id
    have hconst : Tendsto (fun s : ℝ => (4 * eta / c) * s) atTop atTop :=
      hid.const_mul_atTop (show 0 < 4 * eta / c by positivity)
    exact hconst.congr' (by
      filter_upwards [] with s
      field_simp [hc.ne'])
  refine Filter.tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  exact cubic_tilt_binomial_mean_lower_bound alpha phi c eta s ha hphi hc heta hs

/-- Four divided by the actual binomial mean tends to zero. -/
theorem tendsto_four_div_cubic_tilt_binomial_mean (alpha phi c eta : ℝ)
    (ha : 0 < alpha) (hphi : 0 < phi) (hc : 0 < c) (heta : 0 < eta) :
    Tendsto
      (fun s : ℝ =>
        let n : ℕ := Nat.ceil (s ^ 3)
        let delta : ℝ := 8 * eta * s / (alpha * phi * c * (n : ℝ))
        let m : ℕ := Nat.ceil (phi * (n : ℝ))
        4 / ((m : ℝ) * delta * alpha / 2))
      atTop (𝓝 0) := by
  have hmean := tendsto_cubic_tilt_binomial_mean_atTop alpha phi c eta ha hphi hc heta
  let mean : ℝ → ℝ := fun s =>
    let n : ℕ := Nat.ceil (s ^ 3)
    let delta : ℝ := 8 * eta * s / (alpha * phi * c * (n : ℝ))
    let m : ℕ := Nat.ceil (phi * (n : ℝ))
    (m : ℝ) * delta * alpha / 2
  have hmean' : Tendsto mean atTop atTop := by
    simpa only [mean] using hmean
  change Tendsto (fun s : ℝ => 4 / mean s) atTop (𝓝 0)
  have hinv : Tendsto (fun s : ℝ => (mean s)⁻¹) atTop (𝓝 0) := by
    apply Tendsto.congr' ?_ (tendsto_inv_atTop_zero.comp hmean')
    filter_upwards [] with s
    rfl
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul hinv)

/-- The source exponential cost under the explicit deterministic strip count.
The premise on `k` is only an arithmetic input to this implication. -/
theorem cubic_tilt_exponential_cost_bound (alpha phi c eta s : ℝ)
    (ha : 0 < alpha) (hphi : 0 < phi) (hc : 0 < c) (heta : 0 < eta)
    (hs : 1 ≤ s) (k : ℕ)
    (hk : (k : ℝ) ≤ 34 * (Nat.ceil (s ^ 3) : ℝ) * s) :
    Real.exp
        ((3 : ℝ) / 2 *
          (8 * eta * s / (alpha * phi * c * (Nat.ceil (s ^ 3) : ℝ))) ^ 2 *
          (k : ℝ)) ≤
      Real.exp
        ((3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2)) *
          (s ^ 3 / (Nat.ceil (s ^ 3) : ℝ))) ∧
    Real.exp
        ((3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2)) *
          (s ^ 3 / (Nat.ceil (s ^ 3) : ℝ))) ≤
      Real.exp (3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2) : ℝ) := by
  let n : ℝ := (Nat.ceil (s ^ 3) : ℕ)
  let delta : ℝ := 8 * eta * s / (alpha * phi * c * n)
  have hceil : s ^ 3 ≤ n := by
    dsimp [n]
    exact (cubic_length_ceil_bounds s hs).2.1
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < s ^ 3) hceil
  have hscaleSq : delta ^ 2 =
      (64 * eta ^ 2 * s ^ 2) / (alpha ^ 2 * phi ^ 2 * c ^ 2 * n ^ 2) := by
    dsimp [delta, n]
    field_simp [ha.ne', hphi.ne', hc.ne', hnpos.ne']
    ring
  have hkmul : delta ^ 2 * (k : ℝ) ≤ delta ^ 2 * (34 * n * s) :=
    mul_le_mul_of_nonneg_left hk (sq_nonneg delta)
  have hscaled : (3 : ℝ) / 2 * delta ^ 2 * (k : ℝ) ≤
      (3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2)) * (s ^ 3 / n) := by
    calc
      (3 : ℝ) / 2 * delta ^ 2 * (k : ℝ) ≤
          (3 : ℝ) / 2 * delta ^ 2 * (34 * n * s) := by
            have h := mul_le_mul_of_nonneg_left hkmul
              (show 0 ≤ (3 : ℝ) / 2 by positivity)
            simpa only [mul_assoc] using h
      _ = (3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2)) * (s ^ 3 / n) := by
            rw [hscaleSq]
            field_simp [ha.ne', hphi.ne', hc.ne', hnpos.ne']
            ring
  have hratio : s ^ 3 / n ≤ 1 := (div_le_one hnpos).2 hceil
  have hconstant : 0 ≤ 3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2) := by
    positivity
  have hfinal :
      (3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2)) * (s ^ 3 / n) ≤
        3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2) := by
    calc
      (3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2)) * (s ^ 3 / n) ≤
          (3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2)) * 1 :=
            mul_le_mul_of_nonneg_left hratio hconstant
      _ = 3264 * eta ^ 2 / (alpha ^ 2 * phi ^ 2 * c ^ 2) := by ring
  constructor
  · exact Real.exp_le_exp.mpr hscaled
  · exact Real.exp_le_exp.mpr hfinal

end LPPDifferentiability

end
