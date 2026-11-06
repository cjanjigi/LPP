/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.CubicTiltScaling
public import LPP_Foundations.Analysis.HomogeneousRescaling

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Shape continuity on a cubic strip

The cubic scale and the signed transverse strip condition put every normalized
endpoint difference in one shrinking neighborhood of the reference direction.
Continuity controls the shape there, and the existing homogeneous extension
returns the estimate to the original scale.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace LPPDifferentiability

/-- A strict shape gap at an interior direction gives the source's uniform
shape bound for every natural endpoint difference in the cubic strip. -/
theorem eventually_cubic_tilt_strip_shape_bound
    (g : Quadrant → ℝ)
    (hg : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a phi : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hphi : 0 < phi)
    (hgap : g (toQuadrant (a, 1 - a)) ≤ 1 - 4 * phi) :
    ∀ᶠ s : ℝ in atTop,
      ∀ d : ℕ × ℕ,
        d.1 + d.2 = Nat.ceil (s ^ 3) →
        |(1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)| ≤ 16 * s →
        g (toQuadrant ((d.1 : ℝ), (d.2 : ℝ))) ≤
          (1 - 3 * phi) * (Nat.ceil (s ^ 3) : ℝ) := by
  let q : Quadrant := toQuadrant (a, 1 - a)
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.continuousAt_iff.mp (hg.continuousAt : ContinuousAt g q)) phi hphi
  have hpow : Tendsto (fun s : ℝ => s ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hinv : Tendsto (fun s : ℝ => (s ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hsmallLimit : Tendsto (fun s : ℝ => 16 / s ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun s : ℝ => 16 * (s ^ 2)⁻¹) atTop (𝓝 (16 * 0)))
  have hsmall : ∀ᶠ s : ℝ in atTop, 16 / s ^ 2 < δ :=
    hsmallLimit.eventually (Iio_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with s hs hsδ
  intro d hd hstrip
  let n : ℝ := (Nat.ceil (s ^ 3) : ℝ)
  have hnNat : 1 ≤ Nat.ceil (s ^ 3) := (cubic_length_ceil_bounds s hs).1
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hnNat)
  have hs3n : s ^ 3 ≤ n := by
    dsimp [n]
    exact (cubic_length_ceil_bounds s hs).2.1
  have hdR : (d.1 : ℝ) + (d.2 : ℝ) = n := by
    dsimp [n]
    exact_mod_cast hd
  have hratio : s / n ≤ 1 / s ^ 2 := by
    have hs2 : 0 < s ^ 2 := by positivity
    apply (div_le_iff₀ hn).2
    calc
      s = s ^ 3 / s ^ 2 := by field_simp [hs2.ne']
      _ ≤ n / s ^ 2 := div_le_div_of_nonneg_right hs3n (sq_nonneg s)
      _ = (1 / s ^ 2) * n := by ring
  let rho : ℝ := (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)
  have hrhoBound : |rho| ≤ 16 * s := by
    simpa only [rho] using hstrip
  have hrhoDiv : |rho / n| ≤ 16 / s ^ 2 := by
    rw [abs_div, abs_of_pos hn]
    calc
      |rho| / n ≤ (16 * s) / n := div_le_div_of_nonneg_right hrhoBound hn.le
      _ = 16 * (s / n) := by ring
      _ ≤ 16 * (1 / s ^ 2) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 16 / s ^ 2 := by ring
  have hrho : rho = (d.1 : ℝ) - a * n := by
    dsimp [rho]
    rw [← hdR]
    ring
  have hratioSum : (d.1 : ℝ) / n + (d.2 : ℝ) / n = 1 := by
    rw [← add_div, hdR, div_self hn.ne']
  have hfirst : (d.1 : ℝ) / n = a + rho / n := by
    rw [hrho]
    field_simp [hn.ne']; ring
  have hsecond : (d.2 : ℝ) / n = 1 - a - rho / n := by
    linarith [hratioSum, hfirst]
  let x : ℝ × ℝ := ((d.1 : ℝ) / n, (d.2 : ℝ) / n)
  let z : ℝ × ℝ := ((d.1 : ℝ), (d.2 : ℝ))
  have hx₁ : 0 ≤ x.1 := by dsimp [x]; positivity
  have hx₂ : 0 ≤ x.2 := by dsimp [x]; positivity
  have hsigned : x = (a + rho / n, 1 - a - rho / n) := by
    apply Prod.ext
    · dsimp [x]
      exact hfirst
    · dsimp [x]
      exact hsecond
  let y : Quadrant := toQuadrant x
  have hycoord : quadrantInclusion y = x := by
    dsimp [y]
    exact quadrantInclusion_toQuadrant x hx₁ hx₂
  have hqcoord : quadrantInclusion q = (a, 1 - a) := by
    dsimp [q]
    exact quadrantInclusion_toQuadrant (a, 1 - a) ha₀.le (by linarith [ha₁])
  have hy₁ : (y.1 : ℝ) = x.1 := congrArg Prod.fst hycoord
  have hy₂ : (y.2 : ℝ) = x.2 := congrArg Prod.snd hycoord
  have hq₁ : (q.1 : ℝ) = a := congrArg Prod.fst hqcoord
  have hq₂ : (q.2 : ℝ) = 1 - a := congrArg Prod.snd hqcoord
  have hsigned₁ : x.1 = a + rho / n := congrArg Prod.fst hsigned
  have hsigned₂ : x.2 = 1 - a - rho / n := congrArg Prod.snd hsigned
  have hy₁' : (y.1 : ℝ) = a + rho / n := hy₁.trans hsigned₁
  have hy₂' : (y.2 : ℝ) = 1 - a - rho / n := hy₂.trans hsigned₂
  have hdist₁ : dist y.1 q.1 < δ := by
    calc
      dist y.1 q.1 = |(y.1 : ℝ) - (q.1 : ℝ)| := by rw [NNReal.dist_eq]
      _ = |rho / n| := by rw [hy₁', hq₁]; congr 1; ring
      _ ≤ 16 / s ^ 2 := hrhoDiv
      _ < δ := hsδ
  have hdist₂ : dist y.2 q.2 < δ := by
    calc
      dist y.2 q.2 = |(y.2 : ℝ) - (q.2 : ℝ)| := by rw [NNReal.dist_eq]
      _ = |rho / n| := by
        rw [hy₂', hq₂]
        calc
          |1 - a - rho / n - (1 - a)| = |-(rho / n)| := by congr 1; ring
          _ = |rho / n| := by rw [abs_neg]
      _ ≤ 16 / s ^ 2 := hrhoDiv
      _ < δ := hsδ
  have hdist : dist y q < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hdist₁, hdist₂⟩
  have hclose : dist (g y) (g q) < phi := hmod hdist
  have hnear : g y < g q + phi := by
    rw [Real.dist_eq] at hclose
    have hright := (abs_lt.mp hclose).2
    linarith
  have hgapq : g q ≤ 1 - 4 * phi := by simpa only [q] using hgap
  have hshape : g y < 1 - 3 * phi := by linarith [hnear, hgapq]
  let c : ℝ≥0 := ⟨n, hn.le⟩
  have hscale : c • x = z := by
    apply Prod.ext
    · change n * ((d.1 : ℝ) / n) = (d.1 : ℝ)
      exact mul_div_cancel₀ _ hn.ne'
    · change n * ((d.2 : ℝ) / n) = (d.2 : ℝ)
      exact mul_div_cancel₀ _ hn.ne'
  have hscaleShape : g (toQuadrant z) = n * g y := by
    have h := quadrantExtension_smul g hhom c x
    rw [hscale] at h
    change g (toQuadrant z) = n * g (toQuadrant x) at h
    simpa only [y] using h
  have hfinal : g (toQuadrant z) < (1 - 3 * phi) * n := by
    calc
      g (toQuadrant z) = n * g y := hscaleShape
      _ < n * (1 - 3 * phi) := mul_lt_mul_of_pos_left hshape hn
      _ = (1 - 3 * phi) * n := by ring
  simpa only [z, n] using hfinal.le

end LPPDifferentiability
