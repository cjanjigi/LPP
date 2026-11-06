/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Inclusive
public import Martin2004.Model.LastPassage.Stationary
public import LPP_Foundations.Probability.CoordinateLaw
public import Martin2004.Probability.ExponentialLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Weak law for the boundary sums of the stationary model

In the stationary model the weights are independent exponential variables divided by the
rate of their site. The inclusive passage time along the bottom row, or along the left
column, is a sum of such weights. This file shows that the sum, divided by `N`, exceeds its
expected size by a fixed positive amount `δ` with probability tending to zero.

The proof is a weak law of large numbers by Chebyshev's inequality: the sum of the
`n + 1` weights has mean `1 + n / q` and variance `1 + n / q ^ 2`, where `q` is the rate on
the axis (`1 - ρ` for the row, `ρ` for the column) and the first weight, at the origin, has
rate `1`.

Martin (2004), Theorem 2.4, states the shape asymptotics near the boundary. This file proves moment
identities for the stationary boundary passage-time law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace LPPDifferentiability

/-! ## Chebyshev step -/

/-- Chebyshev step. If `S N` is square integrable with mean `m N` and variance at most
`V N`, if `m N / N` tends to `b`, and if `V N / N ^ 2` tends to zero, then the probability
that `S N / N` exceeds `b + δ` tends to zero. For large `N` the mean is below
`(b + δ / 2) N`, so the event forces a deviation of at least `δ N / 2` from the mean, and
Chebyshev bounds its probability by `4 V N / (δ ^ 2 N ^ 2)`. -/
private theorem tendsto_measure_gt_of_chebyshev {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ) (m V : ℕ → ℝ)
    (hS : ∀ N, MemLp (S N) 2 P) (hm : ∀ N, ∫ ω, S N ω ∂P = m N)
    (hV : ∀ N, variance (S N) P ≤ V N) {b δ : ℝ} (hδ : 0 < δ)
    (hmb : Tendsto (fun N : ℕ => m N / N) atTop (𝓝 b))
    (hV0 : Tendsto (fun N : ℕ => V N / (N : ℝ) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => P {ω | b + δ < S N ω / N}) atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, m N / N < b + δ / 2 :=
    hmb.eventually (gt_mem_nhds (by linarith))
  have hpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact_mod_cast hN
  have hup : Tendsto (fun N : ℕ => ENNReal.ofReal (4 / δ ^ 2 * (V N / (N : ℝ) ^ 2)))
      atTop (𝓝 0) := by
    have h := hV0.const_mul (4 / δ ^ 2)
    rw [mul_zero] at h
    simpa using ENNReal.tendsto_ofReal h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun N => zero_le) ?_
  filter_upwards [hev, hpos] with N hN hNpos
  have hsub : {ω | b + δ < S N ω / N} ⊆
      {ω | δ * N / 2 ≤ |S N ω - ∫ ω, S N ω ∂P|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hm N]
    have h1 : (b + δ) * N < S N ω := (lt_div_iff₀ hNpos).1 hω
    have h2 : m N < (b + δ / 2) * N := (div_lt_iff₀ hNpos).1 hN
    calc δ * N / 2 ≤ S N ω - m N := by nlinarith
      _ ≤ |S N ω - m N| := le_abs_self _
  have hcheb := meas_ge_le_variance_div_sq (hS N) (c := δ * N / 2) (by positivity)
  calc P {ω | b + δ < S N ω / N}
      ≤ P {ω | δ * N / 2 ≤ |S N ω - ∫ ω, S N ω ∂P|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance (S N) P / (δ * N / 2) ^ 2) := hcheb
    _ ≤ ENNReal.ofReal (4 / δ ^ 2 * (V N / (N : ℝ) ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have hle : variance (S N) P / (δ * N / 2) ^ 2 ≤ V N / (δ * N / 2) ^ 2 :=
        div_le_div_of_nonneg_right (hV N) (by positivity)
      refine hle.trans (le_of_eq ?_)
      field_simp
      norm_num

/-! ## One coordinate of the stationary environment -/

/-- The weight at a site of the `Exp(1)` environment is square integrable. -/
private theorem memLp_two_eval (w : Lattice) :
    MemLp (fun ω : Environment => ω w) 2 (environmentLaw (expMeasure 1)) := by
  have hid : MemLp (fun t : ℝ => t) 2 (expMeasure 1) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (integrable_and_integral_sq_expMeasure one_pos).1
  have hmp : MeasurePreserving (fun ω : Environment => ω w)
      (environmentLaw (expMeasure 1)) (expMeasure 1) :=
    ⟨measurable_environment_eval w, environmentLaw_map_eval _ w⟩
  exact hid.comp_measurePreserving hmp

/-- The weight at a site of the `Exp(1)` environment has mean `1`. -/
private theorem integral_eval (w : Lattice) :
    ∫ ω : Environment, ω w ∂environmentLaw (expMeasure 1) = 1 := by
  have h := integral_map (μ := environmentLaw (expMeasure 1))
    (measurable_environment_eval w).aemeasurable
    (f := fun t : ℝ => t) measurable_id.aestronglyMeasurable
  rw [environmentLaw_map_eval] at h
  rw [← h]
  simpa using (integrable_and_integral_id_expMeasure one_pos).2

/-- The weight at a site of the `Exp(1)` environment has variance `1`: second moment `2`
minus squared mean `1`. -/
private theorem variance_eval (w : Lattice) :
    variance (fun ω : Environment => ω w) (environmentLaw (expMeasure 1)) = 1 := by
  have hid : MemLp (fun t : ℝ => t) 2 (expMeasure 1) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (integrable_and_integral_sq_expMeasure one_pos).1
  have hmp : MeasurePreserving (fun ω : Environment => ω w)
      (environmentLaw (expMeasure 1)) (expMeasure 1) :=
    ⟨measurable_environment_eval w, environmentLaw_map_eval _ w⟩
  have h : variance (fun ω : Environment => ω w) (environmentLaw (expMeasure 1)) =
      variance (fun t : ℝ => t) (expMeasure 1) :=
    hmp.variance_fun_comp measurable_id.aemeasurable
  rw [h, variance_eq_sub hid]
  show ∫ t : ℝ, t ^ 2 ∂expMeasure 1 - (∫ t : ℝ, t ∂expMeasure 1) ^ 2 = 1
  rw [(integrable_and_integral_id_expMeasure one_pos).2,
    (integrable_and_integral_sq_expMeasure one_pos).2]
  norm_num

/-- The stationary weight at a site is the inverse of the rate times the original weight. -/
private theorem stationary_coord_eq (ρ : ℝ) (w : Lattice) :
    (fun ω : Environment => stationaryEnvironment ρ ω w) =
      fun ω => (stationaryRate ρ w)⁻¹ * ω w := by
  funext ω
  exact div_eq_inv_mul (ω w) (stationaryRate ρ w)

/-- A stationary weight is square integrable. -/
private theorem memLp_coord (ρ : ℝ) (w : Lattice) :
    MemLp (fun ω : Environment => stationaryEnvironment ρ ω w) 2
      (environmentLaw (expMeasure 1)) := by
  rw [stationary_coord_eq]
  exact (memLp_two_eval w).const_mul _

/-- A stationary weight has mean the inverse of its rate. -/
private theorem integral_coord (ρ : ℝ) (w : Lattice) :
    ∫ ω : Environment, stationaryEnvironment ρ ω w ∂environmentLaw (expMeasure 1) =
      (stationaryRate ρ w)⁻¹ := by
  have h : ∫ ω : Environment, stationaryEnvironment ρ ω w ∂environmentLaw (expMeasure 1) =
      ∫ ω : Environment, (stationaryRate ρ w)⁻¹ * ω w ∂environmentLaw (expMeasure 1) :=
    integral_congr_ae
      (Filter.Eventually.of_forall fun ω => div_eq_inv_mul (ω w) (stationaryRate ρ w))
  rw [h, integral_const_mul, integral_eval, mul_one]

/-- A stationary weight has variance the squared inverse of its rate. -/
private theorem variance_coord (ρ : ℝ) (w : Lattice) :
    variance (fun ω : Environment => stationaryEnvironment ρ ω w)
      (environmentLaw (expMeasure 1)) = ((stationaryRate ρ w)⁻¹) ^ 2 := by
  rw [stationary_coord_eq, variance_const_mul, variance_eval, mul_one]

/-! ## Sums over distinct sites -/

/-- A sum of the stationary weights at `n + 1` distinct sites, the first of rate `1` and the
other `n` of rate `q`, is square integrable with mean `1 + n / q` and variance
`1 + n / q ^ 2`. The variances add because the coordinates are independent. -/
private theorem sites_sum_law (ρ : ℝ) {q : ℝ} {n : ℕ} (z : Fin (n + 1) → Lattice)
    (hz : Function.Injective z) (h0 : stationaryRate ρ (z 0) = 1)
    (hs : ∀ i : Fin n, stationaryRate ρ (z i.succ) = q) :
    MemLp (∑ i, fun ω : Environment => stationaryEnvironment ρ ω (z i)) 2
        (environmentLaw (expMeasure 1)) ∧
      ∫ ω : Environment, ∑ i, stationaryEnvironment ρ ω (z i)
          ∂environmentLaw (expMeasure 1) = 1 + n * q⁻¹ ∧
      variance (∑ i, fun ω : Environment => stationaryEnvironment ρ ω (z i))
          (environmentLaw (expMeasure 1)) = 1 + n * (q⁻¹) ^ 2 := by
  have hmem : ∀ i, MemLp (fun ω : Environment => stationaryEnvironment ρ ω (z i)) 2
      (environmentLaw (expMeasure 1)) := fun i => memLp_coord ρ (z i)
  have hind : iIndepFun (fun i : Fin (n + 1) => fun ω : Environment =>
      stationaryEnvironment ρ ω (z i)) (environmentLaw (expMeasure 1)) :=
    ((iIndepFun_environment_eval (expMeasure 1)).comp
      (fun w (t : ℝ) => t / stationaryRate ρ w)
      (fun w => measurable_id.div_const _)).precomp hz
  refine ⟨memLp_finsetSum' _ fun i _ => hmem i, ?_, ?_⟩
  · rw [integral_finsetSum _ fun i _ => MemLp.integrable one_le_two (hmem i)]
    simp only [integral_coord]
    rw [Fin.sum_univ_succ]
    simp [h0, hs]
  · rw [IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp only [variance_coord]
    rw [Fin.sum_univ_succ]
    simp [h0, hs]

/-- Weak law for a sum over a family of sites. For each `n`, let `z n` list `n + 1` distinct
sites whose first rate is `1` and whose other rates are `q > 0`. If `k N / N` tends to `c`,
the sum over `z (k N)` of the stationary weights, divided by `N`, exceeds `c / q + δ` with
probability tending to zero. -/
private theorem tendsto_measure_sites_gt (ρ : ℝ) {q : ℝ} (hq : 0 < q) (k : ℕ → ℕ) {c : ℝ}
    (hk : Tendsto (fun N : ℕ => (k N : ℝ) / N) atTop (𝓝 c)) {δ : ℝ} (hδ : 0 < δ)
    (z : (n : ℕ) → Fin (n + 1) → Lattice) (hz : ∀ n, Function.Injective (z n))
    (h0 : ∀ n, stationaryRate ρ (z n 0) = 1)
    (hs : ∀ n (i : Fin n), stationaryRate ρ (z n i.succ) = q) :
    Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
      {ω | c / q + δ < (∑ i, stationaryEnvironment ρ ω (z (k N) i)) / N}) atTop (𝓝 0) := by
  have hlaw := fun N => sites_sum_law ρ (z (k N)) (hz (k N)) (h0 (k N)) (hs (k N))
  have hmean : Tendsto (fun N : ℕ => (1 + (k N : ℝ) * q⁻¹) / N) atTop (𝓝 (c / q)) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add (hk.mul_const q⁻¹)
    have hfun : (fun N : ℕ => (1 + (k N : ℝ) * q⁻¹) / N) =
        fun N : ℕ => 1 / (N : ℝ) + (k N : ℝ) / N * q⁻¹ := by
      funext N
      rw [add_div, mul_div_right_comm]
    rw [hfun]
    convert h using 2
    rw [zero_add, div_eq_mul_inv]
  have hvar : Tendsto (fun N : ℕ => (1 + (k N : ℝ) * (q⁻¹) ^ 2) / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have h0' := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h := (h0'.mul h0').add ((hk.mul_const ((q⁻¹) ^ 2)).mul h0')
    have hlim : (0 : ℝ) * 0 + c * (q⁻¹) ^ 2 * 0 = 0 := by ring
    rw [hlim] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hcheb := tendsto_measure_gt_of_chebyshev (environmentLaw (expMeasure 1))
    (fun N => ∑ i, fun ω : Environment => stationaryEnvironment ρ ω (z (k N) i))
    (fun N => 1 + (k N : ℝ) * q⁻¹) (fun N => 1 + (k N : ℝ) * (q⁻¹) ^ 2)
    (fun N => (hlaw N).1)
    (fun N => by simpa only [Finset.sum_apply] using (hlaw N).2.1)
    (fun N => ((hlaw N).2.2).le) hδ hmean hvar
  simpa only [Finset.sum_apply] using hcheb

/-! ## The boundary sums -/

/-- **Weak law for the boundary sums of the stationary model.** In the stationary model
with `Exp(1)` input weights and `0 < ρ < 1`, let `k N / N` tend to `c`. Then for every
`δ > 0` the probability that the bottom-row passage time to `(k N, 0)`, divided by `N`,
exceeds `c / (1 - ρ) + δ` tends to zero, and the probability that the left-column passage
time to `(0, k N)`, divided by `N`, exceeds `c / ρ + δ` tends to zero. The passage times are
sums of independent weights with mean `1 + k N / (1 - ρ)` and `1 + k N / ρ`, and the result is
Chebyshev's inequality. -/
theorem tendsto_measure_stationaryBoundary_gt {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (k : ℕ → ℕ) {c : ℝ} (hk : Tendsto (fun N : ℕ => (k N : ℝ) / N) atTop (𝓝 c))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
        {ω | c / (1 - ρ) + δ <
          inclusivePassage (stationaryEnvironment ρ ω) 0 (k N, 0) / N}) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
        {ω | c / ρ + δ <
          inclusivePassage (stationaryEnvironment ρ ω) 0 (0, k N) / N}) atTop (𝓝 0) := by
  have hH : ∀ (ω : Environment) (n : ℕ),
      inclusivePassage (stationaryEnvironment ρ ω) 0 (n, 0) =
        ∑ i : Fin (n + 1), stationaryEnvironment ρ ω (((i : ℕ) : ℤ), 0) := by
    intro ω n
    rw [inclusivePassage_horizontal]
    simp
  have hV : ∀ (ω : Environment) (n : ℕ),
      inclusivePassage (stationaryEnvironment ρ ω) 0 (0, n) =
        ∑ i : Fin (n + 1), stationaryEnvironment ρ ω (0, ((i : ℕ) : ℤ)) := by
    intro ω n
    rw [inclusivePassage_vertical]
    simp
  refine ⟨?_, ?_⟩
  · simp only [hH]
    refine tendsto_measure_sites_gt ρ (sub_pos.2 hρ1) k hk hδ
      (fun n i => (((i : ℕ) : ℤ), 0)) ?_ ?_ ?_
    · intro n i j hij
      apply Fin.ext
      have h : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := congrArg Prod.fst hij
      exact_mod_cast h
    · intro n
      simp [stationaryRate]
    · intro n i
      simp [stationaryRate]
  · simp only [hV]
    refine tendsto_measure_sites_gt ρ hρ0 k hk hδ
      (fun n i => (0, ((i : ℕ) : ℤ))) ?_ ?_ ?_
    · intro n i j hij
      apply Fin.ext
      have h : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := congrArg Prod.snd hij
      exact_mod_cast h
    · intro n
      simp [stationaryRate]
    · intro n i
      simp [stationaryRate]

end LPPDifferentiability
