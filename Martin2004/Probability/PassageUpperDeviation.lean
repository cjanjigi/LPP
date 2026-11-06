/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Shape.ExpectedRateUniform
public import LPP_Foundations.Model.LastPassage.Inclusive
public import LPP_Foundations.Model.LastPassage.Translate
public import LPP_Foundations.Probability.CoordinateLaw
public import LPP_Foundations.Probability.EnvironmentLaw
public import LPP_Foundations.Probability.PassageMeasurable
public import LPP_Foundations.Probability.Stationarity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Interval

/-!
# Upper deviations of the inclusive passage time, and a mean bound from them

This file proves an upper-tail convergence result for inclusive passage times
from an expected-rate shape, and a mean bound from vanishing upper tails.

* `tendsto_measure_inclusivePassage_gt`: for any law with both square-root
  tails finite and any expected-rate shape `g`, the probability that the
  inclusive passage time over `d N` from `u N`, divided by `N`, exceeds
  `g v + δ` tends to `0`.
* `le_of_tendsto_integral_of_tendsto_measure_gt`: a sequence bounded in
  `L²` whose upper deviations above `c` vanish in probability has limiting mean
  at most `c`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-! ### The mean bound -/

/-- Pointwise bound behind the mean estimate. Off the event `{a < x}` the value
`x` is at most `a`; on it, `x ≤ t x² / 2 + 1 / (2 t)` and `a + |a| ≥ 0`. -/
private theorem le_add_half_mul_sq_add_indicator (a t x e : ℝ) (ht : 0 < t)
    (he₁ : a < x → e = 1) (he₀ : ¬ a < x → e = 0) :
    x ≤ a + t / 2 * x ^ 2 + (1 / (2 * t) + |a|) * e := by
  have hamgm : x ≤ t / 2 * x ^ 2 + 1 / (2 * t) := by
    have h : t / 2 * x ^ 2 + 1 / (2 * t) - x = (t * x - 1) ^ 2 / (2 * t) := by
      field_simp
      ring
    have h' : 0 ≤ (t * x - 1) ^ 2 / (2 * t) := by positivity
    linarith
  have hneg : -a ≤ |a| := neg_le_abs a
  have hsq : 0 ≤ t / 2 * x ^ 2 := by positivity
  by_cases h : a < x
  · rw [he₁ h, mul_one]
    linarith
  · rw [he₀ h, mul_zero]
    linarith [not_lt.1 h]

/-- A sequence bounded in `L²` whose upper deviations above `c` vanish in probability has
limiting mean at most `c`. -/
theorem le_of_tendsto_integral_of_tendsto_measure_gt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ N, MemLp (X N) 2 P) {C L c : ℝ}
    (hC : ∀ N, ∫ ω, X N ω ^ 2 ∂P ≤ C)
    (hL : Tendsto (fun N => ∫ ω, X N ω ∂P) atTop (𝓝 L))
    (hc : ∀ δ : ℝ, 0 < δ → Tendsto (fun N => P {ω | c + δ < X N ω}) atTop (𝓝 0)) :
    L ≤ c := by
  -- For every `δ, t > 0`: `L ≤ (c + δ) + t C / 2`.
  have key : ∀ δ t : ℝ, 0 < δ → 0 < t → L ≤ (c + δ) + t / 2 * C := by
    intro δ t hδ ht
    have hprob : Tendsto (fun N => P.real {ω | c + δ < X N ω}) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hc δ hδ)
      simpa [Function.comp_def, measureReal_def] using h
    have hbound : ∀ N, ∫ ω, X N ω ∂P ≤ (c + δ) + t / 2 * C +
        (1 / (2 * t) + |c + δ|) * P.real {ω | c + δ < X N ω} := by
      intro N
      have hf : Integrable (X N) P := (hX N).integrable (by norm_num)
      have hsq : Integrable (fun ω => X N ω ^ 2) P := (hX N).integrable_sq
      have hA : NullMeasurableSet {ω | c + δ < X N ω} P :=
        nullMeasurableSet_lt aemeasurable_const (hX N).aestronglyMeasurable.aemeasurable
      have hind : Integrable
          (Set.indicator {ω | c + δ < X N ω} (fun _ => (1 : ℝ))) P :=
        (integrable_const (1 : ℝ)).indicator₀ hA
      have hint_ind : ∫ ω, Set.indicator {ω | c + δ < X N ω} (fun _ => (1 : ℝ)) ω ∂P =
          P.real {ω | c + δ < X N ω} := by
        rw [integral_indicator₀ hA, setIntegral_const]
        simp
      have hI1 : Integrable (fun ω => (c + δ) + t / 2 * X N ω ^ 2) P :=
        (integrable_const _).add (hsq.const_mul _)
      have hI2 : Integrable (fun ω => (1 / (2 * t) + |c + δ|) *
          Set.indicator {ω | c + δ < X N ω} (fun _ => (1 : ℝ)) ω) P :=
        hind.const_mul _
      have hrhs : Integrable (fun ω => (c + δ) + t / 2 * X N ω ^ 2 +
          (1 / (2 * t) + |c + δ|) *
            Set.indicator {ω | c + δ < X N ω} (fun _ => (1 : ℝ)) ω) P :=
        hI1.add hI2
      have hmono := integral_mono hf hrhs (fun ω =>
        le_add_half_mul_sq_add_indicator (c + δ) t (X N ω)
          (Set.indicator {ω | c + δ < X N ω} (fun _ => (1 : ℝ)) ω) ht
          (fun h => Set.indicator_of_mem (s := {ω | c + δ < X N ω}) h _)
          (fun h => Set.indicator_of_notMem (s := {ω | c + δ < X N ω}) h _))
      have hexp : ∫ ω, ((c + δ) + t / 2 * X N ω ^ 2 +
          (1 / (2 * t) + |c + δ|) *
            Set.indicator {ω | c + δ < X N ω} (fun _ => (1 : ℝ)) ω) ∂P =
          (c + δ) + t / 2 * ∫ ω, X N ω ^ 2 ∂P +
            (1 / (2 * t) + |c + δ|) * P.real {ω | c + δ < X N ω} := by
        rw [integral_add hI1 hI2, integral_add (integrable_const _) (hsq.const_mul _),
          integral_const_mul, integral_const_mul, hint_ind]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      have hCN := hC N
      have hmul : t / 2 * ∫ ω, X N ω ^ 2 ∂P ≤ t / 2 * C :=
        mul_le_mul_of_nonneg_left hCN (by linarith)
      linarith [hmono, hexp, hmul]
    have hlim : Tendsto (fun N => (c + δ) + t / 2 * C +
        (1 / (2 * t) + |c + δ|) * P.real {ω | c + δ < X N ω}) atTop
        (𝓝 ((c + δ) + t / 2 * C + (1 / (2 * t) + |c + δ|) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hprob)
    rw [mul_zero, add_zero] at hlim
    exact le_of_tendsto_of_tendsto' hL hlim hbound
  by_contra hlt
  have hlt' : c < L := not_le.1 hlt
  have hK : 0 < |C| + 1 := by positivity
  obtain ⟨t, htK⟩ : ∃ t : ℝ, t * (|C| + 1) = (L - c) / 2 :=
    ⟨(L - c) / 2 / (|C| + 1), div_mul_cancel₀ _ hK.ne'⟩
  have htpos : 0 < t := by
    by_contra hneg
    nlinarith [not_lt.1 hneg]
  have hδ : 0 < (L - c) / 4 := by linarith
  have hk := key ((L - c) / 4) t hδ htpos
  have h1 : t / 2 * C ≤ (L - c) / 4 := by
    calc t / 2 * C ≤ t / 2 * (|C| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [le_abs_self C]) (by linarith)
      _ = (L - c) / 4 := by linarith [htK]
  linarith

/-! ### Upper deviations of the inclusive passage time -/

/-- A sequence `x` bounded eventually by `ε s N` for every `ε > 0`, where `s`
converges, tends to zero. -/
private theorem tendsto_zero_of_eventually_le_mul (x s : ℕ → ℝ) {S : ℝ}
    (hs : Tendsto s atTop (𝓝 S))
    (hx : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, |x N| ≤ ε * s N) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hK : 0 < |S| + 1 := by positivity
  have hε : 0 < η / (2 * (|S| + 1)) := by positivity
  have hs' : ∀ᶠ N in atTop, s N < |S| + 1 :=
    hs.eventually (gt_mem_nhds (by linarith [le_abs_self S]))
  filter_upwards [hx _ hε, hs'] with N h1 h2
  rw [Real.dist_eq, sub_zero]
  have h3 : η / (2 * (|S| + 1)) * s N ≤ η / (2 * (|S| + 1)) * (|S| + 1) :=
    mul_le_mul_of_nonneg_left h2.le hε.le
  have h4 : η / (2 * (|S| + 1)) * (|S| + 1) = η / 2 := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  linarith

/-- The deterministic core of the upper-deviation argument. If, for one environment,
`|T(0, z) - g z|` is at most `ε (z₁ + z₂)` for all large `z` and every `ε > 0`, and `g` is
continuous and homogeneous, then `T(0, d N) / N` tends to `g v` whenever
`d N / N → v` and `v` is not the origin. -/
private theorem tendsto_lastPassage_div_of_uniform {g : Quadrant → ℝ}
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (d : ℕ → ℕ × ℕ) (v : Quadrant) (hv : 0 < (v.1 : ℝ) + v.2)
    (hd : Tendsto (fun N : ℕ => (((d N).1 : ℝ) / N, ((d N).2 : ℝ) / N)) atTop
      (𝓝 ((v.1 : ℝ), (v.2 : ℝ))))
    (ω : Environment)
    (hω : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    Tendsto (fun N : ℕ => lastPassage ω 0 (d N) / N) atTop (𝓝 (g v)) := by
  show Tendsto (fun N : ℕ => lastPassage ω (0, 0) (d N) / N) atTop (𝓝 (g v))
  have h1 : Tendsto (fun N : ℕ => ((d N).1 : ℝ) / N) atTop (𝓝 (v.1 : ℝ)) :=
    ((Prod.tendsto_iff _ _).1 hd).1
  have h2 : Tendsto (fun N : ℕ => ((d N).2 : ℝ) / N) atTop (𝓝 (v.2 : ℝ)) :=
    ((Prod.tendsto_iff _ _).1 hd).2
  -- the rescaled displacement, as a point of the quadrant
  have hp : Tendsto (fun N : ℕ =>
      (((N : ℝ≥0)⁻¹ * ((d N).1 : ℝ≥0), (N : ℝ≥0)⁻¹ * ((d N).2 : ℝ≥0)) : Quadrant))
      atTop (𝓝 v) := by
    rw [Prod.tendsto_iff]
    constructor
    · refine NNReal.tendsto_coe.1 ?_
      simpa [div_eq_inv_mul] using h1
    · refine NNReal.tendsto_coe.1 ?_
      simpa [div_eq_inv_mul] using h2
  have hgp : Tendsto (fun N : ℕ =>
      g ((N : ℝ≥0)⁻¹ * ((d N).1 : ℝ≥0), (N : ℝ≥0)⁻¹ * ((d N).2 : ℝ≥0))) atTop
      (𝓝 (g v)) := (hcont.tendsto v).comp hp
  -- homogeneity: `g (d N) / N = g (d N / N)`
  have hgd : Tendsto (fun N : ℕ => g (((d N).1 : ℝ≥0), ((d N).2 : ℝ≥0)) / N) atTop
      (𝓝 (g v)) := by
    refine hgp.congr' ?_
    filter_upwards with N
    refine (hhom (N : ℝ≥0)⁻¹ (((d N).1 : ℝ≥0), ((d N).2 : ℝ≥0))).trans ?_
    simp [div_eq_inv_mul]
  have hS : 0 < (v.1 : ℝ) + v.2 := hv
  have hs : Tendsto (fun N : ℕ => (((d N).1 : ℝ) + ((d N).2 : ℝ)) / N) atTop
      (𝓝 ((v.1 : ℝ) + v.2)) := by
    simpa only [add_div] using h1.add h2
  have hx : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      |(lastPassage ω (0, 0) (d N) - g (((d N).1 : ℝ≥0), ((d N).2 : ℝ≥0))) / N| ≤
        ε * ((((d N).1 : ℝ) + ((d N).2 : ℝ)) / N) := by
    intro ε hε
    obtain ⟨M, hM⟩ := hω ε hε
    have hev1 : ∀ᶠ N : ℕ in atTop,
        ((v.1 : ℝ) + v.2) / 2 < (((d N).1 : ℝ) + ((d N).2 : ℝ)) / N :=
      hs.eventually (lt_mem_nhds (by linarith))
    have hev2 : ∀ᶠ N : ℕ in atTop, 2 * (M : ℝ) / ((v.1 : ℝ) + v.2) < (N : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
    have hev3 : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
    filter_upwards [hev1, hev2, hev3] with N h1' h2' h3'
    have hNpos : (0 : ℝ) < N := by exact_mod_cast h3'
    have e1 : ((v.1 : ℝ) + v.2) / 2 * N < ((d N).1 : ℝ) + ((d N).2 : ℝ) :=
      (lt_div_iff₀ hNpos).1 h1'
    have e2 : 2 * (M : ℝ) < N * ((v.1 : ℝ) + v.2) := (div_lt_iff₀ hS).1 h2'
    have hMreal : (M : ℝ) ≤ ((d N).1 : ℝ) + ((d N).2 : ℝ) := by linarith
    have hMle : M ≤ (d N).1 + (d N).2 := by exact_mod_cast hMreal
    have hz := hM (d N) hMle
    have hz' : |lastPassage ω (0, 0) (d N) - g (((d N).1 : ℝ≥0), ((d N).2 : ℝ≥0))| ≤
        ε * (((d N).1 : ℝ) + ((d N).2 : ℝ)) := by
      have := hz
      push_cast at this
      exact this
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    have hsN : (((d N).1 : ℝ) + ((d N).2 : ℝ)) / N * N =
        ((d N).1 : ℝ) + ((d N).2 : ℝ) := div_mul_cancel₀ _ hNpos.ne'
    calc |lastPassage ω (0, 0) (d N) - g (((d N).1 : ℝ≥0), ((d N).2 : ℝ≥0))|
        ≤ ε * (((d N).1 : ℝ) + ((d N).2 : ℝ)) := hz'
      _ = ε * ((((d N).1 : ℝ) + ((d N).2 : ℝ)) / N) * N := by rw [mul_assoc, hsN]
  have hx0 := tendsto_zero_of_eventually_le_mul
    (fun N : ℕ => (lastPassage ω (0, 0) (d N) - g (((d N).1 : ℝ≥0), ((d N).2 : ℝ≥0))) / N)
    (fun N : ℕ => (((d N).1 : ℝ) + ((d N).2 : ℝ)) / N) hs hx
  have hsum := hx0.add hgd
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with N
  rw [← add_div, sub_add_cancel]

/-- The inclusive passage time is a measurable function of the environment. -/
private theorem measurable_inclusivePassage (u : Lattice) (d : ℕ × ℕ) :
    Measurable (fun ω : Environment => inclusivePassage ω u d) := by
  unfold inclusivePassage
  exact (measurable_lastPassage u d).add (measurable_environment_eval _)

/-- Both tails of a probability law vanish: `μ (Ioi x) → 0` as `x → ∞`. -/
private theorem tendsto_measure_Ioi_atTop_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Tendsto (fun x : ℝ => μ (Ioi x)) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := μ univ))
    (tendsto_measure_Iic_atTop μ) (Or.inl (measure_ne_top μ _))
  rw [tsub_self] at h
  refine h.congr (fun x => ?_)
  rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top μ _)]

/-- Upper deviations in probability for the inclusive passage time with
moving start and endpoint, for any law with both square-root tails. -/
theorem tendsto_measure_inclusivePassage_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    {g : Quadrant → ℝ} (hg : IsExpectedRateShape μ g)
    (u : ℕ → Lattice) (d : ℕ → ℕ × ℕ) (v : Quadrant) (hv : 0 < (v.1 : ℝ) + v.2)
    (hd : Tendsto (fun N : ℕ => (((d N).1 : ℝ) / N, ((d N).2 : ℝ) / N)) atTop
      (𝓝 ((v.1 : ℝ), (v.2 : ℝ))))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      environmentLaw μ {ω | g v + δ < inclusivePassage ω (u N) (d N) / N}) atTop (𝓝 0) := by
  obtain ⟨hcont, hhom, hae⟩ := ae_uniform_of_isExpectedRateShape μ hneg hpos hg
  -- Translation moves the start `u N` to the origin without changing the law.
  have hreduce : ∀ N : ℕ,
      environmentLaw μ {ω | g v + δ < inclusivePassage ω (u N) (d N) / N} =
        environmentLaw μ {ω | g v + δ < inclusivePassage ω 0 (d N) / N} := by
    intro N
    have hτ : Measurable (fun ω : Environment => fun z => ω (u N + z)) :=
      Measurable.of_eval fun z => measurable_pi_apply (u N + z)
    have hmeas : MeasurableSet {ω : Environment | g v + δ < inclusivePassage ω 0 (d N) / N} :=
      measurableSet_lt measurable_const ((measurable_inclusivePassage 0 (d N)).div_const _)
    have hpre : (fun ω : Environment => fun z => ω (u N + z)) ⁻¹'
          {ω : Environment | g v + δ < inclusivePassage ω 0 (d N) / N} =
        {ω | g v + δ < inclusivePassage ω (u N) (d N) / N} := by
      ext ω
      have h : inclusivePassage (fun z => ω (u N + z)) 0 (d N) =
          inclusivePassage ω (u N) (d N) := by
        simp only [inclusivePassage, lastPassage_translate, add_zero, zero_add]
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, h]
    rw [← hpre, ← Measure.map_apply hτ hmeas, environmentLaw_map_translation]
  have hfun : (fun N : ℕ =>
      environmentLaw μ {ω | g v + δ < inclusivePassage ω (u N) (d N) / N}) =
      fun N : ℕ => environmentLaw μ {ω | g v + δ < inclusivePassage ω 0 (d N) / N} :=
    funext hreduce
  rw [hfun]
  -- `T(0, d N) / N → g v` almost surely, hence in probability.
  have hlim : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun N : ℕ => lastPassage ω 0 (d N) / N) atTop (𝓝 (g v)) := by
    filter_upwards [hae] with ω hω
    exact tendsto_lastPassage_div_of_uniform hcont hhom d v hv hd ω hω
  have hmeasure : TendstoInMeasure (environmentLaw μ)
      (fun (N : ℕ) ω => lastPassage ω 0 (d N) / (N : ℝ)) atTop (fun _ => g v) :=
    tendstoInMeasure_of_tendsto_ae
      (fun N => ((measurable_lastPassage 0 (d N)).div_const _).aestronglyMeasurable) hlim
  have hA : Tendsto (fun N : ℕ => environmentLaw μ
      {ω | δ / 2 ≤ dist (lastPassage ω 0 (d N) / (N : ℝ)) (g v)}) atTop (𝓝 0) :=
    tendstoInMeasure_iff_dist.1 hmeasure _ (half_pos hδ)
  -- The weight at the endpoint, divided by `N`, tends to zero in probability.
  obtain ⟨z, hz⟩ : ∃ z : ℕ → Lattice, ∀ (N : ℕ) (ω : Environment),
      inclusivePassage ω 0 (d N) = lastPassage ω 0 (d N) + ω (z N) :=
    ⟨fun N => 0 + (((d N).1 : ℤ), ((d N).2 : ℤ)), fun N ω => rfl⟩
  have hwtail : ∀ N : ℕ, 0 < N →
      environmentLaw μ {ω : Environment | δ / 2 < ω (z N) / (N : ℝ)} =
        μ (Ioi (δ / 2 * N)) := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hW : MeasurableSet {t : ℝ | δ / 2 < t / (N : ℝ)} :=
      measurableSet_lt measurable_const (measurable_id.div_const _)
    have hset : {t : ℝ | δ / 2 < t / (N : ℝ)} = Ioi (δ / 2 * N) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
      exact lt_div_iff₀ hNr
    calc environmentLaw μ {ω : Environment | δ / 2 < ω (z N) / (N : ℝ)}
        = ((environmentLaw μ).map (fun ω : Environment => ω (z N)))
            {t : ℝ | δ / 2 < t / (N : ℝ)} :=
          (Measure.map_apply (measurable_environment_eval _) hW).symm
      _ = μ (Ioi (δ / 2 * N)) := by rw [environmentLaw_map_eval, hset]
  have hB : Tendsto (fun N : ℕ => environmentLaw μ
      {ω : Environment | δ / 2 < ω (z N) / (N : ℝ)}) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => μ (Ioi (δ / 2 * N))) atTop (𝓝 0) :=
      (tendsto_measure_Ioi_atTop_zero μ).comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (half_pos hδ))
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (hwtail N hN).symm
  -- Union bound and squeeze.
  have hsum : Tendsto (fun N : ℕ =>
      environmentLaw μ {ω | δ / 2 ≤ dist (lastPassage ω 0 (d N) / (N : ℝ)) (g v)} +
        environmentLaw μ {ω : Environment | δ / 2 < ω (z N) / (N : ℝ)}) atTop (𝓝 0) := by
    have := hA.add hB
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun N => zero_le) (fun N => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  have hsplit : inclusivePassage ω 0 (d N) / N =
      lastPassage ω 0 (d N) / N + ω (z N) / N := by
    rw [hz N ω, add_div]
  by_cases hw : δ / 2 < ω (z N) / (N : ℝ)
  · exact Or.inr hw
  · left
    show δ / 2 ≤ dist (lastPassage ω 0 (d N) / (N : ℝ)) (g v)
    rw [Real.dist_eq]
    have hle : δ / 2 ≤ lastPassage ω 0 (d N) / N - g v := by
      rw [hsplit] at hω
      linarith [not_lt.1 hw]
    exact hle.trans (le_abs_self _)

end LPPDifferentiability
