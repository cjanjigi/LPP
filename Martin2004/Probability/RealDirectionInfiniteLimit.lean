/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.RealDirectionFiniteLimit
public import Martin2004.Probability.ERealFloorRate
public import LPP_Foundations.Probability.EnvironmentMap
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.PassageMeasurable
public import Martin2004.Analysis.RationalPassageNormalization
public import LPP_Foundations.Model.LastPassage.Locality
import Mathlib.Tactic

/-!
# Real direction, infinite case: the passage time grows faster than linearly

Martin (2004), Proposition 2.1 (i) says that `T(⌊n x⌋)/n` tends to `g(x)` almost surely, where the
value `g(x) = +∞` is allowed. Martin gives no proof for non-lattice directions.
`RealDirectionFiniteLimit` treats a finite expected rate; this file treats the rate `+∞` by cutting
every weight from above.

* For a natural number `M`, the clipped environment `ω^M = min(ω, M)` has the law
  `environmentLaw (μ.map (min · M))`, and this clipped law still has a finite mean.
* The weights of `ω^M` are at most `M`, so the expected rate `g_M` of the clipped law is finite, and
  the finite case gives `T(ω^M; ⌊n x⌋)/n → g_M` almost surely.
* `ω^M ≤ ω` gives `T(ω^M) ≤ T(ω)`, so the liminf of `T(ω; ⌊n x⌋)/n` is at least `g_M` for every `M`.
* The per-`n` lower bound for the rate and dominated convergence in `M` give `g_M` arbitrarily
  large, hence `T(⌊n x⌋)/n → +∞` almost surely.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- Clip every site weight from above at the natural number `M`, giving the environment `ω^M`. -/
private abbrev clipEnv (M : ℕ) (ω : Environment) : Environment := fun z => min (ω z) (M : ℝ)

private theorem measurable_clip (M : ℕ) : Measurable (fun t : ℝ => min t (M : ℝ)) :=
  measurable_id.min measurable_const

private theorem measurable_clipEnv (M : ℕ) : Measurable (clipEnv M) :=
  measurable_coordinatewise_environment_map _ (measurable_clip M)

/-- Clipping from above at a nonnegative level does not increase the absolute value. -/
private theorem abs_clip_le (M : ℕ) (t : ℝ) : |min t (M : ℝ)| ≤ |t| := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine abs_le.mpr ⟨le_min (neg_abs_le t) ?_, (min_le_left _ _).trans (le_abs_self t)⟩
  linarith [abs_nonneg t]

/-- The clipped one-site law has a finite mean. -/
private theorem clipLaw_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (M : ℕ) :
    Integrable (fun t : ℝ => t) (μ.map (fun t : ℝ => min t (M : ℝ))) := by
  refine (integrable_map_measure (g := fun t : ℝ => t) measurable_id.aestronglyMeasurable
    (measurable_clip M).aemeasurable).mpr ?_
  exact hμ.norm.mono' (measurable_clip M).aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa using abs_clip_le M t)

/-- The mean of the clipped law is the mean of the clipped weight. -/
private theorem integral_clipLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℕ) :
    ∫ t : ℝ, t ∂(μ.map (fun t : ℝ => min t (M : ℝ))) = ∫ t : ℝ, min t (M : ℝ) ∂μ :=
  integral_map (measurable_clip M).aemeasurable measurable_id.aestronglyMeasurable

/-- The mean of a passage time under the clipped law is the mean of the passage time of the clipped
environment under the original law (via `environmentLaw_map_coordinatewise`). -/
private theorem integral_lastPassage_clip (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℕ)
    (b : ℕ × ℕ) :
    ∫ ω : Environment, lastPassage ω 0 b ∂environmentLaw (μ.map (fun t : ℝ => min t (M : ℝ))) =
      ∫ ω : Environment, lastPassage (clipEnv M ω) 0 b ∂environmentLaw μ := by
  rw [← environmentLaw_map_coordinatewise μ _ (measurable_clip M)]
  exact integral_map (measurable_clipEnv M).aemeasurable
    (measurable_lastPassage 0 b).aestronglyMeasurable

/-- Passage times of the clipped environment are integrable under the original law. -/
private theorem integrable_lastPassage_clip (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (M : ℕ) (b : ℕ × ℕ) :
    Integrable (fun ω : Environment => lastPassage (clipEnv M ω) 0 b) (environmentLaw μ) := by
  have h := integrable_lastPassage (μ.map (fun t : ℝ => min t (M : ℝ))) (clipLaw_integrable μ hμ M)
    0 b
  rw [← environmentLaw_map_coordinatewise μ _ (measurable_clip M)] at h
  exact (integrable_map_measure (measurable_lastPassage 0 b).aestronglyMeasurable
    (measurable_clipEnv M).aemeasurable).mp h

/-- The expected rate of the clipped law is at most `M (x₁ + x₂)`, so it is finite. Every weight of
the clipped environment is at most `M` (`lastPassage_le_const`). -/
private theorem rate_clip_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (M : ℕ) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (μ.map (fun t : ℝ => min t (M : ℝ)))) / (n : ℝ)) : ℝ) : EReal))
      atTop (𝓝 g)) :
    g ≤ (((M : ℝ) * ((x.1 : ℝ) + (x.2 : ℝ)) : ℝ) : EReal) := by
  refine le_of_tendsto hg (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  rw [EReal.coe_le_coe_iff, integral_lastPassage_clip]
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmean : ∫ ω : Environment, lastPassage (clipEnv M ω) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ ≤
      ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (M : ℝ) := by
    have h := integral_mono (integrable_lastPassage_clip μ hμ M _)
      (integrable_const (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (M : ℝ)))
      (fun ω => lastPassage_le_const (clipEnv M ω) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) (M : ℝ) fun z => min_le_right _ _)
    simpa using h
  have hlen : ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) ≤
      (n : ℝ) * ((x.1 : ℝ) + (x.2 : ℝ)) := by
    have h1 := Nat.floor_le (mul_nonneg hn0.le (NNReal.coe_nonneg x.1))
    have h2 := Nat.floor_le (mul_nonneg hn0.le (NNReal.coe_nonneg x.2))
    push_cast
    linarith
  rw [div_le_iff₀ hn0]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith [mul_le_mul_of_nonneg_right hlen hM]

/-- Dominated convergence in the clipping level: the mean passage time of the clipped environment
tends to the mean passage time. Clipping increases with `M`, so `T(ω^0) ≤ T(ω^M) ≤ T(ω)`. -/
private theorem tendsto_integral_lastPassage_clip (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (b : ℕ × ℕ) :
    Tendsto (fun M : ℕ => ∫ ω : Environment, lastPassage (clipEnv M ω) 0 b ∂environmentLaw μ)
      atTop (𝓝 (∫ ω : Environment, lastPassage ω 0 b ∂environmentLaw μ)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun ω => |lastPassage (clipEnv 0 ω) 0 b| + |lastPassage ω 0 b|)
    (fun M => ((measurable_lastPassage 0 b).comp (measurable_clipEnv M)).aestronglyMeasurable)
    ((integrable_lastPassage_clip μ hμ 0 b).abs.add (integrable_lastPassage μ hμ 0 b).abs)
    (fun M => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · have h0 : lastPassage (clipEnv 0 ω) 0 b ≤ lastPassage (clipEnv M ω) 0 b :=
      lastPassage_mono _ _ _ _ fun z => min_le_min le_rfl (Nat.cast_le.mpr (Nat.zero_le M))
    have h1 : lastPassage (clipEnv M ω) 0 b ≤ lastPassage ω 0 b :=
      lastPassage_mono _ _ _ _ fun z => min_le_left _ _
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le (lastPassage (clipEnv 0 ω) 0 b), abs_nonneg (lastPassage ω 0 b)]
    · linarith [le_abs_self (lastPassage ω 0 b), abs_nonneg (lastPassage (clipEnv 0 ω) 0 b)]
  · -- locality: once `M` exceeds the weights on the finite box, clipping changes nothing
    obtain ⟨C, hC⟩ := ((Set.finite_Icc (0 : Lattice) (0 + ((b.1 : ℤ), (b.2 : ℤ)))).image ω).bddAbove
    obtain ⟨M0, hM0⟩ := exists_nat_ge C
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨M0, fun M hM => ?_⟩)
    refine lastPassage_eq_of_eqOn fun z hz => ?_
    exact (min_eq_left ((hC ⟨z, hz, rfl⟩).trans (hM0.trans (Nat.cast_le.mpr hM)))).symm

/-- Dominated convergence for the one-site mean: `∫ min(t, M) dμ → ∫ t dμ`. -/
private theorem tendsto_integral_clip (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) :
    Tendsto (fun M : ℕ => ∫ t : ℝ, min t (M : ℝ) ∂μ) atTop (𝓝 (∫ t : ℝ, t ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun t => |t|)
    (fun M => (measurable_clip M).aestronglyMeasurable) hμ.abs
    (fun M => Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
  · rw [Real.norm_eq_abs]
    exact abs_clip_le M t
  · obtain ⟨M0, hM0⟩ := exists_nat_ge t
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨M0, fun M hM => ?_⟩)
    exact (min_eq_left (hM0.trans (Nat.cast_le.mpr hM))).symm

/-- If the expected rate of `μ` is `+∞`, the finite expected rates `g_M` of the clipped laws are
unbounded. For each real `K` some `M` has `K < g_M`. -/
private theorem exists_clip_rate_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 ⊤))
    (gM : ℕ → EReal)
    (hgM : ∀ M : ℕ, Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (μ.map (fun t : ℝ => min t (M : ℝ)))) / (n : ℝ)) : ℝ) : EReal))
      atTop (𝓝 (gM M)))
    (hfin : ∀ M : ℕ, gM M ≠ ⊤) (K : ℝ) :
    ∃ M : ℕ, K < (gM M).toReal := by
  set m : ℝ := ∫ t : ℝ, t ∂μ with hm
  set s : ℝ := (x.1 : ℝ) + (x.2 : ℝ) with hs
  set a : ℕ → ℝ := fun n => ∫ ω : Environment, lastPassage ω 0
    (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ with ha
  set ℓ : ℕ → ℕ := fun n => ⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ with hℓ
  -- the rate bound at `+∞` holds with a real value `L n` that tends to `+∞`
  have hreal : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop atTop := by
    refine tendsto_atTop.mpr fun B => ?_
    filter_upwards [EReal.tendsto_nhds_top_iff_real.mp hg B] with n hn
    exact (EReal.coe_lt_coe_iff.mp hn).le
  have hlen : Tendsto (fun n : ℕ => m * s - m * ((ℓ n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) (NNReal.coe_nonneg _)
      (NNReal.coe_nonneg _)).const_mul m
    simpa [hs, hℓ] using (tendsto_const_nhds (x := m * s)).sub h
  have hL : Tendsto (fun n : ℕ => (a n - (ℓ n : ℝ) * m) / (n : ℝ) + m * s) atTop atTop := by
    refine (hreal.atTop_add hlen).congr fun n => ?_
    ring
  obtain ⟨n, hKn, hn⟩ := ((hL.eventually_gt_atTop (K + 1)).and (eventually_gt_atTop 0)).exists
  -- for this `n`, the lower bound of 3.1 for the clipped law tends to the one of `μ`
  have hconv : Tendsto (fun M : ℕ =>
      ((∫ ω : Environment, lastPassage (clipEnv M ω) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
        (ℓ n : ℝ) * ∫ t : ℝ, min t (M : ℝ) ∂μ) / (n : ℝ) +
        (∫ t : ℝ, min t (M : ℝ) ∂μ) * s) atTop (𝓝 ((a n - (ℓ n : ℝ) * m) / (n : ℝ) + m * s)) :=
    (((tendsto_integral_lastPassage_clip μ hμ _).sub
      ((tendsto_integral_clip μ hμ).const_mul (ℓ n : ℝ))).div_const (n : ℝ)).add
      ((tendsto_integral_clip μ hμ).mul_const s)
  obtain ⟨M, hM⟩ := (hconv.eventually_const_lt (by linarith : K < _)).exists
  refine ⟨M, lt_of_lt_of_le hM ?_⟩
  have hper := expected_floor_rate_ereal_per_n_lower_bound (μ.map (fun t : ℝ => min t (M : ℝ)))
    (clipLaw_integrable μ hμ M) x (gM M) (hgM M) n hn
  rw [integral_lastPassage_clip, integral_clipLaw] at hper
  have h := EReal.toReal_le_toReal hper (EReal.coe_ne_bot _) (hfin M)
  rwa [EReal.toReal_coe] at h

/-- Martin (2004), Proposition 2.1 (i), infinite case, in every real direction (Martin gives no
proof for non-lattice directions; the clipping argument supplies one). Let `μ` have a finite mean
and let `x` be a direction in the closed quadrant whose expected rate `E T(⌊n x⌋)/n` tends to `+∞`
in `EReal`. Then almost surely `T(⌊n x⌋)/n` tends to `+∞` in `EReal`. -/
theorem tendsto_lastPassage_floor_ae_of_rate_top (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 ⊤)) :
    ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
      ((lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
        (n : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊤) := by
  -- the finite expected rates `g_M` of the clipped laws
  have hex : ∀ M : ℕ, ∃ g : EReal, Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (μ.map (fun t : ℝ => min t (M : ℝ)))) / (n : ℝ)) : ℝ) : EReal))
      atTop (𝓝 g) := fun M => by
    exact expected_floor_rate_ereal_limit_exists _ (clipLaw_integrable μ hμ M) x
  choose gM hgM using hex
  have hfin : ∀ M : ℕ, gM M ≠ ⊤ := fun M =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (rate_clip_le μ hμ x M (gM M) (hgM M))
  -- the finite case for the clipped environment
  have hae : ∀ M : ℕ, ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ => lastPassage (clipEnv M ω) 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) / (n : ℝ)) atTop (𝓝 (gM M).toReal) := by
    intro M
    have h := (tendsto_lastPassage_floor_ae_and_L1 (μ.map (fun t : ℝ => min t (M : ℝ)))
      (clipLaw_integrable μ hμ M) x (gM M) (hgM M) (hfin M)).1
    rw [← environmentLaw_map_coordinatewise μ _ (measurable_clip M)] at h
    exact ae_of_ae_map (measurable_clipEnv M).aemeasurable h
  -- countably many null sets, then comparison `T(ω^M) ≤ T(ω)`
  filter_upwards [ae_all_iff.mpr hae] with ω hω
  rw [EReal.tendsto_nhds_top_iff_real]
  intro K
  obtain ⟨M, hM⟩ := exists_clip_rate_gt μ hμ x hg gM hgM hfin K
  filter_upwards [(hω M).eventually_const_lt hM] with n hn
  refine EReal.coe_lt_coe_iff.mpr (hn.trans_le ?_)
  exact div_le_div_of_nonneg_right
    (lastPassage_mono _ _ _ _ fun z => min_le_left _ _) (Nat.cast_nonneg n)

end LPPDifferentiability
