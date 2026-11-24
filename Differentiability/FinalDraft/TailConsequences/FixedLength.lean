/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.CrossingRemarks.Translation
public import Differentiability.FinalDraft.TailConsequences.FiniteSites
import Differentiability.Model.FiniteLevelStripCardinality
import LPP_Foundations.Model.Paths.Level
import Martin2004.Probability.RealExpectedTruncation
import Mathlib.Tactic

/-! The direct fixed-length fast-crossing estimate from Section 4 of the final
differentiability draft, Remark "The role of n". -/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace LPPDifferentiability.FinalDraft

/-- The integrated square-root upper tail implies that the strict upper tail
is little-o of the inverse square, by integration over `(t/2,t]`. -/
theorem tendsto_sq_mul_upper_tail_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : (∫⁻ t in Ioi (0 : ℝ), μ (Ioi t) ^ (1 / 2 : ℝ)) < ∞) :
    Tendsto (fun t : ℝ => t ^ 2 * μ.real (Ioi t)) atTop (𝓝 0) := by
  let f (t : ℝ) : ℝ≥0∞ := μ (Ioi t) ^ (1 / 2 : ℝ)
  have hf : Antitone f := fun _ _ h => ENNReal.rpow_le_rpow (measure_mono (Ioi_subset_Ioi h))
    (by norm_num)
  let q (t : ℝ) : ℝ := (∫⁻ r in Ioi (t / 2), f r).toReal
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have hq : Tendsto q atTop (𝓝 0) :=
    (tendsto_martin_positive_tail_toReal_zero μ hpos).comp hhalf
  have hh : Tendsto (fun t : ℝ => t * Real.sqrt (μ.real (Ioi t))) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t => 2 * q t)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hhalfpos : 0 < t / 2 := half_pos ht
      have hlen : t - t / 2 = t / 2 := by ring
      have hbound : ENNReal.ofReal (t / 2) * f t ≤ ∫⁻ r in Ioi (t / 2), f r := by
        calc
          ENNReal.ofReal (t / 2) * f t = ∫⁻ _ in Ioc (t / 2) t, f t := by
            rw [setLIntegral_const, Real.volume_Ioc, hlen, mul_comm]
          _ ≤ ∫⁻ r in Ioc (t / 2) t, f r :=
            setLIntegral_mono' measurableSet_Ioc fun r hr => hf hr.2
          _ ≤ ∫⁻ r in Ioi (t / 2), f r := lintegral_mono_set Ioc_subset_Ioi_self
      have hfinite : (∫⁻ r in Ioi (t / 2), f r) < ∞ :=
        (lintegral_mono_set (Ioi_subset_Ioi hhalfpos.le)).trans_lt hpos
      have hreal := ENNReal.toReal_mono hfinite.ne hbound
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hhalfpos.le] at hreal
      change (t / 2) * (μ (Ioi t) ^ (1 / 2 : ℝ)).toReal ≤ q t at hreal
      rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow] at hreal
      change (t / 2) * Real.sqrt (μ.real (Ioi t)) ≤ q t at hreal
      linarith only [hreal]
    · simpa only [mul_zero] using hq.const_mul 2
  convert hh.pow 2 using 1
  · ext t
    rw [mul_pow, Real.sq_sqrt measureReal_nonneg]
  · norm_num

private theorem exists_crossingSupport_lower (g : Quadrant → ℝ)
    (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (right : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ × ℕ,
      -(C * ((d.1 + d.2 : ℕ) : ℝ)) ≤ crossingSupport g a right d := by
  let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
  let slope := if right then derivWithin H (Ioi 0) 0 else derivWithin H (Iio 0) 0
  refine ⟨|H 0| + |slope|, by positivity, fun d => ?_⟩
  let length : ℝ := (d.1 : ℝ) + (d.2 : ℝ)
  let ρ := stripTransverse a ((d.1 : ℤ), (d.2 : ℤ))
  have hlength : 0 ≤ length := by dsimp [length]; positivity
  have hρ : |ρ| ≤ length := by
    dsimp [ρ, stripTransverse, length]
    push_cast
    calc
      _ ≤ |(1 - a) * (d.1 : ℝ)| + |a * (d.2 : ℝ)| := abs_sub _ _
      _ = (1 - a) * (d.1 : ℝ) + a * (d.2 : ℝ) := by
        rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr ha₁) (Nat.cast_nonneg _)),
          abs_of_nonneg (mul_nonneg ha₀ (Nat.cast_nonneg _))]
      _ ≤ _ := add_le_add
        (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith))
        (mul_le_of_le_one_left (Nat.cast_nonneg _) ha₁)
  have habs : |crossingSupport g a right d| ≤ (|H 0| + |slope|) * length := by
    change |H 0 * length + slope * ρ| ≤ _
    calc
      _ ≤ |H 0 * length| + |slope * ρ| := abs_add_le _ _
      _ = |H 0| * length + |slope| * |ρ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlength]
      _ ≤ |H 0| * length + |slope| * length :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hρ (abs_nonneg _))
      _ = _ := by ring
  rw [Nat.cast_add]
  exact (neg_le_neg habs).trans (neg_abs_le _)

/-- At each fixed length, the fast-crossing event has probability tending to zero
by the upper-tail condition and a finite-site union bound. The event uses the same
paths and actual signed supporting functional as Proposition `prop:rarefast`. -/
theorem fixed_length_fast_crossing_tendsto_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : (∫⁻ t in Ioi (0 : ℝ), μ (Ioi t) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (right : Bool) (n : ℕ) :
    Tendsto (fun s : ℝ => (environmentLaw μ).real
      (stripCrossingEvent a 0 0 (R * s) n (fun d => crossingSupport g a right d + ε * s)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hsupport⟩ := exists_crossingSupport_lower g a ha₀.le ha₁.le right
  let N : ℕ := max n 1
  let c : ℝ := ε / (2 * (N : ℝ))
  let B : ℝ := ((n + 1 : ℕ) : ℝ) * (2 * R + 1)
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right n 1))
  have hc : 0 < c := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hscale : Tendsto (fun s : ℝ => c * s) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hlim : Tendsto (fun s : ℝ => B / c ^ 2 *
      ((c * s) ^ 2 * μ.real (Ioi (c * s)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_sq_mul_upper_tail_zero μ hpos).comp hscale).const_mul (B / c ^ 2)
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * C * n / ε)] with s hs hsC
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  obtain ⟨Q, hQ, hcard⟩ :=
    exists_finset_signed_level_tube a (R * s) (fun _ => 0) 0 n (mul_nonneg hR.le hs0)
  have hsubset : stripCrossingEvent a 0 0 (R * s) n
      (fun d => crossingSupport g a right d + ε * s) ⊆
        {ω : Environment | ∃ z ∈ Q, c * s < ω z} := by
    intro ω hω
    obtain ⟨u, hu, d, hd, path, hstrip, hfast⟩ := hω
    by_contra hnone
    have hsites (i : Fin (d.1 + d.2)) : path.vertex i.castSucc ∈ Q := by
      rw [hQ]
      have hlevel := path.level i.castSucc
      rw [hu, zero_add, Fin.val_castSucc] at hlevel
      refine ⟨by omega, by omega, ?_⟩
      exact hstrip i.castSucc
    have hbound (i : Fin (d.1 + d.2)) : ω (path.vertex i.castSucc) ≤ c * s :=
      le_of_not_gt fun hi => hnone ⟨_, hsites i, hi⟩
    have hweight : pathWeight ω path ≤ (n : ℝ) * (c * s) := by
      unfold pathWeight
      calc
        _ ≤ ∑ _i : Fin (d.1 + d.2), c * s := Finset.sum_le_sum fun i _ => hbound i
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd]
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (le_max_left n 1)
    have hcap : (n : ℝ) * (c * s) ≤ ε * s / 2 := by
      calc
        _ ≤ (N : ℝ) * (c * s) :=
          mul_le_mul_of_nonneg_right hnN (mul_nonneg hc.le hs0)
        _ = _ := by dsimp [c]; field_simp
    have hscore := hsupport d
    rw [hd] at hscore
    have hsC' := (div_le_iff₀ hε).mp hsC
    change crossingSupport g a right d + ε * s < pathWeight ω path at hfast
    linarith only [hweight, hcap, hscore, hsC', hfast]
  have hcount : (Q.card : ℝ) ≤ B * s ^ 2 := by
    refine hcard.trans ?_
    dsimp [B]
    have hw : 2 * (R * s) + 1 ≤ (2 * R + 1) * s := by linarith
    have hs2 : s ≤ s ^ 2 := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs)]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) * ((2 * R + 1) * s) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = ((n + 1 : ℕ) : ℝ) * (2 * R + 1) * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs2 hB
  calc
    _ ≤ (environmentLaw μ).real {ω : Environment | ∃ z ∈ Q, c * s < ω z} :=
      measureReal_mono hsubset
    _ ≤ (Q.card : ℝ) * μ.real (Ioi (c * s)) := measureReal_exists_site_above_le μ Q _
    _ ≤ B * s ^ 2 * μ.real (Ioi (c * s)) := mul_le_mul_of_nonneg_right hcount measureReal_nonneg
    _ = _ := by field_simp

end LPPDifferentiability.FinalDraft
