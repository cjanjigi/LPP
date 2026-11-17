/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.ProcessSample
public import Busemann.Frozen.Definitions.FiniteBusemannSharedHorizonLaw
public import Busemann.Frozen.Definitions.FiniteBusemannArrayAtSharedHorizon
public import Busemann.Frozen.Definitions.SupportTilt
public import Martin2004.Shape.ExpectedRateShape
public import LPP_Foundations.Probability.EnvironmentLaw
public import ProbabilityBasics.Probability.AbsoluteMomentTail
import Busemann.Finite.SharedHorizonMoments
import Busemann.Finite.NegativeTails
import Busemann.Finite.Measurability
import LPP_Foundations.Probability.MartinFirstMoment
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.WeakMean
import ProbabilityBasics.Probability.UniformOriginTails
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! One-sided mean control for a weak limit of the literal joint finite laws. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

private theorem site_negative_excess_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) :
    Tendsto (fun k : ℕ => ∫ t : ℝ, max (-t - (k : ℝ)) 0 ∂μ) atTop (𝓝 0) := by
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun t : ℝ => max (-t - (k : ℝ)) 0) μ :=
    ((measurable_id.neg.sub measurable_const).max measurable_const).aestronglyMeasurable
  have hbound (k : ℕ) : ∀ᵐ t : ℝ ∂μ,
      ‖max (-t - (k : ℝ)) 0‖ ≤ |t| := by
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have ht : -t ≤ |t| := neg_le_abs t
    exact max_le (by linarith only [hk, ht]) (abs_nonneg t)
  have hpoint : ∀ᵐ t : ℝ ∂μ,
      Tendsto (fun k : ℕ => max (-t - (k : ℝ)) 0) atTop (𝓝 0) := by
    filter_upwards [] with t
    apply tendsto_const_nhds.congr'
    obtain ⟨K, hK⟩ := exists_nat_ge (-t)
    filter_upwards [eventually_ge_atTop K] with k hk
    have hk' : (-t) ≤ (k : ℝ) := hK.trans (by exact_mod_cast hk)
    simp only [max_eq_right (by linarith : -t - (k : ℝ) ≤ 0)]
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun t : ℝ => |t|) hmeas hμ.abs hbound hpoint
  simpa only [integral_zero] using hdct

private theorem finite_positive_tail_le_excess
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun t : ℝ => t) μ)
    (h : ℝ × ℝ) (x : Lattice) (i : Fin 2) (n k : ℕ) :
    (∫ p : Environment × Fin (n + 1),
      positiveTail (2 * k) (-finiteBusemannEdge p.1 h x
        ((p.2.val + 1 : ℕ) : ℤ) i) ∂finiteBusemannSharedHorizonLaw μ n) ≤
      2 * ∫ t : ℝ, max (-t - (k : ℝ)) 0 ∂μ := by
  let : IsProbabilityMeasure (finiteBusemannSharedHorizonLaw μ n) := by
    change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
    infer_instance
  let E : Environment × Fin (n + 1) → ℝ := fun p =>
    finiteBusemannEdge p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i
  have hE : Integrable E (finiteBusemannSharedHorizonLaw μ n) := by
    rw [finiteBusemannSharedHorizonLaw]
    exact integrable_uniformOrigin_family (environmentLaw μ) n
      (fun u ω => finiteBusemannEdge ω h x ((u.val + 1 : ℕ) : ℤ) i)
      (fun u => measurable_finiteBusemannEdge h x ((u.val + 1 : ℕ) : ℤ) i)
      (fun u => integrable_finiteBusemannEdge μ hμ h x ((u.val + 1 : ℕ) : ℤ) i)
  have hleft : Integrable (fun p => positiveTail (2 * k) (-E p))
      (finiteBusemannSharedHorizonLaw μ n) :=
    integrable_positiveTail _ _ hE.neg _
  have hexcess : Integrable (fun p => max (-E p - (k : ℝ)) 0)
      (finiteBusemannSharedHorizonLaw μ n) :=
    (hE.neg.sub (integrable_const (k : ℝ))).pos_part
  have hpoint (p : Environment × Fin (n + 1)) :
      positiveTail (2 * k) (-E p) ≤ 2 * max (-E p - (k : ℝ)) 0 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    unfold positiveTail
    split_ifs with hp
    · have hp' : 0 < -E p := by
        by_contra hn
        have hn' : -E p ≤ 0 := le_of_not_gt hn
        rw [max_eq_right hn'] at hp
        linarith only [hk, hp]
      rw [max_eq_left hp'.le] at hp ⊢
      have hex : 0 ≤ -E p - (k : ℝ) := by linarith [hp]
      rw [max_eq_left hex]
      linarith [hp]
    · exact mul_nonneg (by norm_num) (le_max_right _ _)
  have hmono := integral_mono hleft (hexcess.const_mul 2) hpoint
  simp only [integral_const_mul] at hmono
  have hsite := integral_finite_busemann_edge_negative_excess_shared_horizon_le
    μ hμ h x i n (k : ℝ) (Nat.cast_nonneg _)
  dsimp only [E] at hmono
  linarith only [hmono, hsite]

/-- The actual shared-horizon weak limit has integrable coordinates with mean
at most the negative supporting tilt, as in JR arXiv:1810.03580v3 after (4.17). -/
theorem integral_edge_le_neg_tilt_of_finiteBusemann_weak_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : ℕ → SupportTilt g)
    (P : ProbabilityMeasure ProcessSample) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hweak :
      let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
        (show ProbabilityMeasure (Environment × Fin (n + 1)) from
          ⟨finiteBusemannSharedHorizonLaw μ n, by
            change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
            infer_instance⟩).map
          (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p))
      Tendsto (ν ∘ φ) atTop (𝓝 P)) :
    ∀ j x i, Integrable (fun s : ProcessSample => s.2 j x i) (P : Measure ProcessSample) ∧
      (∫ s : ProcessSample, s.2 j x i ∂(P : Measure ProcessSample)) ≤
        -finiteTiltCoordinate (h j).val i := by
  classical
  intro j x i
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  have hμ : Integrable (fun t : ℝ => t) μ := integrable_id_of_martin_tails μ hneg hpos
  have hmoment' : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞ :=
    ⟨p, hp, hpMoment⟩
  let S (n : ℕ) (q : Environment × Fin (n + 1)) : ProcessSample :=
    (q.1, finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) q)
  let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
    (show ProbabilityMeasure (Environment × Fin (n + 1)) from
      ⟨finiteBusemannSharedHorizonLaw μ n, by
        change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
        infer_instance⟩).map (S n)
  let G : ProcessSample → ℝ := fun s => -s.2 j x i
  have hS (n : ℕ) : Measurable (S n) :=
    measurable_fst.prodMk (measurable_finiteBusemannArrayAtSharedHorizon n _)
  have hG : Continuous G := by
    have heval : Continuous (fun s : ProcessSample => s.2 j x i) :=
      (continuous_apply i).comp ((continuous_apply x).comp
        ((continuous_apply j).comp continuous_snd))
    exact heval.neg
  let ρ : ℕ → ProbabilityMeasure ℝ := fun n => (ν (φ n)).map G
  let ρlim : ProbabilityMeasure ℝ := P.map G
  have hρweak : Tendsto ρ atTop (𝓝 ρlim) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (ν ∘ φ) P hweak hG
  let E (n : ℕ) (q : Environment × Fin (n + 1)) : ℝ :=
    finiteBusemannEdge q.1 (h j).val x ((q.2.val + 1 : ℕ) : ℤ) i
  have hE (n : ℕ) : Integrable (E n) (finiteBusemannSharedHorizonLaw μ n) := by
    rw [finiteBusemannSharedHorizonLaw]
    exact integrable_uniformOrigin_family (environmentLaw μ) n
      (fun u ω => finiteBusemannEdge ω (h j).val x ((u.val + 1 : ℕ) : ℤ) i)
      (fun u => measurable_finiteBusemannEdge (h j).val x ((u.val + 1 : ℕ) : ℤ) i)
      (fun u => integrable_finiteBusemannEdge μ hμ (h j).val x ((u.val + 1 : ℕ) : ℤ) i)
  have hnegE (n : ℕ) : Measurable (fun q => -E n q) := by
    change Measurable (G ∘ S n)
    exact hG.measurable.comp (hS n)
  have hmap (n : ℕ) :
      (ρ n : Measure ℝ) =
        (finiteBusemannSharedHorizonLaw μ (φ n)).map (fun q => -E (φ n) q) := by
    simp only [ρ, ProbabilityMeasure.toMeasure_map]
    change Measure.map G (Measure.map (S (φ n))
      (finiteBusemannSharedHorizonLaw μ (φ n))) = _
    rw [Measure.map_map hG.measurable (hS (φ n))]
    rfl
  have hρint (n : ℕ) : Integrable (fun t : ℝ => t) (ρ n : Measure ℝ) := by
    rw [hmap]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      ((hnegE (φ n)).aemeasurable)).2 (hE (φ n)).neg
  obtain ⟨C, _, hC⟩ := exists_uniform_integral_abs_finiteBusemannEdge_sharedHorizon_bound
    μ hmoment' g hg (h j) x i
  have hρbound (n : ℕ) : (∫ t : ℝ, |t| ∂(ρ n : Measure ℝ)) ≤ C := by
    rw [hmap, integral_map (hnegE (φ n)).aemeasurable
      (continuous_abs.measurable.aestronglyMeasurable)]
    simp only [abs_neg]
    exact hC (φ n)
  have hρmean : Tendsto (fun n => ∫ t : ℝ, t ∂(ρ n : Measure ℝ))
      atTop (𝓝 (finiteTiltCoordinate (h j).val i)) := by
    have hm := (tendsto_integral_finiteBusemannEdge_sharedHorizon
      μ hmoment' g hg (h j) x i).comp hφ.tendsto_atTop
    have hm' := hm.neg
    simp only [neg_neg] at hm'
    apply hm'.congr'
    apply Eventually.of_forall
    intro n
    change -(∫ q, E (φ n) q ∂finiteBusemannSharedHorizonLaw μ (φ n)) =
      ∫ t : ℝ, t ∂(ρ n : Measure ℝ)
    rw [hmap]
    change -(∫ q, E (φ n) q ∂finiteBusemannSharedHorizonLaw μ (φ n)) =
      ∫ t : ℝ, id t ∂(finiteBusemannSharedHorizonLaw μ (φ n)).map (fun q => -E (φ n) q)
    rw [integral_map (hnegE (φ n)).aemeasurable measurable_id.aestronglyMeasurable]
    simp only [id_eq, integral_neg]
  have htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n,
      (∫ t in {t : ℝ | R < max t 0}, max t 0 ∂(ρ n : Measure ℝ)) < ε := by
    intro ε hε
    have hlim := site_negative_excess_tendsto_zero μ hμ
    have hk := (tendsto_order.1 hlim).2 (ε / 2) (by linarith)
    obtain ⟨K, hK⟩ := eventually_atTop.1 hk
    refine ⟨2 * K, fun n => ?_⟩
    have hsite : (∫ t : ℝ, max (-t - (K : ℝ)) 0 ∂μ) < ε / 2 := hK K le_rfl
    have hfinite := finite_positive_tail_le_excess μ hμ (h j).val x i (φ n) K
    have heq :
        (∫ t in {t : ℝ | (2 * K : ℝ) < max t 0}, max t 0 ∂(ρ n : Measure ℝ)) =
        ∫ q : Environment × Fin (φ n + 1),
          positiveTail (2 * K) (-E (φ n) q)
            ∂finiteBusemannSharedHorizonLaw μ (φ n) := by
      have hs : MeasurableSet {t : ℝ | (2 * K : ℝ) < max t 0} :=
        measurableSet_lt measurable_const (measurable_id.max measurable_const)
      have hind := integral_indicator (μ := (ρ n : Measure ℝ))
        (f := fun t : ℝ => max t 0) hs
      rw [← hind]
      have hfun : ({t : ℝ | (2 * K : ℝ) < max t 0}.indicator
          (fun t => max t 0)) = positiveTail (2 * K) := by
        funext t
        simp only [positiveTail, Set.indicator_apply, Set.mem_ofPred_eq]
      rw [hfun, hmap, integral_map (hnegE (φ n)).aemeasurable
        ((measurable_positiveTail (2 * K)).aestronglyMeasurable)]
    rw [heq]
    linarith only [hfinite, hsite]
  have hlimInt := integrable_id_of_weak_abs_integral_le ρ ρlim hρweak hρint C hρbound
  have hmean := mean_le_of_weak_abs_integral_le_pos_tails
    ρ ρlim hρweak hρint C hρbound htail (finiteTiltCoordinate (h j).val i) hρmean
  have hGint : Integrable G (P : Measure ProcessSample) := by
    have hm := (integrable_map_measure measurable_id.aestronglyMeasurable
      hG.measurable.aemeasurable).1 hlimInt
    exact hm
  constructor
  · have ht := hGint.neg
    change Integrable (fun s : ProcessSample => -(-s.2 j x i))
      (P : Measure ProcessSample) at ht
    simpa only [neg_neg] using ht
  · have heq : (∫ t : ℝ, t ∂(ρlim : Measure ℝ)) =
        -(∫ s : ProcessSample, s.2 j x i ∂(P : Measure ProcessSample)) := by
      change (∫ t : ℝ, id t ∂(P : Measure ProcessSample).map G) = _
      rw [integral_map hG.measurable.aemeasurable measurable_id.aestronglyMeasurable]
      exact integral_neg _
    rw [heq] at hmean
    linarith only [hmean]

end LPP.Busemann
