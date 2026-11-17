/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Finite.PressureApproximation
import Busemann.Finite.Integrability
import Busemann.Finite.Measurability
import LPP_Foundations.Analysis.PassageMomentBound
import LPP_Foundations.Probability.MartinFirstMoment
import LPP_Foundations.Model.LastPassage.Truncation
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Expected pressure of the literal finite tilted potential. The uniform mean
clipping producer and min truncation justify the expected limit required in
JR1810.03580v3, proof of Theorem 4.8 near (4.17). -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

private theorem clipped_potential_abs_le (ω : Environment) (h : ℝ × ℝ)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ) :
    |(finiteTiltedPotential (fun v => max (-L) (min L (ω v))) h 0 (n : ℤ)).toReal| ≤
      (n : ℝ) * (L + max |h.1| |h.2|) := by
  let η : Environment := fun v => max (-L) (min L (ω v))
  let m : ℕ := ((n : ℤ) - ((0 : Lattice).1 + (0 : Lattice).2)).toNat
  have hactive : (0 : Lattice).1 + (0 : Lattice).2 ≤ (n : ℤ) := by simp
  have hm : m = n := by simp [m]
  -- Bound each candidate on the literal diagonal before taking its maximum.
  have hcandidate (k : Fin (m + 1)) :
      |lastPassage η 0 (k.val, m - k.val) + h.1 * (k.val : ℝ) +
        h.2 * ((m - k.val : ℕ) : ℝ)| ≤ (n : ℝ) * (L + max |h.1| |h.2|) := by
    have hlength : k.val + (m - k.val) = n := by have := k.isLt; omega
    have hpass := lastPassage_clipped_abs_le ω 0 (k.val, m - k.val) L hL
    rw [hlength] at hpass
    calc
      _ ≤ |lastPassage η 0 (k.val, m - k.val)| +
          |h.1 * (k.val : ℝ)| + |h.2 * ((m - k.val : ℕ) : ℝ)| := by
        have hfirst := abs_add_le (lastPassage η 0 (k.val, m - k.val))
          (h.1 * (k.val : ℝ))
        have hsecond := abs_add_le (lastPassage η 0 (k.val, m - k.val) +
          h.1 * (k.val : ℝ)) (h.2 * ((m - k.val : ℕ) : ℝ))
        linarith only [hfirst, hsecond]
      _ ≤ (n : ℝ) * L + max |h.1| |h.2| * (k.val : ℝ) +
          max |h.1| |h.2| * ((m - k.val : ℕ) : ℝ) := by
        have hkabs : |(k.val : ℝ)| = (k.val : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg k.val)
        have hmkabs : |((m - k.val : ℕ) : ℝ)| = ((m - k.val : ℕ) : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg (m - k.val))
        rw [abs_mul, abs_mul, hkabs, hmkabs]
        exact add_le_add (add_le_add hpass
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
      _ = _ := by
        have hcast : (k.val : ℝ) + ((m - k.val : ℕ) : ℝ) = n := by
          exact_mod_cast hlength
        calc
          _ = (n : ℝ) * L + max |h.1| |h.2| *
              ((k.val : ℝ) + ((m - k.val : ℕ) : ℝ)) := by ring
          _ = _ := by rw [hcast]; ring
  have hupperE : finiteTiltedPotential η h 0 (n : ℤ) ≤
      (((n : ℝ) * (L + max |h.1| |h.2|) : ℝ) : EReal) := by
    apply (finiteTiltedPotential_le_coe_iff η h 0 (n : ℤ) hactive _).mpr
    intro k
    exact (abs_le.mp (hcandidate k)).2
  have hupper : (finiteTiltedPotential η h 0 (n : ℤ)).toReal ≤
      (n : ℝ) * (L + max |h.1| |h.2|) := by
    simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal hupperE
      (finiteTiltedPotential_ne_bot η h 0 (n : ℤ) hactive) (EReal.coe_ne_top _)
  let k₀ : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
  have hzeroE := finiteTiltedPotential_candidate_le η h 0 (n : ℤ) hactive k₀
  have hzero := EReal.toReal_le_toReal hzeroE (EReal.coe_ne_bot _)
    (finiteTiltedPotential_ne_top η h 0 (n : ℤ) hactive)
  simp only [EReal.toReal_coe] at hzero
  exact abs_le.mpr ⟨(abs_le.mp (hcandidate k₀)).1.trans hzero, hupper⟩

/-- The actual finite tilted potential has zero normalized expected limit at
an actual supporting tilt under the native absolute real moment p>2. Uniform
mean clipping control justifies the limit exchange in JR1810.03580v3, proof
of Theorem 4.8 near equation (4.17). No nonconstancy assumption is needed. -/
theorem integral_finiteTiltedPotential_div_tendsto_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : SupportTilt g) :
    Tendsto (fun n : ℕ => (∫ ω : Environment,
      (finiteTiltedPotential ω h.val (0 : Lattice) (n : ℤ)).toReal
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 0) := by
  classical
  -- The native moment supplies the actual tail and first-moment inputs.
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  have hfirst := integrable_id_of_martin_tails μ hneg hpos
  let F : ℕ → Environment → ℝ := fun n ω =>
    (finiteTiltedPotential ω h.val 0 (n : ℤ)).toReal
  let X : ℕ → Environment → ℝ := fun n ω => |F n ω| / (n : ℝ)
  have hiF (n : ℕ) : Integrable (F n) (environmentLaw μ) :=
    integrable_finiteTiltedPotential_toReal μ hfirst h.val 0 n
  have hiX (n : ℕ) : Integrable (X n) (environmentLaw μ) := by
    simpa only [Real.norm_eq_abs] using (hiF n).norm.div_const (n : ℝ)
  have hXnonneg (n : ℕ) (ω : Environment) : 0 ≤ X n ω :=
    div_nonneg (abs_nonneg _) (Nat.cast_nonneg n)
  -- Use the almost-sure limit of the same finite potential.
  have hXlim : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n => X n ω) atTop (𝓝 0) := by
    filter_upwards [ae_finiteTiltedPotential_div_tendsto_zero μ
      ⟨p, hp, hpMoment⟩ g hg h] with ω hω
    have ht := (continuous_abs.tendsto (0 : ℝ)).comp hω
    simp only [abs_zero] at ht
    convert ht using 1
    funext n
    change |F n ω| / (n : ℝ) = |F n ω / (n : ℝ)|
    have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [abs_div, hnabs]
  have hmeanX : Tendsto (fun n => ∫ ω, X n ω ∂environmentLaw μ) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    -- One deterministic cutoff controls the maximum error at every horizon.
    obtain ⟨L, hL, hclip⟩ := exists_uniform_mean_lastPassage_clipping_bound
      μ hpos hneg (ε / 8) (by positivity)
    let K : ℝ := max 1 (L + max |h.val.1| |h.val.2|)
    have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    let E : ℕ → Environment → ℝ := fun n ω =>
      Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (n + 1) =>
        |lastPassage ω 0 (k.val, n - k.val) -
          lastPassage (fun v => max (-L) (min L (ω v))) 0 (k.val, n - k.val)|)
    have hiE (n : ℕ) (hn : 1 ≤ n) : Integrable (E n) (environmentLaw μ) :=
      (hclip L le_rfl n hn).1
    have hmeanE (n : ℕ) (hn : 1 ≤ n) :
        (∫ ω, E n ω ∂environmentLaw μ) / (n : ℝ) ≤ ε / 8 := by
      apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
      exact (hclip L le_rfl n hn).2
    have hEnonneg (n : ℕ) (ω : Environment) : 0 ≤ E n ω :=
      (abs_nonneg _).trans (Finset.le_sup'
        (fun k : Fin (n + 1) => |lastPassage ω 0 (k.val, n - k.val) -
          lastPassage (fun v => max (-L) (min L (ω v))) 0 (k.val, n - k.val)|)
        (Finset.mem_univ (0 : Fin (n + 1))))
    let Y : ℕ → Environment → ℝ := fun n ω => min (X n ω) (2 * K)
    have hiY (n : ℕ) : Integrable (Y n) (environmentLaw μ) :=
      (hiX n).inf (integrable_const _)
    -- The bounded truncations justify this limit exchange directly.
    have hYlim : Tendsto (fun n => ∫ ω, Y n ω ∂environmentLaw μ) atTop (𝓝 0) := by
      have ht := tendsto_integral_of_dominated_convergence (fun _ : Environment => 2 * K)
        (fun n => (hiY n).aestronglyMeasurable) (integrable_const (2 * K))
        (fun n => Filter.Eventually.of_forall (fun ω => by
          change ‖min (X n ω) (2 * K)‖ ≤ 2 * K
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hXnonneg n ω) (by positivity))]
          exact min_le_right _ _))
        (show ∀ᵐ ω ∂environmentLaw μ,
          Tendsto (fun n => Y n ω) atTop (𝓝 (0 : ℝ)) from by
          filter_upwards [hXlim] with ω hω
          simpa only [min_eq_left (by positivity : (0 : ℝ) ≤ 2 * K)] using
            hω.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * K) atTop (𝓝 (2 * K))))
      simpa only [integral_zero] using ht
    have hYsmall := hYlim.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hYsmall
    refine ⟨max 1 N, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
    have hnN : N ≤ n := (le_max_right _ _).trans hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    -- Compare the actual normalized magnitude with its clipped value.
    have hpoint (ω : Environment) : X n ω ≤ 2 * (E n ω / (n : ℝ)) + Y n ω := by
      have hdiff := finiteTiltedPotential_sub_abs_le_passage_sup ω
        (fun v => max (-L) (min L (ω v))) h.val n
      have hbounded := clipped_potential_abs_le ω h.val L hL n
      have hboundedK :
          |(finiteTiltedPotential (fun v => max (-L) (min L (ω v))) h.val 0 (n : ℤ)).toReal| ≤
            (n : ℝ) * K :=
        hbounded.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg n))
      have htri := abs_sub_le (F n ω)
        (finiteTiltedPotential (fun v => max (-L) (min L (ω v))) h.val 0 (n : ℤ)).toReal 0
      simp only [sub_zero] at htri
      have hupper : X n ω ≤ E n ω / (n : ℝ) + K := by
        apply (div_le_iff₀ hnpos).mpr
        dsimp only [F] at htri
        change |F n ω| ≤ _
        have hb : |F n ω| ≤ E n ω + (n : ℝ) * K :=
          htri.trans (add_le_add hdiff hboundedK)
        calc
          |F n ω| ≤ E n ω + (n : ℝ) * K := hb
          _ = (E n ω / (n : ℝ) + K) * (n : ℝ) := by field_simp [ne_of_gt hnpos]
      have hEdiv : 0 ≤ E n ω / (n : ℝ) := div_nonneg (hEnonneg n ω) hnpos.le
      by_cases hcase : X n ω ≤ 2 * K
      · change X n ω ≤ 2 * (E n ω / (n : ℝ)) + min (X n ω) (2 * K)
        rw [min_eq_left hcase]
        linarith only [hEdiv]
      · change X n ω ≤ 2 * (E n ω / (n : ℝ)) + min (X n ω) (2 * K)
        rw [min_eq_right (le_of_not_ge hcase)]
        linarith only [hupper, hEdiv, hK]
    have hmeanbound : (∫ ω, X n ω ∂environmentLaw μ) ≤
        2 * ((∫ ω, E n ω ∂environmentLaw μ) / (n : ℝ)) +
          ∫ ω, Y n ω ∂environmentLaw μ := by
      calc
        _ ≤ ∫ ω, 2 * (E n ω / (n : ℝ)) + Y n ω ∂environmentLaw μ :=
          integral_mono (hiX n) ((((hiE n hn1).div_const (n : ℝ)).const_mul 2).add (hiY n)) hpoint
        _ = _ := by
          rw [integral_add (((hiE n hn1).div_const (n : ℝ)).const_mul 2) (hiY n),
            integral_const_mul, integral_div]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (hXnonneg n))]
    have hsmall := hN n hnN
    have hE := hmeanE n hn1
    linarith only [hmeanbound, hsmall, hE, hε]
  -- The absolute mean bound gives the requested signed expected pressure.
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun n => abs_nonneg _)
    (fun n => ?_) hmeanX
  have hb := (abs_integral_le_integral_abs
    (μ := environmentLaw μ) (f := fun ω => F n ω / (n : ℝ)))
  rw [integral_div] at hb
  have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  simpa only [X, abs_div, hnabs] using hb

end LPP.Busemann
