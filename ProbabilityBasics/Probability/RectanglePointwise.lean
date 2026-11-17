/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Probability.RectangleCountableMaximal
import ProbabilityBasics.Probability.L1JointCoboundaryApproximation
import ProbabilityBasics.Analysis.RectangleInvariant
import ProbabilityBasics.Analysis.RectangleCoboundary
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-! Almost sure convergence of actual fixed-aspect prefix rectangle averages. -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace ProbabilityBasics

private theorem exists_rectangle_good_approximation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (a : ℝ) (ha : 0 < a) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    let A : (Ω → ℝ) → ℕ → Ω → ℝ := fun h n s => (∑ z ∈ R n, h (T z s)) / (n : ℝ)^2
    ∃ h : Ω → ℝ, Integrable h μ ∧
      (∀ᵐ s ∂μ, ∃ l : ℝ, Tendsto (fun n : ℕ => A h n s) atTop (𝓝 l)) ∧
      (∫ s, |f s - h s| ∂μ) < a := by
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let A : (Ω → ℝ) → ℕ → Ω → ℝ := fun h n s => (∑ z ∈ R n, h (T z s)) / (n : ℝ)^2
  let S : Fin 2 → Ω → Ω := fun i => T (if i = 0 then (1, 0) else (0, 1))
  have hS (i : Fin 2) : MeasurePreserving (S i) μ μ :=
    hT (if i = 0 then (1, 0) else (0, 1))
  -- Actual function-level density supplies the invariant term and both bounded coefficients.
  obtain ⟨g, φ0, φ1, M0, M1, _, hgi, hInv, hφ0m, hφ1m, hM0, hM1,
      hB0, hB1, hError⟩ :=
    exists_l1_joint_invariant_bounded_coboundary_approx μ S hS f hf a ha
  let c0 : Ω → ℝ := fun s => φ0 s - φ0 (S 0 s)
  let c1 : Ω → ℝ := fun s => φ1 s - φ1 (S 1 s)
  let h : Ω → ℝ := fun s => g s + c0 s + c1 s
  have hφ0Lp : MemLp φ0 (1 : ℝ≥0∞) μ := by
    apply MemLp.of_bound hφ0m.aestronglyMeasurable M0
    exact Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hB0 s
  have hφ1Lp : MemLp φ1 (1 : ℝ≥0∞) μ := by
    apply MemLp.of_bound hφ1m.aestronglyMeasurable M1
    exact Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hB1 s
  have hφ0i : Integrable φ0 μ := memLp_one_iff_integrable.mp hφ0Lp
  have hφ1i : Integrable φ1 μ := memLp_one_iff_integrable.mp hφ1Lp
  have hc0i : Integrable c0 μ := by
    simpa only [c0, Function.comp_apply] using
      hφ0i.sub' ((hS 0).integrable_comp_of_integrable hφ0i)
  have hc1i : Integrable c1 μ := by
    simpa only [c1, Function.comp_apply] using
      hφ1i.sub' ((hS 1).integrable_comp_of_integrable hφ1i)
  have hhi : Integrable h μ := by
    simpa only [h] using (hgi.fun_add hc0i).fun_add hc1i
  -- Consume the actual invariant and both pointwise bounded-coboundary limit theorems.
  have hgConv : ∀ᵐ s ∂μ, Tendsto (fun n : ℕ => A g n s)
      atTop (𝓝 (b 0 * b 1 * g s)) :=
    ae_tendsto_prefix_rectangle_of_unit_invariant μ T hzero hadd hT g hInv b hb
  have hc0Conv : ∀ s, Tendsto (fun n : ℕ => A c0 n s) atTop (𝓝 0) :=
    tendsto_prefix_rectangle_bounded_coboundary T hzero hadd φ0 M0 hM0 hB0 b hb 0
  have hc1Conv : ∀ s, Tendsto (fun n : ℕ => A c1 n s) atTop (𝓝 0) :=
    tendsto_prefix_rectangle_bounded_coboundary T hzero hadd φ1 M1 hM1 hB1 b hb 1
  have hSum (n : ℕ) (s : Ω) : A h n s = A g n s + A c0 n s + A c1 n s := by
    dsimp only [A, h]
    simp only [Finset.sum_add_distrib, add_div]
  refine ⟨h, hhi, ?_, ?_⟩
  · filter_upwards [hgConv] with s hs
    refine ⟨b 0 * b 1 * g s, ?_⟩
    have hSumConv : Tendsto (fun n : ℕ => A g n s + A c0 n s + A c1 n s)
        atTop (𝓝 (b 0 * b 1 * g s)) := by
      simpa only [add_zero] using (hs.add (hc0Conv s)).add (hc1Conv s)
    exact hSumConv.congr' (Eventually.of_forall fun n => (hSum n s).symm)
  · simpa only [h, c0, c1] using hError

/-- For an integrable real observable, actual fixed-aspect prefix rectangle
averages converge almost surely to a finite real limit. This is Krengel,
Ergodic Theorems, §6.2 Theorem 2.8, using the dense good class and weak maximal
Cauchy closure. No ergodicity or identification of the random limit is asserted. -/
theorem ae_tendsto_prefix_rectangle_averages
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    ∀ᵐ s ∂μ, ∃ l : ℝ,
      Tendsto (fun n : ℕ =>
        (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2) atTop (𝓝 l) := by
  classical
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let A : (Ω → ℝ) → ℕ → Ω → ℝ := fun h n s => (∑ z ∈ R n, h (T z s)) / (n : ℝ)^2
  change ∀ᵐ s ∂μ, ∃ l : ℝ, Tendsto (fun n : ℕ => A f n s) atTop (𝓝 l)
  have hSub (h k : Ω → ℝ) (n : ℕ) (s : Ω) : A (h - k) n s = A h n s - A k n s := by
    dsimp only [A]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  let D : ℝ → Set Ω := fun τ => {s | ∀ K : ℕ, ∃ p ≥ K, ∃ q ≥ K,
    τ ≤ |A f p s - A f q s|}
  -- Each positive tolerance's actual Cauchy-failure set has zero outer measure.
  have hBadZero (τ : ℝ) (hτ : 0 < τ) : μ (D τ) = 0 := by
    have hBound (a : ℝ) (ha : 0 < a) : μ.real (D τ) ≤ (32 * b 0 * b 1 / τ) * a := by
      obtain ⟨h, hhi, hConv, hError⟩ :=
        exists_rectangle_good_approximation μ T hzero hadd hT f hf b hb a ha
      let r : Ω → ℝ := f - h
      have hri : Integrable r μ := hf.sub hhi
      let E : Set Ω := {s | ∃ n : ℕ, τ / 8 < |A r n s|}
      have hErrorR : (∫ s, |r s| ∂μ) < a := by
        simpa only [r, Pi.sub_apply] using hError
      have hDecomp (n : ℕ) (s : Ω) : A f n s = A h n s + A r n s := by
        have hr := hSub f h n s
        change A r n s = A f n s - A h n s at hr
        linarith only [hr]
      -- On the good-limit event, a uniformly small residual excludes Cauchy failure.
      have hSubset : D τ ≤ᵐ[μ] E := by
        filter_upwards [hConv] with s hs
        intro hsD
        by_contra hsE
        have hSmall (n : ℕ) : |A r n s| ≤ τ / 8 := by
          exact le_of_not_gt (fun hn => hsE ⟨n, hn⟩)
        obtain ⟨l, hl⟩ := hs
        obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (τ / 2) (half_pos hτ)
        obtain ⟨p, hp, q, hq, hBad⟩ := hsD K
        have hGood : |A h p s - A h q s| < τ / 2 := by
          simpa only [dist_eq_norm, Real.norm_eq_abs] using hK p hp q hq
        have hIdentity : A f p s - A f q s =
            (A h p s - A h q s) + (A r p s - A r q s) := by
          rw [hDecomp p s, hDecomp q s]
          ring
        have hTriangle : |A f p s - A f q s| ≤
            |A h p s - A h q s| + |A r p s| + |A r q s| := by
          rw [hIdentity]
          have h0 := abs_add_le (A h p s - A h q s) (A r p s - A r q s)
          have h1 := abs_sub (A r p s) (A r q s)
          linarith only [h0, h1]
        linarith only [hBad, hTriangle, hGood, hSmall p, hSmall q, hτ]
      -- Genuine outer-measure inclusion handles original nonmeasurable-input events.
      have hMeasureMono : μ.real (D τ) ≤ μ.real E :=
        ENNReal.toReal_mono (measure_ne_top μ E) (measure_mono_ae hSubset)
      have hMax := (prefix_rectangle_maximal_bound_and_ae_bounded μ T hzero hadd hT r hri b hb).1
        (τ / 8) (by positivity)
      change μ.real E ≤ (4 * b 0 * b 1 / (τ / 8)) * ∫ s, |r s| ∂μ at hMax
      have hConstant : 4 * b 0 * b 1 / (τ / 8) = 32 * b 0 * b 1 / τ := by
        rw [div_div_eq_mul_div]
        ring
      rw [hConstant] at hMax
      have hNonneg : 0 ≤ 32 * b 0 * b 1 / τ :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hb 0).le) (hb 1).le) hτ.le
      exact hMeasureMono.trans (hMax.trans (mul_le_mul_of_nonneg_left hErrorR.le hNonneg))
    have hRealLe : μ.real (D τ) ≤ 0 := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat (32 * b 0 * b 1 / τ))
      filter_upwards [eventually_gt_atTop 0] with k hk
      have hkReal : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
      have h := hBound (1 / (k : ℝ)) (one_div_pos.mpr hkReal)
      simpa only [div_eq_mul_inv, one_mul] using h
    exact (measureReal_eq_zero_iff (measure_ne_top μ (D τ))).mp
      (le_antisymm hRealLe measureReal_nonneg)
  -- One countable intersection over reciprocal tolerances gives the full Cauchy criterion.
  have hAll : ∀ᵐ s ∂μ, ∀ k : ℕ, s ∉ D (1 / ((k : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hBadZero (1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [hAll] with s hs
  have hCauchy : CauchySeq (fun n : ℕ => A f n s) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have hNot := hs k
    change ¬(∀ K : ℕ, ∃ p ≥ K, ∃ q ≥ K,
      1 / ((k : ℝ) + 1) ≤ |A f p s - A f q s|) at hNot
    push Not at hNot
    obtain ⟨K, hK⟩ := hNot
    refine ⟨K, ?_⟩
    intro p hp q hq
    simpa only [dist_eq_norm, Real.norm_eq_abs] using (hK p hp q hq).trans hk
  exact cauchySeq_tendsto_of_complete hCauchy

end ProbabilityBasics
