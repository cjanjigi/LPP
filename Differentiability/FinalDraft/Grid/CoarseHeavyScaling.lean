/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Grid.HeavyTrials
import Differentiability.Analysis.GridScaleCounts
import Differentiability.Analysis.HeavyVertexDecay
import Differentiability.Model.FiniteLevelStripCardinality
import Differentiability.Model.Paths.GridCoarseGeneralAssembly
import Differentiability.Probability.FiniteHeavyVertices
import ProbabilityBasics.Probability.PositiveMomentTail
import Mathlib.Tactic

/-! # Coarse trial caps under an improved characteristic-length bound

The upper-tail discussion of `differentiability_final_draft.tex`, subsection `sub:ub_mom-chat`,
applies an improved power of the characteristic length to the heavy-vertex lemma.
Here the improved bound is a hypothesis on the actual characteristic lengths. It
controls the canonical coarse blocks at the earlier scale `k-j`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The common upper bound for the failure probability of a coarse trial cap
when the characteristic-length exponent is `gamma`. -/
noncomputable def gridHeavyTailOfLengthPower (μ : Measure ℝ) (p gamma : ℝ) (k : ℕ) : ℝ :=
  17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ ((1 + gamma - p) * ((k : ℝ) - 3) / 4)

/-- Count the sites in the canonical closed block and apply the positive moment bound to
the cap on those sites. The hypothesis `l ≤ w^gamma / 2` is the improved mesh bound. -/
theorem grid_trialCap_finite_bound_of_mesh_le_half_width_power
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p gamma : ℝ) (hp : 0 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a : ℝ) (I h : ℤ) (l b j w : ℕ) (ν : Fin (j ^ 2))
    (hw : 1 ≤ w) (hb : 2 * b < l) (hl : (l : ℝ) ≤ (w : ℝ) ^ gamma / 2) :
    let c := coarseCrossingCentre a h w I b (ν.val + 1)
    ∃ S : Finset Lattice,
      (∀ z, z ∈ S ↔ z ∈ gridCrossingBlock a w I l b c) ∧
      (S.card : ℝ) ≤ 17 * (w : ℝ) ^ (1 + gamma) ∧
      (environmentLaw μ).real (gridTrialCap a I h l b j w ν)ᶜ ≤
        17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (w : ℝ) ^ (1 + gamma - p) := by
  intro c
  let ρ : ℝ := (1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ)
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hwpos : (0 : ℝ) < w := zero_lt_one.trans_le hwR
  obtain ⟨S, hmem, hcount⟩ := exists_finset_signed_level_tube a (8 * (w : ℝ)) (fun _ => ρ)
    (I + (b : ℤ)) (l - 2 * b) (by positivity)
  have hlast : I + (b : ℤ) + ((l - 2 * b : ℕ) : ℤ) = I + (l : ℤ) - (b : ℤ) := by omega
  have hS (z : Lattice) : z ∈ S ↔ z ∈ gridCrossingBlock a w I l b c := by
    simpa only [gridCrossingBlock, Set.mem_ofPred_eq, hlast, ρ] using hmem z
  have hlevels : ((l - 2 * b + 1 : ℕ) : ℝ) ≤ 2 * (l : ℝ) := by
    exact_mod_cast (show l - 2 * b + 1 ≤ 2 * l by omega)
  have hsites : 2 * (8 * (w : ℝ)) + 1 ≤ 17 * (w : ℝ) := by linarith only [hwR]
  have hcard : (S.card : ℝ) ≤ 17 * (w : ℝ) ^ (1 + gamma) := by
    calc
      _ ≤ ((l - 2 * b + 1 : ℕ) : ℝ) * (2 * (8 * (w : ℝ)) + 1) := hcount
      _ ≤ (2 * (l : ℝ)) * (17 * (w : ℝ)) := mul_le_mul hlevels hsites (by positivity) (by positivity)
      _ ≤ ((w : ℝ) ^ gamma) * (17 * (w : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by linarith only [hl]) (by positivity)
      _ = 17 * (w : ℝ) ^ (1 + gamma) := by
        rw [Real.rpow_add hwpos, Real.rpow_one]
        ring
  have hbad : (gridTrialCap a I h l b j w ν)ᶜ = {ω : Environment | ∃ z ∈ S, (w : ℝ) < ω z} := by
    ext ω
    simp only [gridTrialCap, gridUpperCap, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall,
      not_le, exists_prop, hS, c]
  let Cp : ℝ := ∫ x : ℝ, (max x 0) ^ p ∂μ
  have hCp : 0 ≤ Cp := integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hMarkov := (measureReal_exists_upper_heavy_site_le_and_safe_ge μ hp hmom w hwpos S).2.1
  refine ⟨S, hS, hcard, ?_⟩
  rw [hbad]
  calc
    _ ≤ (S.card : ℝ) * Cp * (w : ℝ) ^ (-p) := hMarkov
    _ ≤ (17 * (w : ℝ) ^ (1 + gamma)) * Cp * (w : ℝ) ^ (-p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hCp)
        (Real.rpow_nonneg hwpos.le _)
    _ = 17 * Cp * (w : ℝ) ^ (1 + gamma - p) := by
      have hmul : (w : ℝ) ^ (1 + gamma - p) = (w : ℝ) ^ (1 + gamma) * (w : ℝ) ^ (-p) := by
        simpa only [← sub_eq_add_neg] using Real.rpow_add hwpos (1 + gamma) (-p)
      rw [hmul]
      ring

private theorem grid_heavy_tail_of_length_power_le_half_eventually
    (μ : Measure ℝ) (p gamma q0 : ℝ) (hp : 1 + gamma < p) (hq0 : 0 < q0) :
    Tendsto (gridHeavyTailOfLengthPower μ p gamma) atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, gridHeavyTailOfLengthPower μ p gamma k ≤ q0 / 2 := by
  have hCp : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have he : -(p + 3 - gamma - 4) = 1 + gamma - p := by ring
  change Tendsto (fun k : ℕ => 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
    (2 : ℝ) ^ ((1 + gamma - p) * ((k : ℝ) - 3) / 4)) atTop (𝓝 0) ∧ _
  simpa only [he, gridHeavyTailOfLengthPower] using
    (heavy_vertex_block_tail_decay (p := p + 3 - gamma) (by linarith only [hp]) hCp hq0)

private theorem grid_block_moment_bound_le_uniform_tail
    (μ : Measure ℝ) (p gamma : ℝ) (hp : 1 + gamma < p) (k j : ℕ)
    (hk : k ≤ 4 * (k - j) + 3) :
    17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
      ((2 : ℝ) ^ (k - j)) ^ (1 + gamma - p) ≤ gridHeavyTailOfLengthPower μ p gamma k := by
  have hCp : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hkR : (k : ℝ) ≤ 4 * ((k - j : ℕ) : ℝ) + 3 := by exact_mod_cast hk
  have hpow : (2 : ℝ) ^ (((k : ℝ) - 3) / 4) ≤ (2 : ℝ) ^ (k - j) := by
    rw [← Real.rpow_natCast (2 : ℝ) (k - j)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hkR])
  have hpos : (0 : ℝ) < 2 ^ (((k : ℝ) - 3) / 4) := Real.rpow_pos_of_pos zero_lt_two _
  have hmon := Real.rpow_le_rpow_of_nonpos hpos hpow (show 1 + gamma - p ≤ 0 by linarith only [hp])
  unfold gridHeavyTailOfLengthPower
  have he : ((2 : ℝ) ^ (((k : ℝ) - 3) / 4)) ^ (1 + gamma - p) =
      (2 : ℝ) ^ ((1 + gamma - p) * ((k : ℝ) - 3) / 4) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  exact mul_le_mul_of_nonneg_left (hmon.trans_eq he) (mul_nonneg (by norm_num) hCp)

private theorem canonical_capped_trials_of_finite_blocks
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a G K q0 : ℝ)
    (I h : ℤ) (l b j w : ℕ) (hw : (1 : ℝ) ≤ w) (hb : 2 * b ≤ l)
    (S : Fin (j ^ 2) → Finset Lattice)
    (hS : ∀ ν z, z ∈ S ν ↔
      z ∈ gridCrossingBlock a w I l b (coarseCrossingCentre a h w I b (ν.val + 1)))
    (hE₀ : q0 < (environmentLaw μ).real (gridCrossingTrial a G K w 0 (l - 2 * b) 0 0))
    (hsmall : ∀ ν, (environmentLaw μ).real (gridTrialCap a I h l b j w ν)ᶜ ≤ q0 / 2) :
    iIndepSet (gridCappedTrial a G K I h l b j w) (environmentLaw μ) ∧
      ∀ ν, q0 / 2 ≤ (environmentLaw μ).real (gridCappedTrial a G K I h l b j w ν) := by
  let c (ν : Fin (j ^ 2)) := coarseCrossingCentre a h w I b (ν.val + 1)
  have hE₀eq : gridCrossingTrial a G K w 0 (l - 2 * b) 0 0 =
      {ω : Environment | ∃ (u : Lattice) (d : ℕ × ℕ) (y : Path u d),
        u.1 + u.2 = 0 ∧ d.1 + d.2 = l - 2 * b ∧
        (∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ)| ≤ 8 * (w : ℝ)) ∧
        G * ((l - 2 * b : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω y} := by
    simp only [gridCrossingTrial, Nat.sub_zero, Nat.cast_zero, add_zero,
      Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, sub_zero]
  have hcap (ν : Fin (j ^ 2)) : {ω : Environment | ∀ z ∈ S ν, ω z ≤ (w : ℝ)} =
      gridTrialCap a I h l b j w ν := by
    ext ω
    simp only [gridTrialCap, gridUpperCap, Set.mem_ofPred_eq, hS]
  have hsmall' (ν : Fin (j ^ 2)) :
      (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ S ν, ω z ≤ (w : ℝ)} ≤ q0 / 2 := by
    change (environmentLaw μ).real {ω : Environment | ∀ z ∈ S ν, ω z ≤ (w : ℝ)}ᶜ ≤ q0 / 2
    rw [hcap]
    exact hsmall ν
  obtain ⟨hind, hprob, -⟩ := heavy_crossing_trials_indep μ a G K w h hw I l b (j ^ 2) hb c
    (fun ν => (coarse_crossing_centre_spec a h w I b (ν.val + 1)).1)
    (fun ν => (coarse_crossing_centre_spec a h w I b (ν.val + 1)).2)
    (fun ν => gridCrossingTrial a G K w I l b (c ν)) (fun _ => rfl)
    (gridCrossingTrial a G K w 0 (l - 2 * b) 0 0) hE₀eq S (fun ν z => hS ν z) q0 hE₀ hsmall'
  have hEvent : (fun ν => gridCrossingTrial a G K w I l b (c ν) ∩
      {ω : Environment | ∀ z ∈ S ν, ω z ≤ (w : ℝ)}) = gridCappedTrial a G K I h l b j w := by
    funext ν
    rw [hcap, gridCappedTrial_eq_inter_gridTrialCap]
  rw [hEvent] at hind
  refine ⟨hind, fun ν => ?_⟩
  rw [← congrFun hEvent ν]
  exact hprob ν

/-- Under a conditional improved power bound on the actual characteristic lengths,
the coarse cap failure probabilities tend uniformly to zero for `1 + gamma < p`.
The standing shape calculation uses `2 < p`. The same fixed capped trials
are jointly independent and have probability at least `q0/2` at sufficiently large records.
The improved bound is applied at the earlier scale `k-j`. -/
theorem heavy_grid_trials_of_characteristic_length_power
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p' : ℝ, 1 < p' ∧ (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (p gamma : ℝ) (hp₂ : 2 < p) (hp : 1 + gamma < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (Gtop : ℝ)
    (htop : Tendsto (fun n : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(n : ℝ) * a⌋₊, ⌊(n : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) (q0 : ℝ) (hq0₀ : 0 < q0) (hq0₁ : q0 < 1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl := derivWithin H (Iio 0) 0
    let dr := derivWithin H (Ioi 0) 0
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let G := H 0
    let cstar : ℝ := 50 / min a (1 - a)
    let P : ℕ → ℕ → ℝ := fun k n => (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * (2 : ℝ) ^ k) ∧
        G * (n : ℝ) - K * (2 : ℝ) ^ k < pathWeight ω q}
    ∃ (k0 : ℕ) (m nk : ℕ → ℕ) (record : Set ℕ),
      0 < k0 ∧ record.Infinite ∧ Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ k) atTop atTop ∧
      (∀ k, k0 ≤ k →
        (∃ n : ℕ, (2 : ℝ) ^ m k / 2 < n ∧ (n : ℝ) ≤ 2 ^ m k ∧ P k n ≤ q0) ∧
        (∀ j : ℕ, (∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0) →
          m k ≤ j) ∧
        m k ≤ 3 * k ∧
        (∀ n : ℕ, 1 ≤ n → (n : ℝ) < 2 ^ m k / 2 → q0 < P k n) ∧
        ((2 : ℝ) ^ m k / 2 < nk k ∧ (nk k : ℝ) ≤ 2 ^ m k ∧ P k (nk k) ≤ q0 ∧
          ∀ n : ℕ, (2 : ℝ) ^ m k / 2 < n → (n : ℝ) ≤ 2 ^ m k → P k (nk k) ≤ P k n)) ∧
      (∀ k ∈ record, k0 ≤ k ∧ ∀ j : ℕ, j ≤ k - k0 →
        (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j)) ∧
      Tendsto (gridHeavyTailOfLengthPower μ p gamma) atTop (𝓝 0) ∧
      ((∀ᶠ r : ℕ in atTop, (2 : ℝ) ^ m r ≤ ((2 : ℝ) ^ r) ^ gamma) →
        ∀ (A R : ℝ), 0 < A → 0 < R → ∀ J : ℕ, 1 ≤ J →
        ∃ k1 : ℕ, ∀ k ∈ record, k1 ≤ k →
          ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
          let l : ℕ := 2 ^ (m k - 4 * j - 1)
          let w : ℕ := 2 ^ (k - j)
          let b := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
          8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ) →
          ∀ I : ℤ, (l : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * (2 : ℝ) ^ m k →
          ∀ h : ℤ, (∃ ρ : ℝ, (h : ℝ) * (w : ℝ) ≤ ρ ∧
            ρ < ((h : ℝ) + 1) * (w : ℝ) ∧ |ρ| ≤ R * (2 : ℝ) ^ k) →
          (l : ℝ) ≤ (w : ℝ) ^ gamma / 2 ∧
          (∀ ν : Fin (j ^ 2),
            (environmentLaw μ).real (gridTrialCap a I h l b j w ν)ᶜ ≤
              17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (w : ℝ) ^ (1 + gamma - p) ∧
            (environmentLaw μ).real (gridTrialCap a I h l b j w ν)ᶜ ≤
              gridHeavyTailOfLengthPower μ p gamma k) ∧
          iIndepSet (gridCappedTrial a G K I h l b j w) (environmentLaw μ) ∧
          ∀ ν : Fin (j ^ 2), q0 / 2 ≤ (environmentLaw μ).real (gridCappedTrial a G K I h l b j w ν)) := by
  intro H dl dr K G cstar P
  have hpos := positive_integrated_sqrt_tail_lt_top_of_moment μ hp₂ hmom
  obtain ⟨k0, hk0, m, nk, record, hgrowth, hchar, hinf, hrecord, htrial⟩ :=
    characteristic_length_records μ hneg hpos g hgcont hghom hgconc hgshape a ha₀ ha₁ Gtop
      htop hgap q0 hq0₀ hq0₁
  have hG : G = g (toQuadrant (a, 1 - a)) := by
    simp only [G, H, quadrantExtension, add_zero, sub_zero]
  have htrial' : gridRecordTrials μ a G K q0 k0 m record := by
    rw [hG]
    exact htrial
  have ⟨htail, htailHalf⟩ := grid_heavy_tail_of_length_power_le_half_eventually μ p gamma q0 hp hq0₀
  have hcstar : 1 ≤ cstar := (by norm_num : (1 : ℝ) ≤ 100).trans
    (coarse_direction_facts a cstar (StairGeometry.slopeCutoff a) rfl ha₀ ha₁ rfl).2.2.2.2.2
  refine ⟨k0, m, nk, record, hk0, hinf, hgrowth, ?_, hrecord, htail, ?_⟩
  · dsimp only [P]
    rw [hG]
    exact hchar
  intro hImproved A R _ _ J hJ
  obtain ⟨kPower, hkPower⟩ := eventually_atTop.mp hImproved
  obtain ⟨kTail, hkTail⟩ := eventually_atTop.mp htailHalf
  refine ⟨max (4 * max k0 kPower + 3) kTail, ?_⟩
  intro k hk hlarge j hJj hj l w b hc I _ _ h _
  have hkBase : 4 * max k0 kPower + 3 ≤ k := (le_max_left _ _).trans hlarge
  have hk0' : 4 * k0 + 3 ≤ k := by have := le_max_left k0 kPower; omega
  have hkPow' : 4 * kPower + 3 ≤ k := by have := le_max_right k0 kPower; omega
  have hmk := (hchar k (hrecord k hk).1).2.2.1
  have hjBound := (grid_jstar_bounds (m := m k) (rfl : ⌈((m k : ℝ) - 1) / 4⌉₊ = _)).2
  have hkWidth : k ≤ 4 * (k - j) + 3 := by omega
  have hkj₀ : j ≤ k - k0 := by omega
  have hkjPower : kPower ≤ k - j := by omega
  have hwc : (w : ℝ) = (2 : ℝ) ^ (k - j) := by dsimp only [w]; push_cast; rfl
  have hlc : (l : ℝ) = (2 : ℝ) ^ (m k - 4 * j - 1) := by dsimp only [l]; push_cast; rfl
  have hw : 1 ≤ w := Nat.one_le_two_pow
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hJ.trans hJj
  have hX : 1 ≤ cstar * (j : ℝ) ^ 2 * (w : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hcstar (one_le_pow₀ hjR)) hwR
  obtain ⟨-, -, -, -, hl8, hremain⟩ := grid_coarse_trim_bounds hX (by simpa only [mul_assoc] using hc)
  have hbEq : (b : ℝ) = (⌈cstar * (j : ℝ) ^ 2 * (w : ℝ)⌉₊ : ℝ) := by
    simp only [b, mul_assoc]
  rw [← hbEq] at hremain
  have hb : 2 * b < l := by
    exact_mod_cast (show (2 : ℝ) * (b : ℝ) < (l : ℝ) by linarith only [hremain])
  have hbPos : 0 < b := by
    apply Nat.ceil_pos.mpr
    simpa only [mul_assoc] using zero_lt_one.trans_le hX
  have hlLarge : 1 < (2 : ℝ) ^ (m k - 4 * j - 1) := by rw [← hlc]; linarith only [hl8]
  have hmeshdbl := mesh_double_le_length m k j ((hrecord k hk).2 j hkj₀) hlLarge
  have hpow := hkPower (k - j) hkjPower
  have hlPower : (l : ℝ) ≤ (w : ℝ) ^ gamma / 2 := by
    rw [hlc, hwc]
    linarith only [hmeshdbl, hpow]
  have hMoment := grid_block_moment_bound_le_uniform_tail μ p gamma hp k j hkWidth
  choose S hS _ hcap using fun ν : Fin (j ^ 2) =>
    grid_trialCap_finite_bound_of_mesh_le_half_width_power μ p gamma (by linarith only [hp₂]) hmom
      a I h l b j w ν hw hb hlPower
  have hUniform (ν : Fin (j ^ 2)) :
      (environmentLaw μ).real (gridTrialCap a I h l b j w ν)ᶜ ≤ gridHeavyTailOfLengthPower μ p gamma k := by
    exact (hcap ν).trans (by rw [hwc]; exact hMoment)
  have hE₀ : q0 < (environmentLaw μ).real (gridCrossingTrial a G K w 0 (l - 2 * b) 0 0) := by
    have htrialBound := (htrial' k hk hk0' j hj).1 (l - 2 * b) (by omega)
      (by rw [← hlc]; exact_mod_cast (show l - 2 * b < l by omega))
    refine htrialBound.trans_le (le_of_eq (congrArg (environmentLaw μ).real ?_))
    ext ω
    simp only [gridCrossingTrial, Set.mem_ofPred_eq, Nat.sub_zero, Nat.cast_zero,
      add_zero, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, sub_zero, hwc]
    constructor
    · rintro ⟨u, hu, e, he, y, hy, hweight⟩
      exact ⟨u, e, y, hu, he, hy, hweight⟩
    · rintro ⟨u, e, y, hu, he, hy, hweight⟩
      exact ⟨u, hu, e, he, y, hy, hweight⟩
  refine ⟨hlPower, fun ν => ⟨hcap ν, hUniform ν⟩, ?_⟩
  exact canonical_capped_trials_of_finite_blocks μ a G K q0 I h l b j w hwR hb.le S hS hE₀
    (fun ν => (hUniform ν).trans (hkTail k ((le_max_right _ _).trans hlarge)))

end LPPDifferentiability
