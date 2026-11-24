/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Grid.GeneralTheorem
public import Differentiability.Probability.HeavyCrossingTrials
import all Differentiability.Probability.GridCoarseGoodProbability
import Differentiability.Analysis.HeavyVertexDecay
import Differentiability.Model.Paths.GridCoarseGeneralAssembly
import Martin2004.Probability.ShapeAboveMean
import ProbabilityBasics.Probability.PositiveMomentTail
import Mathlib.Tactic

/-! # Heavy vertices and capped crossing trials

The working-region cap, the uniform block cap, and the success probabilities
and joint independence for the same fixed capped trials in Appendix B
(source label `lem:heavy` in `differentiability_final_draft.tex`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

open StairGeometry

/-- The cap `H` on the closed crossing block at its fixed rounded centre. -/
def gridTrialCap (a : ℝ) (I h : ℤ) (l m j w : ℕ) (ν : Fin (j ^ 2)) : Set Environment :=
  gridUpperCap (gridCrossingBlock a w I l m
    (coarseCrossingCentre a h w I m (ν.val + 1))) w

/-- The cap failure bound in the source, uniform in every variable within a scale. -/
noncomputable def gridHeavyTail (μ : Measure ℝ) (p : ℝ) (k : ℕ) : ℝ :=
  17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4)

/-- The fixed capped crossing event uses exactly the cap on its own block. -/
theorem gridCappedTrial_eq_inter_gridTrialCap
    (a G K : ℝ) (I h : ℤ) (l m j w : ℕ) (ν : Fin (j ^ 2)) :
    gridCappedTrial a G K I h l m j w ν =
      gridCrossingTrial a G K w I l m (coarseCrossingCentre a h w I m (ν.val + 1)) ∩
        gridTrialCap a I h l m j w ν := rfl

private theorem fixed_grid_heavy_trials
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 4 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a G K cstar q0 : ℝ) (hcstar : 1 ≤ cstar) (k j mk : ℕ) (hj : 1 ≤ j)
    (hk4 : k ≤ 4 * (k - j) + 3)
    (hcoarse : 8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤
      ((2 ^ (mk - 4 * j - 1) : ℕ) : ℝ))
    (hhalf : 1 < (2 : ℝ) ^ (mk - 4 * j - 1) →
      (2 : ℝ) ^ (mk - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2)
    (hP : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < (2 : ℝ) ^ (mk - 4 * j - 1) →
      q0 < (environmentLaw μ).real {ω : Environment |
        ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
            8 * (2 : ℝ) ^ (k - j)) ∧
          G * (n : ℝ) - K * (2 : ℝ) ^ (k - j) < pathWeight ω q})
    (I h : ℤ) :
    let l : ℕ := 2 ^ (mk - 4 * j - 1)
    let w : ℕ := 2 ^ (k - j)
    let m' := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
    (∀ ν : Fin (j ^ 2),
      (environmentLaw μ).real (gridTrialCap a I h l m' j w ν)ᶜ ≤ gridHeavyTail μ p k) ∧
    (gridHeavyTail μ p k ≤ q0 / 2 →
      iIndepSet (gridCappedTrial a G K I h l m' j w) (environmentLaw μ) ∧
      ∀ ν : Fin (j ^ 2), q0 / 2 ≤ (environmentLaw μ).real (gridCappedTrial a G K I h l m' j w ν)) := by
  classical
  intro l w m'
  have hwc : (w : ℝ) = (2 : ℝ) ^ (k - j) := by dsimp only [w]; push_cast; rfl
  have hlc : (l : ℝ) = (2 : ℝ) ^ (mk - 4 * j - 1) := by dsimp only [l]; push_cast; rfl
  have hw1 : (1 : ℝ) ≤ (w : ℝ) := by rw [hwc]; exact one_le_pow₀ (by norm_num)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hX : 1 ≤ cstar * ((j : ℝ) ^ 2 * (w : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hcstar (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) hw1)
  have hc : 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ) := hcoarse
  have hl8 : (8 : ℝ) ≤ (l : ℝ) := by nlinarith only [hc, hX]
  have hlw : (l : ℝ) ≤ (w : ℝ) ^ 3 / 2 := by rw [hlc, hwc]; exact hhalf (by rw [← hlc]; linarith)
  have hinset : (m' : ℝ) < cstar * ((j : ℝ) ^ 2 * (w : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (zero_le_one.trans hX)
  have hinsetPos : 0 < m' := Nat.ceil_pos.2 (zero_lt_one.trans_le hX)
  have htrim : 2 * m' < l := by
    exact_mod_cast (show (2 : ℝ) * (m' : ℝ) < (l : ℝ) by nlinarith only [hinset, hc, hl8, hX])
  let c (ν : Fin (j ^ 2)) := coarseCrossingCentre a h w I m' (ν.val + 1)
  choose B hB hcard using fun ν : Fin (j ^ 2) =>
    exists_grid_crossing_block_finset a w I l m' (c ν) hw1 htrim hlw
  have cap (ν : Fin (j ^ 2)) : {ω : Environment | ∀ z ∈ B ν, ω z ≤ (w : ℝ)} =
      gridTrialCap a I h l m' j w ν := by
    ext ω
    simp only [gridTrialCap, gridUpperCap, Set.mem_ofPred_eq, hB ν, c]
  have hcap (ν : Fin (j ^ 2)) :
      (environmentLaw μ).real (gridTrialCap a I h l m' j w ν)ᶜ ≤ gridHeavyTail μ p k := by
    rw [← cap]
    exact heavy_block_failure_le μ hp hmom (B ν) w k j hwc hk4 (hcard ν)
  refine ⟨hcap, fun hsmall => ?_⟩
  let n := l - 2 * m'
  let E₀ : Set Environment := gridCrossingTrial a G K w 0 n 0 0
  have hn : (n : ℝ) < (2 : ℝ) ^ (mk - 4 * j - 1) := by
    rw [← hlc]
    exact_mod_cast (show n < l by dsimp only [n]; omega)
  have hE₀ : q0 < (environmentLaw μ).real E₀ := by
    refine (hP n (by dsimp only [n]; omega) hn).trans_le (le_of_eq (congrArg (environmentLaw μ).real ?_))
    ext ω
    simp only [E₀, gridCrossingTrial, mem_ofPred_eq, Nat.sub_zero, Nat.cast_zero,
      add_zero, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, sub_zero, hwc]
    constructor
    · rintro ⟨u, hu, e, he, q, hq, hweight⟩
      exact ⟨u, e, q, hu, he, hq, hweight⟩
    · rintro ⟨u, e, q, hu, he, hq, hweight⟩
      exact ⟨u, hu, e, he, q, hq, hweight⟩
  have hE₀eq : E₀ = {ω : Environment | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = 0 ∧ d.1 + d.2 = l - 2 * m' ∧
      (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ)| ≤ 8 * (w : ℝ)) ∧
      G * ((l - 2 * m' : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x} := by
    simp only [E₀, n, gridCrossingTrial, Nat.sub_zero, Nat.cast_zero, add_zero,
      Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, sub_zero]
  have hB' (ν : Fin (j ^ 2)) (z : Lattice) := hB ν z
  have hs (ν : Fin (j ^ 2)) :
      (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ (w : ℝ)} ≤ q0 / 2 := by
    change (environmentLaw μ).real {ω : Environment | ∀ z ∈ B ν, ω z ≤ (w : ℝ)}ᶜ ≤ q0 / 2
    rw [cap]
    exact (hcap ν).trans hsmall
  obtain ⟨hind, hprob, -⟩ := heavy_crossing_trials_indep μ a G K w h hw1 I l m'
    (j ^ 2) htrim.le c
    (fun ν => (coarse_crossing_centre_spec a h w I m' (ν.val + 1)).1)
    (fun ν => (coarse_crossing_centre_spec a h w I m' (ν.val + 1)).2)
    (fun ν => gridCrossingTrial a G K w I l m' (c ν)) (fun _ => rfl) E₀ hE₀eq B hB' q0 hE₀ hs
  have hEvent : (fun ν => gridCrossingTrial a G K w I l m' (c ν) ∩
      {ω : Environment | ∀ z ∈ B ν, ω z ≤ (w : ℝ)}) = gridCappedTrial a G K I h l m' j w := by
    funext ν
    rw [cap, gridCappedTrial_eq_inter_gridTrialCap]
  rw [hEvent] at hind
  refine ⟨hind, fun ν => ?_⟩
  rw [← congrFun hEvent ν]
  exact hprob ν

/-- The heavy-vertex lemma (`lem:heavy`) on the actual characteristic record scales. The working
region and fixed trial blocks have vanishing cap failure probabilities, and
the same capped trials are jointly independent at a fixed cell and each
have success probability at least `q₀/2` at every sufficiently large record. -/
theorem heavy_grid_trials
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p' : ℝ, 1 < p' ∧ (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (p : ℝ) (hp : 4 < p)
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
    let Cm := ∫ x, max (-x) 0 ∂μ
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
      gridRecordTrials μ a G K q0 k0 m record ∧
      Tendsto (gridHeavyTail μ p) atTop (𝓝 0) ∧
      ∀ (K₁ K₃ : ℕ) (A R ε₀ : ℝ), 0 < A → 0 < R → 0 < ε₀ → ∀ J : ℕ, 1 ≤ J →
        let C₁ := 8 * cstar * (G + 2 * Cm) + 2 * K + 2 * (trimLength (slopeCutoff a) K₁ K₃ : ℝ) +
          3 * cstar + 1
        let Ehv (k : ℕ) := gridUpperCap (workingRegion a A R C₁ m k)
          (ε₀ * (2 : ℝ) ^ k / (k : ℝ))
        Tendsto (fun k : ℕ => (environmentLaw μ).real (Ehv k)ᶜ) (atTop ⊓ 𝓟 record) (𝓝 0) ∧
        ∃ k1 : ℕ, ∀ k ∈ record, k1 ≤ k →
          ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
          let l : ℕ := 2 ^ (m k - 4 * j - 1)
          let w : ℕ := 2 ^ (k - j)
          let m' := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
          8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ) →
          ∀ I : ℤ, (l : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * (2 : ℝ) ^ m k →
          ∀ h : ℤ, (∃ ρ : ℝ, (h : ℝ) * (w : ℝ) ≤ ρ ∧
            ρ < ((h : ℝ) + 1) * (w : ℝ) ∧ |ρ| ≤ R * (2 : ℝ) ^ k) →
          (∀ ν : Fin (j ^ 2),
            (environmentLaw μ).real (gridTrialCap a I h l m' j w ν)ᶜ ≤ gridHeavyTail μ p k) ∧
          iIndepSet (gridCappedTrial a G K I h l m' j w) (environmentLaw μ) ∧
          ∀ ν : Fin (j ^ 2), q0 / 2 ≤ (environmentLaw μ).real (gridCappedTrial a G K I h l m' j w ν) := by
  intro H dl dr K G Cm cstar P
  have hpos := positive_integrated_sqrt_tail_lt_top_of_moment μ
    ((by norm_num : (2 : ℝ) < 4).trans hp) hmom
  obtain ⟨k0, hk0, m, nk, record, hgrowth, hchar, hinf, hrecord, htrials⟩ :=
    characteristic_length_records μ hneg hpos g hgcont hghom hgconc hgshape a ha₀ ha₁ Gtop
      htop hgap q0 hq0₀ hq0₁
  have hG : G = g (toQuadrant (a, 1 - a)) := by
    simp only [G, H, quadrantExtension, add_zero, sub_zero]
  have htrial : gridRecordTrials μ a G K q0 k0 m record := by rw [hG]; exact htrials
  have hm3 (k : ℕ) (hk : k0 ≤ k) : m k ≤ 3 * k := (hchar k hk).2.2.1
  have hCp : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have ⟨htail, hsmall⟩ := heavy_vertex_block_tail_decay hp hCp hq0₀
  obtain ⟨kT, hkT⟩ := eventually_atTop.mp hsmall
  have hcstar : 1 ≤ cstar :=
    (by norm_num : (1 : ℝ) ≤ 100).trans (coarse_direction_facts a cstar (slopeCutoff a) rfl ha₀ ha₁ rfl).2.2.2.2.2
  have hmean : (∫ x : ℝ, x ∂μ) ≤ G := by
    have hab : a.toNNReal + (1 - a).toNNReal = 1 := by
      rw [← Real.toNNReal_add ha₀.le (sub_nonneg.mpr ha₁.le)]
      norm_num
    rw [hG]
    exact integral_le_shape_of_negative_moment_and_positive_tail μ hneg hpos g hgcont hghom
      hgconc hgshape a.toNNReal (1 - a).toNNReal hab
  have hCm : 0 ≤ Cm := integral_nonneg fun _ => le_max_right _ _
  have hGC : 0 ≤ G + 2 * Cm := by
    linarith only [hmean, hCm, neg_integral_neg_part_le_integral_grid μ]
  refine ⟨k0, m, nk, record, hk0, hinf, hgrowth, ?_, hrecord, htrial, htail, ?_⟩
  · dsimp only [P]
    rw [hG]
    exact hchar
  · intro K₁ K₃ A R ε₀ hA hR hε₀ J hJ C₁ Ehv
    have hC₁ : 0 ≤ C₁ := by
      dsimp only [C₁, K]
      positivity
    refine ⟨grid_working_cap_failure_tendsto μ hp hmom a A R C₁ ε₀ hA hR hC₁ hε₀
      k0 m record (fun k hk _ => hm3 k hk), max (4 * k0 + 3) kT, ?_⟩
    intro k hk hlarge j hJj hj l w m' hc I _ _ h _
    have hk' : 4 * k0 + 3 ≤ k := (le_max_left _ _).trans hlarge
    have hmk := hm3 k (by omega)
    have hjstar := (grid_jstar_bounds (m := m k) (rfl : ⌈((m k : ℝ) - 1) / 4⌉₊ = _)).2
    have hk4 : k ≤ 4 * (k - j) + 3 := by omega
    obtain ⟨hP, hhalf⟩ := htrial k hk hk' j hj
    obtain ⟨hcap, hsuccess⟩ := fixed_grid_heavy_trials μ hp hmom a G K cstar q0 hcstar
      k j (m k) (hJ.trans hJj) hk4 hc hhalf hP I h
    exact ⟨hcap, hsuccess (hkT k ((le_max_right _ _).trans hlarge))⟩

end LPPDifferentiability
